"""Tests du détecteur d'axiomes jumeaux (N1 + scan).

La règle de conception de `phi_terme` : **valider toute feature map sur des
paires dont la similarité est CONNUE d'avance**.  Une feature map fausse ne lève
aucune exception — elle rend des cosinus plausibles et faux.  Ces tests sont donc
l'instrument, pas une formalité.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, app, egal, non, et, equiv, appartient, pourtout,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from outils_ia.vecteurs.phi_terme import phi, sim, taille, BudgetDepasse


def _seg_ext_avant_reparation(R):
    """La forme d'AVANT la réparation du 31 juillet 2026 : le terme ne porte PAS
    le graphe, l'axiome le mentionne LIBRE.  Deux R distincts donnent alors deux
    axiomes contradictoires sur LE MÊME terme — c'est le défaut `seg_ext`.

    ⚠️ Ce fixture reconstruit un défaut RÉPARÉ : `axiome_segment_extremite` est
    aujourd'hui clos et ne peut plus produire la paire.  Sans ce fixture, le
    détecteur n'aurait plus aucun cas positif à se mettre sous la dent, et son
    test dégénérerait en « il ne trouve rien » — ce qui ne prouve rien."""
    vE, vx, vy, vR = var("E"), var("x"), var("y"), var(R)
    terme = app("seg_ext_old", vE, vx)
    return pourtout("E", pourtout("x", pourtout("y",
        equiv(appartient(vy, terme),
              et(et(appartient(vy, vE), appartient(E.couple(vy, vx), vR)),
                 non(egal(vy, vx)))))))


def test_calibrage_ordre_des_cosinus():
    """L'ordre des similarités doit reproduire celui du prototype du 31 juillet :
    identité > défaut > même sujet > même famille > sans rapport."""
    a1 = _seg_ext_avant_reparation("R1")
    a2 = _seg_ext_avant_reparation("R2")
    identite = sim(a1, a1)
    defaut = sim(a1, a2)
    famille = sim(E.AXIOME_REUNION, E.AXIOME_INTER)
    sans_rapport = sim(E.AXIOME_VIDE, E.AXIOME_REUNION)
    assert abs(identite - 1.0) < 1e-9, "un objet doit être à cosinus 1 de lui-même"
    assert defaut > 0.95, f"la paire du défaut doit franchir 0,95 (mesuré {defaut})"
    assert defaut > famille > sans_rapport, \
        f"ordre rompu : défaut {defaut}, famille {famille}, étranger {sans_rapport}"


def test_interdit_1_etiquette_porte_tag_ET_nom():
    """Avec `tag` seul, tous les `app` se confondent et deux termes distincts
    mesurent 1,0000 — le premier bug du prototype."""
    assert sim(app("alpha", var("x")), app("beta", var("x"))) < 1.0


def test_interdit_2_les_enfants_d_un_terme_sont_dans_args():
    """Un marcheur qui lit `.termes` au lieu de `.args` s'arrête au premier
    niveau : deux termes de profondeurs différentes deviendraient identiques."""
    plat = app("f", var("x"))
    profond = app("f", app("g", app("h", var("x"))))
    assert taille(profond) > taille(plat)
    assert sim(plat, profond) < 1.0


def test_determinisme_entre_appels():
    """blake2b, pas `hash()` : celui-ci est randomisé par processus et rendrait
    tout cosinus publié non reproductible."""
    ax = E.AXIOME_PAIRE
    assert phi(ax) == phi(ax)


def test_garde_anti_tau():
    """Le budget lève plutôt que de rendre un vecteur calculé sur un arbre
    tronqué en silence."""
    try:
        phi(E.AXIOME_REUNION, budget=5)
    except BudgetDepasse:
        return
    raise AssertionError("la garde anti-τ n'a pas déclenché")


def test_scan_retrouve_le_candidat_h_iso_max():
    """👑 Le balayage doit retrouver l'unique candidat sérieux du corpus —
    deux théories caractérisant `h_iso_max` — et lui seul."""
    from outils_ia.vecteurs.scan_jumeaux import collecte, paires
    scannes, ecartees, _ = collecte()
    assert scannes and ecartees, "le balayage doit scanner ET écarter"
    jumeaux = [p for p in paires(scannes) if p["jumeaux"]]
    assert len(jumeaux) == 1, \
        f"attendu 1 paire de jumeaux, mesuré {len(jumeaux)}"
    assert jumeaux[0]["partages"] == {"h_iso_max"}, jumeaux[0]["partages"]
    assert jumeaux[0]["cos"] > 0.99


def test_mentionner_un_terme_n_est_pas_le_caracteriser():
    """🔴 RÉGRESSION (5 août 2026).  Le premier critère — « les symboles propres
    à l'axiome » — appariait `axiome_majorants_F` et `axiome_intervalle_entiers`
    parce que tous deux contiennent `interv_ent` ; or le premier ne fait que le
    MENTIONNER dans son membre droit.  Deux axiomes qui mentionnent un terme ne
    sont pas en conflit ; deux qui le DÉFINISSENT le sont."""
    from outils_ia.vecteurs.scan_jumeaux import (
        terme_caracterise, vocabulaire_de_base,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_sup_cardinal import (
        axiome_majorants_F,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        axiome_intervalle_entiers,
    )
    commun = vocabulaire_de_base()
    assert terme_caracterise(axiome_intervalle_entiers(), commun) == {"interv_ent"}
    assert "interv_ent" not in terme_caracterise(axiome_majorants_F(), commun)


def test_la_conjonction_fait_le_verdict():
    """Le cosinus SEUL ne suffit pas : le balayage contient des paires au sommet
    de l'échelle qui caractérisent des termes DIFFÉRENTS et ne doivent lever
    aucune alarme.  C'est le second membre qui transforme un score en verdict."""
    from outils_ia.vecteurs.scan_jumeaux import collecte, paires
    scannes, _, _ = collecte()
    ps = paires(scannes)
    hautes_sans_alarme = [p for p in ps if p["cos"] >= 0.99 and not p["jumeaux"]]
    assert hautes_sans_alarme, \
        "sans faux positif du score seul, la conjonction serait superflue"
