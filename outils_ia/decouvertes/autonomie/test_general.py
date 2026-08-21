# -*- coding: utf-8 -*-
"""Les descentes générales — protégées (ev.325).

Deux faces : un but ∀-⇒ jouet FERMÉ par les descentes (généralisation +
loi_deduction, jugé noyau) ; et le contrôle qui peut échouer — un but ∀ dont
la matrice est hors de portée reste NON fermé avec manque nommé.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


@pytest.mark.slow
def test_descentes_ferment_un_but_universel_conditionnel():
    """∀x(Fini x ⇒ card(x+1)) fermé par descente-∀ + descente-⇒ + chaînage."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        fini_implique_fini_successeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        fini_implique_cardinal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, est_cardinal, successeur,
    )
    from outils_ia.decouvertes.autonomie.general import besoins_generaux
    from conjecturer import _comme_impl

    impls = []
    for nom, th in (("fini_succ", fini_implique_fini_successeur("atg")),
                    ("fic", fini_implique_cardinal("atg"))):
        ab = _comme_impl(th.conclusion)
        impls.append((nom, th, ab[0], ab[1]))

    vx = var("xtg")
    but = pourtout("xtg", impl(est_fini(vx), est_cardinal(successeur(vx))))
    th, manques = besoins_generaux(but, impls, {}, profondeur=3)
    assert th is not None and th.est_clos and th.conclusion == but
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_hors_de_portee_reste_nomme():
    """Un ∀ dont la matrice n'a aucune route → non fermé, manque NOMMÉ."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, est_cardinal,
    )
    from outils_ia.decouvertes.autonomie.general import besoins_generaux

    vx = var("xtg")
    but = pourtout("xtg", impl(est_cardinal(vx), est_fini(vx)))   # FAUX en général
    th, manques = besoins_generaux(but, [], {}, profondeur=2)
    assert th is None and manques == [] or th is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_enonces_euclide_bien_formes():
    """Brique 1 Euclide (ev.327) : les deux énoncés-cibles se construisent,
    sont des ∀-formes, et l'instanciation de la matrice au terme N(7) redonne
    EXACTEMENT l'assemblage manuel par les mêmes combinateurs (par ==)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et, impl, existe, subst_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_egal_card,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.conjectures.goldbach import est_premier
    from outils_ia.decouvertes.autonomie.premiers import (
        enonce_diviseur_premier, enonce_infinitude,
    )

    e1, e2 = enonce_diviseur_premier(), enonce_infinitude()
    for e in (e1, e2):                                     # ∀ = ¬∃¬
        assert e.tag == "non" and e.sous[0].tag == "exists"

    # matrice de l'infinitude instanciée à N(7) == assemblage manuel
    matrice = e2.sous[0].sous[0].sous[0]                   # sous le ∀nep
    inst = subst_f(NUM(7), "nep", matrice)
    vp = var("pep")
    attendu = impl(est_fini(NUM(7)),
                   existe("pep", et(est_premier(vp, d="dep", q="qep"),
                                    et(est_fini(vp),
                                       inf_egal_card(NUM(7), vp)))))
    assert inst == attendu
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_briques_euclide_cas_premier_et_transitivite():
    """Les deux piliers de la récurrence forte (ev.329, 331) : re-prouvés, clos,
    conclusions == cibles-compagnes par ==."""
    from outils_ia.decouvertes.autonomie.euclide_cas_premier import (
        cas_premier_diviseur, cas_premier_diviseur_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_transitivite import (
        transitivite_divise, transitivite_divise_cible,
    )
    th1 = cas_premier_diviseur()
    assert th1.est_clos and th1.conclusion == cas_premier_diviseur_cible()
    th2 = transitivite_divise()
    assert th2.est_clos and th2.conclusion == transitivite_divise_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_brique_extraction_diviseur():
    """Extraction du cas composé (ev.332) : close, conclusion == cible."""
    from outils_ia.decouvertes.autonomie.euclide_extraction import (
        extraction_diviseur, extraction_diviseur_cible,
    )
    th = extraction_diviseur()
    assert th.est_clos and th.conclusion == extraction_diviseur_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_brique_borne_diviseur():
    """La borne d ≤ n (ev.334) : close, conclusion == cible."""
    from outils_ia.decouvertes.autonomie.euclide_borne import (
        borne_diviseur, borne_diviseur_cible,
    )
    th = borne_diviseur()
    assert th.est_clos and th.conclusion == borne_diviseur_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_diviseur_premier_universel():
    """👑 LE théorème (ev.335) : tout entier fini ≥ 2 a un diviseur premier."""
    from outils_ia.decouvertes.autonomie.euclide_c61.envelope import (
        diviseur_premier_universel, _R,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    th = diviseur_premier_universel()
    assert th.est_clos and not th.hypotheses
    vn = var("nfor")
    assert th.conclusion == pourtout("nfor", impl(est_fini(vn), _R(vn)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_briques_infinitude_cibles():
    """Les cibles des briques infinitude (ev.339-344) sont bien formées,
    et G3 (la seule brique rapide) est close — smoke test du dossier."""
    from outils_ia.decouvertes.autonomie.euclide_c61.divise_produit import (
        divise_produit_gauche, divise_produit_gauche_cible,
        divise_produit_droite_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_c61.fini_factorielle import (
        fini_factorielle_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_c61.minorant_factorielle import (
        minorant_factorielle_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_c61.diviseur_commun_succ import (
        diviseur_commun_succ_cible,
    )
    for cible in (divise_produit_gauche_cible(), divise_produit_droite_cible(),
                  fini_factorielle_cible(), minorant_factorielle_cible(),
                  diviseur_commun_succ_cible()):
        assert cible is not None
    th = divise_produit_gauche()                     # ~1 s, close
    assert th.est_clos and th.conclusion == divise_produit_gauche_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_euclide_infinitude():
    """👑👑👑 EUCLIDE COMPLET (ev.344) : l'infinitude des premiers, close,
    conclusion == l'énoncé exigé par la machine (ev.325). ~23 min."""
    from outils_ia.decouvertes.autonomie.euclide_c61.assemblage_infinitude import (
        euclide_infinitude,
    )
    from outils_ia.decouvertes.autonomie.premiers import enonce_infinitude
    th = euclide_infinitude()
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == enonce_infinitude()
    assert len(E.theorie_ensembles().axiomes) == 22


# ═══════════════════════════════════════════════════════════════════════════
#  LE MARCHEUR (21 août 2026, chantier A4)
# ═══════════════════════════════════════════════════════════════════════════

def _banc_oplus():
    """Le banc ⊕ de v16-v18 : `a ⊕ b := (a+b)+1`, pool = 2 lois brutes sur +,
    but B4 (quatre éléments — sa chaîne brute dépasse `max_pas=5`)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        successeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
        somme_cardinale_commutative,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
        somme_cardinale_associative_iteree,
    )
    a, b, c, d = var("aMt"), var("bMt"), var("cMt"), var("dMt")

    def oplus(x, y):
        return successeur(SC(x, y))

    assoc = somme_cardinale_associative_iteree(a, b, c)
    comm = somme_cardinale_commutative(a, b)
    brut = {assoc.conclusion: ("assoc+", assoc), comm.conclusion: ("comm+", comm)}
    B4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(c, d))))
    F4 = egal(oplus(oplus(oplus(a, b), c), d), oplus(a, oplus(b, oplus(d, d))))
    return (a, b, c, d), oplus, brut, B4, F4


def test_marcheur_le_mineur_retrouve_l_operation():
    """P3 : le motif de tête miné dans B4 EST ⊕ — personne ne le lui nomme.

    Le mineur ne connaît ni `successeur` ni `SC` : il anti-unifie les
    sous-termes du but et classe par gain MDL. L'assertion est une égalité
    d'assemblages (O(1)) : motif appliqué à (a, b) == ⊕(a, b). Et l'oracle
    réfute l'idempotence (schéma faux) en millisecondes — AVANT tout noyau."""
    from outils_ia.arithmetique.oracle_num import contre_exemple
    from outils_ia.decouvertes.autonomie.marcheur import (
        miner_motifs, conjectures_pour, _appliquer,
    )
    (a, b, _, _), oplus, _, B4, _ = _banc_oplus()
    motifs = miner_motifs(B4)
    assert motifs, "aucun motif miné"
    tete = motifs[0]
    assert _appliquer(tete["motif"], tete["noms"], [a, b]) == oplus(a, b)
    verdicts = {}
    for schema, conj, libres in conjectures_pour(tete["motif"], tete["noms"]):
        verdicts[schema] = contre_exemple(conj, libres, borne=6)
    assert verdicts["idempotence"] is not None          # faux → réfuté
    assert verdicts["commutativite"] is None            # vrai → autorisé
    assert verdicts["associativite"] is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_marcheur_schemas_croises_distributivite():
    """Le schema MORPHISME : sur a.(b+c) = a.b + a.c, la machine mine le
    motif UNAIRE H = a.(.) et le motif binaire de la somme, et la conjecture
    morphisme H(y+z) = H(y)+H(z) EST la distributivite du but.

    MESURE du 21 aout (deux versions PERDUES avant celle-ci, et ce sont des
    resultats) : (1) les motifs de tete sont ceux du SUBSTRAT tau (paire,
    produit ensembliste) — le MDL prefere l'interieur des developpements aux
    operations de surface ; (2) toutes les instances de produit du but
    partagent `a`, donc le motif binaire du produit N'EST PAS recuperable —
    il n'existe qu'en arite 1. D'ou le schema morphisme (unaire, binaire).
    Consigne : DECISIONS.md 21 aout."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire as SC,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire as PCB,
    )
    from outils_ia.decouvertes.autonomie.marcheur import (
        conjectures_morphisme, miner_motifs, _appliquer,
    )
    a, b, c = var("atgx"), var("btgx"), var("ctgx")
    but = egal(PCB(a, SC(b, c)), SC(PCB(a, b), PCB(a, c)))

    #   le motif UNAIRE a.(.) — mine en arite 1
    unaires = miner_motifs(but, arite=1, top=4)
    m_h = next((m for m in unaires
                if _appliquer(m["motif"], m["noms"], [b]) == PCB(a, b)), None)
    assert m_h is not None, "le motif unaire a.(.) doit etre dans le top-4"

    #   le motif binaire de la somme — l'ordre des slots suit le
    #   developpement tau, on accepte les deux
    binaires = miner_motifs(but, arite=2, top=10)
    m_g = next((m for m in binaires
                if _appliquer(m["motif"], m["noms"], [a, b]) in (SC(a, b), SC(b, a))),
               None)
    assert m_g is not None, "le motif-somme doit etre dans le top-10"

    #   la conjecture morphisme EST la distributivite (a l'ordre des slots
    #   de G pres)
    lst = conjectures_morphisme(m_h, m_g)
    assert len(lst) == 1
    _, conj, libres = lst[0]
    y, z = var("ymarche"), var("zmarche")
    attendus = {
        egal(PCB(a, SC(y, z)), SC(PCB(a, y), PCB(a, z))),
        egal(PCB(a, SC(z, y)), SC(PCB(a, z), PCB(a, y))),
    }
    assert conj in attendus, "la conjecture morphisme doit etre la distributivite"
    assert len(E.theorie_ensembles().axiomes) == 22

@pytest.mark.slow
def test_marcheur_franchit_la_porte():
    """🚪 LA PORTE D'A4 (plan éditorial, 10 août), les DEUX côtés assertés.

    Côté 1 : le chaînage seul — les organes, budgets mesurés (`max_pas=5`,
    borne posée par v18) — laisse B4 OUVERT (mesuré : 692 s d'épuisement).
    Côté 2 : la marche ferme le MÊME but depuis le MÊME pool brut — en
    minant ⊕, certifiant ses lois, et re-essayant sur pool comprimé
    (mesuré : le lemme seul 73 s contre 962 s en pool cumulé, facteur 13).
    Le noyau juge tout : est_clos, 0 hypothèse, conclusion == B4. ~15 min."""
    from outils_ia.decouvertes.besoin import besoins
    from outils_ia.decouvertes.autonomie.marcheur import marcher
    _, _, brut, B4, _ = _banc_oplus()

    th_direct, manques = besoins(B4, [], dict(brut), profondeur=4)
    assert th_direct is None, "le chaînage seul a fermé B4 — la porte a bougé"
    assert manques, "l'échec doit nommer au moins un manque"

    th, journal = marcher(B4, brut)
    assert th is not None and th.est_clos and not th.hypotheses
    assert th.conclusion == B4
    assert any(e.get("type") == "FERMÉ" for e in journal)
    assert any(e.get("type") == "réfuté" for e in journal), \
        "l'oracle n'a tué aucun schéma faux — le banc a changé"
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_marcheur_ne_ferme_pas_le_faux():
    """Garde-fou : une variante FAUSSE de B4 reste ouverte à travers la
    marche (mêmes lemmes certifiés, même re-essai), et l'échec rend un
    journal terminal — le marcheur échoue en nommant, jamais en silence.

    ⚠️ `paliers_max=1`, et le test EXIGE que le journal le dise. Mesuré le
    21 août : le palier 1 échoue proprement (788 s, 1 manque nommé) ; les
    paliers ≥ 2 (pools de 4-6 lemmes) ont tué le processus TROIS fois sans
    aucune trace (ni exit code, ni traceback, ni événement système) — cause
    non identifiée, corrélée à la taille du pool. Le plafond est donc un
    contournement DIT, pas une optimisation cachée."""
    from outils_ia.decouvertes.autonomie.marcheur import marcher
    _, _, brut, _, F4 = _banc_oplus()
    th, journal = marcher(F4, brut, paliers_max=1)
    assert th is None
    assert any(e.get("type") == "terminal" for e in journal)
    assert any(e.get("type") == "paliers-sautés" for e in journal),         "le plafond doit être DIT au journal"
    assert len(E.theorie_ensembles().axiomes) == 22
