"""Tests §II.2 — FORMULE (23) en ÉGALITÉ D'ENSEMBLES PLEINE (fidélité Bourbaki,
Résumé E.R.12 §3 item 3d) :

    (23)   (X × Y) ∩ (X' × Y') = (X ∩ X') × (Y ∩ Y')        [ÉGALITÉ D'ENSEMBLES]

On APPELLE le théorème (impératif), on vérifie la CLÔTURE (0 hypothèse non
déchargée), conclusion == cible (énoncé visé littéral), et que theorie_ensembles()
reste à 22 axiomes (aucun axiome ajouté).

Un test VERROUILLE que le conséquent est l'ÉGALITÉ D'ENSEMBLES (nœud '='), PAS
l'équivalence d'appartenance d'un couple (anti-régression de l'« écart de portée
systématique des égalités de produits »).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, inclus, et, alpha_egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
import bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_inter_ensembliste as M


def test_formule_23_ensembliste_clos_et_cible():
    t = M.produit_inter_ensembliste()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == M.produit_inter_ensembliste_cible()


def test_formule_23_parametrable():
    t = M.produit_inter_ensembliste(a="P", b="Pp", c="Q", d="Qp", e="U", f="V")
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == M.produit_inter_ensembliste_cible(
        a="P", b="Pp", c="Q", d="Qp", e="U", f="V")


def test_formule_23_est_egalite_densembles_pas_couple_level():
    """ANTI-RÉGRESSION : (23) est livrée en ÉGALITÉ D'ENSEMBLES (nœud '='),
    PAS comme équivalence d'appartenance d'un couple."""
    t = M.produit_inter_ensembliste()
    X, Xp, Y, Yp = var("X"), var("Xp"), var("Y"), var("Yp")
    A = E.intersection(E.produit(X, Y), E.produit(Xp, Yp))      # (X×Y)∩(X'×Y')
    B = E.produit(E.intersection(X, Xp), E.intersection(Y, Yp)) # (X∩X')×(Y∩Y')
    conseq = t.conclusion.sous[1]                              # conséquent de l'implication
    assert conseq.tag == "=", "le conséquent doit être une ÉGALITÉ d'ensembles"
    assert conseq == egal(A, B)                                # ÉGALITÉ FIDÈLE (formule 23)
    assert A != B                                              # membres distincts (non vacueux)


def test_formule_23_hypotheses_ambiants_honnetes():
    """Les hypothèses sont les AMBIANTS honnêtes (X⊂E, X'⊂E, Y⊂F, Y'⊂F), JAMAIS
    la conclusion elle-même."""
    t = M.produit_inter_ensembliste()
    X, Xp, Y, Yp, Ev, Fv = (var("X"), var("Xp"), var("Y"), var("Yp"),
                            var("E"), var("F"))
    hyp = et(et(et(inclus(X, Ev), inclus(Xp, Ev)), inclus(Y, Fv)), inclus(Yp, Fv))
    # l'implication P⇒Q est désucrée en (non P) ∨ Q : l'antécédent est sous[0].sous[0]
    ante = t.conclusion.sous[0].sous[0]
    assert alpha_egal(ante, hyp)                 # antécédent = conjonction des 4 ambiants
    # cohérence stricte avec l'énoncé visé exporté
    assert ante == M.produit_inter_ensembliste_cible().sous[0].sous[0]
    # l'antécédent N'EST PAS la conclusion (= l'égalité (23)) elle-même
    assert not alpha_egal(ante, t.conclusion.sous[1])


def test_theorie_inchangee_22():
    M.produit_inter_ensembliste()
    assert len(E.theorie_ensembles().axiomes) == 22
