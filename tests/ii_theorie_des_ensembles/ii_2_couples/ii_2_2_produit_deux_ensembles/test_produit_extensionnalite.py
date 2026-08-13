"""Tests §II.2 — EXTENSIONNALITÉ DES PRODUITS : passage couple-level → ÉGALITÉ
D'ENSEMBLES (fidélité Bourbaki, en-tête E.R.12 + formule (22)).

Pour CHAQUE résultat : on APPELLE le théorème (impératif), on vérifie la CLÔTURE
(0 hypothèse non déchargée), conclusion == cible (énoncé visé littéral), et que
theorie_ensembles() reste à 22 axiomes (aucun axiome ajouté).

Le test de (22) vérifie EN PLUS que le conséquent est l'ÉGALITÉ D'ENSEMBLES (==,
nœud '='), PAS l'équivalence d'appartenance d'un couple (anti-régression du trou
« écart de portée systématique des égalités de produits »).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
import bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_extensionnalite as M


def test_couple_decomposition_clos_et_cible():
    t = M.couple_decomposition()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == M.couple_decomposition_cible()
    # forme attendue littérale : (z∈X×Y) ⇒ z = (pr₁z, pr₂z)
    z = var("z")
    attendu = impl(_in(z, E.produit(var("X"), var("Y"))),
                   egal(z, E.couple(E.pr1(z), E.pr2(z))))
    assert t.conclusion == attendu


def test_couple_decomposition_parametrable():
    # z="t" (≠ « w », trou de congruence réservé par les tactiques du noyau).
    t = M.couple_decomposition(a="P", b="Q", z="t")
    assert t.est_clos
    assert t.conclusion == M.couple_decomposition_cible(a="P", b="Q", z="t")


def test_produit_egalite_par_couples_clos_et_cible():
    t = M.produit_egalite_par_couples()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == M.produit_egalite_par_couples_cible()
    # le conséquent est bien l'ÉGALITÉ A=B
    conseq = t.conclusion.sous[1]
    assert conseq.tag == "=" and conseq == egal(var("A"), var("B"))


def test_produit_egalite_par_couples_parametrable():
    t = M.produit_egalite_par_couples(a="P", b="Q", e="U", f="V")
    assert t.est_clos
    assert t.conclusion == M.produit_egalite_par_couples_cible(a="P", b="Q", e="U", f="V")


def test_formule_22_ensembliste_clos_et_cible():
    t = M.produit_distrib_reunion_premier_facteur_ensembliste()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == M.produit_distrib_reunion_premier_facteur_ensembliste_cible()


def test_formule_22_est_egalite_densembles_pas_couple_level():
    """ANTI-RÉGRESSION : (22) est livrée en ÉGALITÉ D'ENSEMBLES (nœud '='),
    PAS comme équivalence d'appartenance d'un couple."""
    t = M.produit_distrib_reunion_premier_facteur_ensembliste()
    X, Xp, Y = var("X"), var("Xp"), var("Y")
    A = E.reunion(E.produit(X, Y), E.produit(Xp, Y))   # (X×Y)∪(X'×Y)
    B = E.produit(E.reunion(X, Xp), Y)                 # (X∪X')×Y
    conseq = t.conclusion.sous[1]                      # conséquent de l'implication
    assert conseq.tag == "=", "le conséquent doit être une ÉGALITÉ d'ensembles"
    assert conseq == egal(A, B)                        # ÉGALITÉ FIDÈLE (formule 22)
    assert A != B                                      # membres distincts (non vacueux)


def test_formule_22_hypotheses_ambiants_honnetes():
    """Les hypothèses sont les AMBIANTS honnêtes (X⊂E, X'⊂E, Y⊂F), JAMAIS la
    conclusion elle-même."""
    t = M.produit_distrib_reunion_premier_facteur_ensembliste()
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus, et
    X, Xp, Y, Ev, Fv = var("X"), var("Xp"), var("Y"), var("E"), var("F")
    hyp = et(et(inclus(X, Ev), inclus(Xp, Ev)), inclus(Y, Fv))
    assert t.conclusion.sous[0].sous[0] == hyp   # antécédent = conjonction des ambiants


def test_theorie_inchangee_22():
    M.couple_decomposition()
    M.produit_egalite_par_couples()
    M.produit_distrib_reunion_premier_facteur_ensembliste()
    assert len(E.theorie_ensembles().axiomes) == 22


def _in(t, ens):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient
    return appartient(t, ens)
