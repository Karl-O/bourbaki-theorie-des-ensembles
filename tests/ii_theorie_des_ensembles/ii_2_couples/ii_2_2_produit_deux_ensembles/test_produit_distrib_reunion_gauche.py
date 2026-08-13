"""Tests §II.2 — distributivité du produit sur la réunion, RÉUNION SUR LE PREMIER
FACTEUR (formule (22) du Résumé E.R.12 : (X×Y)∪(X'×Y) = (X∪X')×Y), au niveau de
l'appartenance d'un couple (forme couple-level, comme le module dual A×(B∪C)).

Vérifie (honnêteté LCF stricte) : CLÔTURE (0 hyp), conclusion == l'ÉQUIVALENCE
FIDÈLE littérale entre les deux appartenances, NON-VACUITÉ (les deux membres
DIFFÈRENT), et theorie_ensembles() = 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, equiv, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
import bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_distrib_reunion_gauche as M


def _couple_in(prod):
    return appartient(E.couple(var("u"), var("v")), prod)


def test_distrib_reunion_premier_facteur_clos_et_fidele():
    t = M.couple_dans_produit_distrib_reunion_premier_facteur()
    assert t.est_clos and not t.hypotheses
    lhs = _couple_in(E.reunion(E.produit(var("X"), var("Y")),
                               E.produit(var("Xp"), var("Y"))))   # (u,v)∈(X×Y)∪(X'×Y)
    rhs = _couple_in(E.produit(E.reunion(var("X"), var("Xp")),
                               var("Y")))                          # (u,v)∈(X∪X')×Y
    assert t.conclusion == equiv(lhs, rhs)        # ÉNONCÉ FIDÈLE LITTÉRAL (formule 22)
    assert lhs != rhs                              # NON vacueux (membres distincts)


def test_alias_identique():
    # L'alias orienté « résultat » renvoie exactement le même théorème.
    assert (M.produit_distrib_reunion_premier_facteur().conclusion
            == M.couple_dans_produit_distrib_reunion_premier_facteur().conclusion)


def test_parametrable():
    t = M.couple_dans_produit_distrib_reunion_premier_facteur(
        u="x", v="y", a="P", b="Q", c="R")
    assert t.est_clos
    lhs = appartient(E.couple(var("x"), var("y")),
                     E.reunion(E.produit(var("P"), var("R")), E.produit(var("Q"), var("R"))))
    rhs = appartient(E.couple(var("x"), var("y")),
                     E.produit(E.reunion(var("P"), var("Q")), var("R")))
    assert t.conclusion == equiv(lhs, rhs)


def test_theorie_inchangee_22():
    M.couple_dans_produit_distrib_reunion_premier_facteur()
    assert len(E.theorie_ensembles().axiomes) == 22
