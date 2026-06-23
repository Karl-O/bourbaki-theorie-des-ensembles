"""Test — Proposition 4 (E.II.42) : associativité de la composée de graphes."""
from bourbaki.logique.i_1_termes_relations.formule import var, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_composee_assoc import composee_associative


def test_composee_associative():
    th = composee_associative()
    G1, G2, G3 = var("G1"), var("G2"), var("G3")
    cible = egal(E.composee(E.composee(G3, G2), G1),
                 E.composee(G3, E.composee(G2, G1)))
    assert th.conclusion == cible
    assert th.est_clos
    assert th.hypotheses == frozenset()


def test_composee_associative_noms():
    """Variante avec d'autres noms de graphes (instances-termes)."""
    th = composee_associative("F", "G", "H")
    F, G, H = var("F"), var("G"), var("H")
    cible = egal(E.composee(E.composee(H, G), F),
                 E.composee(H, E.composee(G, F)))
    assert th.conclusion == cible
    assert th.est_clos
