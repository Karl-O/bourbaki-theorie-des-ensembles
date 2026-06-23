"""Test §II.3.7/§III.3 — la composée de deux bijections est une bijection.

⊢ (est_bijection_de(F,X,Y) et est_bijection_de(G,Y,Z)) ⇒ est_bijection_de(G∘F, X, Z).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_composee_bijection import (
    composee_bijection, composee_bijection_conjoints)


def test_composee_bijection_conjoints():
    """⊢_{bij(F,X,Y), bij(G,Y,Z)} est_bijection_de(G∘F, X, Z), hyps = exactement les deux."""
    vF, vG, vX, vY, vZ = var("F"), var("G"), var("X"), var("Y"), var("Z")
    t = composee_bijection_conjoints("F", "G", "X", "Y", "Z")
    comp = E.composee(vG, vF)
    assert t.conclusion == est_bijection_de(comp, vX, vZ)
    assert t.hypotheses == {est_bijection_de(vF, vX, vY),
                            est_bijection_de(vG, vY, vZ)}


def test_composee_bijection():
    """⊢ (bij(F,X,Y) et bij(G,Y,Z)) ⇒ bij(G∘F, X, Z) : THÉORÈME CLOS."""
    vF, vG, vX, vY, vZ = var("F"), var("G"), var("X"), var("Y"), var("Z")
    t = composee_bijection("F", "G", "X", "Y", "Z")
    comp = E.composee(vG, vF)
    cible = impl(et(est_bijection_de(vF, vX, vY), est_bijection_de(vG, vY, vZ)),
                 est_bijection_de(comp, vX, vZ))
    assert t.conclusion == cible
    assert t.est_clos
