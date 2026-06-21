"""Tests du diagnostic EXACT de l'obstruction de gluing factorielle (§III.5.8/6.2).

Ces tests NE dérivent aucun théorème : ils VÉRIFIENT le diagnostic exécutable
(corrige la docstring antérieure qui blâmait « y » : le binder collisionnant est « v »)
et que le noyau reste à 22 axiomes.
"""
import bourbaki.ensembles.ensembles_abrege as E
from bourbaki.entiers.ensembles_factorielle_gluing_diag import (
    binders_arithmetique_cardinale, diagnostiquer_capture,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_arithmetique_bake_binders_interdits():
    """(S2)∩(S1) : successeur ET produit bakent {u,v,y,z} ⊆ témoins du gluing."""
    info = binders_arithmetique_cardinale()
    # successeur et produit développent l'équipotence → binders {F,Z,u,up,v,y,z}
    assert "v" in info["successeur"]
    assert "v" in info["produit"]
    # l'intersection avec les témoins hardcodés du gluing contient bien v (et u,y,z)
    assert set(info["_collision"]) == {"u", "v", "y", "z"}


def test_binder_collisionnant_est_v_pas_y():
    """Le diagnostic EXÉCUTABLE confirme : capture sur « v », rendue « @0 »."""
    rap = diagnostiquer_capture()
    assert rap, "le diagnostic aurait dû atteindre le point de rupture"
    assert rap["binder_collision"] == "v"
    # côté mineure : le v littéral ; côté antécédent : capture-avoidance @0
    assert rap["mineure"][0] == "v" or rap["mineure"][1] == "v"
    assert rap["antecedent"][1] == "@0"
