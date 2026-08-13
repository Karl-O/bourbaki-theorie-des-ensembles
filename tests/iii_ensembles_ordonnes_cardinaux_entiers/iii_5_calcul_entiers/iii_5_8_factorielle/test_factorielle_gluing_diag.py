"""Tests du diagnostic EXACT de l'obstruction de gluing factorielle (§III.5.8/6.2).

Ces tests NE dérivent aucun théorème : ils VÉRIFIENT le diagnostic exécutable
(corrige la docstring antérieure qui blâmait « y » : le binder collisionnant est « v »)
et que le noyau reste à 22 axiomes.
"""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_gluing_diag import (
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


def test_plus_aucun_point_de_rupture():
    """Depuis le fix subst (2026-07-24), le diagnostic ne trouve PLUS de rupture :
    l'ancienne « capture sur v rendue @0 » était un renommage GRATUIT (v pas libre
    sous le liant), supprimé par le court-circuit CS — rapport vide = gluing sain."""
    rap = diagnostiquer_capture()
    assert rap == {}, f"rupture réapparue : {rap}"
