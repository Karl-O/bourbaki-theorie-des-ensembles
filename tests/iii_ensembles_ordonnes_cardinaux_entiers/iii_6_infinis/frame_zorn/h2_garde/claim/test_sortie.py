# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_sortie.py — la contradiction et sa forme de sortie."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, inclus, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_sortie import (
    u_non_vide, non_strict_sous_garde,
)


def test_u_non_vide():
    """{Card U = Card S₀, S₀ infini} ⊢ ¬(U = ∅)."""
    t = u_non_vide()
    assert t.conclusion == non(egal(var("Ucadre"), E.VIDE))
    assert len(t.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_non_strict_sous_garde():
    """🎯 ⊢ ¬(Card S₀ < Card E) — et la conclusion est libre de U, ψ, u."""
    vE, vS, vU = var("E"), var("S0"), var("Ucadre")
    t = non_strict_sous_garde()
    assert t.conclusion == non(inf_strict_card(cardinal(vS), cardinal(vE)))
    for nom in ("Ucadre", "psi", "z"):
        assert nom not in libres_f(t.conclusion)
    #  exactement trois hypothèses dépendent du témoin U : le paquet, le
    #  cardinal de U et le garde — les trois qui seront consommées.
    avec_U = [h for h in t.hypotheses if "Ucadre" in libres_f(h)]
    assert len(avec_U) == 3, "hypothèses en U : %d" % len(avec_U)
    assert inclus(vU, E.difference(vE, vS)) in avec_U
    assert egal(cardinal(vU), cardinal(vS)) in avec_U
