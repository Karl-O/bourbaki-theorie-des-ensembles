# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_paquet.py — le rangement des hypothèses de STEP 5.

Ce que le test verrouille : après rangement, SEULES trois hypothèses mentionnent
encore le témoin U — le paquet, le témoin u∈U et le garde U⊂E∖S₀ — les trois qui
seront consommées à la sortie de portée.  Toute régression amont (une hypothèse
en U qui réapparaît) casse ici."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, appartient, inclus, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_paquet import (
    paquet_extension, contradiction_sous_paquet, _conjoints_du_paquet,
)


def test_paquet_six_conjoints():
    """Le paquet collationne 6 conjoints (canari : STEP 5 a-t-il changé ?)."""
    assert len(_conjoints_du_paquet("E", "S0", "phi0", "psi", "Ucadre", "uwit")) == 6


def test_contradiction_sous_paquet():
    """{paquet, u∈U, U⊂E∖S₀, données du maximal} ⊢ ¬(u∈U)."""
    vE, vS, vU, vu = var("E"), var("S0"), var("Ucadre"), var("uwit")
    t = contradiction_sous_paquet()
    assert t.conclusion == non(appartient(vu, vU))
    assert len(t.hypotheses) == 7
    avec_U = {h for h in t.hypotheses if "Ucadre" in libres_f(h)}
    assert avec_U == {paquet_extension(), appartient(vu, vU),
                      inclus(vU, E.difference(vE, vS))}, \
        "une hypothèse en U hors des trois consommables"
    assert not any("psi" in libres_f(h) for h in t.hypotheses
                   if h != paquet_extension()), "ψ hors du paquet"
    assert len(E.theorie_ensembles().axiomes) == 22
