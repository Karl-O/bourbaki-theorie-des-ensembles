"""Tests §III.6.3 — échelle finale Hessenberg a²=a (P5a/P5b/P5c)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f, non, egal, var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p5a_psi_uwit_elimines():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_p5 import (
        negation_strict_sous_temoins_UF_plat,
    )
    t = negation_strict_sous_temoins_UF_plat()
    # conclusion = marqueur FALSUM ψ/uwit-free
    assert t.conclusion == non(egal(var("E"), var("E")))
    # aucune hyp ne mentionne ψ ni uwit
    for h in t.hypotheses:
        assert "psi" not in libres_f(h), h
        assert "uwit" not in libres_f(h), h
    # lock absent
    assert egal(E.reunion(var("S0"), var("Ucadre")), var("S0")) not in t.hypotheses
    assert t.conclusion not in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
