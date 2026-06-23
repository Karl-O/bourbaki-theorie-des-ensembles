"""Tests STEP B2 — pelage des témoins de la chaîne de contradiction Hessenberg."""
from bourbaki.logique.formule import libres_f, egal, non, var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.cardinaux.ensembles_frame_extension_finale import cadre_ensemble
from bourbaki.cardinaux.ensembles_hessenberg_stepb2 import (
    negation_strict_sous_temoins_UF, b2_blocker_classification,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_b1_psi_uwit_elimines():
    """B1 : ψ et uwit ÉLIMINÉS ; conclusion marqueur ; Card F=Card U + Card U≠0 honnêtes."""
    b1 = negation_strict_sous_temoins_UF()
    allfree = set().union(*[set(libres_f(h)) for h in b1.hypotheses])
    assert "psi" not in allfree, "B1 : psi encore libre dans une hyp"
    assert "uwit" not in allfree, "B1 : uwit encore libre dans une hyp"
    assert allfree <= {"E", "S0", "Ucadre", "phi0"}, f"B1 : vars inattendues {allfree}"
    # lock absent
    lock = egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))
    assert lock not in b1.hypotheses
    # hyps honnêtes apparues
    F = cadre_ensemble("S0", "Ucadre")
    assert egal(cardinal(F), cardinal(var("Ucadre"))) in b1.hypotheses
    assert non(egal(cardinal(var("Ucadre")), cardinal(E.VIDE))) in b1.hypotheses
    # conclusion = marqueur falsum
    assert b1.conclusion == non(egal(var("E"), var("E")))


def test_b2_blocker_classification():
    """B2 : verdict mécanique — 4 hyps Ucadre sont le MUR disjoint-sum irréductible."""
    b1, table = b2_blocker_classification()
    assert len(table) == 9
    mur = [t for t in table if not t["dischargeable"]]
    assert len(mur) == 4, f"attendu 4 hyps-mur, vu {len(mur)}"
    # toutes les hyps-mur mentionnent Ucadre ⇒ existe_elimination(Ucadre) impossible
    for t in mur:
        assert "Ucadre" in t["free"]
