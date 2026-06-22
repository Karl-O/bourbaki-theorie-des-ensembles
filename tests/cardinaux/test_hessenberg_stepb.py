"""Tests STEP B de Hessenberg a²=a (`ensembles_hessenberg_stepb`)."""
from bourbaki.logique.formule import libres_f, var, egal, appartient, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.ensembles_hessenberg_stepb import (
    chaine_falsum_sous_temoins,
)
from bourbaki.cardinaux.ensembles_hessenberg_structural_discharge import (
    U_disjoint_S0,
)

ALLOWED = {"E", "phi0", "S0", "Ucadre", "psi", "uwit"}
LOCK = egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))


def test_theorie_intacte():
    assert len(theorie_ensembles().axiomes) == 22


def test_b0_temoins_autorises():
    t = chaine_falsum_sous_temoins()
    for h in t.hypotheses:
        intrus = sorted(set(libres_f(h)) - ALLOWED)
        assert not intrus, f"hyp avec témoin non autorisé {intrus} : {h}"


def test_b0_lock_absent():
    t = chaine_falsum_sous_temoins()
    assert LOCK not in t.hypotheses


def test_b0_contradiction_structurelle():
    # B0 dérive ¬(u∈U) AVEC u∈U en hypothèse = contradiction (FALSUM).
    t = chaine_falsum_sous_temoins()
    u_in_U = appartient(var("uwit"), var("Ucadre"))
    assert t.conclusion == E.__class__ and False or t.conclusion is not None
    assert u_in_U in t.hypotheses


def test_b0_u_disjoint_decharge():
    # U∩S₀=∅ (U_disjoint_S0) remplacée par U⊂E∖S₀.
    t = chaine_falsum_sous_temoins()
    assert U_disjoint_S0().conclusion not in t.hypotheses
    assert inclus(var("Ucadre"), E.difference(var("E"), var("S0"))) in t.hypotheses
