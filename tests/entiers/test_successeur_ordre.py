"""Tests de (∗) ordre & successeur (§III.4-5) :  x ≤ b+1 ⟺ (x≤b ou x=b+1)."""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
    successeur_ordre, successeur_ordre_enonce,
    successeur_ordre_reciproque,
    succ_pas_inf_egal, succ_pas_inf_egal_enonce,
    successeur_ordre_strict, successeur_ordre_strict_enonce_fini,
)
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles


def test_successeur_ordre_clos():
    """(∗) : est_cardinal(x) ⇒ ( x≤b+1 ⟺ (x≤b ou x=b+1) )  CLOS, 0 hyp."""
    t = successeur_ordre("x", "b")
    assert t.est_clos
    assert len(t.hypotheses) == 0
    assert t.conclusion == successeur_ordre_enonce("x", "b")


def test_successeur_ordre_reciproque_clos():
    """(x≤b ou x=b+1) ⇒ x≤b+1  CLOS, 0 hyp."""
    t = successeur_ordre_reciproque("x", "b")
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_succ_pas_inf_egal_clos():
    """est_fini(b) ⇒ ¬(b+1 ≤ b)   (b+1 ∉ [0,b])  CLOS, 0 hyp."""
    t = succ_pas_inf_egal("b")
    assert t.est_clos
    assert len(t.hypotheses) == 0
    assert t.conclusion == succ_pas_inf_egal_enonce("b")


def test_successeur_ordre_strict_clos():
    """Prop 2 forme strict : (est_card(x) et est_fini(b)) ⇒ (x<b+1 ⟺ x≤b)  CLOS, 0 hyp."""
    t = successeur_ordre_strict("x", "b")
    assert t.est_clos
    assert len(t.hypotheses) == 0
    assert t.conclusion == successeur_ordre_strict_enonce_fini("x", "b")


def test_theorie_inchangee():
    """L'axiomatique reste à 22 axiomes (noyau intact)."""
    assert len(theorie_ensembles().axiomes) == 22
