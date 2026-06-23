"""Tests §III.6.3 — Hessenberg a²=a, P5b (élimination Ucadre) + P5c (assemblage final).

P5b `negation_strict_sous_maximal` ⊢ ¬(Card S₀<Card E), témoin Ucadre ÉLIMINÉ, aucune
hyp ne mentionne Ucadre/psi/uwit, lock absent.
P5c `hessenberg_a_carre_egal_a_REEL` ⊢ est_infini(Card E) ⇒ Card E·Card E=Card E,
conclusion E-SEULE, aucun témoin (S0/Ucadre/phi0/psi/uwit/Smx/phimx/mmx) libre ; les
seules hypothèses résiduelles sont les 2 résidus E-niveau de frame_a_maximal (Zorn).
"""
from bourbaki.logique.formule import libres_f, non, egal, var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p5b_ucadre_elimine():
    from bourbaki.cardinaux.ensembles_hessenberg_p5c import (
        negation_strict_sous_maximal, negation_strict_sous_maximal_cible,
    )
    t = negation_strict_sous_maximal()
    assert t.conclusion == negation_strict_sous_maximal_cible()
    for h in t.hypotheses:
        f = libres_f(h)
        assert "Ucadre" not in f, h
        assert "psi" not in f, h
        assert "uwit" not in f, h
    assert egal(E.reunion(var("S0"), var("Ucadre")), var("S0")) not in t.hypotheses
    assert t.conclusion not in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p5c_hessenberg_reel():
    from bourbaki.cardinaux.ensembles_hessenberg_p5c import (
        hessenberg_a_carre_egal_a_REEL, hessenberg_a_carre_egal_a_REEL_cible,
    )
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    t = hessenberg_a_carre_egal_a_REEL()
    # conclusion LITTÉRALE = enonce_hessenberg(E), E-seule
    assert t.conclusion == enonce_hessenberg("E")
    assert t.conclusion == hessenberg_a_carre_egal_a_REEL_cible()
    # AUCUN témoin libre dans les hyps résiduelles (seules vars libres ⊆ {E})
    interdits = {"Ucadre", "psi", "uwit", "Smx", "phimx", "mmx", "S0", "phi0"}
    for h in t.hypotheses:
        assert not (interdits & set(libres_f(h))), h
        assert set(libres_f(h)) <= {"E"}, h
    # lock absent
    assert egal(E.reunion(var("S0"), var("Ucadre")), var("S0")) not in t.hypotheses
    assert t.conclusion not in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
