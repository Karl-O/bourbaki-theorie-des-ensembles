"""Tests §III.2 — comparabilité dérivée + sens réciproque de l'iso t↦seg(t) rendu
INCONDITIONNEL (la comparabilité, hypothèse de seg_reflechit_ordre, est déchargée via
la totalité du bon ordre).  theorie=22, anti-tautologie.
"""
from bourbaki.logique.formule import var, ou, impl, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_bien_ordonne_seg_iso as S
from bourbaki.cardinaux.ensembles_bien_ordonne_lemme_1_segments import (
    seg, comparables_dans,
)


def _Rf(R="R"):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


def test_comparabilite_derivee():
    """{ bo, t∈a, s∈a } ⊢ R{t,s} ou R{s,t}  (comparabilité = théorème, pas hypothèse)."""
    comp = S.comparabilite_dans_bon_ordre()
    assert not comp.est_clos
    assert len(comp.hypotheses) == 3        # bo, t∈a, s∈a
    assert comp.conclusion == comparables_dans("R", "a", "t", "s")
    assert comp.conclusion not in comp.hypotheses


def test_reflechit_ordre_total():
    """{ bo, t∈a, s∈a } ⊢ (seg(t)⊂seg(s)) ⇒ R{t,s} ; la comparabilité N'EST PLUS
    une hypothèse (déchargée)."""
    refl = S.seg_reflechit_ordre_total()
    assert not refl.est_clos
    assert len(refl.hypotheses) == 3
    # comparabilité déchargée : comparables_dans n'est PLUS dans les hypothèses
    assert comparables_dans("R", "a", "t", "s") not in refl.hypotheses
    # conclusion = l'implication réciproque
    Rf = _Rf("R")
    from bourbaki.logique.formule import inclus
    cible = impl(inclus(seg("R", "a", "t"), seg("R", "a", "s")), Rf(var("t"), var("s")))
    assert refl.conclusion == cible
    assert refl.conclusion not in refl.hypotheses


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
