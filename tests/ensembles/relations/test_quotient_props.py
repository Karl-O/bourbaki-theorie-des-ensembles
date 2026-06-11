"""Tests V9 — §II.6 THÉORÈMES du quotient (factorisation C57, décomposition
effective f=i∘b∘p, unicité = propriété universelle).

Vérifient la conclusion EXACTE (== cible) + les hypothèses EXPLICITES (jamais de
tautologie vide, jamais postulé) des théorèmes de `ensembles_quotient_props`.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, appartient, pourtout)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de
from bourbaki.ensembles.relations import ensembles_quotient_props as Q


# ════════════════════════════════════════════════════════════════════════════
# 1.  factorisation_valeur :  f = h∘p  ⊢  f(x) = h(p(x))   (C57, niveau valeur)
# ════════════════════════════════════════════════════════════════════════════
def test_factorisation_valeur():
    vf, vh, vP, vx = var("f"), var("h"), var("P"), var("x")
    t = Q.factorisation_valeur()
    # conclusion exacte : valeur(f,x) = h(p(x))
    assert t.conclusion == egal(E.valeur(vf, vx), E.valeur(vh, E.valeur(vP, vx)))
    # l'égalité de graphes f = h∘p est une hypothèse EXPLICITE (jamais postulée)
    assert egal(vf, E.composee(vh, vP)) in t.hypotheses
    # théorème NON vide : il y a de vraies hypothèses C46 + la factorisation
    assert len(t.hypotheses) >= 1 and not t.est_clos


# ════════════════════════════════════════════════════════════════════════════
# 2.  factorisation ⇒ compatible :  p(x)=p(y) ⇒ f(x)=f(y)   (C57, sens dur)
# ════════════════════════════════════════════════════════════════════════════
def test_factorisation_implique_compatible():
    vf, vh, vP, vx, vyb = var("f"), var("h"), var("P"), var("x"), var("yb")
    t = Q.factorisation_implique_compatible()
    px, py = E.valeur(vP, vx), E.valeur(vP, vyb)
    # (p(x)=p(yb)) ⇒ (f(x)=f(yb))
    assert t.conclusion == impl(egal(px, py),
                                egal(E.valeur(vf, vx), E.valeur(vf, vyb)))
    assert egal(vf, E.composee(vh, vP)) in t.hypotheses


def test_relation_Rp_def():
    vP, va, vb = var("P"), var("a"), var("b")
    R = Q.relation_Rp(vP)
    assert R(va, vb) == egal(E.valeur(vP, va), E.valeur(vP, vb))


def test_factorisation_compatible_Rp():
    vf, vh, vP, vx, vyb, vE = (var("f"), var("h"), var("P"),
                               var("x"), var("yb"), var("E"))
    t = Q.factorisation_compatible_Rp()
    px, py = E.valeur(vP, vx), E.valeur(vP, vyb)
    inner = impl(et(appartient(vx, vE), appartient(vyb, vE)),
                 impl(egal(px, py), egal(E.valeur(vf, vx), E.valeur(vf, vyb))))
    expect = pourtout("x", pourtout("yb", inner))
    assert t.conclusion == expect
    # f = h∘P parmi les hypothèses, et plusieurs conditions universelles (≥ 3 hyps)
    assert egal(vf, E.composee(vh, vP)) in t.hypotheses
    assert len(t.hypotheses) >= 3 and not t.est_clos


# ════════════════════════════════════════════════════════════════════════════
# 3.  décomposition canonique EFFECTIVE :  f = i∘b∘p ⊢ f(x) = i(b(p(x)))
# ════════════════════════════════════════════════════════════════════════════
def test_decomposition_valeur():
    vF, vb, vP, vi, vx = (var("F"), var("b"), var("P"), var("i"), var("x"))
    t = Q.decomposition_valeur()
    # valeur(F,x) = i(b(p(x)))
    assert t.conclusion == egal(E.valeur(vF, vx),
                                E.valeur(vi, E.valeur(vb, E.valeur(vP, vx))))
    # F = i∘(b∘P) hypothèse EXPLICITE (composée Bourbaki : applique p, puis b, puis i)
    assert egal(vF, E.composee(vi, E.composee(vb, vP))) in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
# 4.  UNICITÉ (propriété universelle du quotient)
# ════════════════════════════════════════════════════════════════════════════
def test_factorisation_meme_valeurs():
    vh, vhp, vP, vx = var("h"), var("hp"), var("P"), var("x")
    t = Q.factorisation_meme_valeurs()
    px = E.valeur(vP, vx)
    # h(p(x)) = h'(p(x))
    assert t.conclusion == egal(E.valeur(vh, px), E.valeur(vhp, px))
    # les DEUX factorisations sont des hypothèses explicites
    assert egal(var("f"), E.composee(vh, vP)) in t.hypotheses
    assert egal(var("f"), E.composee(vhp, vP)) in t.hypotheses


def test_surjectivite_ponctuelle_def():
    from bourbaki.logique.formule import existe
    vP, vQ = var("P"), var("Q")
    f = Q.surjectivite_ponctuelle(vP, vQ)
    vt, vx = var("t"), var("xa")
    assert f == pourtout("t", impl(appartient(vt, vQ),
                                   existe("xa", egal(vt, E.valeur(vP, vx)))))


def test_coincidence_ponctuelle_graphe_def():
    vgh, vghp, vP, vx = var("gh"), var("ghp"), var("P"), var("x")
    f = Q.coincidence_ponctuelle_graphe(vgh, vghp, vP)
    px = E.valeur(vP, vx)
    assert f == pourtout("x", egal(E.valeur(vgh, px), E.valeur(vghp, px)))


def test_coincidence_sur_quotient():
    vh, vhp, vQ = var("h"), var("hp"), var("Q")
    t = Q.coincidence_sur_quotient()
    # conclusion == egalite_valeurs_application(h, h', Q) (= hyp de valeurs de aev)
    assert t.conclusion == Q.egalite_valeurs_application(vh, vhp, vQ)
    # surjectivité ponctuelle de p est une hypothèse explicite (binder « x » interne)
    assert Q.surjectivite_ponctuelle(var("P"), vQ, t="x", x="xa") in t.hypotheses


def test_factorisation_unique():
    vh, vhp = var("h"), var("hp")
    t = Q.factorisation_unique()
    # UNICITÉ : h = h'
    assert t.conclusion == egal(vh, vhp)
    # appartenances 𝓕(Q;F) explicites (jamais postulées)
    vQ, vFb = var("Q"), var("F")
    assert appartient(vh, E.applications(vQ, vFb)) in t.hypotheses
    assert appartient(vhp, E.applications(vQ, vFb)) in t.hypotheses
    # surjectivité ponctuelle de p présente (binder « x » interne)
    assert Q.surjectivite_ponctuelle(var("P"), vQ, t="x", x="xa") in t.hypotheses
    # théorème NON vide
    assert len(t.hypotheses) >= 2 and not t.est_clos
