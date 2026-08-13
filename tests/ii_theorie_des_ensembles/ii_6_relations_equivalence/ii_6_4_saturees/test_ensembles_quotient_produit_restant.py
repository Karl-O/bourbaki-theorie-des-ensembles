"""Tests miroir — §II.6 restant : produit de relations d'équivalence, relation
induite (transitivité/réflexivité), « plus fine » préordre, saturation.

Pour les théorèmes INCONDITIONNELS on vérifie `.est_clos` (== 0 hyp = PROUVÉ) et la
conclusion-cible.  Pour les théorèmes CONDITIONNELS (salvage fort), on vérifie que
les HYPOTHÈSES sont exactement les prémisses explicites attendues (anti-affaibli :
ni plus, ni moins) ET que la conclusion est la cible (anti-tautologie : conclusion
≠ hypothèses).  theorie_ensembles() == 22 (intangible).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl, equiv, pourtout, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_4_saturees.ensembles_quotient_produit_restant import (
    relation_produit_couples, _relation_induite,
    produit_symetrique, produit_transitive, produit_relation_equivalence,
    induite_transitive, induite_reflexive_dans, induite_relation_equivalence,
    plus_fine_reflexive, plus_fine_transitive,
    saturee_implique_classe_incluse,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── §6.8 — produit de relations d'équivalence ────────────────────────────────
def test_produit_symetrique():
    th = produit_symetrique()
    R, Rp = E.rel_graphe("GR"), E.rel_graphe("GRp")
    S = relation_produit_couples(R, Rp)
    # conclusion == est_symetrique(R×R')  (la cible exacte)
    assert th.conclusion == E.est_symetrique(S, "u", "v")
    # hypothèses == {R sym, R' sym}  (exactement les prémisses, rien postulé)
    assert th.hypotheses == frozenset({
        E.est_symetrique(R, "a", "b"), E.est_symetrique(Rp, "a", "b")})
    # anti-tautologie : conclusion ≠ une simple hypothèse
    assert th.conclusion not in th.hypotheses


def test_produit_transitive():
    th = produit_transitive()
    R, Rp = E.rel_graphe("GR"), E.rel_graphe("GRp")
    S = relation_produit_couples(R, Rp)
    assert th.conclusion == E.est_transitive(S, "u", "v", "wb")
    assert th.hypotheses == frozenset({
        E.est_transitive(R, "a", "b", "c"), E.est_transitive(Rp, "a", "b", "c")})
    assert th.conclusion not in th.hypotheses


def test_produit_relation_equivalence():
    th = produit_relation_equivalence()
    R, Rp = E.rel_graphe("GR"), E.rel_graphe("GRp")
    S = relation_produit_couples(R, Rp)
    # conclusion == est_relation_equivalence(R×R')  (sym ET trans du produit)
    assert th.conclusion == E.est_relation_equivalence(S, "u", "v", "wb")
    # hypothèses == {R sym, R trans, R' sym, R' trans}
    assert th.hypotheses == frozenset({
        E.est_symetrique(R, "a", "b"), E.est_transitive(R, "a", "b", "c"),
        E.est_symetrique(Rp, "a", "b"), E.est_transitive(Rp, "a", "b", "c")})


# ── §6.6 — relation induite R_A ──────────────────────────────────────────────
def test_induite_transitive():
    th = induite_transitive()
    R = E.rel_graphe("GR")
    RA = _relation_induite(R, var("A"))
    assert th.conclusion == E.est_transitive(RA, "x", "y", "z")
    assert th.hypotheses == frozenset({E.est_transitive(R, "a", "b", "c")})
    assert th.conclusion not in th.hypotheses


def test_induite_reflexive_dans():
    th = induite_reflexive_dans()
    R = E.rel_graphe("GR")
    RA = _relation_induite(R, var("A"))
    # conclusion == est_reflexive_dans(R_A, A)  = (∀x)(R_A{x,x} ⇔ x∈A)
    assert th.conclusion == E.est_reflexive_dans(RA, var("A"), "x")
    # hypothèses == {R réflexive dans E, A⊂E ponctuel}
    a, e, x = var("A"), var("E"), var("x")
    AsubE = pourtout("x", impl(appartient(x, a), appartient(x, e)))
    assert th.hypotheses == frozenset({E.est_reflexive_dans(R, e, "x"), AsubE})


def test_induite_relation_equivalence():
    th = induite_relation_equivalence()
    R = E.rel_graphe("GR")
    RA = _relation_induite(R, var("A"))
    assert th.conclusion == E.est_relation_equivalence(RA, "x", "y", "z")
    assert th.hypotheses == frozenset({
        E.est_symetrique(R, "a", "b"), E.est_transitive(R, "a", "b", "c")})


# ── §6.7 — « plus fine » préordre ────────────────────────────────────────────
def test_plus_fine_reflexive_inconditionnel():
    th = plus_fine_reflexive()
    # INCONDITIONNEL : zéro hypothèse → est_clos
    assert th.est_clos
    assert len(th.hypotheses) == 0
    R = E.rel_graphe("GR")
    assert th.conclusion == E.plus_fine(R, R, "x", "y")


def test_plus_fine_transitive():
    th = plus_fine_transitive()
    S, T, R = E.rel_graphe("GS"), E.rel_graphe("GT"), E.rel_graphe("GR")
    assert th.conclusion == E.plus_fine(S, R, "x", "y")
    assert th.hypotheses == frozenset({
        E.plus_fine(S, T, "x", "y"), E.plus_fine(T, R, "x", "y")})
    assert th.conclusion not in th.hypotheses


# ── §6.4 — saturation ────────────────────────────────────────────────────────
def test_saturee_implique_classe_incluse():
    th = saturee_implique_classe_incluse()
    g, a, x, y = var("G"), var("A"), var("x"), var("y")
    # conclusion : (x∈A et (x,y)∈G) ⇒ y∈A   (R{x,y} = (x,y)∈G via rel_graphe)
    cible = impl(et(appartient(x, a), appartient(E.couple(x, y), g)), appartient(y, a))
    assert th.conclusion == cible
    # hypothèse : A saturée pour R  (exactement)
    assert th.hypotheses == frozenset({E.est_saturee(a, g, a, x="x")})
    # anti-tautologie : conclusion ≠ hypothèse
    assert th.conclusion not in th.hypotheses
