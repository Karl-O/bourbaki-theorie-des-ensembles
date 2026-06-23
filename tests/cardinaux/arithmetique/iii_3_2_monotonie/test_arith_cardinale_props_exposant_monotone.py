"""Tests — §III.3.2/III.3.5 MONOTONIE de l'EXPONENTIATION cardinale
(ensembles_arith_cardinale_props_exposant_monotone).

  (0) inf_egal_transporte_cardinal      ⊢ (X ≤ Y) ⇒ (Card X ≤ Card Y)   INCONDITIONNEL.
  (1) exposant_monotone_base_conditionnel    ⊢ (𝓕(C;A) ≤ 𝓕(C;B)) ⇒ (a^c ≤ b^c).
  (2) exposant_monotone_exposant_conditionnel ⊢ (𝓕(C;A) ≤ 𝓕(D;A)) ⇒ (a^c ≤ a^d).

(1)-(2) sont CONDITIONNELS à l'injection de SUPPORTS (espaces de fonctions) ; leur
décharge (construction de cette injection) est le verrou dur reporté.  NON
tautologiques : l'hypothèse porte sur les supports, la conclusion sur leurs
cardinaux a^c/b^c.  theorie=22.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, impl
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie import (
    ensembles_arith_cardinale_props_exposant_monotone as X)


def test_theorie_intangible_22():
    """La théorie des ensembles reste à 22 axiomes (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inf_egal_transporte_cardinal_clos():
    """(0) — ⊢ (X ≤ Y) ⇒ (Card X ≤ Card Y), CLOS, conclusion EXACTE."""
    thm = X.inf_egal_transporte_cardinal()
    cible = impl(inf_egal_card(var("X"), var("Y")),
                 inf_egal_card(cardinal(var("X")), cardinal(var("Y"))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


def test_inf_egal_transporte_cardinal_non_tautologie():
    """Anti-tautologie : (X ≤ Y) (sur les ensembles) ≠ (Card X ≤ Card Y) (cardinaux)."""
    thm = X.inf_egal_transporte_cardinal()
    ante, cons = thm.conclusion.sous
    assert ante != cons


def test_inf_egal_transporte_cardinal_termes():
    """(0) tient pour des TERMES composés (supports d'applications)."""
    FCA = E.applications(var("C"), var("A"))
    FCB = E.applications(var("C"), var("B"))
    thm = X.inf_egal_transporte_cardinal(FCA, FCB)
    cible = impl(inf_egal_card(FCA, FCB), inf_egal_card(cardinal(FCA), cardinal(FCB)))
    assert thm.est_clos
    assert thm.conclusion == cible


def test_exposant_monotone_base_conditionnel():
    """(1) — ⊢ (𝓕(C;A) ≤ 𝓕(C;B)) ⇒ (a^c ≤ b^c), CLOS sous la seule hyp de support."""
    thm = X.exposant_monotone_base_conditionnel()
    FCA = E.applications(var("C"), var("A"))
    FCB = E.applications(var("C"), var("B"))
    cible = impl(inf_egal_card(FCA, FCB), inf_egal_card(cardinal(FCA), cardinal(FCB)))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible
    # NON tautologique
    assert thm.conclusion.sous[0] != thm.conclusion.sous[1]


def test_exposant_monotone_exposant_conditionnel():
    """(2) — ⊢ (𝓕(C;A) ≤ 𝓕(D;A)) ⇒ (a^c ≤ a^d), CLOS sous la seule hyp de support."""
    thm = X.exposant_monotone_exposant_conditionnel()
    FCA = E.applications(var("C"), var("A"))
    FDA = E.applications(var("D"), var("A"))
    cible = impl(inf_egal_card(FCA, FDA), inf_egal_card(cardinal(FCA), cardinal(FDA)))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible
    assert thm.conclusion.sous[0] != thm.conclusion.sous[1]
