"""Tests — §III.3.6 : PROPOSITION 13 (soustraction cardinale).

Énoncé Bourbaki (E.III.3.6, Prop 13) :  a ≥ b ⟺ (∃c) a = b + c.
On certifie :
  • le sens RÉCIPROQUE (⇐) INCONDITIONNEL : (a = b+c) ⇒ b ≤ a, et sa forme
    existentielle ((∃c)a=b+c) ⇒ b ≤ a, plus la brique b ≤ b+c ;
  • le sens DIRECT (⇒) CONDITIONNÉ à l'existence du complément cardinal (hypothèse
    EXPLICITE, le cœur combinatoire étant reporté).
Chaque test vérifie que la conclusion certifiée EST EXACTEMENT la cible Bourbaki,
et la clôture (.est_clos), avec hypothèses résiduelles vides (sauf hyp explicite).
"""
from bourbaki.logique.formule import var, egal, existe, impl, et
from bourbaki.cardinaux import ensembles_cardinaux_props_restantes as P
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire


# ── b ≤ b+c  (brique du sens ⇐) ────────────────────────────────────────────────
def test_inf_egal_b_somme():
    """⊢ b ≤ (b + c)   (INCONDITIONNEL ; injection canonique gauche + transitivité)."""
    t = P.inf_egal_b_somme("B", "C")
    bc = somme_cardinale_binaire(var("B"), var("C"))
    assert t.conclusion == inf_egal_card(var("B"), bc)
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ── Prop 13, sens RÉCIPROQUE (⇐) ──────────────────────────────────────────────
def test_prop13_si_somme():
    """⊢ (a = b + c) ⇒ (b ≤ a)   (Prop 13 ⇐, INCONDITIONNEL)."""
    t = P.prop13_si_somme("A", "B", "C")
    bc = somme_cardinale_binaire(var("B"), var("C"))
    assert t.conclusion == impl(egal(var("A"), bc), inf_egal_card(var("B"), var("A")))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_prop13_existe_implique_inf_egal():
    """⊢ ((∃c) a = b + c) ⇒ (b ≤ a)   (Prop 13 ⇐ existentiel, INCONDITIONNEL)."""
    t = P.prop13_existe_implique_inf_egal("A", "B", "C")
    ant = existe("C", egal(var("A"), somme_cardinale_binaire(var("B"), var("C"))))
    assert t.conclusion == impl(ant, inf_egal_card(var("B"), var("A")))
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ── Card idempotent : Card(Card X) = Card X ───────────────────────────────────
def test_cardinal_idempotent():
    """⊢ Card(Card X) = Card X   (un cardinal est son propre cardinal)."""
    t = P._cardinal_idempotent_t(var("X"))
    assert t.conclusion == egal(cardinal(cardinal(var("X"))), cardinal(var("X")))
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ── Prop 13, sens DIRECT (⇒), CONDITIONNEL au complément cardinal ─────────────
def test_prop13_forward_conditionnel():
    """⊢ (a cardinal et complément cardinal) ⇒ (∃c) a = b + c   (Prop 13 ⇒, CONDITIONNEL)."""
    t = P.prop13_forward_conditionnel("B", "A", "C")
    est_card_a = existe("Xa", egal(var("A"), cardinal(var("Xa"))))
    comp = existe("C", egal(cardinal(var("A")), somme_cardinale_binaire(var("B"), var("C"))))
    goal = existe("C", egal(var("A"), somme_cardinale_binaire(var("B"), var("C"))))
    assert t.conclusion == impl(et(est_card_a, comp), goal)
    assert t.est_clos
    assert t.hypotheses == frozenset()
