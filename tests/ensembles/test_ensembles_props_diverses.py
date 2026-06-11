"""Tests V9 — Propositions diverses §III.3.2 : INVARIANCE de ≤ par équipotence.

On vérifie pour chaque théorème : (a) il est CLOS (.est_clos), (b) 0 hypothèse,
(c) sa conclusion est LITTÉRALEMENT la cible attendue (anti-affaibli strict), et
(d) la théorie reste à 22 axiomes (rien postulé)."""
from __future__ import annotations

from bourbaki.logique.formule import var, et, impl, equiv
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, equipotent
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.ensembles.ensembles_props_diverses import (
    equipotence_implique_inf_egal_inverse,
    equipotents_mutuellement_inf_egal,
    inf_egal_invariant_gauche,
    inf_egal_invariant_droite,
    inf_egal_invariant_equipotence,
    inf_egal_equivalence_gauche,
    inf_egal_equivalence_droite,
)


def _clos0(t):
    return t.est_clos and len(t.hypotheses) == 0


def test_theorie_intangible():
    # theorie_ensembles() doit rester à 22 axiomes (aucun axiome introduit)
    assert len(theorie_ensembles().axiomes) == 22


def test_equipotence_implique_inf_egal_inverse():
    # ⊢ Eq(X,Y) ⇒ (Y ≤ X)
    t = equipotence_implique_inf_egal_inverse("X", "Y")
    cible = impl(equipotent(var("X"), var("Y")),
                 inf_egal_card(var("Y"), var("X")))
    assert _clos0(t) and t.conclusion == cible


def test_equipotents_mutuellement_inf_egal():
    # ⊢ Eq(X,Y) ⇒ (X ≤ Y et Y ≤ X)
    t = equipotents_mutuellement_inf_egal("X", "Y")
    cible = impl(equipotent(var("X"), var("Y")),
                 et(inf_egal_card(var("X"), var("Y")),
                    inf_egal_card(var("Y"), var("X"))))
    assert _clos0(t) and t.conclusion == cible


def test_inf_egal_invariant_gauche():
    # ⊢ Eq(X,X') ⇒ ((X ≤ Y) ⇒ (X' ≤ Y))
    t = inf_egal_invariant_gauche("X", "Xp", "Y")
    cible = impl(equipotent(var("X"), var("Xp")),
                 impl(inf_egal_card(var("X"), var("Y")),
                      inf_egal_card(var("Xp"), var("Y"))))
    assert _clos0(t) and t.conclusion == cible


def test_inf_egal_invariant_droite():
    # ⊢ Eq(Y,Y') ⇒ ((X ≤ Y) ⇒ (X ≤ Y'))
    t = inf_egal_invariant_droite("X", "Y", "Yp")
    cible = impl(equipotent(var("Y"), var("Yp")),
                 impl(inf_egal_card(var("X"), var("Y")),
                      inf_egal_card(var("X"), var("Yp"))))
    assert _clos0(t) and t.conclusion == cible


def test_inf_egal_invariant_equipotence():
    # 🎯 ⊢ (Eq(X,X') et Eq(Y,Y')) ⇒ ((X ≤ Y) ⇒ (X' ≤ Y'))
    t = inf_egal_invariant_equipotence("X", "Xp", "Y", "Yp")
    cible = impl(et(equipotent(var("X"), var("Xp")),
                    equipotent(var("Y"), var("Yp"))),
                 impl(inf_egal_card(var("X"), var("Y")),
                      inf_egal_card(var("Xp"), var("Yp"))))
    assert _clos0(t) and t.conclusion == cible


def test_inf_egal_equivalence_gauche():
    # ⊢ Eq(X,Y) ⇒ ((X ≤ Z) ⇔ (Y ≤ Z))
    t = inf_egal_equivalence_gauche("X", "Y", "Z")
    cible = impl(equipotent(var("X"), var("Y")),
                 equiv(inf_egal_card(var("X"), var("Z")),
                       inf_egal_card(var("Y"), var("Z"))))
    assert _clos0(t) and t.conclusion == cible


def test_inf_egal_equivalence_droite():
    # ⊢ Eq(X,Y) ⇒ ((Z ≤ X) ⇔ (Z ≤ Y))
    t = inf_egal_equivalence_droite("Z", "X", "Y")
    cible = impl(equipotent(var("X"), var("Y")),
                 equiv(inf_egal_card(var("Z"), var("X")),
                       inf_egal_card(var("Z"), var("Y"))))
    assert _clos0(t) and t.conclusion == cible


def test_pas_tautologie():
    # anti-tautologie : la conclusion de l'invariance pleine n'est PAS de la forme P⇒P.
    # impl(A,B) se désucre en ou(non(A), B) ; on récupère A (positif) et B.
    t = inf_egal_invariant_equipotence("X", "Xp", "Y", "Yp")
    cible = t.conclusion
    assert cible.tag == "ou"
    ante_pos = cible.sous[0].sous[0]   # A dans ou(non(A), B)
    cons = cible.sous[1]               # B
    # A = (Eq(X,X') et Eq(Y,Y'))  ;  B = ((X≤Y) ⇒ (X'≤Y'))  ;  A ≠ B
    assert ante_pos != cons
