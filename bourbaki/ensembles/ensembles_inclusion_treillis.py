"""§II.1 — CARACTÉRISATIONS de l'inclusion par ∩ / ∪ (lien ordre ↔ treillis).

Bourbaki E.II.1 : l'inclusion ⊂ se lit dans le treillis (∪, ∩) :

    A ⊂ B   ⇔   A∩B = A          A ⊂ B   ⇔   A∪B = B

CLOSES (0 hyp).  Sens ⇒ par extensionnalité (sous l'hypothèse A⊂B, z∈A ⇔ (z∈A et z∈B),
resp. z∈B ⇔ (z∈A ou z∈B)).  Sens ⇐ par Leibniz (S6) sur l'égalité d'ensembles.
theorie_ensembles() INCHANGÉE = 22.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, appartient, et, ou, inclus, egal
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_theoremes import _instance_reunion, egalite_par_extension
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _instance_inter(a, b, z):
    return instancie(instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_INTER), a), b), z)


def _oui_g(a, b):
    """⊢ A ⇒ (A∨B)."""
    return N.s2(a, b)


def _oui_d(a, b):
    """⊢ B ⇒ (A∨B)."""
    return syllogisme(N.s2(b, a), N.s3(b, a))


def inclusion_ssi_intersection_egale(a="A", b="B"):
    """⊢ (A ⊂ B) ⇔ (A∩B = A)."""
    va, vb, vz = _t(a), _t(b), var("z")
    zA, zB = appartient(vz, va), appartient(vz, vb)
    AB = E.intersection(va, vb)
    # ── ⇒ : A⊂B ⇒ A∩B=A ──
    H = N.assume(inclus(va, vb))
    char_u = N.generalisation("z", _instance_inter(va, vb, vz))           # z∈A∩B ⇔ (z∈A et z∈B)
    cv_fwd = N.loi_deduction(zA, conjonction_intro(N.assume(zA),
                             N.modus_ponens(N.assume(zA), instancie(H, vz))))   # z∈A ⇒ (z∈A et z∈B)
    cv_bwd = N.loi_deduction(et(zA, zB), conjonction_elim_gauche(N.assume(et(zA, zB))))
    char_v = N.generalisation("z", conjonction_intro(cv_fwd, cv_bwd))    # z∈A ⇔ (z∈A et z∈B)  [sous H]
    imp1 = N.loi_deduction(inclus(va, vb), egalite_par_extension(char_u, char_v, AB, va))
    # ── ⇐ : A∩B=A ⇒ A⊂B ──
    Heq = N.assume(egal(AB, va))
    sym = N.modus_ponens(Heq, symetrie(AB, va))                          # A = A∩B
    leib = N.modus_ponens(sym, N.s6(va, AB, "w", appartient(vz, var("w"))))   # z∈A ⇔ z∈A∩B
    inter_to_zB = syllogisme(equivalence_avant(_instance_inter(va, vb, vz)),
                             N.loi_deduction(et(zA, zB), conjonction_elim_droite(N.assume(et(zA, zB)))))
    zA_to_zB = syllogisme(equivalence_avant(leib), inter_to_zB)          # z∈A ⇒ z∈B  [sous Heq]
    imp2 = N.loi_deduction(egal(AB, va), N.generalisation("z", zA_to_zB))
    return conjonction_intro(imp1, imp2)


def inclusion_ssi_reunion_egale(a="A", b="B"):
    """⊢ (A ⊂ B) ⇔ (A∪B = B)."""
    va, vb, vz = _t(a), _t(b), var("z")
    zA, zB = appartient(vz, va), appartient(vz, vb)
    AB = E.reunion(va, vb)
    # ── ⇒ : A⊂B ⇒ A∪B=B ──
    H = N.assume(inclus(va, vb))
    char_u = N.generalisation("z", _instance_reunion(va, vb, vz))        # z∈A∪B ⇔ (z∈A ou z∈B)
    cv_fwd = _oui_d(zA, zB)                                              # z∈B ⇒ (z∈A ou z∈B)
    cv_bwd = N.loi_deduction(ou(zA, zB), cas(N.assume(ou(zA, zB)), instancie(H, vz), a_implique_a(zB)))
    char_v = N.generalisation("z", conjonction_intro(cv_fwd, cv_bwd))    # z∈B ⇔ (z∈A ou z∈B)  [sous H]
    imp1 = N.loi_deduction(inclus(va, vb), egalite_par_extension(char_u, char_v, AB, vb))
    # ── ⇐ : A∪B=B ⇒ A⊂B ──
    Heq = N.assume(egal(AB, vb))
    leib = N.modus_ponens(Heq, N.s6(AB, vb, "w", appartient(vz, var("w"))))   # z∈A∪B ⇔ z∈B
    zA_to_union = syllogisme(_oui_g(zA, zB), equivalence_arriere(_instance_reunion(va, vb, vz)))  # z∈A ⇒ z∈A∪B
    zA_to_zB = syllogisme(zA_to_union, equivalence_avant(leib))          # z∈A ⇒ z∈A∪B ⇒ z∈B  [sous Heq]
    imp2 = N.loi_deduction(egal(AB, vb), N.generalisation("z", zA_to_zB))
    return conjonction_intro(imp1, imp2)


__all__ = ["inclusion_ssi_intersection_egale", "inclusion_ssi_reunion_egale"]
