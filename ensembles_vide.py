"""§II — caractérisation de l'ensemble vide : A=∅ ⇔ (∀z)¬(z∈A).

Brique réutilisée partout (≠∅ ⇔ a un élément). Forward = Leibniz sur AXIOME_VIDE ;
backward = double inclusion (ex falso + axiome du vide) puis extensionnalité A1.
"""
from __future__ import annotations

from formule import Terme, var, egal, non, impl, appartient, pourtout, existe, inclus
import noyau_abrege as N
from tactiques_abrege2 import (conjonction_intro, equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, contraposition, dni, dne,
                               instanciation_en_x)
import ensembles_abrege as E
from tactiques_abrege_egalite import symetrie
from tactiques_abrege_quantif import congruence_existe
from ensembles_theoremes import extensionnalite_appliquee


def vide_ssi_sans_element(a="A"):
    """⊢ (A = ∅) ⇔ (∀z)¬(z ∈ A).   (a : variable-nom ou terme quelconque sans z libre.)

    Liant fixé à « z » (cohérent avec inclus/A1 utilisés par l'extensionnalité)."""
    vA, vz = (a if isinstance(a, Terme) else var(a)), var("z")
    sans = pourtout("z", non(appartient(vz, vA)))             # (∀z)¬(z∈A)
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)  # (∀z)¬(z∈∅)

    # ── sens direct : A=∅ ⇒ (∀z)¬(z∈A) ─────────────────────────────────────────
    h = N.assume(egal(vA, E.VIDE))
    vide_egal_a = N.modus_ponens(h, symetrie(vA, E.VIDE))     # ∅=A
    leib = N.s6(E.VIDE, vA, "W", pourtout("z", non(appartient(vz, var("W")))))
    equ = N.modus_ponens(vide_egal_a, leib)                  # (∀z)¬(z∈∅) ⇔ (∀z)¬(z∈A)
    fwd = N.loi_deduction(egal(vA, E.VIDE),
                          N.modus_ponens(ax_vide, equivalence_avant(equ)))

    # ── réciproque : (∀z)¬(z∈A) ⇒ A=∅ ─────────────────────────────────────────
    hs = N.assume(sans)
    nzA = N.modus_ponens(hs, instanciation_en_x(non(appartient(vz, vA)), "z"))   # ¬(z∈A)
    a_sub_vide = N.generalisation("z", N.modus_ponens(
        nzA, N.s2(non(appartient(vz, vA)), appartient(vz, E.VIDE))))             # A⊂∅
    nz0 = N.modus_ponens(ax_vide, instanciation_en_x(non(appartient(vz, E.VIDE)), "z"))
    vide_sub_a = N.generalisation("z", N.modus_ponens(
        nz0, N.s2(non(appartient(vz, E.VIDE)), appartient(vz, vA))))             # ∅⊂A
    ext = extensionnalite_appliquee(vA, E.VIDE)              # (A⊂∅ et ∅⊂A) ⇒ A=∅
    bwd = N.loi_deduction(sans, N.modus_ponens(
        conjonction_intro(a_sub_vide, vide_sub_a), ext))

    return conjonction_intro(fwd, bwd)


def _equiv_neg(thm_pq):
    """⊢ (P⇔Q) ⟹ ⊢ (¬P ⇔ ¬Q)  (congruence de la négation)."""
    return conjonction_intro(contraposition(equivalence_arriere(thm_pq)),
                             contraposition(equivalence_avant(thm_pq)))


def non_vide_ssi_element(a="A"):
    """⊢ ¬(A = ∅) ⇔ (∃z)(z ∈ A).   (a : variable-nom ou terme sans z libre.)"""
    vA, vz = (a if isinstance(a, Terme) else var(a)), var("z")
    R = appartient(vz, vA)
    neg_vide = _equiv_neg(vide_ssi_sans_element(vA))   # ¬(A=∅) ⇔ ¬(∀z)¬R   [= ¬¬(∃z)¬¬R]
    P = existe("z", non(non(R)))                       # (∃z)¬¬R
    step1 = conjonction_intro(dne(P), dni(P))          # ¬¬P ⇔ P   (¬(∀z)¬R ⇔ (∃z)¬¬R)
    step2 = congruence_existe(conjonction_intro(dne(R), dni(R)), "z")   # (∃z)¬¬R ⇔ (∃z)R
    bridge = equivalence_transitivite(step1, step2)    # ¬(∀z)¬R ⇔ (∃z)R
    return equivalence_transitivite(neg_vide, bridge)  # ¬(A=∅) ⇔ (∃z)(z∈A)


__all__ = ["vide_ssi_sans_element", "non_vide_ssi_element"]
