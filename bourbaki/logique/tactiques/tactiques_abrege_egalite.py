"""Couche égalitaire abrégée — symétrie, transitivité, congruence des termes.

Portage au niveau abrégé (∃ nœud primitif) des théorèmes 2-3 et du critère C44,
tous construits à partir du SEUL schéma S6 ⊢ (T=U) ⇒ ((T|x)R ⇔ (U|x)R) et de la
réflexivité primitive (Th1). Aucune nouvelle primitive : tout est dérivé.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, subst_t
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant, equivalence_arriere


def symetrie(t, u):
    """⊢ (T = U) ⇒ (U = T).  (Théorème 2, E.I.40.)"""
    # R{w} := (w = T) ; (T|w)R = (T=T), (U|w)R = (U=T).
    w = "w"
    R = egal(var(w), t)
    h = N.assume(egal(t, u))
    eq = N.modus_ponens(h, N.s6(t, u, w, R))           # (T=T) ⇔ (U=T)
    res = N.modus_ponens(N.reflexivite(t), equivalence_avant(eq))   # ⊢ U=T
    return N.loi_deduction(egal(t, u), res)


def transitivite(t, u, v):
    """⊢ ((T=U) et (U=V)) ⇒ (T=V).  (Théorème 3, E.I.40.) — forme à 2 prémisses."""
    # via S6 : R{w} := (T = w) ; de U=V on tire (T=U) ⇔ (T=V).
    w = "w"
    R = egal(t, var(w))
    htu = N.assume(egal(t, u))
    huv = N.assume(egal(u, v))
    eq = N.modus_ponens(huv, N.s6(u, v, w, R))         # (T=U) ⇔ (T=V)
    ttv = N.modus_ponens(htu, equivalence_avant(eq))   # {T=U, U=V} ⊢ T=V
    return ttv                                         # hypothèses {T=U, U=V}


def composer_egalites(thm_tu, thm_uv):
    """Γ⊢(T=U), Δ⊢(U=V) ⟹ Γ∪Δ ⊢ (T=V).  (transitivité appliquée à deux preuves.)"""
    t, u = thm_tu.conclusion.termes
    u2, v = thm_uv.conclusion.termes
    if u != u2:
        raise ValueError("maillon central non concordant pour la transitivité")
    w = "w"
    R = egal(t, var(w))                                # (U|w)R=(T=U), (V|w)R=(T=V)
    eq = N.modus_ponens(thm_uv, N.s6(u, v, w, R))      # (T=U) ⇔ (T=V)
    return N.modus_ponens(thm_tu, equivalence_avant(eq))


def congruence_terme(t, u, v, w="w"):
    """⊢ (T = U) ⇒ (V{T} = V{U}).  Substitutivité de = pour les termes (C44).

    V est un terme contenant la variable-trou `w` ; V{T} = (T|w)V."""
    vt = subst_t(t, w, v)
    vu = subst_t(u, w, v)
    R = egal(v, vu)                                    # (T|w)R = (Vt=Vu), (U|w)R = (Vu=Vu)
    h = N.assume(egal(t, u))
    eq = N.modus_ponens(h, N.s6(t, u, w, R))           # (Vt=Vu) ⇔ (Vu=Vu)
    res = N.modus_ponens(N.reflexivite(vu), equivalence_arriere(eq))   # ⊢ Vt=Vu
    return N.loi_deduction(egal(t, u), res)


__all__ = ["symetrie", "transitivite", "composer_egalites", "congruence_terme"]
