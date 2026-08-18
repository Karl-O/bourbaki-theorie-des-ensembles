"""§III.4.3 — VARIANTE 4 : récurrence DESCENDANTE (E III.33 L.34 - E III.34 L.7).

Bourbaki : « Soient a, b deux entiers, a≤b, R{n} telle que R{b} et
(∀n)((a≤n<b et R{n+1}) ⇒ R{n}). Alors (∀n)((a≤n≤b) ⇒ R{n}). On a en effet
(a≤n<b et ¬R{n}) ⇒ ¬R{n+1} [contraposée] ; si, pour un n∈[a,b], on avait ¬R{n},
on déduirait de 3) [variante 3 ascendante] ¬R{b}, contraire à R{b}. »

RÉDUCTION À LA VARIANTE 3 (le livre) :
  · `pas_ascendant_non_R` : de la prémisse descendante, par contraposition,
        (∀m)((Fini m et a≤m et m<b et ¬R{m}) ⇒ ¬R{m+1}) ;
  · pour n∈[a,b] fixé : par l'absurde, ¬R{n} + le pas ascendant + recurrence_intervalle
    appliquée à ¬R sur [n,b] donnent ¬R{b} (en m=b), contredisant R{b}, d'où R{n} (DNE).

Hypothèses honnêtes : { hypothese_recurrence_descendante(R,a,b), est_cardinal(a),
est_fini(b), predecesseur_fini_universel }.  theorie_ensembles == 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, egal)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu, contraposition)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_transitive_general)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    inf_egal_reflexif)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    hypothese_recurrence_descendante, conclusion_recurrence_descendante,
    hypothese_recurrence_intervalle)


def _ex_falso(thm_a, thm_na, cible):
    imp = N.modus_ponens(thm_na, N.s2(non(thm_a.conclusion), cible))
    return N.modus_ponens(thm_a, imp)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _trans(u, v, w):
    g = inf_egal_transitive_general("Xt4", "Yt4", "Zt4")
    return instancie(instancie(instancie(g, u), v), w)


# @livre Ch.III §4.3 Demo.- | E III.34 L.2-3 | PDF p.137  (« (a≤n<b et ¬R{n}) ⇒ ¬R{n+1} » — contraposée)
def pas_ascendant_non_R(R, a="ades", b="bdes", m="mdes"):
    """{ hypothese_recurrence_descendante(R,a,b) }
        ⊢ (∀m)((Fini m et a≤m et m<b et ¬R{m}) ⇒ ¬R{m+1}).

    Contraposée du pas descendant : sous (Fini m et a≤m et m<b), R{m+1}⇒R{m},
    donc ¬R{m}⇒¬R{m+1}."""
    va, vb, vm = var(a), var(b), var(m)
    sm = successeur(vm)
    hyp = hypothese_recurrence_descendante(R, va, vb, "ndes")
    desc = conjonction_elim_droite(N.assume(hyp))       # (∀n)((Fini n et a≤n et n<b et R{n+1})⇒R{n})

    guards = et(et(est_fini(vm), inf_egal_card(va, vm)), inf_strict_card(vm, vb))
    ante = et(guards, non(R(vm)))                       # (Fini m et a≤m et m<b) et ¬R{m}
    hA = N.assume(ante)
    g = conjonction_elim_gauche(hA)                     # guards
    desc_m = instancie(desc, vm)                        # (guards et R{m+1}) ⇒ R{m}
    # curry : sous guards, R{m+1} ⇒ R{m}
    hRsm = N.assume(R(sm))
    Rm = N.modus_ponens(conjonction_intro(g, hRsm), desc_m)
    imp_desc = N.loi_deduction(R(sm), Rm)              # R{m+1} ⇒ R{m}
    nRsm = N.modus_ponens(conjonction_elim_droite(hA), contraposition(imp_desc))  # ¬R{m+1}
    res = N.generalisation(m, N.loi_deduction(ante, nRsm))
    assert res.hypotheses == frozenset({hyp}), "pas ascendant ¬R : hyps ≠ {hyp desc}"
    return res


# @livre Ch.III §4.3 Rem.4 | E III.33 L.34-36 | PDF p.136
# @livre Ch.III §4.3 Demo.- | E III.34 L.1-7 | PDF p.137  (« variante 3 sur ¬R + contradiction » — DÉRIVÉ)
# @livre Ch.III §4.3 Demo.- | E III.34 L.4-12 | PDF p.137  (démonstration de recurrence_descendante)
def recurrence_descendante(R, a="ades", b="bdes"):
    """🎯🎯 VARIANTE 4 (« récurrence descendante », E III.33-34) — DÉRIVÉE via la variante 3 :

        { hypothese_recurrence_descendante(R,a,b), est_fini(b), predecesseur_fini_universel }
        ⊢ (∀n)( (n entier et a≤n≤b) ⇒ R{n} ).

    Pour n∈[a,b] fixé, par l'absurde : ¬R{n} + le pas ascendant de ¬R (contraposée)
    + recurrence_intervalle(¬R) sur [n,b] donnent ¬R{b} (en m=b), contredisant R{b}."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_intervalle_preuve import (
        recurrence_intervalle)
    va, vb = var(a), var(b)
    hyp = hypothese_recurrence_descendante(R, va, vb, "ndes")
    Rb = conjonction_elim_gauche(N.assume(hyp))         # R{b}
    fini_b = N.assume(est_fini(vb))
    asc = pas_ascendant_non_R(R, a, b, "mdes")          # {hyp} ⊢ pas ascendant de ¬R (avec a≤m)

    def Rp(t):
        return non(R(t))

    # n∈[a,b] fixé — on applique recurrence_intervalle DIRECTEMENT à la base n (=var("nfin"))
    # et la borne b : pas de generalise/instancie (qui α-renommerait les liants internes).
    vn = var("nfin")
    ri = recurrence_intervalle(Rp, a="nfin", b=b)   # {H_int(¬R,n,b), card(n), pred} ⊢ concl_int(¬R,n,b)
    ante = et(et(est_fini(vn), inf_egal_card(va, vn)), inf_egal_card(vn, vb))
    hAnte = N.assume(ante)
    fini_n = conjonction_elim_gauche(conjonction_elim_gauche(hAnte))
    a_le_n = conjonction_elim_droite(conjonction_elim_gauche(hAnte))
    n_le_b = conjonction_elim_droite(hAnte)
    card_n = conjonction_elim_gauche(fini_n)

    # H_int(¬R, n, b) = ¬R{n} et (pas ascendant sur [n,b), binder "nint")
    h_nR_n = N.assume(non(R(vn)))
    vm = var("nint")
    sm = successeur(vm)
    ante_m = et(et(et(est_fini(vm), inf_egal_card(vn, vm)), inf_strict_card(vm, vb)), non(R(vm)))
    hAm = N.assume(ante_m)
    fini_m = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hAm)))
    n_le_m = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hAm)))
    m_lt_b = conjonction_elim_droite(conjonction_elim_gauche(hAm))
    nR_m = conjonction_elim_droite(hAm)
    a_le_m = N.modus_ponens(conjonction_intro(a_le_n, n_le_m), _trans(va, vn, vm))   # a≤m
    asc_m = instancie(asc, vm)                          # (Fini m et a≤m et m<b et ¬R{m})⇒¬R{m+1}
    nR_sm = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_intro(fini_m, a_le_m), m_lt_b), nR_m), asc_m)
    asc_step_n = N.generalisation("nint", N.loi_deduction(ante_m, nR_sm))
    asc_hyp = conjonction_intro(h_nR_n, asc_step_n)     # == H_int(¬R, n, b)  (vérifié structurellement)

    # décharger les hypothèses H_int(¬R,n,b) et card(n) de ri  →  concl_int(¬R,n,b)
    hyp_int_nb = hypothese_recurrence_intervalle(Rp, vn, vb, "nint")
    concl_int_nb = _cut(_cut(ri, hyp_int_nb, asc_hyp), est_cardinal(vn), card_n)  # (∀m)((Fini m et n≤m et m≤b)⇒¬R{m})

    b_le_b = instancie(N.generalisation("Xr4", inf_egal_reflexif("Xr4")), vb)   # b≤b
    concl_at_b = instancie(concl_int_nb, vb)            # (Fini b et n≤b et b≤b)⇒¬R{b}
    nR_b = N.modus_ponens(
        conjonction_intro(conjonction_intro(fini_b, n_le_b), b_le_b), concl_at_b)  # ¬R{b}

    # contradiction R{b}/¬R{b} → R{n}  (par tiers exclu)
    br_neg = N.loi_deduction(non(R(vn)), _ex_falso(Rb, nR_b, R(vn)))   # ¬R{n} ⇒ R{n}
    R_n = cas(tiers_exclu(R(vn)), a_implique_a(R(vn)), br_neg)         # R{n}
    res = N.generalisation("nfin", N.loi_deduction(ante, R_n))

    assert res.conclusion == conclusion_recurrence_descendante(R, va, vb, "nfin"), \
        "variante 4 : conclusion inattendue"
    return res


__all__ = ["pas_ascendant_non_R", "recurrence_descendante"]
