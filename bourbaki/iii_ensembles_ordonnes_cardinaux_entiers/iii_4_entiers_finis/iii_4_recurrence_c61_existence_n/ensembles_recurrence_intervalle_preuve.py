"""§III.4.3 — VARIANTE 3 : récurrence limitée à un intervalle [a,b] (E III.33 L.27-33).

Bourbaki (E III.33 3)) : « Soient a, b deux entiers tels que a ≤ b, R{n} une
relation telle que R{a} et (∀n)((n entier et a≤n<b et R{n}) ⇒ R{n+1}) soient
vraies. Alors (∀n)((n entier et a≤n≤b) ⇒ R{n}) est vraie. On procède comme dans
le cas précédent [variante 2], en prenant pour S{n} la relation (a≤n≤b) ⇒ R{n}. »

Miroir de la variante 2 (« à partir de k »), avec en plus la borne supérieure b :
  (1) S{0} = (a≤0 et 0≤b) ⇒ R{0}  : sous a≤0, comme 0≤a, a=0 (antisym), R{0}=R{a} ;
  (2) S{n} ⇒ S{n+1} sous (a≤n+1 et n+1≤b) : de n+1≤b on tire n≤b (n≤n+1≤b) et n<b
      (n≠b car n+1≤b et succ_pas_inf_egal) ; disjonction sur a≤n — si a≤n alors
      a≤n≤b donne R{n} [S{n}] puis a≤n<b donne R{n+1} [prémisse] ; sinon a=n+1,
      R{n+1}=R{a} ;
  (3) C61 (principe_recurrence_preuve) sur S, puis décurryfiage → conclusion.

Hypothèses honnêtes : { hypothese_recurrence_intervalle(R,a,b), est_cardinal(a),
predecesseur_fini_universel }.  theorie_ensembles == 22, rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, egal, impl)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu, equivalence_avant, equivalence_arriere, contraposition)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal, cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_bornes import (
    zero_inf_egal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card, inf_egal_transitive_general)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_c58_ordre_strict import (
    c58_ordre_strict)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    inf_egal_reflexif)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, est_fini, successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero, cardinal_vide_egale_vide)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
    successeur_ordre_strict, succ_pas_inf_egal, successeur_ordre)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    hypothese_recurrence_intervalle, conclusion_recurrence_intervalle)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def _ex_falso(thm_a, thm_na, cible):
    imp = N.modus_ponens(thm_na, N.s2(non(thm_a.conclusion), cible))
    return N.modus_ponens(thm_a, imp)


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        antecedent_consequent)
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _antisym(u, v):
    g = inf_egal_antisymetrique_card("uas3", "vas3")
    return instancie(instancie(g, u), v)


def _trans(u, v, w):
    g = inf_egal_transitive_general("Xt3", "Yt3", "Zt3")
    return instancie(instancie(instancie(g, u), v), w)


def _zero_le(t):
    """⊢ 0 ≤ t  (borne inférieure, inconditionnel)."""
    le_vide = instancie(N.generalisation("A", zero_inf_egal("A")), t)
    vide_eq_zero = N.modus_ponens(cardinal_vide_egale_vide(),
                                  symetrie(cardinal(E.VIDE), E.VIDE))
    leib0 = N.s6(E.VIDE, cardinal(E.VIDE), "wz3", inf_egal_card(var("wz3"), t))
    return N.modus_ponens(le_vide, equivalence_avant(N.modus_ponens(vide_eq_zero, leib0)))


def s_intervalle(R, a, b, n):
    """S{n} := (a ≤ n  et  n ≤ b) ⇒ R{n}."""
    va = a if not isinstance(a, str) else var(a)
    vb = b if not isinstance(b, str) else var(b)
    vn = n if not isinstance(n, str) else var(n)
    return impl(et(inf_egal_card(va, vn), inf_egal_card(vn, vb)), R(vn))


# @livre Ch.III §4.3 Rem.3 | E III.33 L.27-33 | PDF p.136
# @livre Ch.III §4.3 Demo.- | E III.33 L.32-32 | PDF p.136  (S{0} — DÉRIVÉ)
def s_intervalle_en_zero(R, a="aint", b="bint"):
    """🎯 { R{a}, est_cardinal(a) } ⊢ S{0} = (a≤0 et 0≤b) ⇒ R{0}."""
    va, vb = var(a), var(b)
    S0 = s_intervalle(R, va, vb, ZERO)
    hyp = hypothese_recurrence_intervalle(R, va, vb, "nint")
    Ra = conjonction_elim_gauche(N.assume(hyp))
    card_a = N.assume(est_cardinal(va))
    card_0 = conjonction_elim_gauche(fini_zero())

    h_ant = N.assume(et(inf_egal_card(va, ZERO), inf_egal_card(ZERO, vb)))  # a≤0 et 0≤b
    a_le_0 = conjonction_elim_gauche(h_ant)
    zero_a = _zero_le(va)                                # 0 ≤ a
    a_eq_0 = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_intro(a_le_0, zero_a), card_a), card_0),
        _antisym(va, ZERO))                             # a = 0
    leib = N.s6(va, ZERO, "wa3", R(var("wa3")))         # (a=0) ⇒ (R{a} ⇔ R{0})
    r0 = N.modus_ponens(Ra, equivalence_avant(N.modus_ponens(a_eq_0, leib)))
    res = N.loi_deduction(et(inf_egal_card(va, ZERO), inf_egal_card(ZERO, vb)), r0)
    assert res.conclusion == S0, "S{0} intervalle : conclusion inattendue"
    assert res.hypotheses == frozenset({hyp, est_cardinal(va)}), "S{0} intervalle : hyps inattendues"
    return res


# @livre Ch.III §4.3 Demo.- | E III.33 L.32-33 | PDF p.136  (« (n entier et S{n}) ⇒ S{n+1} » — DÉRIVÉ)
def heredite_s_intervalle(R, a="aint", b="bint", n="niph"):
    """🎯 { hypothese_recurrence_intervalle(R,a,b), est_cardinal(a) }
        ⊢ (∀n)((Fini n et S{n}) ⇒ S{n+1}),   S{n} := (a≤n et n≤b) ⇒ R{n}."""
    va, vb, vn = var(a), var(b), var(n)
    sn = successeur(vn)
    S_n = s_intervalle(R, va, vb, vn)
    S_sn = s_intervalle(R, va, vb, sn)
    hyp = hypothese_recurrence_intervalle(R, va, vb, "nint")

    hHyp = N.assume(hyp)
    Ra = conjonction_elim_gauche(hHyp)
    step = conjonction_elim_droite(hHyp)                # (∀nint)((Fini et a≤n et n<b et R{n})⇒R{n+1})
    card_a = N.assume(est_cardinal(va))

    hFS = N.assume(et(est_fini(vn), S_n))
    fini_n = conjonction_elim_gauche(hFS)
    thm_Sn = conjonction_elim_droite(hFS)               # (a≤n et n≤b) ⇒ R{n}
    card_n = conjonction_elim_gauche(fini_n)            # est_cardinal(n)

    h_ant = N.assume(et(inf_egal_card(va, sn), inf_egal_card(sn, vb)))  # a≤n+1 et n+1≤b
    a_le_sn = conjonction_elim_gauche(h_ant)
    sn_le_b = conjonction_elim_droite(h_ant)           # n+1 ≤ b

    # n ≤ n+1  (successeur_ordre + réflexivité), puis n ≤ b (transitivité)
    so_eq = N.modus_ponens(card_n, successeur_ordre(n, n))   # (n≤n+1)⇔(n≤n ou n=n+1)
    n_le_n = inf_egal_reflexif(n)                       # n≤n
    n_le_sn = N.modus_ponens(
        N.modus_ponens(n_le_n, N.s2(inf_egal_card(vn, vn), egal(vn, sn))),
        equivalence_arriere(so_eq))                    # n≤n+1
    n_le_b = N.modus_ponens(conjonction_intro(n_le_sn, sn_le_b), _trans(vn, sn, vb))  # n≤b

    # n < b : n≤b et n≠b ; n≠b car n=b donnerait n+1≤n (contre succ_pas_inf_egal)
    not_sn_le_n = N.modus_ponens(fini_n, succ_pas_inf_egal(n))   # ¬(n+1≤n)
    h_eq_nb = N.assume(egal(vn, vb))
    leib_b = N.s6(vn, vb, "wb3h", inf_egal_card(sn, var("wb3h")))  # (n=b)⇒(n+1≤n ⇔ n+1≤b)
    sn_le_n = N.modus_ponens(sn_le_b,
        equivalence_arriere(N.modus_ponens(h_eq_nb, leib_b)))  # n+1≤n
    n_ne_b = _refute_self(N.loi_deduction(egal(vn, vb),
        _ex_falso(sn_le_n, not_sn_le_n, non(egal(vn, vb)))))    # ¬(n=b)
    n_lt_b = conjonction_intro(n_le_b, n_ne_b)          # n<b (= et(n≤b, ¬(n=b)))

    # disjonction sur a≤n
    h_a_le_n = N.assume(inf_egal_card(va, vn))
    r_n = N.modus_ponens(conjonction_intro(h_a_le_n, n_le_b), thm_Sn)   # R{n}
    step_n = instancie(step, vn)
    r_sn_1 = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_intro(fini_n, h_a_le_n), n_lt_b), r_n),
        step_n)                                         # R{n+1}
    br1 = N.loi_deduction(inf_egal_card(va, vn), r_sn_1)

    h_not_le = N.assume(non(inf_egal_card(va, vn)))
    sos = successeur_ordre_strict(a, n)                 # (card a et fini n) ⇒ (a<n+1 ⇔ a≤n)
    eq_sos = N.modus_ponens(conjonction_intro(card_a, fini_n), sos)
    not_a_lt = N.modus_ponens(h_not_le, contraposition(equivalence_avant(eq_sos)))  # ¬(a<n+1)
    c58_at = instancie(instancie(
        N.generalisation("x58", N.generalisation("y58", c58_ordre_strict())), va), sn)  # a≤n+1⇔(a<n+1 ou a=n+1)
    disj_sn = N.modus_ponens(a_le_sn, equivalence_avant(c58_at))
    brA = N.loi_deduction(inf_strict_card(va, sn),
                          _ex_falso(N.assume(inf_strict_card(va, sn)), not_a_lt, egal(va, sn)))
    brB = a_implique_a(egal(va, sn))
    a_eq_sn = cas(disj_sn, brA, brB)                   # a = n+1
    leib_a = N.s6(va, sn, "wa3h", R(var("wa3h")))      # (a=n+1)⇒(R{a}⇔R{n+1})
    r_sn_2 = N.modus_ponens(Ra, equivalence_avant(N.modus_ponens(a_eq_sn, leib_a)))
    br2 = N.loi_deduction(non(inf_egal_card(va, vn)), r_sn_2)

    r_sn = cas(tiers_exclu(inf_egal_card(va, vn)), br1, br2)   # R{n+1}
    imp_sn = N.loi_deduction(et(inf_egal_card(va, sn), inf_egal_card(sn, vb)), r_sn)  # S{n+1}
    assert imp_sn.conclusion == S_sn, "S{n+1} intervalle : forme inattendue"
    her = N.loi_deduction(et(est_fini(vn), S_n), imp_sn)
    res = N.generalisation(n, her)
    assert res.hypotheses == frozenset({hyp, est_cardinal(va)}), "hérédité intervalle : hyps inattendues"
    return res


# @livre Ch.III §4.3 Rem.3 | E III.33 L.27-31 | PDF p.136
# @livre Ch.III §4.3 Demo.- | E III.33 L.32-33 | PDF p.136  (« C61 sur S puis retour » — DÉRIVÉ)
def recurrence_intervalle(R, a="aint", b="bint"):
    """🎯🎯 VARIANTE 3 (« récurrence limitée à [a,b] », E III.33 L.27-33) — DÉRIVÉE de C61 :

        { hypothese_recurrence_intervalle(R,a,b), est_cardinal(a), predecesseur_fini_universel }
        ⊢ (∀n)( (n entier et a≤n≤b) ⇒ R{n} )."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve)
    va, vb = var(a), var(b)

    def P(t):
        return s_intervalle(R, va, vb, t)

    base = s_intervalle_en_zero(R, a, b)
    her = heredite_s_intervalle(R, a, b, "niph")
    c61 = principe_recurrence_preuve(P, n="niph")
    tout_S = N.modus_ponens(conjonction_intro(base, her), c61)   # ∀n(Fini n ⇒ S{n})

    vn = var("nint")
    imp_curry = instancie(tout_S, vn)                  # Fini n ⇒ ((a≤n et n≤b) ⇒ R{n})
    ante = et(et(est_fini(vn), inf_egal_card(va, vn)), inf_egal_card(vn, vb))
    hA = N.assume(ante)
    fini_n = conjonction_elim_gauche(conjonction_elim_gauche(hA))
    a_le_n = conjonction_elim_droite(conjonction_elim_gauche(hA))
    n_le_b = conjonction_elim_droite(hA)
    S_n = N.modus_ponens(fini_n, imp_curry)            # (a≤n et n≤b) ⇒ R{n}
    C = N.modus_ponens(conjonction_intro(a_le_n, n_le_b), S_n)   # R{n}
    uncurried = N.loi_deduction(ante, C)
    res = N.generalisation("nint", uncurried)

    assert res.conclusion == conclusion_recurrence_intervalle(R, va, vb, "nint"), \
        "variante 3 : conclusion inattendue"
    assert len(res.hypotheses) == 3, "variante 3 : hypothèses ≠ 3"
    return res


__all__ = ["s_intervalle", "s_intervalle_en_zero",
           "heredite_s_intervalle", "recurrence_intervalle"]
