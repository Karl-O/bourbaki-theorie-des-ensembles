"""§III.4.3 — VARIANTE 2 : récurrence « à partir de k » (E III.33 L.16-26), DÉRIVÉE de C61.

Bourbaki (E III.33 2)) : « Soient k un entier, R{n} une relation telle que
R{k} et (∀n)((n entier ≥ k et R{n}) ⇒ R{n+1}) soient vraies. Alors
(∀n)((n entier ≥ k) ⇒ R{n}) est vraie. En effet, soit S{n} := (n≥k) ⇒ R{n} ;
par disjonction des cas S{0} est vraie ; (n entier et S{n}) ⇒ S{n+1} ; C61 donne
(∀n)(n entier ⇒ S{n}), d'où l'assertion. »

Trois maillons, comme la variante 1 (récurrence forte, fichier voisin) :
  (1) S{0} = (k≤0) ⇒ R{0}  : sous k≤0, comme 0≤k (borne inférieure) l'antisymétrie
      donne k=0, donc R{0}=R{k} (Leibniz ; R{k} est une hypothèse) ;
  (2) S{n} ⇒ S{n+1} : sous k≤n+1, disjonction sur (k≤n) — si k≤n, S{n} donne R{n}
      puis la prémisse « à partir de k » donne R{n+1} ; sinon ¬(k≤n) donne
      ¬(k<n+1) [successeur_ordre_strict] donc, C58 sur k≤n+1, k=n+1, d'où R{n+1}=R{k} ;
  (3) C61 (principe_recurrence_preuve) sur S, puis retour à R.

Hypothèses honnêtes du résultat : { hypothese_recurrence_depuis(R,k), est_cardinal(k),
predecesseur_fini_universel } (les deux dernières = gardes/résidu hérités).
theorie_ensembles == 22, rien postulé.
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
    inf_egal_antisymetrique_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_c58_ordre_strict import (
    c58_ordre_strict)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, est_fini, successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero, cardinal_vide_egale_vide)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
    successeur_ordre_strict)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    hypothese_recurrence_depuis, conclusion_recurrence_depuis)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible."""
    imp = N.modus_ponens(thm_na, N.s2(non(thm_a.conclusion), cible))
    return N.modus_ponens(thm_a, imp)


def _antisym(u, v):
    """⊢ ( u≤v et v≤u et card(u) et card(v) ) ⇒ u=v."""
    g = inf_egal_antisymetrique_card("uas2", "vas2")
    return instancie(instancie(g, u), v)


def _zero_le(t):
    """⊢ 0 ≤ t   (borne inférieure, INCONDITIONNEL : ∅≤t puis réécriture ∅=Card∅=0)."""
    le_vide = instancie(N.generalisation("A", zero_inf_egal("A")), t)          # ∅ ≤ t
    vide_eq_zero = N.modus_ponens(cardinal_vide_egale_vide(),
                                  symetrie(cardinal(E.VIDE), E.VIDE))          # ∅ = Card(∅)
    leib0 = N.s6(E.VIDE, cardinal(E.VIDE), "wz2", inf_egal_card(var("wz2"), t))  # (∅=Card∅)⇒(∅≤t ⇔ 0≤t)
    return N.modus_ponens(le_vide, equivalence_avant(N.modus_ponens(vide_eq_zero, leib0)))


def s_depuis(R, k, n):
    """S{n} := (k ≤ n) ⇒ R{n}   (« R vaut À PARTIR de k »)."""
    vk = k if not isinstance(k, str) else var(k)
    vn = n if not isinstance(n, str) else var(n)
    return impl(inf_egal_card(vk, vn), R(vn))


# @livre Ch.III §4.3 Rem.2 | E III.33 L.16-26 | PDF p.136
# @livre Ch.III §4.3 Demo.- | E III.33 L.22-22 | PDF p.136  (S{0} par disjonction des cas — DÉRIVÉ)
def s_depuis_en_zero(R, k="kdep"):
    """🎯 { R{k}, est_cardinal(k) } ⊢ S{0} = (k≤0) ⇒ R{0}.

    Sous k≤0 : 0≤k (borne) + antisymétrie ⇒ k=0 ; R{k} + Leibniz ⇒ R{0}."""
    vk = var(k)
    S0 = s_depuis(R, vk, ZERO)                          # (k≤0) ⇒ R{0}
    hyp = hypothese_recurrence_depuis(R, vk, "ndep")
    Rk = conjonction_elim_gauche(N.assume(hyp))         # R{k}
    card_k = N.assume(est_cardinal(vk))                 # garde
    card_0 = conjonction_elim_gauche(fini_zero())       # est_cardinal(0)

    h_k0 = N.assume(inf_egal_card(vk, ZERO))            # k ≤ 0
    zero_k = _zero_le(vk)                               # 0 ≤ k
    ante_as = conjonction_intro(conjonction_intro(conjonction_intro(h_k0, zero_k),
                                                   card_k), card_0)
    k_eq_0 = N.modus_ponens(ante_as, _antisym(vk, ZERO))   # k = 0
    # R{0} = R{k} réécrit par k=0 (Leibniz)
    leib = N.s6(vk, ZERO, "wk2", R(var("wk2")))            # (k=0) ⇒ (R{k} ⇔ R{0})
    r0 = N.modus_ponens(Rk, equivalence_avant(N.modus_ponens(k_eq_0, leib)))  # R{0}
    res = N.loi_deduction(inf_egal_card(vk, ZERO), r0)     # (k≤0) ⇒ R{0}
    assert res.conclusion == S0, "S{0} : conclusion ≠ s_depuis(R,k,0)"
    assert res.hypotheses == frozenset({hyp, est_cardinal(vk)}), "S{0} : hyps inattendues"
    return res


# @livre Ch.III §4.3 Demo.- | E III.33 L.23-24 | PDF p.136  (« (n entier et S{n}) ⇒ S{n+1} » — DÉRIVÉ)
def heredite_s_depuis(R, k="kdep", n="ndph"):
    """🎯 { hypothese_recurrence_depuis(R,k), est_cardinal(k) }
        ⊢ (∀n)((Fini n et S{n}) ⇒ S{n+1}),   S{n} := (k≤n)⇒R{n}.

    Sous Fini(n), S{n}, k≤n+1 : disjonction sur (k≤n).  Si k≤n, S{n} donne R{n}
    puis la prémisse « à partir de k » donne R{n+1}.  Sinon ¬(k≤n) ⇒ ¬(k<n+1)
    (successeur_ordre_strict), et C58 sur k≤n+1 force k=n+1, d'où R{n+1}=R{k}."""
    vk, vn = var(k), var(n)
    sn = successeur(vn)
    S_n = s_depuis(R, vk, vn)
    S_sn = s_depuis(R, vk, sn)
    hyp = hypothese_recurrence_depuis(R, vk, "ndep")

    hHyp = N.assume(hyp)
    Rk = conjonction_elim_gauche(hHyp)                  # R{k}
    step = conjonction_elim_droite(hHyp)                # (∀ndep)((Fini ndep et k≤ndep et R{ndep})⇒R{ndep+1})
    card_k = N.assume(est_cardinal(vk))

    hFS = N.assume(et(est_fini(vn), S_n))               # Fini n et S{n}
    fini_n = conjonction_elim_gauche(hFS)
    thm_Sn = conjonction_elim_droite(hFS)               # (k≤n) ⇒ R{n}

    h_le_sn = N.assume(inf_egal_card(vk, sn))           # k ≤ n+1

    # cas 1 : k≤n
    h_le_n = N.assume(inf_egal_card(vk, vn))
    r_n = N.modus_ponens(h_le_n, thm_Sn)                # R{n}
    step_n = instancie(step, vn)                        # (Fini n et k≤n et R{n}) ⇒ R{n+1}
    r_sn_1 = N.modus_ponens(
        conjonction_intro(conjonction_intro(fini_n, h_le_n), r_n), step_n)   # R{n+1}
    br1 = N.loi_deduction(inf_egal_card(vk, vn), r_sn_1)

    # cas 2 : ¬(k≤n) → k=n+1 → R{n+1}=R{k}
    h_not_le = N.assume(non(inf_egal_card(vk, vn)))
    sos = successeur_ordre_strict(k, n)                 # (card k et fini n) ⇒ (k<n+1 ⇔ k≤n)
    eq_sos = N.modus_ponens(conjonction_intro(card_k, fini_n), sos)
    not_k_lt = N.modus_ponens(h_not_le, contraposition(equivalence_avant(eq_sos)))  # ¬(k<n+1)
    c58_at = instancie(instancie(
        N.generalisation("x58", N.generalisation("y58", c58_ordre_strict())), vk), sn)  # k≤n+1 ⇔ (k<n+1 ou k=n+1)
    disj_sn = N.modus_ponens(h_le_sn, equivalence_avant(c58_at))      # k<n+1 ou k=n+1
    brA = N.loi_deduction(inf_strict_card(vk, sn),
                          _ex_falso(N.assume(inf_strict_card(vk, sn)), not_k_lt, egal(vk, sn)))
    brB = a_implique_a(egal(vk, sn))
    k_eq_sn = cas(disj_sn, brA, brB)                   # k = n+1
    leib = N.s6(vk, sn, "wh2", R(var("wh2")))          # (k=n+1) ⇒ (R{k} ⇔ R{n+1})
    r_sn_2 = N.modus_ponens(Rk, equivalence_avant(N.modus_ponens(k_eq_sn, leib)))  # R{n+1}
    br2 = N.loi_deduction(non(inf_egal_card(vk, vn)), r_sn_2)

    r_sn = cas(tiers_exclu(inf_egal_card(vk, vn)), br1, br2)   # R{n+1}
    imp_sn = N.loi_deduction(inf_egal_card(vk, sn), r_sn)      # (k≤n+1) ⇒ R{n+1} = S{n+1}
    assert imp_sn.conclusion == S_sn, "S{n+1} : forme inattendue"
    her = N.loi_deduction(et(est_fini(vn), S_n), imp_sn)
    res = N.generalisation(n, her)
    assert res.hypotheses == frozenset({hyp, est_cardinal(vk)}), "hérédité : hyps inattendues"
    return res


# @livre Ch.III §4.3 Rem.2 | E III.33 L.16-19 | PDF p.136
# @livre Ch.III §4.3 Demo.- | E III.33 L.25-26 | PDF p.136  (« C61 sur S, puis retour à R » — DÉRIVÉ)
def recurrence_depuis(R, k="kdep"):
    """🎯🎯 VARIANTE 2 (« récurrence à partir de k », E III.33 L.16-26) — DÉRIVÉE de C61 :

        { hypothese_recurrence_depuis(R,k), est_cardinal(k), predecesseur_fini_universel }
        ⊢ (∀n)( (n entier et n≥k) ⇒ R{n} ).

    S{0} (s_depuis_en_zero) + hérédité (heredite_s_depuis) + C61
    (principe_recurrence_preuve) donnent (∀n)(Fini n ⇒ S{n}) ; le décurryfiage
    (Fini n ⇒ (k≤n ⇒ R{n})) → ((Fini n et k≤n) ⇒ R{n}) conclut."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve)

    vk = var(k)

    def P(t):
        return s_depuis(R, vk, t)

    base = s_depuis_en_zero(R, k)                       # {hyp, card k} ⊢ S{0}
    her = heredite_s_depuis(R, k, "ndph")              # {hyp, card k} ⊢ ∀n((Fini n et S{n})⇒S{n+1})
    c61 = principe_recurrence_preuve(P, n="ndph")      # {pred_univ} ⊢ (S0 et her) ⇒ ∀n(Fini⇒S)
    tout_S = N.modus_ponens(conjonction_intro(base, her), c61)   # ∀n(Fini n ⇒ S{n})

    # décurryfiage → conclusion_recurrence_depuis
    vn = var("ndep")
    imp_curry = instancie(tout_S, vn)                  # Fini n ⇒ (k≤n ⇒ R{n})
    hAB = N.assume(et(est_fini(vn), inf_egal_card(vk, vn)))
    C = N.modus_ponens(conjonction_elim_droite(hAB),
                       N.modus_ponens(conjonction_elim_gauche(hAB), imp_curry))  # R{n}
    uncurried = N.loi_deduction(et(est_fini(vn), inf_egal_card(vk, vn)), C)
    res = N.generalisation("ndep", uncurried)

    assert res.conclusion == conclusion_recurrence_depuis(R, vk, "ndep"), \
        "variante 2 : conclusion ≠ (∀n)((n entier et n≥k) ⇒ R{n})"
    assert len(res.hypotheses) == 3, "variante 2 : hypothèses ≠ {hyp, card k, pred_univ}"
    return res


__all__ = ["s_depuis", "s_depuis_en_zero", "heredite_s_depuis", "recurrence_depuis"]
