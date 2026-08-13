"""§III.5.6 Th.1 — DIVISION EUCLIDIENNE, EXISTENCE (assemblage final par récurrence forte).

⊢ {b≠0, Fini b, + résidus C61} ⊢ (∀n)( Fini n ⇒ (∃q)(∃r)( b·q + r = n  et  r < b ) ).

Assemble les briques déjà closes :
  · _pas_petit  {a fini}(a<b) ⇒ R{a}                     [ensembles_division_existence]
  · _pas_grand  {a fini,b fini,b≤a,R{a−b}} ⇒ R{a}        [ensembles_division_existence]
  · _diff_strict / _diff_est_fini  (a−b<a , a−b fini)     [ensembles_division_recurrence]
  · recurrence_forte(R_rec)  ⊢ {H, pred_univ}⇒(∀n)(Fini n⇒R_rec{n})   [C61 variante 1]
  · trichotomie_finis  (a<b) ou (a=b) ou (b<a)  [CLOS]

_strong_step prouve H = (∀n)(S{n} ⇒ R_rec{n}), R_rec{n} = (Fini n ⇒ R{n}), par TRICHOTOMIE :
n<b ⇒ _pas_petit ; b≤n ⇒ _pas_grand avec R{n−b} tiré de S{n} au point p=n−b (licite car n−b<n
[_diff_strict] et n−b fini [_diff_est_fini]).  Puis recurrence_forte décharge H.

RÉSIDUS HONNÊTES : b≠0 (hypothèse de Bourbaki) ; predecesseur_fini_universel (résidu C61 standard) ;
principe_recurrence + cardinal_pas_entre (résidus C61 hérités de _diff_est_fini / « sous-ensemble d'un
fini est fini ») ⇒ EXISTENCE « CLOS modulo C61 » (comme l'existence de ℕ elle-même).  theorie == 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, ou, impl, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie, equivalence_avant, cas)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import strict_implique_inf_egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import trichotomie_finis
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import diff_somme
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence import (
    _R_rel, _pas_petit, _pas_grand)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_recurrence import (
    _diff_strict, _diff_est_fini)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_forte_preuve import recurrence_forte
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    s_recurrence_forte, hypothese_recurrence_forte, conclusion_recurrence)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, P, proofP):
    """Décharge l'hypothèse P de `thm` en la remplaçant par sa preuve `proofP`."""
    return N.modus_ponens(proofP, N.loi_deduction(P, thm))


def _R_rec(vb):
    """n ↦ (Fini n ⇒ R{n})   (relation gardée pour la récurrence forte)."""
    return lambda t: impl(est_fini(t), _R_rel(vb, t))


def enonce_division_existence(b="bdf"):
    vb = var(b)
    return conclusion_recurrence(_R_rec(vb), "nfor")


# @livre Ch.III §5.6 Demo.- | E III.39 L.10-19 | PDF p.142   (pas de récurrence forte)
def _strong_step(b="bdf"):
    """⊢ {Fini b, b≠0, + résidus C61} ⊢ (∀n)( S{n} ⇒ R_rec{n} ) = H.   (LE cœur : trichotomie.)"""
    vb = _t(b)
    R_rec = _R_rec(vb)
    vn = var("nfor")
    diff = diff_somme(vn, vb, "c")                            # n − b
    S_n = s_recurrence_forte(R_rec, vn, "pfor")               # (∀p)((n fini ∧ p fini ∧ p<n)⇒R_rec{p})

    fin_b = N.assume(est_fini(vb))
    b_ne0 = N.assume(non(egal(vb, ZERO)))
    h_S = N.assume(S_n)
    h_fin_n = N.assume(est_fini(vn))
    card_n = N.modus_ponens(h_fin_n, fini_implique_cardinal(vn))   # {Fini n} est_cardinal n
    card_b = N.modus_ponens(fin_b, fini_implique_cardinal(vb))     # {Fini b} est_cardinal b

    lt_nb = inf_strict_card(vn, vb)                          # n < b
    eqnb = egal(vn, vb)                                      # n = b
    lt_bn = inf_strict_card(vb, vn)                          # b < n
    le_bn_f = inf_egal_card(vb, vn)                          # b ≤ n

    # ── CAS n < b : _pas_petit ──
    R_petit = N.modus_ponens(N.assume(lt_nb), _pas_petit("nfor", "bdf"))   # R{n}
    branch_petit = N.loi_deduction(lt_nb, R_petit)          # (n<b) ⇒ R{n}

    # ── build_grand(le_bn) : R{n} sous b≤n (via _pas_grand + R{n−b} depuis S{n}) ──
    def build_grand(le_bn):
        S_at = instancie(h_S, diff)                          # (n fini ∧ diff fini ∧ diff<n) ⇒ R_rec{diff}
        ds = _diff_strict("nfor", "bdf")                     # diff < n   {card n,card b,b≤n,Fini n,Fini b,b≠0}
        de = _diff_est_fini("nfor", "bdf")                   # diff fini  {card n,card b,b≤n,Fini n,+C61}
        for P, pr in [(est_cardinal(vn), card_n), (est_cardinal(vb), card_b), (le_bn_f, le_bn)]:
            ds = _cut(ds, P, pr)
            de = _cut(de, P, pr)
        ante = conjonction_intro(conjonction_intro(h_fin_n, de), ds)   # n fini ∧ diff fini ∧ diff<n
        R_rec_diff = N.modus_ponens(ante, S_at)              # R_rec{diff} = (Fini diff ⇒ R{n−b})
        R_diff = N.modus_ponens(de, R_rec_diff)              # R{n−b}
        pg = _pas_grand("nfor", "bdf")                       # {Fini n,Fini b,b≤n,R{n−b}} R{n}
        for P, pr in [(est_fini(vn), h_fin_n), (est_fini(vb), fin_b),
                      (le_bn_f, le_bn), (_R_rel(vb, diff), R_diff)]:
            pg = _cut(pg, P, pr)
        return pg                                            # R{n}

    # ── CAS b < n : b≤n par strict_implique_inf_egal ──
    le_from_ltbn = N.modus_ponens(N.assume(lt_bn), strict_implique_inf_egal("bdf", "nfor"))  # b≤n
    branch_ltbn = N.loi_deduction(lt_bn, build_grand(le_from_ltbn))   # (b<n) ⇒ R{n}

    # ── CAS n = b : b≤n par réflexivité b≤b réécrite b→n ──
    h_eqnb = N.assume(eqnb)                                  # n = b
    eq_bn = N.modus_ponens(h_eqnb, symetrie(vn, vb))         # b = n
    refl_bb = inf_egal_reflexif(vb.nom)                      # b ≤ b
    leibr = N.s6(vb, vn, "wr", inf_egal_card(vb, var("wr")))  # (b=n) ⇒ (b≤b ⇔ b≤n)
    le_from_eq = N.modus_ponens(refl_bb, equivalence_avant(N.modus_ponens(eq_bn, leibr)))  # b≤n
    branch_eq = N.loi_deduction(eqnb, build_grand(le_from_eq))   # (n=b) ⇒ R{n}

    # ── recombiner : (n=b OU b<n) ⇒ R{n}, puis trichotomie ──
    disj_rest = ou(eqnb, lt_bn)
    R_rest = cas(N.assume(disj_rest), branch_eq, branch_ltbn)   # R{n}  [sous (n=b OU b<n)]
    branch_rest = N.loi_deduction(disj_rest, R_rest)         # ((n=b)OU(b<n)) ⇒ R{n}
    trich = trichotomie_finis("nfor", "bdf")                 # (n<b) OU ((n=b) OU (b<n))
    R_n = cas(trich, branch_petit, branch_rest)              # R{n}  = _R_rel(vb, vn)

    # ── H = (∀n)(S{n} ⇒ (Fini n ⇒ R{n})) ──
    R_rec_body = N.loi_deduction(est_fini(vn), R_n)          # Fini n ⇒ R{n} = R_rec{n}
    step = N.loi_deduction(S_n, R_rec_body)                  # S{n} ⇒ R_rec{n}
    H_proof = N.generalisation("nfor", step)                 # (∀n)(S{n} ⇒ R_rec{n})
    assert H_proof.conclusion == hypothese_recurrence_forte(R_rec, "nfor", "pfor"), \
        "_strong_step : H ≠ hypothese_recurrence_forte"
    return H_proof


# @livre Ch.III §5.6 Th.1 | E III.39 L.10-19 | PDF p.142
def division_existence(b="bdf"):
    """🎯 THÉORÈME 1 §III.5.6 — EXISTENCE de la division euclidienne :
    ⊢ {b≠0, Fini b, + résidus C61} ⊢ (∀n)( Fini n ⇒ (∃q)(∃r)( b·q+r=n et r<b ) )."""
    vb = _t(b)
    R_rec = _R_rec(vb)
    H_proof = _strong_step(b)                                # ⊢ H
    rf = recurrence_forte(R_rec, "pfor")                     # {H, pred_univ} ⊢ (∀n)(Fini n ⇒ R_rec{n})
    H = hypothese_recurrence_forte(R_rec, "nfor", "pfor")
    res = _cut(rf, H, H_proof)                               # décharge H
    assert res.conclusion == enonce_division_existence(b), "division_existence : conclusion inattendue"
    return res


__all__ = ["enonce_division_existence", "_strong_step", "division_existence"]
