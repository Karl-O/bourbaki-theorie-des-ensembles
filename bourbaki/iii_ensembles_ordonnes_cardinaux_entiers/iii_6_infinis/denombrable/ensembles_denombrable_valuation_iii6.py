# -*- coding: utf-8 -*-
"""§III.6 (prérequis Lemme 2, ℵ₀·ℵ₀=ℵ₀) — le PONT « a^(m+d) = a^m · a^d » au niveau
des opérations cardinales du dépôt (brique W3a de la 2-valuation).

🎯 CIBLE.  `exposant_somme_pont(base, m, d)` :

    ⊢ exposant_cardinal_binaire(base, m+d) = produit_cardinal_binaire(base^m, base^d),

avec m+d := somme_cardinale_binaire(m,d) = Card(m⊔d) et base^x :=
exposant_cardinal_binaire(base, x) = Card(𝓕(x; base)).  INCONDITIONNEL (0 hyp) :
les trois maillons sont Eq-ponts d'invariance, tous CLOS.

CHAÎNE (composer_egalites ×2), miroir exact de `distributivite_operations` :
  g1  Card(𝓕(Card(m⊔d); base)) = Card(𝓕(m⊔d; base))
      [Eq(Card(m⊔d), m⊔d) (equipotent_son_cardinal + symétrie) poussée par le
       keystone `eq_exposant_invariant` (but A ∀-clos puis instancié au TERME
       base), puis Prop. 1 directe] ;
  g2  Card(𝓕(m⊔d; base)) = Card(𝓕(m;base) × 𝓕(d;base))
      [`prop9_close` (a^(b+c)=a^b·a^c, INCONDITIONNEL, Cantor–Bernstein)] ;
  g3  Card(𝓕(m;base) × 𝓕(d;base)) = Card(base^m × base^d)
      [Eq(S, Card S) ×2 poussées par `eq_produit_invariant` (témoins F/G
       α-figés), puis Prop. 1 directe].

Usage aval : W3 (2-valuation, base:=DEUX) et W4 (3-injectivité, base:=TROIS).
theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _eq_son_cardinal_terme(t):
    """⊢ Eq(T, Card T) pour un TERME T (∀-clôture de equipotent_son_cardinal)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal)
    return instancie(N.generalisation("X", equipotent_son_cardinal("X")), _t(t))


def _eq_sym_t(tX, tY, eq_thm):
    """De ⊢ Eq(X,Y) déduit ⊢ Eq(Y,X)   (symétrie de Eq via _sym_all, aux termes)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        _sym_all)
    return N.modus_ponens(eq_thm, instancie(instancie(_sym_all(), _t(tX)), _t(tY)))


def exposant_somme_pont_cible(base, m, d):
    """Formule : base^(m+d) = base^m · base^d   (niveau opérations cardinales)."""
    vb, vm, vd = _t(base), _t(m), _t(d)
    lhs = exposant_cardinal_binaire(vb, somme_cardinale_binaire(vm, vd))
    rhs = produit_cardinal_binaire(exposant_cardinal_binaire(vb, vm),
                                   exposant_cardinal_binaire(vb, vd))
    return egal(lhs, rhs)


# @livre Ch.III §3.5 Cor.1 | E III.28 L.29-30 | PDF p.131
def exposant_somme_pont(base, m="mvw", d="dvw"):
    """🎯 ⊢ base^(m+d) = base^m · base^d.   (Cor.1 §III.3.5 aux OPÉRATIONS cardinales.)

    Voir la chaîne g1-g2-g3 en tête de module.  base, m, d : noms OU termes ;
    INCONDITIONNEL (0 hyp)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import (
        eq_exposant_invariant)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
        eq_produit_invariant)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_final_close import (
        prop9_close)

    vb, vm, vd = _t(base), _t(m), _t(d)
    MD = somme_disjointe(vm, vd)                       # m ⊔ d
    SC = cardinal(MD)                                  # m + d = Card(m⊔d)
    Fsc = E.applications(SC, vb)                       # 𝓕(m+d; base)
    Fmd = E.applications(MD, vb)                       # 𝓕(m⊔d; base)
    Fm = E.applications(vm, vb)                        # 𝓕(m; base)
    Fd = E.applications(vd, vb)                        # 𝓕(d; base)
    expm = exposant_cardinal_binaire(vb, vm)           # base^m = Card 𝓕(m;base)
    expd = exposant_cardinal_binaire(vb, vd)           # base^d

    # g1 : Card 𝓕(m+d;base) = Card 𝓕(m⊔d;base)
    eq_sc_md = _eq_sym_t(MD, SC, _eq_son_cardinal_terme(MD))     # Eq(Card(m⊔d), m⊔d)
    #   keystone AUX NOMS (ses sous-lemmes internes sont à noms fixes X/Y) :
    #   ∀-clore sur A, X, Y puis instancier aux TERMES (le noyau α-gère les
    #   τ-cardinaux passés en argument)
    g_inv = N.generalisation("A", N.generalisation("X", N.generalisation(
        "Y", eq_exposant_invariant("X", "Y", "A"))))
    inv_exp = instancie(instancie(instancie(g_inv, vb), SC), MD)
    eq_F = N.modus_ponens(eq_sc_md, inv_exp)           # Eq(𝓕(m+d;base), 𝓕(m⊔d;base))
    g1 = N.modus_ponens(eq_F, _prop1_direct_t(Fsc, Fmd))

    # g2 : Card 𝓕(m⊔d;base) = Card(𝓕(m;base) × 𝓕(d;base))   (Prop. 9, INCONDITIONNEL)
    g2 = prop9_close(vb, vm, vd)

    # g3 : Card(𝓕(m;base) × 𝓕(d;base)) = Card(base^m × base^d)
    eq_m = _eq_son_cardinal_terme(Fm)                  # Eq(𝓕(m;base), base^m)
    eq_d = _eq_son_cardinal_terme(Fd)                  # Eq(𝓕(d;base), base^d)
    inv_prod = eq_produit_invariant("F", "G", Fm, Fd, expm, expd)
    eq_prod = N.modus_ponens(conjonction_intro(eq_m, eq_d), inv_prod)
    g3 = N.modus_ponens(eq_prod, _prop1_direct_t(E.produit(Fm, Fd),
                                                 E.produit(expm, expd)))

    res = composer_egalites(composer_egalites(g1, g2), g3)
    assert res.conclusion == exposant_somme_pont_cible(vb, vm, vd), \
        f"exposant_somme_pont : conclusion inattendue\n{res.conclusion}"
    assert not res.hypotheses, "exposant_somme_pont : hypothèses résiduelles"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  W3b — base^n ≠ 0   (récurrence C61 ; base := Card(base_inner), non nulle)
# ══════════════════════════════════════════════════════════════════════════════
def puissance_non_nulle_cible(base, n="npnz"):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import non, impl
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, ZERO)
    vb, vn = _t(base), _t(n)
    return impl(est_fini(vn), non(egal(exposant_cardinal_binaire(vb, vn), ZERO)))


# @livre Ch.III §6.3 Demo.Lem2 | E III.48 L.4-16 | PDF p.151  (base^n ≠ 0 — support de la simplification)
def puissance_non_nulle(base_inner, nn_thm, n="npnz", k="kpnz"):
    """🎯 ⊢ Fini n ⇒ ¬( base^n = 0 ),   base := Card(base_inner).

    `nn_thm` : théorème CLOS ⊢ ¬(base = 0) fourni par l'appelant (pour DEUX :
    successeur_non_nul(UN), car DEUX = succ(UN) littéralement).  Récurrence C61,
    P[n] := ¬(base^n = 0) :
      • P[0]  : base^0 = Card(𝓕(∅;base)) [B0_preuve] = Card({∅}) [exposant_zero_
        egale_un] = 1 [un_egale_card_singleton sym] ; ¬(1=0) = successeur_non_nul(0) ;
      • pas   : base^(n+1) = base^n·base [puissance_succ_eq_incond ∀-clos aux termes] ;
        ¬(produit = 0) par Prop. 7 (∀-close aux termes) dont les membres Card(·)
        se replient par IDEMPOTENCE (Card(Card X) = Card X) sur P[n] et nn_thm."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import non, impl, pourtout
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, successeur, ZERO, UN)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (
        un_egale_card_singleton)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        _card_idempotent_t)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import (
        successeur_non_nul)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_entiers_inconditionnel import (
        B0_preuve)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
        exposant_zero_egale_un)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes_prop7 import (
        prop7_produit_non_nul)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_injection_iii6 import (
        puissance_succ_eq_incond)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
        _fini_et_P_implique_succ)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve, predecesseur_fini_universel)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite, equivalence_arriere)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie)

    def _cut(thm, hyp, pr):
        return N.modus_ponens(pr, N.loi_deduction(hyp, thm))

    def _card_est_cardinal_t(tX):
        from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
            card_est_un_cardinal)
        return instancie(N.generalisation("Xcuc3",
            card_est_un_cardinal("Xcuc3", lieur="X")), _t(tX))

    base = cardinal(_t(base_inner))
    vn = var(n)
    P = lambda b: non(egal(exposant_cardinal_binaire(base, _t(b)), ZERO))

    # ── P[0] : ¬(base^0 = 0) ──────────────────────────────────────────────
    exp0 = exposant_cardinal_binaire(base, ZERO)
    card_un = cardinal(E.singleton(E.VIDE))
    chain = composer_egalites(composer_egalites(
        B0_preuve(base), exposant_zero_egale_un(base)),
        N.modus_ponens(un_egale_card_singleton(), symetrie(UN, card_un)))  # base^0 = UN
    nn_un = successeur_non_nul(ZERO)                     # ¬(UN = 0)  (UN = succ 0)
    leib0 = N.modus_ponens(chain, N.s6(exp0, UN, "wpnz",
                                       non(egal(var("wpnz"), ZERO))))
    p0 = N.modus_ponens(nn_un, equivalence_arriere(leib0))
    assert p0.conclusion == P(ZERO), "puissance_non_nulle : P[0] mal formé"

    # ── pas : (Fini n et P[n]) ⇒ P[n+1] ──────────────────────────────────
    expn = exposant_cardinal_binaire(base, vn)
    exps = exposant_cardinal_binaire(base, successeur(vn))
    prod = produit_cardinal_binaire(expn, base)
    h = N.assume(et(est_fini(vn), P(vn)))
    fn = conjonction_elim_gauche(h)
    pn = conjonction_elim_droite(h)                      # ¬(base^n = 0)
    # base^(n+1) = base^n · base   (∀-clos aux termes)
    g_pse = N.generalisation("Apsi", N.generalisation("Npsi",
        puissance_succ_eq_incond("Apsi", "Npsi")))
    pse = instancie(instancie(g_pse, base), vn)
    eq_s = N.modus_ponens(conjonction_intro(_card_est_cardinal_t(_t(base_inner)), fn), pse)
    # Prop. 7 ∀-close : ¬(Card(base^n × base) = 0) ⇔ (¬(Card base^n = 0) et ¬(Card base = 0))
    g7 = N.generalisation("A", N.generalisation("B", prop7_produit_non_nul("A", "B")))
    p7 = instancie(instancie(g7, expn), base)
    # membres droits par IDEMPOTENCE de Card
    idem_n = _card_idempotent_t(E.applications(vn, base))     # Card(base^n) = base^n
    nn_cn = N.modus_ponens(pn, equivalence_arriere(N.modus_ponens(
        idem_n, N.s6(cardinal(expn), expn, "wpnz2", non(egal(var("wpnz2"), ZERO))))))
    idem_b = _card_idempotent_t(_t(base_inner))               # Card(base) = base
    nn_cb = N.modus_ponens(nn_thm, equivalence_arriere(N.modus_ponens(
        idem_b, N.s6(cardinal(base), base, "wpnz3", non(egal(var("wpnz3"), ZERO))))))
    nn_prod = N.modus_ponens(conjonction_intro(nn_cn, nn_cb),
                             equivalence_arriere(p7))    # ¬(base^n·base = 0)
    leib_s = N.modus_ponens(eq_s, N.s6(exps, prod, "wpnz4",
                                       non(egal(var("wpnz4"), ZERO))))
    p_succ = N.modus_ponens(nn_prod, equivalence_arriere(leib_s))
    step = N.generalisation(n, N.loi_deduction(et(est_fini(vn), P(vn)), p_succ))
    assert step.conclusion == _fini_et_P_implique_succ(P, n), \
        "puissance_non_nulle : pas mal formé"

    # ── assemblage C61 (patron pair_neq_impair) ──────────────────────────
    princ = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    if pfu in princ.hypotheses:
        princ = _cut(princ, pfu, predecesseur_fini_universel_preuve(k=k))
    fini_implique_P = N.modus_ponens(conjonction_intro(p0, step), princ)
    res = instancie(fini_implique_P, vn)                 # Fini n ⇒ ¬(base^n = 0)
    assert res.conclusion == puissance_non_nulle_cible(base, n), \
        f"puissance_non_nulle : conclusion inattendue\n{res.conclusion}"
    assert not res.hypotheses, "puissance_non_nulle : hypothèses résiduelles"
    return res


def deux_puissance_non_nulle(n="npnz", k="kpnz"):
    """⊢ Fini n ⇒ ¬( 2^n = 0 ).   (DEUX = succ(UN) = Card(UN⊔{∅}) littéralement.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import (
        successeur_non_nul)
    inner = somme_disjointe(UN, E.singleton(E.VIDE))     # DEUX = Card(UN⊔{∅})
    return puissance_non_nulle(inner, successeur_non_nul(UN), n, k)


__all__ = ["exposant_somme_pont", "exposant_somme_pont_cible",
           "puissance_non_nulle", "puissance_non_nulle_cible",
           "deux_puissance_non_nulle"]
