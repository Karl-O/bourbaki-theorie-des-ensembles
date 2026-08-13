"""§III.5 — PROPOSITION 4 (E.III.5), parties PROPRES : STRICTE CROISSANCE et
INJECTIVITÉ de la translation par un entier.

Débloquées par `simplification_additive_finie` (Cor. 3 §III.5, CLOS, 0 hyp).
La SURJECTIVITÉ / l'isomorphisme d'ordre restent un résidu dur — NON traités ici.

    prop4_translation_injective :
        ⊢ ( est_entier(a) et est_cardinal(x) et est_cardinal(x') ) ⇒
              ( a+x = a+x' ⇒ x = x' ).
        (Réécriture directe de `simplification_additive_finie`.)

    prop4_translation_stricte :
        ⊢ ( est_entier(a) et est_cardinal(x) et est_cardinal(x') ) ⇒
              ( x < x' ⇒ a+x < a+x' ).
        ( x < x' :⇔ (x≤x' et x≠x') ; a+x ≤ a+x' par `prop4_translation_croissante`
          (monotonie LARGE), a+x ≠ a+x' par contraposée de l'injectivité. )

⚠️ theorie_ensembles() = 22.  0 hyp.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_entier
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)

# briques CLOSES réutilisées
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_simplification_additive import (
    simplification_additive_finie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_prop4_iii5 import (
    prop4_translation_croissante,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  INJECTIVITÉ :  (est_entier a et card x et card x') ⇒ (a+x = a+x' ⇒ x = x')
# ════════════════════════════════════════════════════════════════════════════
def prop4_translation_injective_enonce(a="aP4", x="xP4", xp="xpP4"):
    va, vx, vxp = _t(a), _t(x), _t(xp)
    ax = somme_cardinale_binaire(va, vx)
    axp = somme_cardinale_binaire(va, vxp)
    ante = et(et(est_entier(va), est_cardinal(vx)), est_cardinal(vxp))
    return impl(ante, impl(egal(ax, axp), egal(vx, vxp)))


def _injective_sous_hyps(va, vx, vxp, h_ent, h_cx, h_cxp, k):
    """{ces hyps} ⊢ (a+x = a+x') ⇒ (x = x').

    Renvoie la PREUVE de l'implication (a+x=a+x')⇒(x=x') ouverte sous h_ent/h_cx/h_cxp."""
    # simplification_additive_finie(·) : est_entier A ⇒ (∀c)(∀c')((card c et card c' et A+c=A+c')⇒c=c')
    saf = simplification_additive_finie(a="aSAFp4", C="cSAFp4", Cp="cpSAFp4", k=k)
    saf_a = instancie(N.generalisation("aSAFp4", saf), va)   # est_entier a ⇒ P(a)
    Pa = N.modus_ponens(h_ent, saf_a)                       # (∀c)(∀c')(...⇒c=c')
    Pa_cc = instancie(instancie(Pa, vx), vxp)              # (card x et card x' et a+x=a+x') ⇒ x=x'

    ax = somme_cardinale_binaire(va, vx)
    axp = somme_cardinale_binaire(va, vxp)
    h_eq = N.assume(egal(ax, axp))                          # a+x = a+x'
    x_eq_xp = N.modus_ponens(
        conjonction_intro(conjonction_intro(h_cx, h_cxp), h_eq), Pa_cc)  # x = x'
    return N.loi_deduction(egal(ax, axp), x_eq_xp)          # (a+x=a+x') ⇒ (x=x')


# @livre Ch.III §5.3 Prop.4 | E III.37 L.27-35 | PDF p.140
def prop4_translation_injective(a="aP4", x="xP4", xp="xpP4", k="kP4inj"):
    """🎯 ⊢ ( est_entier(a) et card x et card x' ) ⇒ ( a+x = a+x' ⇒ x = x' ).
       (CLOS, 0 hyp — INJECTIVITÉ de la translation par un entier, Prop. 4 §III.5.)"""
    va, vx, vxp = _t(a), _t(x), _t(xp)
    ante = et(et(est_entier(va), est_cardinal(vx)), est_cardinal(vxp))
    h = N.assume(ante)
    h_ent = conjonction_elim_gauche(conjonction_elim_gauche(h))
    h_cx = conjonction_elim_droite(conjonction_elim_gauche(h))
    h_cxp = conjonction_elim_droite(h)

    impl_eq = _injective_sous_hyps(va, vx, vxp, h_ent, h_cx, h_cxp, k)
    res = N.loi_deduction(ante, impl_eq)
    assert res.conclusion == prop4_translation_injective_enonce(a, x, xp), \
        "prop4_translation_injective : conclusion ≠ énoncé attendu"
    assert res.est_clos and not res.hypotheses, "prop4_translation_injective : non close !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  STRICTE CROISSANCE : (est_entier a et card x et card x') ⇒ (x<x' ⇒ a+x<a+x')
# ════════════════════════════════════════════════════════════════════════════
def prop4_translation_stricte_enonce(a="aP4", x="xP4", xp="xpP4"):
    va, vx, vxp = _t(a), _t(x), _t(xp)
    ax = somme_cardinale_binaire(va, vx)
    axp = somme_cardinale_binaire(va, vxp)
    ante = et(et(est_entier(va), est_cardinal(vx)), est_cardinal(vxp))
    return impl(ante, impl(inf_strict_card(vx, vxp), inf_strict_card(ax, axp)))


# @livre Ch.III §5.3 Prop.4 | E III.37 L.27-35 | PDF p.140
def prop4_translation_stricte(a="aP4", x="xP4", xp="xpP4", k="kP4str"):
    """🎯 ⊢ ( est_entier(a) et card x et card x' ) ⇒ ( x < x' ⇒ a+x < a+x' ).
       (CLOS, 0 hyp — STRICTE CROISSANCE de la translation par un entier, Prop. 4 §III.5.)

    x<x' = (x≤x' et x≠x').  De x≤x' : a+x ≤ a+x' (prop4_translation_croissante).
    Pour a+x ≠ a+x' : par l'INJECTIVITÉ, a+x=a+x' ⇒ x=x', or x≠x' → contradiction →
    ¬(a+x=a+x').  D'où a+x < a+x' = (a+x≤a+x' et a+x≠a+x')."""
    va, vx, vxp = _t(a), _t(x), _t(xp)
    ax = somme_cardinale_binaire(va, vx)
    axp = somme_cardinale_binaire(va, vxp)

    ante = et(et(est_entier(va), est_cardinal(vx)), est_cardinal(vxp))
    h = N.assume(ante)
    h_ent = conjonction_elim_gauche(conjonction_elim_gauche(h))
    h_cx = conjonction_elim_droite(conjonction_elim_gauche(h))
    h_cxp = conjonction_elim_droite(h)

    lt = inf_strict_card(vx, vxp)                            # x < x' = (x≤x' et x≠x')
    h_lt = N.assume(lt)
    le_xxp = conjonction_elim_gauche(h_lt)                   # x ≤ x'
    ne_xxp = conjonction_elim_droite(h_lt)                   # ¬(x = x')

    # a+x ≤ a+x'  (monotonie LARGE)
    croiss = prop4_translation_croissante(a="acrP4", x="xcrP4", x2="xpcrP4")
    croiss_g = N.generalisation("acrP4", N.generalisation("xcrP4",
        N.generalisation("xpcrP4", croiss)))
    croiss_inst = instancie(instancie(instancie(croiss_g, va), vx), vxp)  # (x≤x')⇒(a+x≤a+x')
    le_axaxp = N.modus_ponens(le_xxp, croiss_inst)          # a+x ≤ a+x'

    # ¬(a+x = a+x')  via contraposée de l'injectivité
    inj_impl = _injective_sous_hyps(va, vx, vxp, h_ent, h_cx, h_cxp, k)  # (a+x=a+x')⇒(x=x')
    h_eq_ax = N.assume(egal(ax, axp))                       # a+x = a+x'
    x_eq_xp = N.modus_ponens(h_eq_ax, inj_impl)            # x = x'   [sous a+x=a+x']
    # x=x' et ¬(x=x') → ¬(a+x=a+x')   (idiome S2/S1)
    falso = N.modus_ponens(x_eq_xp, N.modus_ponens(ne_xxp,
        N.s2(non(egal(vx, vxp)), non(egal(ax, axp)))))      # ¬(a+x=a+x')  [sous a+x=a+x']
    ne_axaxp = N.modus_ponens(N.loi_deduction(egal(ax, axp), falso),
                              N.s1(non(egal(ax, axp))))      # ¬(a+x = a+x')

    lt_ax = conjonction_intro(le_axaxp, ne_axaxp)           # a+x < a+x' = (a+x≤a+x' et a+x≠a+x')
    assert lt_ax.conclusion == inf_strict_card(ax, axp), "a+x<a+x' mal formé"

    inner = N.loi_deduction(lt, lt_ax)                      # (x<x') ⇒ (a+x<a+x')
    res = N.loi_deduction(ante, inner)
    assert res.conclusion == prop4_translation_stricte_enonce(a, x, xp), \
        "prop4_translation_stricte : conclusion ≠ énoncé attendu"
    assert res.est_clos and not res.hypotheses, "prop4_translation_stricte : non close !"
    return res


__all__ = [
    "prop4_translation_injective", "prop4_translation_injective_enonce",
    "prop4_translation_stricte", "prop4_translation_stricte_enonce",
]
