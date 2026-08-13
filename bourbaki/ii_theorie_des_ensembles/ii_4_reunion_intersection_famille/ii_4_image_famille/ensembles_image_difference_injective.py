"""§II.4.5 (E.II.27) — COROLLAIRE de la Prop. 6 : IMAGE DIRECTE d'une DIFFÉRENCE
sous INJECTION.

    f injection de A dans B  ⟹  (∀X ⊂ A)  f⟨A∖X⟩ = f⟨A⟩ ∖ f⟨X⟩

CONDITIONNEL (hyp honnête `Injective(f)`, jamais postulée — déchargée par
loi_deduction).  C'est le DUAL EXACT de `image_reciproque_difference`
(est_fonctionnel(f) ⇒ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩) du module
`ensembles_image_algebre_binaire_ii4`, où l'on remplace l'image RÉCIPROQUE par
l'image DIRECTE : les couples sont (x,a)∈f (antécédent x, valeur a) au lieu de
(x,a)∈f⁻¹, et l'univalence (= est_fonctionnel) devient l'INJECTIVITÉ.

Pourquoi l'injectivité, et seulement pour un sens.  Posons a∈f⟨A∖X⟩ via un
témoin x∈A∖X, (x,a)∈f.  On a immédiatement x∈A (donc a∈f⟨A⟩) et ¬x∈X.  Pour
conclure a∉f⟨X⟩ il faut écarter qu'un AUTRE antécédent x'∈X atteigne la même
valeur a ; c'est exactement ce qu'interdit Injective(f) : (x,a)∈f et (x',a)∈f
forcent x=x', d'où x'∈X donnerait x∈X — contradiction.

  • Sens ⊇  (a∈f⟨A⟩∖f⟨X⟩ ⇒ a∈f⟨A∖X⟩) : INCONDITIONNEL.  Témoin x∈A, (x,a)∈f ;
    ¬x∈X par contraposition de (x∈X ⇒ a∈f⟨X⟩) qui contredit ¬a∈f⟨X⟩.
  • Sens ⊆  (a∈f⟨A∖X⟩ ⇒ a∈f⟨A⟩∖f⟨X⟩) : INJECTIVITÉ, via le sous-lemme
    (a∈f⟨X⟩ ⇒ x∈X) — témoin x', (x',a)∈f, x'∈X ; Injective(f) sur (x,a),(x',a)
    [même valeur a] donne x=x' ; Leibniz S6 transporte x'∈X en x∈X.

Preuve pointwise (A1 + AXIOME_IMAGE + AXIOME_DIFF).  theorie_ensembles()
inchangée (22 axiomes).  Primitives N.* uniquement ; aucun Theoreme fabriqué.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, appartient, impl, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, contraposition)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee)

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    membre_image, _instance_diff)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_recip_famille_ii4 import (
    injective)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Cor. de la Prop. 6 (E.II.27) — IMAGE DIRECTE d'une DIFFÉRENCE sous INJECTION.
#     Injective(f) ⇒ f⟨A∖X⟩ = f⟨A⟩ ∖ f⟨X⟩
# ════════════════════════════════════════════════════════════════════════════
def cible_image_difference_injective(f="f", a="A", x="X"):
    """Énoncé-cible : Injective(f) ⇒ f⟨A∖X⟩ = f⟨A⟩ ∖ f⟨X⟩."""
    vf, vA, vX = _t(f), _t(a), _t(x)
    lhs = E.image(vf, E.difference(vA, vX))
    rhs = E.difference(E.image(vf, vA), E.image(vf, vX))
    return impl(injective(vf), egal(lhs, rhs))


# @livre Ch.II §4.5 Cor.- | E II.27 L.27-31 | PDF p.78
def image_difference_injective(f="f", a="A", x="X"):
    """⊢ Injective(f) ⇒ f⟨A∖X⟩ = f⟨A⟩ ∖ f⟨X⟩.   (E.II.27, Cor. Prop. 6 ; CLOS, 0 hyp.)

    DUAL EXACT de `image_reciproque_difference` : image RÉCIPROQUE → image
    DIRECTE (couples (x,a)∈f), est_fonctionnel → Injective.
    ⊇ inconditionnel ; ⊆ via INJECTIVITÉ (si x∉X mais a∈f⟨X⟩ via x', alors x=x'∈X)."""
    vf, vA, vX = _t(f), _t(a), _t(x)
    va, vx, vxp = var("z"), var("x"), var("xp")
    diff = E.difference(vA, vX)
    fA = E.image(vf, vA)
    fX = E.image(vf, vX)
    lhs = E.image(vf, diff)
    rhs = E.difference(fA, fX)

    hinj = N.assume(injective(vf))
    cpl = lambda u: appartient(E.couple(u, va), vf)        # (u,a)∈f  (antécédent u, valeur a)
    bodyA = lambda u: et(appartient(u, vA), cpl(u))
    bodyX = lambda u: et(appartient(u, vX), cpl(u))
    bodyD = lambda u: et(appartient(u, diff), cpl(u))

    mem_lhs = membre_image(vf, diff, va)     # a∈f⟨A∖X⟩ ⇔ (∃x)bodyD(x)
    mem_A = membre_image(vf, vA, va)         # a∈f⟨A⟩   ⇔ (∃x)bodyA(x)
    mem_X = membre_image(vf, vX, va)         # a∈f⟨X⟩   ⇔ (∃x)bodyX(x)
    inst_rhs = _instance_diff(fA, fX, va)    # a∈rhs ⇔ (a∈f⟨A⟩ et ¬a∈f⟨X⟩)
    aX_f = appartient(va, fX)

    # Sous-lemme : (a∈f⟨X⟩) ⇒ (x∈X), VALIDE sous (x,a)∈f fixé + injectivité.
    #   a∈f⟨X⟩ ⇒ (∃x')bodyX(x') ; sous x' : x'∈X, (x',a)∈f ; injective x=x' ; x∈X.
    def aX_implique_xinX(x_cpl):
        h_aX = N.assume(aX_f)
        ex_Xp0 = N.modus_ponens(h_aX, equivalence_avant(mem_X))      # (∃x)bodyX(x)
        ex_Xp = N.modus_ponens(ex_Xp0, equivalence_avant(alpha_existe("x", "xp", bodyX(vx))))
        hbX = N.assume(bodyX(vxp))
        xp_in_X = conjonction_elim_gauche(hbX)
        xp_cpl = conjonction_elim_droite(hbX)                        # (x',a)∈f
        # injective(f) sur (x,a),(x',a) [même valeur a] : x=x'
        inj_inst = instancie(instancie(instancie(hinj, vx), vxp), va)  # ((x,a)∈f et (x',a)∈f)⇒x=x'
        x_eq_xp = N.modus_ponens(conjonction_intro(x_cpl, xp_cpl), inj_inst)   # x=x'
        x_in_X = N.modus_ponens(xp_in_X, equivalence_arriere(
            N.modus_ponens(x_eq_xp, N.s6(vx, vxp, "w", appartient(var("w"), vX)))))  # x'∈X⇒x∈X
        imp = existe_elimination(N.loi_deduction(bodyX(vxp), x_in_X), "xp")
        return N.loi_deduction(aX_f, N.modus_ponens(ex_Xp, imp))     # ⊢ a∈f⟨X⟩ ⇒ x∈X

    # ── ⊆ : a∈lhs ⇒ a∈rhs  (INJECTIVITÉ) ──────────────────────────────────────
    h_lhs = N.assume(appartient(va, lhs))
    ex_D = N.modus_ponens(h_lhs, equivalence_avant(mem_lhs))         # (∃x)bodyD(x)
    hbD = N.assume(bodyD(vx))
    x_in_diff = conjonction_elim_gauche(hbD)
    x_cpl = conjonction_elim_droite(hbD)                             # (x,a)∈f
    x_in_A = conjonction_elim_gauche(N.modus_ponens(
        x_in_diff, equivalence_avant(_instance_diff(vA, vX, vx))))   # x∈A
    x_not_X = conjonction_elim_droite(N.modus_ponens(
        x_in_diff, equivalence_avant(_instance_diff(vA, vX, vx))))   # ¬x∈X
    aA = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_A, x_cpl),
                                       N.s5(bodyA(vx), vx, "x")),
                        equivalence_arriere(mem_A))                  # a∈f⟨A⟩
    # ¬(a∈f⟨X⟩) par contraposition de (a∈f⟨X⟩⇒x∈X) avec ¬x∈X
    not_aX = N.modus_ponens(x_not_X, contraposition(aX_implique_xinX(x_cpl)))  # ¬a∈f⟨X⟩
    rhs_mem = N.modus_ponens(conjonction_intro(aA, not_aX), equivalence_arriere(inst_rhs))
    incl_LR = N.generalisation("z", N.loi_deduction(
        appartient(va, lhs),
        N.modus_ponens(ex_D, existe_elimination(N.loi_deduction(bodyD(vx), rhs_mem), "x"))))

    # ── ⊇ : a∈rhs ⇒ a∈lhs  (inconditionnel) ───────────────────────────────────
    h_rhs = N.assume(appartient(va, rhs))
    and_rhs = N.modus_ponens(h_rhs, equivalence_avant(inst_rhs))
    aA2 = conjonction_elim_gauche(and_rhs)                           # a∈f⟨A⟩
    not_aX2 = conjonction_elim_droite(and_rhs)                       # ¬a∈f⟨X⟩
    ex_A = N.modus_ponens(aA2, equivalence_avant(mem_A))             # (∃x)bodyA(x)
    hbA = N.assume(bodyA(vx))
    x_in_A2 = conjonction_elim_gauche(hbA)
    x_cpl2 = conjonction_elim_droite(hbA)                            # (x,a)∈f
    # ¬x∈X : si x∈X alors a∈f⟨X⟩ (témoin x), contredit not_aX2.
    h_xX = N.assume(appartient(vx, vX))
    aX_from_x = N.modus_ponens(N.modus_ponens(conjonction_intro(h_xX, x_cpl2),
                                              N.s5(bodyX(vx), vx, "x")),
                               equivalence_arriere(mem_X))           # a∈f⟨X⟩
    x_not_X2 = N.modus_ponens(not_aX2, contraposition(
        N.loi_deduction(appartient(vx, vX), aX_from_x)))             # ¬x∈X
    x_in_diff2 = N.modus_ponens(conjonction_intro(x_in_A2, x_not_X2),
                                equivalence_arriere(_instance_diff(vA, vX, vx)))
    aD = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_diff2, x_cpl2),
                                       N.s5(bodyD(vx), vx, "x")),
                        equivalence_arriere(mem_lhs))                # a∈lhs
    incl_RL = N.generalisation("z", N.loi_deduction(
        appartient(va, rhs),
        N.modus_ponens(ex_A, existe_elimination(N.loi_deduction(bodyA(vx), aD), "x"))))

    eq = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                        extensionnalite_appliquee(lhs, rhs))
    return N.loi_deduction(injective(vf), eq)


__all__ = [
    "image_difference_injective", "cible_image_difference_injective",
]
