"""§II.4 (E.II.27) — ALGÈBRE BINAIRE DE L'IMAGE DIRECTE / RÉCIPROQUE.

Complète, à DEUX ensembles, les formules de l'§II.4 sur ∪ / ∩ / ∖ pour
l'image directe f⟨⟩ et l'image réciproque f⁻¹⟨⟩ (E.II.25–27 ; Prop. 3, 4, 6).

INCONDITIONNELLES (correspondance f quelconque) :
  • image_reunion_binaire        ⊢ f⟨B∪Y⟩ = f⟨B⟩ ∪ f⟨Y⟩          (Prop. 3, 1re formule)

CONDITIONNELLES (honnête hyp `est_fonctionnel(f)`, i.e. f application) :
  • image_reciproque_inter_binaire ⊢ est_fonctionnel(f) ⇒ f⁻¹⟨B∩Y⟩ = f⁻¹⟨B⟩ ∩ f⁻¹⟨Y⟩
  • image_reciproque_difference  ⊢ est_fonctionnel(f) ⇒ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩

INCLUSION HONNÊTE (image DIRECTE ∩ : l'ÉGALITÉ exige f INJECTIVE, pas seulement
fonctionnelle — cf. E.II.25 — donc on ne livre que l'inclusion inconditionnelle) :
  • image_inter_inclusion        ⊢ f⟨B∩Y⟩ ⊂ f⟨B⟩ ∩ f⟨Y⟩

Pour l'image RÉCIPROQUE, Bourbaki (E.II.27) écrit f⁻¹⟨A∩B⟩=f⁻¹⟨A⟩∩f⁻¹⟨B⟩
« en vertu de la prop. 4 », i.e. pour une APPLICATION f.  Le sens ⊆ est toujours
vrai, mais le sens ⊇ (un même antécédent x atteint A et B → atteint A∩B) exige
l'UNIVALENCE : si f(x)∈A et f(x)∈B alors f(x)∈A∩B, ce qui demande que x ait UNE
valeur.  Idem pour la différence (Prop. 6).  D'où l'hypothèse honnête.

Preuve : tout est pointwise (A1 + AXIOME_IMAGE + AXIOME_INTER/DIFF/REUNION).
AXIOME_IMAGE : y∈G⟨X⟩ ⇔ (∃x)(x∈X et (x,y)∈G).  Pour l'image directe G:=f, pour la
réciproque G:=f⁻¹ (couple (x,a)∈f⁻¹).  theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, et, ou, non, appartient, existe, impl, Terme)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
    instancie, equivalence_transitivite as etr, equivalence_symetrie as esym,
    et_congruence_gauche, et_congruence_droite, comm_et, et_ou_distrib,
    ou_congruence, assoc_et, cas)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import congruence_existe
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux.ensembles_produit_union_carre import existe_ou


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Membres élémentaires (instances directes des axiomes).
# ════════════════════════════════════════════════════════════════════════════
def membre_image(f, Z, a):
    """⊢ a ∈ f⟨Z⟩ ⇔ (∃x)(x∈Z et (x,a)∈f).

    Instance directe de AXIOME_IMAGE (G:=f, X:=Z, y:=a).  Liant interne « x »."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, f), Z), a)


def membre_image_reciproque(f, Z, a):
    """⊢ a ∈ f⁻¹⟨Z⟩ ⇔ (∃x)(x∈Z et (x,a)∈f⁻¹).  (G:=reciproque(f).)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, E.reciproque(f)), Z), a)


def _instance_reunion(a, b, z):
    """⊢ (z ∈ a∪b) ⇔ (z∈a ou z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def _instance_inter(a, b, z):
    """⊢ (z ∈ a∩b) ⇔ (z∈a et z∈b)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _instance_diff(a, b, z):
    """⊢ (z ∈ a∖b) ⇔ (z∈a et ¬(z∈b))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, a), b), z)


# ════════════════════════════════════════════════════════════════════════════
#  1. IMAGE DIRECTE D'UNE RÉUNION — INCONDITIONNEL  (E.II.27, Prop. 3).
#     f⟨B∪Y⟩ = f⟨B⟩ ∪ f⟨Y⟩
# ════════════════════════════════════════════════════════════════════════════
def cible_image_reunion_binaire(f="f", b="B", y="Y"):
    vf, vb, vy = _t(f), _t(b), _t(y)
    gauche = E.image(vf, E.reunion(vb, vy))
    droite = E.reunion(E.image(vf, vb), E.image(vf, vy))
    return egal(gauche, droite)


def image_reunion_binaire(f="f", b="B", y="Y"):
    """⊢ f⟨B∪Y⟩ = f⟨B⟩ ∪ f⟨Y⟩.   (E.II.27 binaire — CLOS, 0 hyp, INCOND.)"""
    vf, vb, vy = _t(f), _t(b), _t(y)
    va, vx = var("a"), var("x")
    reun = E.reunion(vb, vy)
    couple = appartient(E.couple(vx, va), vf)          # (x,a)∈f  (corps AXIOME_IMAGE, G:=f)
    inB = appartient(vx, vb)
    inY = appartient(vx, vy)

    # ── membre gauche : a∈f⟨B∪Y⟩ ⇔ (∃x)Bx ∨ (∃x)Yx ─────────────────────────
    L = membre_image(vf, reun, va)                     # ⇔ (∃x)(x∈B∪Y et (x,a)∈f)
    reun_x = _instance_reunion(vb, vy, vx)             # x∈B∪Y ⇔ (x∈B ∨ x∈Y)
    L2 = etr(L, congruence_existe(et_congruence_gauche(reun_x, couple), "x"))
    #     ⇔ (∃x)((x∈B ∨ x∈Y) et (x,a)∈f)
    commute = comm_et(ou(inB, inY), couple)
    distrib = et_ou_distrib(couple, inB, inY)
    recommute = ou_congruence(comm_et(couple, inB), comm_et(couple, inY))
    corps = etr(etr(commute, distrib), recommute)      # ((x∈B∨x∈Y) et (x,a)∈f) ⇔ (Bx ∨ Yx)
    Bx = et(inB, couple)
    Yx = et(inY, couple)
    L3 = etr(L2, congruence_existe(corps, "x"))         # ⇔ (∃x)(Bx ∨ Yx)
    L4 = etr(L3, existe_ou("x", Bx, Yx))                # ⇔ (∃x)Bx ∨ (∃x)Yx
    char_L = N.generalisation("a", L4)

    # ── membre droit : a∈f⟨B⟩∪f⟨Y⟩ ⇔ (∃x)Bx ∨ (∃x)Yx ──────────────────────
    R = _instance_reunion(E.image(vf, vb), E.image(vf, vy), va)
    mB = membre_image(vf, vb, va)                      # a∈f⟨B⟩ ⇔ (∃x)Bx
    mY = membre_image(vf, vy, va)                      # a∈f⟨Y⟩ ⇔ (∃x)Yx
    R2 = etr(R, ou_congruence(mB, mY))                 # ⇔ (∃x)Bx ∨ (∃x)Yx
    char_R = N.generalisation("a", R2)

    return egalite_par_extension(
        char_L, char_R,
        E.image(vf, reun),
        E.reunion(E.image(vf, vb), E.image(vf, vy)))


# ════════════════════════════════════════════════════════════════════════════
#  Outils communs aux lemmes CONDITIONNELS (hyp `est_fonctionnel(f)`).
# ════════════════════════════════════════════════════════════════════════════
from bourbaki.logique.i_1_termes_relations.formule import pourtout, subst_f
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import syllogisme
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee


def _univalence(vf, hfunc, a, x, xp):
    """De hfunc:⊢est_fonctionnel(f) déduire ⊢ ((a,x)∈f et (a,x')∈f) ⇒ x=x'.

    Instance de (∀u)(∀v)(∀z)(((u,v)∈f et (u,z)∈f)⇒v=z) en u:=a, v:=x, z:=x'."""
    return instancie(instancie(instancie(hfunc, a), x), xp)


# ════════════════════════════════════════════════════════════════════════════
#  2. IMAGE RÉCIPROQUE D'UNE INTERSECTION — CONDITIONNEL  (E.II.27, Prop. 4/6).
#     est_fonctionnel(f) ⇒ f⁻¹⟨B∩Y⟩ = f⁻¹⟨B⟩ ∩ f⁻¹⟨Y⟩
# ════════════════════════════════════════════════════════════════════════════
def cible_image_reciproque_inter_binaire(f="f", b="B", y="Y"):
    vf, vb, vy = _t(f), _t(b), _t(y)
    lhs = E.image(E.reciproque(vf), E.intersection(vb, vy))
    rhs = E.intersection(E.image(E.reciproque(vf), vb),
                         E.image(E.reciproque(vf), vy))
    return impl(E.est_fonctionnel(vf), egal(lhs, rhs))


def image_reciproque_inter_binaire(f="f", b="B", y="Y"):
    """⊢ est_fonctionnel(f) ⇒ f⁻¹⟨B∩Y⟩ = f⁻¹⟨B⟩ ∩ f⁻¹⟨Y⟩.   (E.II.27 ; CLOS, 0 hyp.)

    ⊆ inconditionnel ; ⊇ via UNIVALENCE de f (univalence = est_fonctionnel)."""
    vf, vb, vy = _t(f), _t(b), _t(y)
    va, vx, vxp = var("z"), var("x"), var("xp")
    inter = E.intersection(vb, vy)
    fB = E.image(E.reciproque(vf), vb)
    fY = E.image(E.reciproque(vf), vy)
    lhs = E.image(E.reciproque(vf), inter)
    rhs = E.intersection(fB, fY)

    hfunc = N.assume(E.est_fonctionnel(vf))

    # membres : x⁻¹couple = (x,a)∈f⁻¹
    cpl = lambda u: appartient(E.couple(u, va), E.reciproque(vf))   # (u,a)∈f⁻¹
    bodyB = lambda u: et(appartient(u, vb), cpl(u))
    bodyY = lambda u: et(appartient(u, vy), cpl(u))
    bodyI = lambda u: et(appartient(u, inter), cpl(u))

    mem_lhs = membre_image_reciproque(vf, inter, va)   # a∈f⁻¹⟨B∩Y⟩ ⇔ (∃x)bodyI(x)
    mem_B = membre_image_reciproque(vf, vb, va)        # a∈f⁻¹⟨B⟩   ⇔ (∃x)bodyB(x)
    mem_Y = membre_image_reciproque(vf, vy, va)        # a∈f⁻¹⟨Y⟩   ⇔ (∃x)bodyY(x)
    inst_rhs = _instance_inter(fB, fY, va)             # a∈rhs ⇔ (a∈f⁻¹⟨B⟩ et a∈f⁻¹⟨Y⟩)

    # ── ⊆ : a∈lhs ⇒ a∈rhs  (inconditionnel) ───────────────────────────────────
    h_lhs = N.assume(appartient(va, lhs))
    ex_I = N.modus_ponens(h_lhs, equivalence_avant(mem_lhs))   # (∃x)bodyI(x)
    #   bodyI(x) ⇒ (a∈f⁻¹⟨B⟩ et a∈f⁻¹⟨Y⟩)
    hbI = N.assume(bodyI(vx))
    x_in_inter = conjonction_elim_gauche(hbI)
    x_cpl = conjonction_elim_droite(hbI)
    x_in_B = N.modus_ponens(x_in_inter, equivalence_avant(_instance_inter(vb, vy, vx)))
    x_in_B = conjonction_elim_gauche(x_in_B)
    x_in_Y = conjonction_elim_droite(N.modus_ponens(
        x_in_inter, equivalence_avant(_instance_inter(vb, vy, vx))))
    # (∃x)bodyB(x) et (∃x)bodyY(x)
    aB = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_B, x_cpl),
                                       N.s5(bodyB(vx), vx, "x")),
                        equivalence_arriere(mem_B))   # a∈f⁻¹⟨B⟩
    aY = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_Y, x_cpl),
                                       N.s5(bodyY(vx), vx, "x")),
                        equivalence_arriere(mem_Y))   # a∈f⁻¹⟨Y⟩
    rhs_mem = N.modus_ponens(conjonction_intro(aB, aY), equivalence_arriere(inst_rhs))
    incl_imp = existe_elimination(N.loi_deduction(bodyI(vx), rhs_mem), "x")
    incl_LR = N.generalisation("z", N.loi_deduction(
        appartient(va, lhs), N.modus_ponens(ex_I, incl_imp)))   # (∀a)(a∈lhs⇒a∈rhs)

    # ── ⊇ : a∈rhs ⇒ a∈lhs  (UNIVALENCE) ───────────────────────────────────────
    h_rhs = N.assume(appartient(va, rhs))
    and_BY = N.modus_ponens(h_rhs, equivalence_avant(inst_rhs))
    ex_B = N.modus_ponens(conjonction_elim_gauche(and_BY), equivalence_avant(mem_B))  # (∃x)bodyB(x)
    ex_Y0 = N.modus_ponens(conjonction_elim_droite(and_BY), equivalence_avant(mem_Y)) # (∃x)bodyY(x)
    ex_Y = N.modus_ponens(ex_Y0, equivalence_avant(alpha_existe("x", "xp", bodyY(vx))))  # (∃xp)bodyY(xp)
    # sous témoins x (∈B) et x' (∈Y) : montrer (∃x)bodyI(x), donc a∈lhs.
    hbB = N.assume(bodyB(vx))     # x∈B et (x,a)∈f⁻¹
    hbY = N.assume(bodyY(vxp))    # x'∈Y et (x',a)∈f⁻¹
    x_in_B2 = conjonction_elim_gauche(hbB)
    xp_in_Y2 = conjonction_elim_gauche(hbY)
    x_cpl2 = conjonction_elim_droite(hbB)      # (x,a)∈f⁻¹
    xp_cpl2 = conjonction_elim_droite(hbY)     # (x',a)∈f⁻¹
    # convertir en f : (a,x)∈f, (a,x')∈f
    ax_f = N.modus_ponens(x_cpl2, equivalence_avant(couple_reciproque(vf, vx, va)))
    axp_f = N.modus_ponens(xp_cpl2, equivalence_avant(couple_reciproque(vf, vxp, va)))
    # univalence : ((a,x)∈f et (a,x')∈f) ⇒ x=x'
    x_eq_xp = N.modus_ponens(conjonction_intro(ax_f, axp_f),
                             _univalence(vf, hfunc, va, vx, vxp))   # x = x'
    # x'∈B (de x∈B par x=x') : x∈B et x'=x → x'∈B ; on veut x∈B∩Y donc besoin x∈Y.
    # x∈Y depuis x'∈Y et x=x' : congruence sur appartient(·,Y).
    # x'=x  (symétrie via S6 : (x=x') ⇒ ((x=x) ⇔ (x'=x)))
    xp_eq_x = N.modus_ponens(N.reflexivite(vx), equivalence_avant(
        N.modus_ponens(x_eq_xp, N.s6(vx, vxp, "w", egal(var("w"), vx)))))
    x_in_Y2 = N.modus_ponens(xp_in_Y2, equivalence_avant(
        N.modus_ponens(xp_eq_x, N.s6(vxp, vx, "w", appartient(var("w"), vy)))))  # x'∈Y ⇒ x∈Y
    x_in_inter2 = N.modus_ponens(conjonction_intro(x_in_B2, x_in_Y2),
                                 equivalence_arriere(_instance_inter(vb, vy, vx)))
    witnessI = conjonction_intro(x_in_inter2, x_cpl2)    # bodyI(x)
    ex_I2 = N.modus_ponens(witnessI, N.s5(bodyI(vx), vx, "x"))   # (∃x)bodyI(x)
    lhs_mem = N.modus_ponens(ex_I2, equivalence_arriere(mem_lhs))   # a∈lhs
    # décharger témoins x' puis x
    imp_after_Y = existe_elimination(N.loi_deduction(bodyY(vxp), lhs_mem), "xp")
    after_Y = N.modus_ponens(ex_Y, imp_after_Y)          # a∈lhs (sous témoin x)
    imp_after_B = existe_elimination(N.loi_deduction(bodyB(vx), after_Y), "x")
    incl_RL = N.generalisation("z", N.loi_deduction(
        appartient(va, rhs), N.modus_ponens(ex_B, imp_after_B)))   # (∀a)(a∈rhs⇒a∈lhs)

    eq = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                        extensionnalite_appliquee(lhs, rhs))       # lhs=rhs
    return N.loi_deduction(E.est_fonctionnel(vf), eq)


from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition


# ════════════════════════════════════════════════════════════════════════════
#  4. IMAGE DIRECTE D'UNE INTERSECTION — INCLUSION INCONDITIONNELLE  (E.II.25).
#     f⟨B∩Y⟩ ⊂ f⟨B⟩ ∩ f⟨Y⟩
#
#  ⚠ HONNÊTETÉ : l'ÉGALITÉ f⟨B∩Y⟩ = f⟨B⟩∩f⟨Y⟩ N'EST PAS vraie pour f seulement
#  `est_fonctionnel` (= application).  Bourbaki E.II.25 : l'inclusion ⊂ vaut
#  toujours, mais l'égalité exige f INJECTIVE (deux antécédents distincts x∈B,
#  x'∈Y de la même valeur a ne donnent PAS d'antécédent commun dans B∩Y).
#  est_fonctionnel contraint la VALEUR par antécédent, pas l'ANTÉCÉDENT par valeur.
#  On livre donc honnêtement l'INCLUSION inconditionnelle, sans postuler l'égalité.
#  (La version-égalité demanderait l'hyp `est_fonctionnel(reciproque(f))`, i.e.
#   l'injectivité de f, symétrique du lemme réciproque ci-dessus.)
# ════════════════════════════════════════════════════════════════════════════
def cible_image_inter_inclusion(f="f", b="B", y="Y"):
    vf, vb, vy = _t(f), _t(b), _t(y)
    lhs = E.image(vf, E.intersection(vb, vy))
    rhs = E.intersection(E.image(vf, vb), E.image(vf, vy))
    return E.inclus(lhs, rhs)


def image_inter_inclusion(f="f", b="B", y="Y"):
    """⊢ f⟨B∩Y⟩ ⊂ f⟨B⟩ ∩ f⟨Y⟩.   (E.II.25 — CLOS, 0 hyp, INCONDITIONNEL.)

    L'inclusion vaut pour f QUELCONQUE.  L'égalité réciproque exigerait f injective
    (cf. note du module) — NON livrée pour rester honnête."""
    vf, vb, vy = _t(f), _t(b), _t(y)
    va, vx = var("z"), var("x")
    inter = E.intersection(vb, vy)
    fB = E.image(vf, vb)
    fY = E.image(vf, vy)
    lhs = E.image(vf, inter)
    rhs = E.intersection(fB, fY)

    cpl = lambda u: appartient(E.couple(u, va), vf)        # (u,a)∈f
    bodyB = lambda u: et(appartient(u, vb), cpl(u))
    bodyY = lambda u: et(appartient(u, vy), cpl(u))
    bodyI = lambda u: et(appartient(u, inter), cpl(u))

    mem_lhs = membre_image(vf, inter, va)                  # a∈f⟨B∩Y⟩ ⇔ (∃x)bodyI(x)
    mem_B = membre_image(vf, vb, va)
    mem_Y = membre_image(vf, vy, va)
    inst_rhs = _instance_inter(fB, fY, va)

    h_lhs = N.assume(appartient(va, lhs))
    ex_I = N.modus_ponens(h_lhs, equivalence_avant(mem_lhs))
    hbI = N.assume(bodyI(vx))
    x_in_inter = conjonction_elim_gauche(hbI)
    x_cpl = conjonction_elim_droite(hbI)
    inter_eq = N.modus_ponens(x_in_inter, equivalence_avant(_instance_inter(vb, vy, vx)))
    x_in_B = conjonction_elim_gauche(inter_eq)
    x_in_Y = conjonction_elim_droite(inter_eq)
    aB = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_B, x_cpl),
                                       N.s5(bodyB(vx), vx, "x")), equivalence_arriere(mem_B))
    aY = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_Y, x_cpl),
                                       N.s5(bodyY(vx), vx, "x")), equivalence_arriere(mem_Y))
    rhs_mem = N.modus_ponens(conjonction_intro(aB, aY), equivalence_arriere(inst_rhs))
    return N.generalisation("z", N.loi_deduction(
        appartient(va, lhs),
        N.modus_ponens(ex_I, existe_elimination(N.loi_deduction(bodyI(vx), rhs_mem), "x"))))


# ════════════════════════════════════════════════════════════════════════════
#  3. IMAGE RÉCIPROQUE D'UNE DIFFÉRENCE — CONDITIONNEL  (E.II.27, Prop. 6).
#     est_fonctionnel(f) ⇒ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩
# ════════════════════════════════════════════════════════════════════════════
def cible_image_reciproque_difference(f="f", b="B", y="Y"):
    vf, vb, vy = _t(f), _t(b), _t(y)
    lhs = E.image(E.reciproque(vf), E.difference(vb, vy))
    rhs = E.difference(E.image(E.reciproque(vf), vb),
                       E.image(E.reciproque(vf), vy))
    return impl(E.est_fonctionnel(vf), egal(lhs, rhs))


def image_reciproque_difference(f="f", b="B", y="Y"):
    """⊢ est_fonctionnel(f) ⇒ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩.   (E.II.27 ; CLOS, 0 hyp.)

    ⊇ inconditionnel ; ⊆ via UNIVALENCE (si x∉Y mais a∈f⁻¹⟨Y⟩ via x', alors x=x'∈Y)."""
    vf, vb, vy = _t(f), _t(b), _t(y)
    va, vx, vxp = var("z"), var("x"), var("xp")
    diff = E.difference(vb, vy)
    fB = E.image(E.reciproque(vf), vb)
    fY = E.image(E.reciproque(vf), vy)
    lhs = E.image(E.reciproque(vf), diff)
    rhs = E.difference(fB, fY)

    hfunc = N.assume(E.est_fonctionnel(vf))
    cpl = lambda u: appartient(E.couple(u, va), E.reciproque(vf))   # (u,a)∈f⁻¹
    bodyB = lambda u: et(appartient(u, vb), cpl(u))
    bodyY = lambda u: et(appartient(u, vy), cpl(u))
    bodyD = lambda u: et(appartient(u, diff), cpl(u))

    mem_lhs = membre_image_reciproque(vf, diff, va)    # a∈f⁻¹⟨B∖Y⟩ ⇔ (∃x)bodyD(x)
    mem_B = membre_image_reciproque(vf, vb, va)        # a∈f⁻¹⟨B⟩   ⇔ (∃x)bodyB(x)
    mem_Y = membre_image_reciproque(vf, vy, va)        # a∈f⁻¹⟨Y⟩   ⇔ (∃x)bodyY(x)
    inst_rhs = _instance_diff(fB, fY, va)              # a∈rhs ⇔ (a∈f⁻¹⟨B⟩ et ¬a∈f⁻¹⟨Y⟩)
    aB_f = appartient(va, fB)
    aY_f = appartient(va, fY)

    # Sous-lemme commun : (a∈f⁻¹⟨Y⟩) ⇒ (x∈Y), VALIDE sous (x,a)∈f⁻¹ fixé + univalence.
    #   a∈f⁻¹⟨Y⟩ ⇒ (∃x')bodyY(x') ; sous x' : (x',a)∈f⁻¹, x'∈Y ; univalence x=x' ; x∈Y.
    def aY_implique_xinY(x_cpl):
        h_aY = N.assume(aY_f)
        ex_Yp0 = N.modus_ponens(h_aY, equivalence_avant(mem_Y))     # (∃x)bodyY(x)
        ex_Yp = N.modus_ponens(ex_Yp0, equivalence_avant(alpha_existe("x", "xp", bodyY(vx))))
        hbY = N.assume(bodyY(vxp))
        xp_in_Y = conjonction_elim_gauche(hbY)
        xp_cpl = conjonction_elim_droite(hbY)                       # (x',a)∈f⁻¹
        ax_f = N.modus_ponens(x_cpl, equivalence_avant(couple_reciproque(vf, vx, va)))    # (a,x)∈f
        axp_f = N.modus_ponens(xp_cpl, equivalence_avant(couple_reciproque(vf, vxp, va))) # (a,x')∈f
        x_eq_xp = N.modus_ponens(conjonction_intro(ax_f, axp_f),
                                 _univalence(vf, hfunc, va, vx, vxp))   # x=x'
        x_in_Y = N.modus_ponens(xp_in_Y, equivalence_arriere(
            N.modus_ponens(x_eq_xp, N.s6(vx, vxp, "w", appartient(var("w"), vy)))))  # (x∈Y⇔x'∈Y); ← : x'∈Y⇒x∈Y
        imp = existe_elimination(N.loi_deduction(bodyY(vxp), x_in_Y), "xp")
        return N.loi_deduction(aY_f, N.modus_ponens(ex_Yp, imp))    # ⊢ a∈f⁻¹⟨Y⟩ ⇒ x∈Y

    # ── ⊆ : a∈lhs ⇒ a∈rhs  (UNIVALENCE) ───────────────────────────────────────
    h_lhs = N.assume(appartient(va, lhs))
    ex_D = N.modus_ponens(h_lhs, equivalence_avant(mem_lhs))        # (∃x)bodyD(x)
    hbD = N.assume(bodyD(vx))
    x_in_diff = conjonction_elim_gauche(hbD)
    x_cpl = conjonction_elim_droite(hbD)                            # (x,a)∈f⁻¹
    x_in_B = conjonction_elim_gauche(N.modus_ponens(
        x_in_diff, equivalence_avant(_instance_diff(vb, vy, vx))))  # x∈B
    x_not_Y = conjonction_elim_droite(N.modus_ponens(
        x_in_diff, equivalence_avant(_instance_diff(vb, vy, vx))))  # ¬x∈Y
    aB = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_B, x_cpl),
                                       N.s5(bodyB(vx), vx, "x")),
                        equivalence_arriere(mem_B))                 # a∈f⁻¹⟨B⟩
    # ¬(a∈f⁻¹⟨Y⟩) par contraposition de (a∈f⁻¹⟨Y⟩⇒x∈Y) avec ¬x∈Y
    not_aY = N.modus_ponens(x_not_Y, contraposition(aY_implique_xinY(x_cpl)))  # ¬a∈f⁻¹⟨Y⟩
    rhs_mem = N.modus_ponens(conjonction_intro(aB, not_aY), equivalence_arriere(inst_rhs))
    incl_LR = N.generalisation("z", N.loi_deduction(
        appartient(va, lhs),
        N.modus_ponens(ex_D, existe_elimination(N.loi_deduction(bodyD(vx), rhs_mem), "x"))))

    # ── ⊇ : a∈rhs ⇒ a∈lhs  (inconditionnel) ───────────────────────────────────
    h_rhs = N.assume(appartient(va, rhs))
    and_rhs = N.modus_ponens(h_rhs, equivalence_avant(inst_rhs))
    aB2 = conjonction_elim_gauche(and_rhs)                          # a∈f⁻¹⟨B⟩
    not_aY2 = conjonction_elim_droite(and_rhs)                      # ¬a∈f⁻¹⟨Y⟩
    ex_B = N.modus_ponens(aB2, equivalence_avant(mem_B))            # (∃x)bodyB(x)
    hbB = N.assume(bodyB(vx))
    x_in_B2 = conjonction_elim_gauche(hbB)
    x_cpl2 = conjonction_elim_droite(hbB)                           # (x,a)∈f⁻¹
    # ¬x∈Y : si x∈Y alors a∈f⁻¹⟨Y⟩ (témoin x), contredit not_aY2.
    h_xY = N.assume(appartient(vx, vy))
    aY_from_x = N.modus_ponens(N.modus_ponens(conjonction_intro(h_xY, x_cpl2),
                                              N.s5(bodyY(vx), vx, "x")),
                               equivalence_arriere(mem_Y))          # a∈f⁻¹⟨Y⟩
    x_not_Y2 = N.modus_ponens(not_aY2, contraposition(
        N.loi_deduction(appartient(vx, vy), aY_from_x)))            # ¬x∈Y
    x_in_diff2 = N.modus_ponens(conjonction_intro(x_in_B2, x_not_Y2),
                                equivalence_arriere(_instance_diff(vb, vy, vx)))
    aD = N.modus_ponens(N.modus_ponens(conjonction_intro(x_in_diff2, x_cpl2),
                                       N.s5(bodyD(vx), vx, "x")),
                        equivalence_arriere(mem_lhs))               # a∈lhs
    incl_RL = N.generalisation("z", N.loi_deduction(
        appartient(va, rhs),
        N.modus_ponens(ex_B, existe_elimination(N.loi_deduction(bodyB(vx), aD), "x"))))

    eq = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                        extensionnalite_appliquee(lhs, rhs))
    return N.loi_deduction(E.est_fonctionnel(vf), eq)


__all__ = [
    "membre_image", "membre_image_reciproque",
    "image_reunion_binaire", "cible_image_reunion_binaire",
    "image_reciproque_inter_binaire", "cible_image_reciproque_inter_binaire",
    "image_reciproque_difference", "cible_image_reciproque_difference",
    "image_inter_inclusion", "cible_image_inter_inclusion",
]
