"""§III.3 — LEMME FONDATEUR « 0 ≠ 1 » :  ⊢ ¬ Eq(∅, {∅}).

Le vide n'est PAS équipotent au singleton {∅}.  Équivaut à Card(∅) ≠ Card({∅})
(via proposition_1_cardinaux), socle de la distinction des entiers naturels (0 ≠ 1),
prérequis de la récurrence C61 et de la Prop. 8 §III.3.

PREUVE (par réfutation de bijection, calquée sur cantor_non_equipotent) :
  Eq(∅, {∅}) = (∃F)(F est le graphe d'une bijection de ∅ sur {∅}).  Pour un tel F :
    • la surjectivité impose  image(F, ∅) = {∅}   (2ᵉ conjoint de est_bijective) ;
    • mais l'image du vide est toujours vide :  image(F, ∅) = ∅   (image_sur_vide,
      car z ∈ F⟨∅⟩ ⇔ (∃x)(x∈∅ et (x,z)∈F) est toujours faux : x∈∅ impossible) ;
    • par transitivité,  {∅} = ∅,  donc  ∅ = {∅}.
  Or  ∅ ≠ {∅}   (vide_distinct_singleton, car ∅∈{∅} mais ¬(∅∈∅)) : contradiction.
  L'hypothèse « F bijection de ∅ sur {∅} » se réfute donc elle-même, d'où ¬Eq(∅, {∅}).

Lemmes (chacun CLOS, certifié noyau, réutilisable) :
  • image_sur_vide          ⊢ image(F, ∅) = ∅      (l'image directe du vide est vide) ;
  • vide_distinct_singleton ⊢ ¬(∅ = {∅})           (le vide n'est pas son singleton) ;
  • vide_non_equipotent_singleton ⊢ ¬ Eq(∅, {∅})   (le théorème fondateur 0 ≠ 1).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, non, et, appartient, existe
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (instancie, equivalence_avant, equivalence_arriere,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               conjonction_intro)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent


def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.   (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    a_imp_z = N.modus_ponens(thm_na, N.s2(non(a), z))   # ¬A ⇒ (A ⇒ Z), appliqué : (A ⇒ Z)
    return N.modus_ponens(thm_a, a_imp_z)               # Z


# ── Lemme 1 : image(F, ∅) = ∅ ─────────────────────────────────────────────────
def image_sur_vide(f="F"):
    """⊢ image(F, ∅) = ∅.   (l'image directe du vide par n'importe quel graphe est vide.)

    Par extension (A1).  AXIOME_IMAGE :  z ∈ F⟨∅⟩ ⇔ (∃x)(x∈∅ et (x,z)∈F).
      • ⇒ : sous le corps (x∈∅ et (x,z)∈F), x∈∅ est impossible (AXIOME_VIDE),
            ex falso donne z∈∅ ; ∃-élimination → z∈F⟨∅⟩ ⇒ z∈∅, d'où F⟨∅⟩ ⊂ ∅ ;
      • ⇐ : z∈∅ impossible (AXIOME_VIDE), ex falso donne z∈F⟨∅⟩, d'où ∅ ⊂ F⟨∅⟩.
    La double inclusion + extensionnalité A1 donnent l'égalité."""
    vF, vz, vx = var(f), var("z"), var("x")
    imgFvide = E.image(vF, E.VIDE)
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)   # (∀G∀X∀y)(y∈G⟨X⟩ ⇔ …)

    # caractérisation de l'image du vide (liant interne « x » conservé : F, ∅ sans « x » lié)
    img_car = instancie(instancie(instancie(ax_img, vF), E.VIDE), vz)  # z∈F⟨∅⟩ ⇔ (∃x)(x∈∅ et (x,z)∈F)

    # ── sens direct : z∈F⟨∅⟩ ⇒ z∈∅ ──────────────────────────────────────────
    body = et(appartient(vx, E.VIDE), appartient(E.couple(vx, vz), vF))   # x∈∅ et (x,z)∈F
    hb = N.assume(body)
    x_in_vide = conjonction_elim_gauche(hb)                   # x∈∅
    nx_vide = instancie(ax_vide, vx)                          # ¬(x∈∅)
    z_in_vide_body = _ex_falso(x_in_vide, nx_vide, appartient(vz, E.VIDE))    # z∈∅  (sous body)
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_vide_body), "x")   # (∃x)body ⇒ z∈∅
    hz = N.assume(appartient(vz, imgFvide))
    ex = N.modus_ponens(hz, equivalence_avant(img_car))       # (∃x)body
    z_in_vide = N.modus_ponens(ex, ex_imp)                    # z∈∅
    img_sub_vide = N.generalisation("z", N.loi_deduction(appartient(vz, imgFvide), z_in_vide))  # F⟨∅⟩ ⊂ ∅

    # ── réciproque : z∈∅ ⇒ z∈F⟨∅⟩ ───────────────────────────────────────────
    nz_vide = instancie(ax_vide, vz)                          # ¬(z∈∅)
    hzv = N.assume(appartient(vz, E.VIDE))
    z_in_img_body = _ex_falso(hzv, nz_vide, appartient(vz, imgFvide))         # z∈F⟨∅⟩  (sous z∈∅)
    vide_sub_img = N.generalisation("z", N.loi_deduction(appartient(vz, E.VIDE), z_in_img_body))  # ∅ ⊂ F⟨∅⟩

    ext = extensionnalite_appliquee(imgFvide, E.VIDE)         # (F⟨∅⟩⊂∅ et ∅⊂F⟨∅⟩) ⇒ F⟨∅⟩=∅
    return N.modus_ponens(conjonction_intro(img_sub_vide, vide_sub_img), ext)


# ── Lemme 2 : ¬(∅ = {∅}) ──────────────────────────────────────────────────────
def vide_distinct_singleton():
    """⊢ ¬(∅ = {∅}).   (le vide n'est pas égal à son singleton.)

    Si ∅ = {∅}, alors de ∅∈{∅} (AXIOME_PAIRE + réflexivité) et {∅}=∅ (symétrie),
    Leibniz (S6) donne ∅∈∅, qui contredit ¬(∅∈∅) (AXIOME_VIDE).  D'où ¬(∅={∅})."""
    vide, sing = E.VIDE, E.singleton(E.VIDE)                  # ∅ , {∅}={∅,∅}

    # ∅∈{∅} :  AXIOME_PAIRE instancié à (∅,∅,∅) donne (∅∈{∅,∅}) ⇔ (∅=∅ ∨ ∅=∅)
    ax_paire = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)
    char = instancie(instancie(instancie(ax_paire, vide), vide), vide)
    refl = N.reflexivite(vide)                               # ∅=∅
    oraa = N.modus_ponens(refl, N.s2(egal(vide, vide), egal(vide, vide)))   # (∅=∅)∨(∅=∅)
    vide_in_sing = N.modus_ponens(oraa, equivalence_arriere(char))          # ∅∈{∅}

    # ¬(∅∈∅) :  AXIOME_VIDE instancié à ∅
    nvv = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vide)   # ¬(∅∈∅)

    # sous ∅={∅} : Leibniz → ∅∈∅, contradiction
    h = N.assume(egal(vide, sing))
    sing_eq_vide = N.modus_ponens(h, symetrie(vide, sing))   # {∅}=∅
    leib = N.s6(sing, vide, "w", appartient(vide, var("w"))) # ({∅}=∅) ⇒ ((∅∈{∅}) ⇔ (∅∈∅))
    equ = N.modus_ponens(sing_eq_vide, leib)
    vide_in_vide = N.modus_ponens(vide_in_sing, equivalence_avant(equ))     # ∅∈∅
    contra = _ex_falso(vide_in_vide, nvv, non(egal(vide, sing)))            # ¬(∅={∅})  (sous ∅={∅})
    imp = N.loi_deduction(egal(vide, sing), contra)          # (∅={∅}) ⇒ ¬(∅={∅})
    return N.modus_ponens(imp, N.s1(non(egal(vide, sing))))  # ¬(∅={∅})


# ── Théorème fondateur : ¬ Eq(∅, {∅})  (« 0 ≠ 1 ») ────────────────────────────
def vide_non_equipotent_singleton():
    """⊢ ¬ Eq(∅, {∅}).   (LEMME FONDATEUR : le vide n'est PAS équipotent à {∅}.)

    Eq(∅, {∅}) = (∃F)(F bijection de ∅ sur {∅}).  Pour un tel F, la surjectivité
    donne image(F,∅) = {∅} ; or image(F,∅) = ∅ (image_sur_vide) ; transitivité →
    {∅} = ∅, donc ∅ = {∅}, contredisant vide_distinct_singleton.  Sous bij : ¬Eq
    (ex falso) ; F non libre dans ¬Eq → (∃F)bij ⇒ ¬Eq = Eq ⇒ ¬Eq ; S1 conclut ¬Eq.

    Équivaut, via proposition_1_cardinaux, à Card(∅) ≠ Card({∅}), soit 0 ≠ 1."""
    vide, sing = E.VIDE, E.singleton(E.VIDE)
    vF = var("F")
    bij = est_bijection_de(vF, vide, sing)                    # F bijection de ∅ sur {∅}
    Eq = equipotent(vide, sing)                              # (∃F)bij

    hbij = N.assume(bij)
    # est_bijection_de = et(et(func, dom), et(injective_dans, est_surjective))
    # est_surjective(F,∅,{∅}) = (image(F,∅) = {∅})  → 2ᵉ conjoint du 2ᵉ conjoint
    surj = conjonction_elim_droite(conjonction_elim_droite(hbij))   # image(F,∅) = {∅}

    img_vide = image_sur_vide("F")                           # image(F,∅) = ∅
    sing_eq_imgF = N.modus_ponens(surj, symetrie(E.image(vF, vide), sing))  # {∅} = image(F,∅)
    sing_eq_vide = composer_egalites(sing_eq_imgF, img_vide)  # {∅} = ∅
    vide_eq_sing = N.modus_ponens(sing_eq_vide, symetrie(sing, vide))       # ∅ = {∅}

    vds = vide_distinct_singleton()                          # ¬(∅ = {∅})
    notEq_under = _ex_falso(vide_eq_sing, vds, non(Eq))      # ¬Eq  (sous bij)
    bij_imp = N.loi_deduction(bij, notEq_under)              # bij ⇒ ¬Eq
    Eq_imp = existe_elimination(bij_imp, "F")               # Eq ⇒ ¬Eq   (F non libre dans ¬Eq)
    return N.modus_ponens(Eq_imp, N.s1(non(Eq)))            # ¬Eq(∅, {∅})


__all__ = ["image_sur_vide", "vide_distinct_singleton", "vide_non_equipotent_singleton"]
