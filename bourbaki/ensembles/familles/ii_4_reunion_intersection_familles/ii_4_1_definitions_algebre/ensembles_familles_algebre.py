"""§II.4 — ALGÈBRE des réunions/intersections de familles (propositions restantes).

Module NEUF (vague II-B).  Ne MODIFIE AUCUN fichier existant ; complète
`ensembles_familles` (déf./monotonie/⋃_∅), `ensembles_familles_demorgan`
(Prop. 5 De Morgan), `ensembles_familles_reunion_props` (Prop. 3/4/6 images) et
`ensembles_chap2_props_restantes` (Cor. Prop. 1 constante, Prop. 1 reparamétrage)
SANS les dupliquer.

On formalise ici, VERBATIM, des propriétés ÉLÉMENTAIRES de E.II.4 encore non
prouvées comme énoncés autonomes :

  • BORNES de la famille (E.II.4.1, propriété fondamentale ⋂ ⊂ X_α ⊂ ⋃) :
        α∈I ⊢ ⋂_{ι∈I} X_ι ⊂ X_α            (`inter_incluse_terme`)
        α∈I ⊢ X_α ⊂ ⋃_{ι∈I} X_ι            (`terme_inclus_reunion`)
        α∈I ⊢ ⋂_{ι∈I} X_ι ⊂ ⋃_{ι∈I} X_ι   (`inter_incluse_reunion`, I≠∅)
    Les trois sont CONDITIONNÉES à l'hypothèse FIDÈLE α∈I (incarne I≠∅), jamais
    postulée.  (Sans I≠∅, ⋂ serait l'univers et ⊄ ⋃=∅.)

  • MONOTONIE EN L'ENSEMBLE D'INDICES (E.II.4.2, croissance par J↦⋃_{ι∈J}) :
        J⊂I ⊢ ⋃_{ι∈J} X_ι ⊂ ⋃_{ι∈I} X_ι   (`reunion_incluse_sous_indices`)
    INCONDITIONNELLE (modulo l'hypothèse fidèle J⊂I).  C'est la monotonie EN
    L'INDICE (à famille f fixée), complémentaire de la monotonie EN LES TERMES
    déjà fournie par `monotonie_reunion_famille`.

  • IMAGE RÉCIPROQUE D'UNE RÉUNION (E.II.4, Prop. 4, PREMIÈRE formule) :
        ⊢ f⁻¹⟨ ⋃_{ι∈I} Y_ι ⟩ = ⋃_{ι∈I} f⁻¹⟨Y_ι⟩     (`image_reciproque_reunion_famille`)
    INCONDITIONNELLE (contrairement à f⁻¹⟨⋂⟩ qui exige l'univalence) : l'image
    réciproque commute toujours avec ⋃.  Complète la Prop. 4 (`ensembles_familles_
    reunion_props` n'avait livré que f⁻¹⟨⋂⟩).  La famille (f⁻¹⟨Y_ι⟩)_ι et son
    axiome de valeur sont RÉUTILISÉS de `ensembles_familles_reunion_props`
    (famille_reciproque / theorie_valeur_reciproque) — AUCUN axiome neuf, et
    theorie_ensembles() reste à 22 axiomes.

STRATÉGIE : appartenance des deux membres calculée comme équivalence sur le
point, généralisée, puis A1 (egalite_par_extension) ; pour les inclusions,
loi de déduction sur « z∈· ⇒ z∈· » généralisée.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, appartient,
                                       existe, pourtout, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg, conjonction_elim_droite as cd,
    equivalence_avant, equivalence_arriere, instancie,
    equivalence_transitivite as etr, equivalence_symetrie as esym,
    et_congruence_droite, et_congruence_gauche)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    congruence_existe, existe_elimination, et_existe_gauche, existe_commute)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
# RÉUTILISATION (pas de duplication) de l'infra famille-réciproque déjà certifiée.
from bourbaki.ensembles.familles.ensembles_familles_reunion_props import (
    membre_image_reciproque, famille_reciproque, _val_recip, _membre_eq, _sym, _t)


# ── instances des axiomes de theorie_ensembles (22 ax., inchangée) ────────────
def _inst_reunion(f, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


# ══════════════════════════════════════════════════════════════════════════════
# BORNES — propriété fondamentale ⋂_{ι∈I} X_ι ⊂ X_α ⊂ ⋃_{ι∈I} X_ι   (E.II.4.1).
# ══════════════════════════════════════════════════════════════════════════════
def inter_incluse_terme(f="X", i="I", a="a"):
    """{α∈I} ⊢ ⋂_{ι∈I} X_ι ⊂ X_α.   (E.II.4.1 — l'intersection est sous chaque terme.)

    CONDITIONNÉE à l'hypothèse FIDÈLE α∈I (jamais postulée).
    z∈⋂X_ι ⇒ (∀i)(i∈I ⇒ z∈X_i) ; en i=α (α∈I) : z∈X_α."""
    vf, vI, va = _t(f), _t(i), _t(a)
    vz = var("z")
    inter = E.inter_famille(vf, vI)
    Xa = E.valeur_famille(vf, va)
    a_in = appartient(va, vI)
    hH = N.assume(a_in)

    hL = N.assume(appartient(vz, inter))
    fa = N.modus_ponens(hL, equivalence_avant(_inst_inter(vf, vI, vz)))  # (∀i)(i∈I ⇒ z∈X_i)
    z_Xa = N.modus_ponens(hH, instancie(fa, va))                        # z∈X_α
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, inter), z_Xa))
    return N.loi_deduction(a_in, incl)


def terme_inclus_reunion(f="X", i="I", a="a"):
    """{α∈I} ⊢ X_α ⊂ ⋃_{ι∈I} X_ι.   (E.II.4.1 — chaque terme est sous la réunion.)

    CONDITIONNÉE à l'hypothèse FIDÈLE α∈I (jamais postulée).
    z∈X_α avec α∈I : témoin ι=α de (∃ι)(ι∈I et z∈X_ι), d'où z∈⋃X_ι."""
    vf, vI, va = _t(f), _t(i), _t(a)
    vz, vi = var("z"), var("i")
    Xa = E.valeur_famille(vf, va)
    reun = E.reunion_famille(vf, vI)
    a_in = appartient(va, vI)
    hH = N.assume(a_in)

    hR = N.assume(appartient(vz, Xa))
    body = et(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    ex_a = N.modus_ponens(conjonction_intro(hH, hR), N.s5(body, va, "i"))  # (∃i)(i∈I et z∈X_i)
    z_reun = N.modus_ponens(ex_a, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, Xa), z_reun))
    return N.loi_deduction(a_in, incl)


def inter_incluse_reunion(f="X", i="I", a="a"):
    """{α∈I} ⊢ ⋂_{ι∈I} X_ι ⊂ ⋃_{ι∈I} X_ι.   (E.II.4.1 — I≠∅ via α∈I.)

    CONDITIONNÉE à l'hypothèse FIDÈLE α∈I (incarne I≠∅ ; sans elle l'inclusion est
    FAUSSE : ⋂_∅ serait l'univers, ⋃_∅=∅).  Composition transitive de
    ⋂ ⊂ X_α (`inter_incluse_terme`) et X_α ⊂ ⋃ (`terme_inclus_reunion`),
    toutes deux sous la même hypothèse α∈I."""
    vf, vI, va = _t(f), _t(i), _t(a)
    vz = var("z")
    inter = E.inter_famille(vf, vI)
    reun = E.reunion_famille(vf, vI)
    a_in = appartient(va, vI)
    hH = N.assume(a_in)

    incl1 = N.modus_ponens(hH, inter_incluse_terme(vf, vI, va))   # ⋂ ⊂ X_α
    incl2 = N.modus_ponens(hH, terme_inclus_reunion(vf, vI, va))  # X_α ⊂ ⋃
    # transitivité de ⊂ point par point : z∈⋂ ⇒ z∈X_α ⇒ z∈⋃
    step1 = instancie(incl1, vz)                                  # z∈⋂ ⇒ z∈X_α
    step2 = instancie(incl2, vz)                                  # z∈X_α ⇒ z∈⋃
    incl = N.generalisation("z", syllogisme(step1, step2))
    return N.loi_deduction(a_in, incl)


# ══════════════════════════════════════════════════════════════════════════════
# MONOTONIE EN L'ENSEMBLE D'INDICES   (E.II.4.2, croissance J ↦ ⋃_{ι∈J} X_ι).
# ══════════════════════════════════════════════════════════════════════════════
def reunion_incluse_sous_indices(f="X", j="J", i="I"):
    """{J ⊂ I} ⊢ ⋃_{ι∈J} X_ι ⊂ ⋃_{ι∈I} X_ι.   (E.II.4.2 — monotonie en l'indice.)

    À FAMILLE f FIXÉE, la réunion croît avec l'ensemble d'indices.  Complète la
    monotonie EN LES TERMES (`monotonie_reunion_famille`).  INCONDITIONNELLE
    modulo l'hypothèse FIDÈLE J⊂I.
    z∈⋃_{J} ⇒ (∃i)(i∈J et z∈X_i) ; pour ce témoin i, i∈J⊂I donne i∈I, d'où
    (i∈I et z∈X_i), soit z∈⋃_{I}."""
    vf, vJ, vI = _t(f), _t(j), _t(i)
    vz, vi = var("z"), var("i")
    Xi = E.valeur_famille(vf, vi)
    reunJ = E.reunion_famille(vf, vJ)
    reunI = E.reunion_famille(vf, vI)
    hyp = inclus(vJ, vI)                                # J⊂I = (∀z')(z'∈J ⇒ z'∈I)
    hH = N.assume(hyp)
    i_in_I_imp = instancie(hH, vi)                      # i∈J ⇒ i∈I

    hL = N.assume(appartient(vz, reunJ))
    exi = N.modus_ponens(hL, equivalence_avant(_inst_reunion(vf, vJ, vz)))  # (∃i)(i∈J et z∈X_i)
    body = et(appartient(vi, vJ), appartient(vz, Xi))
    hb = N.assume(body)
    i_in_I = N.modus_ponens(cg(hb), i_in_I_imp)        # i∈I
    bodyI = et(appartient(vi, vI), appartient(vz, Xi))
    ex_i = N.modus_ponens(conjonction_intro(i_in_I, cd(hb)), N.s5(bodyI, vi, "i"))
    z_reunI = N.modus_ponens(ex_i, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    imp_i = existe_elimination(N.loi_deduction(body, z_reunI), "i")
    z_in = N.modus_ponens(exi, imp_i)
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, reunJ), z_in))
    return N.loi_deduction(hyp, incl)


# ══════════════════════════════════════════════════════════════════════════════
# Prop. 4 (1re formule) — IMAGE RÉCIPROQUE d'une RÉUNION   (E.II.4, Prop. 4).
#   f⁻¹⟨⋃_{ι∈I} Y_ι⟩ = ⋃_{ι∈I} f⁻¹⟨Y_ι⟩       (INCONDITIONNELLE).
# ══════════════════════════════════════════════════════════════════════════════
def image_reciproque_reunion_famille(g="f", f="Y", i="I"):
    """⊢ f⁻¹⟨ ⋃_{ι∈I} Y_ι ⟩ = ⋃_{ι∈I} f⁻¹⟨Y_ι⟩.   (E.II.4, Prop. 4, 1re formule.)

    INCONDITIONNELLE (l'univalence n'est PAS requise, contrairement à f⁻¹⟨⋂⟩).
    f⁻¹⟨Z⟩ := image(reciproque(f), Z).  La famille (f⁻¹⟨Y_ι⟩)_ι et son axiome de
    valeur sont réutilisés de `ensembles_familles_reunion_props` (famille_reciproque
    / theorie_valeur_reciproque).  theorie_ensembles() inchangée (22 axiomes).

    a∈f⁻¹⟨⋃Y⟩ ⇔ (∃x)(x∈⋃Y et (a,x)∈f) ⇔ (∃x)((∃i)(i∈I et x∈Y_i) et (a,x)∈f) ;
    on commute ∃x∃i, regroupe, et tire (∃i)(i∈I et (∃x)(x∈Y_i et (a,x)∈f))
        = (∃i)(i∈I et a∈f⁻¹⟨Y_i⟩) = caractérisation de ⋃f⁻¹⟨Y·⟩."""
    vg, vfam, vI = _t(g), _t(f), _t(i)
    va, vx, vi = var("a"), var("x"), var("i")
    Yi = E.valeur_famille(vfam, vi)
    reun = E.reunion_famille(vfam, vI)
    fam_rec = famille_reciproque(vg, vfam)
    ax_couple = appartient(E.couple(va, vx), vg)        # (a,x)∈f

    # ── membre gauche : a∈f⁻¹⟨⋃Y⟩ ⇔ (∃i)(i∈I et (∃x)(x∈Y_i et (a,x)∈f)) ─────────
    L = membre_image_reciproque(vg, reun, va)           # ⇔ (∃x)(x∈⋃Y et (a,x)∈f)
    reun_x = _inst_reunion(vfam, vI, vx)                # x∈⋃Y ⇔ (∃i)(i∈I et x∈Y_i)
    L2 = etr(L, congruence_existe(et_congruence_gauche(reun_x, ax_couple), "x"))
    Pi = et(appartient(vi, vI), appartient(vx, Yi))     # (i∈I et x∈Y_i)
    # ((∃i)Pi et (a,x)∈f) ⇔ (∃i)(Pi et (a,x)∈f)   (i non libre dans (a,x)∈f)
    L3 = etr(L2, congruence_existe(et_existe_gauche("i", Pi, ax_couple), "x"))
    L4 = etr(L3, existe_commute("x", "i", et(Pi, ax_couple)))   # ⇔ (∃i)(∃x)(Pi et (a,x)∈f)
    # réarranger ((i∈I et x∈Y_i) et (a,x)∈f) ⇔ (i∈I et (x∈Y_i et (a,x)∈f))
    rearr = _assoc_et_droite(appartient(vi, vI), appartient(vx, Yi), ax_couple)
    inner_S = et(appartient(vx, Yi), ax_couple)
    # tirer (∃x) sous (i∈I et ·) :  (∃x)(i∈I et inner_S) ⇔ (i∈I et (∃x)inner_S)
    pull_x = et_existe_droite_sym(appartient(vi, vI), "x", inner_S)
    L5 = etr(L4, congruence_existe(etr(congruence_existe(rearr, "x"), pull_x), "i"))
    char_L = N.generalisation("a", L5)

    # ── membre droit : a∈⋃f⁻¹⟨Y·⟩ ⇔ (∃i)(i∈I et (∃x)(x∈Y_i et (a,x)∈f)) ─────────
    R = _inst_reunion(fam_rec, vI, va)                  # ⇔ (∃i)(i∈I et a∈(f⁻¹⟨Y·⟩)_i)
    val_eq = _membre_eq(E.valeur_famille(fam_rec, vi),
                        E.image(E.reciproque(vg), Yi), _val_recip(vg, vfam, vi), va)
    membre_i = etr(val_eq, membre_image_reciproque(vg, Yi, va))  # a∈(f⁻¹⟨Y·⟩)_i ⇔ (∃x)(x∈Y_i et (a,x)∈f)
    R2 = etr(R, congruence_existe(et_congruence_droite(appartient(vi, vI), membre_i), "i"))
    char_R = N.generalisation("a", R2)

    return egalite_par_extension(char_L, char_R,
                                 E.image(E.reciproque(vg), reun),
                                 E.reunion_famille(fam_rec, vI))


# ── micro-tactiques propositionnelles / quantificationnelles locales ──────────
def _assoc_et_droite(a, b, c):
    """⊢ ((A et B) et C) ⇔ (A et (B et C))."""
    h1 = N.assume(et(et(a, b), c))
    ab = cg(h1)
    fwd = N.loi_deduction(et(et(a, b), c),
                          conjonction_intro(cg(ab), conjonction_intro(cd(ab), cd(h1))))
    h2 = N.assume(et(a, et(b, c)))
    bc = cd(h2)
    bwd = N.loi_deduction(et(a, et(b, c)),
                          conjonction_intro(conjonction_intro(cg(h2), cg(bc)), cd(bc)))
    return conjonction_intro(fwd, bwd)


def et_existe_droite_sym(p, y, q):
    """⊢ (∃y)(P et Q) ⇔ (P et (∃y)Q)   (symétrique de et_existe_droite ; y∉P)."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import et_existe_droite
    return esym(et_existe_droite(p, y, q))


__all__ = [
    "inter_incluse_terme", "terme_inclus_reunion", "inter_incluse_reunion",
    "reunion_incluse_sous_indices", "image_reciproque_reunion_famille",
]
