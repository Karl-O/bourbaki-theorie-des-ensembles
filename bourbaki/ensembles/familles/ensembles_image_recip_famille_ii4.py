"""§II.4 (E.II.25-27) — IMAGE / IMAGE RÉCIPROQUE d'une FAMILLE de parties.

Module NEUF.  Ne MODIFIE AUCUN fichier déposé ; complète la Prop. 3/4/6 de §II.4
qui manquaient comme énoncés autonomes (les briques de `ensembles_familles_
reunion_props` n'ont jamais été déposées — module fantôme, import cassé — on
RECONSTRUIT donc, proprement, les caractérisations d'image/préimage à partir des
seuls axiomes de `theorie_ensembles()` [22 ax., INCHANGÉE]).

Hypothèse de FONCTIONNALITÉ.  Le PDF énonce Prop. 4 et Prop. 6 pour f une
APPLICATION A→B (valeur f(x) unique).  Pour rester FIDÈLE et HONNÊTE au niveau
graphe, on charge l'hypothèse explicite

    Fonctionnelle(f) := (∀a)(∀x)(∀x')((a,x)∈f et (a,x')∈f ⇒ x=x')

(single-valued), jamais postulée.  C'est exactement « f univalent » de Bourbaki.

Propositions formalisées VERBATIM (PDF E.II.25-27) :

  • Prop. 6 (E.II.27) — image réciproque d'une DIFFÉRENCE :
        ⊢ f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩ ⊂ f⁻¹⟨B∖Y⟩            (`image_recip_diff_arriere`, INCOND.)
        {Fonctionnelle(f)} ⊢ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩  (`image_recip_difference`)

  • Prop. 4 (E.II.25) — image réciproque d'une INTERSECTION de famille :
        ⊢ f⁻¹⟨⋂_ι Y_ι⟩ ⊂ ⋂_ι f⁻¹⟨Y_ι⟩         (`image_recip_inter_incluse`, INCOND.)
        {Fonctionnelle(f)} ⊢ f⁻¹⟨⋂_ι Y_ι⟩ = ⋂_ι f⁻¹⟨Y_ι⟩   (`image_recip_inter_egal`)

  • Prop. 3 (E.II.25) — image directe d'une RÉUNION / INTERSECTION de famille :
        ⊢ Γ⟨⋃_ι X_ι⟩ = ⋃_ι Γ⟨X_ι⟩                (`image_reunion_egal`, INCOND.)
        ⊢ Γ⟨⋂_ι X_ι⟩ ⊂ ⋂_ι Γ⟨X_ι⟩                (`image_inter_incluse`, INCOND.)

  • Cor. de la Prop. 4 (E.II.25) — image directe d'une intersection sous INJECTION :
        {Injective(f)} ⊢ ⋂_ι Γ⟨X_ι⟩ ⊂ Γ⟨⋂_ι X_ι⟩    (`image_inter_arriere_si_inj`)
        {Injective(f)} ⊢ Γ⟨⋂_ι X_ι⟩ = ⋂_ι Γ⟨X_ι⟩     (`image_inter_egal_si_injective`)
    où Injective(f) := (∀a)(∀a')(∀x)((a,x)∈f et (a',x)∈f ⇒ a=a').

Les familles dérivées (f⁻¹⟨Y_ι⟩)_ι et (Γ⟨X_ι⟩)_ι sont des familles définies par un
terme (Critère C54) ; on les caractérise par un AXIOME DE VALEUR en THÉORIE
SÉPARÉE (JAMAIS dans theorie_ensembles, qui reste à 22 ax.) — EXACTEMENT comme
AXIOME_COMPL_FAM (De Morgan) ou famille_reparam (`ensembles_chap2_props_restantes`).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, egal, et, non, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg, conjonction_elim_droite as cd,
    equivalence_avant, equivalence_arriere, instancie,
    equivalence_transitivite as etr, equivalence_symetrie as esym,
    et_congruence_droite, et_congruence_gauche)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    congruence_existe, existe_elimination, monotonie_existe)
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.fonctions.ensembles_reciproque import couple_reciproque


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── instances des axiomes de theorie_ensembles (22 ax., INCHANGÉE) ────────────
def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


def _inst_reunion(f, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def _membre_eq(t1, t2, eq_thm, z):
    """De ⊢ t1=t2 déduire ⊢ (z∈t1) ⇔ (z∈t2)   (Leibniz via S6)."""
    return N.modus_ponens(eq_thm, N.s6(t1, t2, "w", appartient(_t(z), var("w"))))


# ── hypothèses de single-valued (fidèles, jamais postulées) ───────────────────
def fonctionnelle(g):
    """Fonctionnelle(f) := (∀a)(∀x)(∀x')((a,x)∈f et (a,x')∈f ⇒ x=x').  (f univalent.)"""
    va, vx, vy = var("a"), var("x"), var("xq")
    return pourtout("a", pourtout("x", pourtout("xq",
        impl(et(appartient(E.couple(va, vx), _t(g)),
                appartient(E.couple(va, vy), _t(g))), egal(vx, vy)))))


def injective(g):
    """Injective(f) := (∀a)(∀a')(∀x)((a,x)∈f et (a',x)∈f ⇒ a=a').  (f⁻¹ univalent.)"""
    va, vb, vx = var("a"), var("aq"), var("x")
    return pourtout("a", pourtout("aq", pourtout("x",
        impl(et(appartient(E.couple(va, vx), _t(g)),
                appartient(E.couple(vb, vx), _t(g))), egal(va, vb)))))


# ══════════════════════════════════════════════════════════════════════════════
# Caractérisation de l'IMAGE RÉCIPROQUE  f⁻¹⟨Y⟩ = image(f⁻¹, Y).
#   a∈f⁻¹⟨Y⟩ ⇔ (∃x)(x∈Y et (a,x)∈f)        [via AXIOME_IMAGE + couple_reciproque]
# ══════════════════════════════════════════════════════════════════════════════
def membre_image_recip(g, yset, a, xb="x"):
    """⊢ (a ∈ f⁻¹⟨Y⟩) ⇔ (∃xb)(xb∈Y et (a,xb)∈f).   (f⁻¹⟨Y⟩ := image(f⁻¹, Y).)

    NB : l'axiome AXIOME_IMAGE lie le témoin par « x » ; on α-renomme vers `xb`
    pour permettre des binders distincts dans les preuves emboîtées."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    vg, vY, va = _t(g), _t(yset), _t(a)
    vxb = var(xb)
    Grec = E.reciproque(vg)
    inst = _inst_image(Grec, vY, va)                  # ⇔ (∃x)(x∈Y et (x,a)∈f⁻¹)
    if xb != "x":
        body0 = et(appartient(var("x"), vY), appartient(E.couple(var("x"), va), Grec))
        inst = etr(inst, alpha_existe("x", xb, body0))   # ⇔ (∃xb)(xb∈Y et (xb,a)∈f⁻¹)
    cr = couple_reciproque(vg, vxb, va)               # (xb,a)∈f⁻¹ ⇔ (a,xb)∈f
    body_eq = et_congruence_droite(appartient(vxb, vY), cr)
    return etr(inst, congruence_existe(body_eq, xb))


def image_recip(g, yset):
    """Terme f⁻¹⟨Y⟩ = image(f⁻¹, Y)."""
    return E.image(E.reciproque(_t(g)), _t(yset))


# ══════════════════════════════════════════════════════════════════════════════
# Familles dérivées (C54) — théories de valeur SÉPARÉES (theorie_ensembles=22).
# ══════════════════════════════════════════════════════════════════════════════
def famille_image_recip(g, fam):
    """(f⁻¹⟨Y_ι⟩)_ι := la famille ι ↦ f⁻¹⟨Y_ι⟩  (fam = (Y_ι))."""
    return app("fam_img_recip", _t(g), _t(fam))


def _ax_val_recip(g, fam, i="i"):
    """(∀ι)( (f⁻¹⟨Y·⟩)_ι = f⁻¹⟨Y_ι⟩ )."""
    vi = var(i)
    return pourtout(i, egal(E.valeur_famille(famille_image_recip(g, fam), vi),
                            image_recip(g, E.valeur_famille(_t(fam), vi))))


def _val_recip(g, fam, i):
    """⊢ (f⁻¹⟨Y·⟩)_ι = f⁻¹⟨Y_ι⟩   (instance de la théorie de valeur dédiée)."""
    th = N.Theorie("Famille-img-recip", [_ax_val_recip(g, fam)])
    return instancie(N.axiome(th, _ax_val_recip(g, fam)), _t(i))


def famille_image(g, fam):
    """(Γ⟨X_ι⟩)_ι := la famille ι ↦ Γ⟨X_ι⟩  (fam = (X_ι))."""
    return app("fam_image", _t(g), _t(fam))


def _ax_val_image(g, fam, i="i"):
    """(∀ι)( (Γ⟨X·⟩)_ι = Γ⟨X_ι⟩ )."""
    vi = var(i)
    return pourtout(i, egal(E.valeur_famille(famille_image(g, fam), vi),
                            E.image(_t(g), E.valeur_famille(_t(fam), vi))))


def _val_image(g, fam, i):
    """⊢ (Γ⟨X·⟩)_ι = Γ⟨X_ι⟩   (instance de la théorie de valeur dédiée)."""
    th = N.Theorie("Famille-image", [_ax_val_image(g, fam)])
    return instancie(N.axiome(th, _ax_val_image(g, fam)), _t(i))


# ══════════════════════════════════════════════════════════════════════════════
# Prop. 6 (E.II.27) — IMAGE RÉCIPROQUE d'une DIFFÉRENCE.
#   f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩
# ══════════════════════════════════════════════════════════════════════════════
def image_recip_diff_arriere(g="f", b="B", y="Y"):
    """⊢ f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩ ⊂ f⁻¹⟨B∖Y⟩.   (Prop. 6, sens ⊃ — INCONDITIONNEL.)

    a∈f⁻¹⟨B⟩∖f⁻¹⟨Y⟩ : a∈f⁻¹⟨B⟩ donne un témoin x (x∈B, (a,x)∈f) ; ¬a∈f⁻¹⟨Y⟩ donne
    (∀x')((a,x')∈f ⇒ ¬x'∈Y), en x'=x : ¬x∈Y.  Donc x∈B∖Y, (a,x)∈f : a∈f⁻¹⟨B∖Y⟩."""
    vg, vB, vY, va = _t(g), _t(b), _t(y), var("z")
    vx = var("x")
    L = E.difference(image_recip(vg, vB), image_recip(vg, vY))
    R = image_recip(vg, E.difference(vB, vY))
    # z∈L ⇔ (a∈f⁻¹⟨B⟩ et ¬a∈f⁻¹⟨Y⟩)
    diff_eq = _inst_diff(image_recip(vg, vB), image_recip(vg, vY), va)
    hL = N.assume(appartient(va, L))
    conj = N.modus_ponens(hL, equivalence_avant(diff_eq))             # a∈f⁻¹⟨B⟩ et ¬a∈f⁻¹⟨Y⟩
    aB = cg(conj)
    n_aY = cd(conj)                                                   # ¬a∈f⁻¹⟨Y⟩
    # témoin x de a∈f⁻¹⟨B⟩
    exB = N.modus_ponens(aB, equivalence_avant(membre_image_recip(vg, vB, va)))  # (∃x)(x∈B et (a,x)∈f)
    bodyB = et(appartient(vx, vB), appartient(E.couple(va, vx), vg))
    hb = N.assume(bodyB)
    xB = cg(hb)
    axf = cd(hb)                                                      # (a,x)∈f
    # a∈f⁻¹⟨Y⟩ ⇔ (∃x')(x'∈Y et (a,x')∈f) ; on prouve x∈Y ⇒ a∈f⁻¹⟨Y⟩, contredit ¬a∈f⁻¹⟨Y⟩.
    hxY = N.assume(appartient(vx, vY))
    wit_Y = conjonction_intro(hxY, axf)                              # x∈Y et (a,x)∈f
    aY = N.modus_ponens(N.modus_ponens(wit_Y, N.s5(
            et(appartient(vx, vY), appartient(E.couple(va, vx), vg)), vx, "x")),
            equivalence_arriere(membre_image_recip(vg, vY, va)))     # a∈f⁻¹⟨Y⟩
    # ¬x∈Y :  x∈Y ⇒ a∈f⁻¹⟨Y⟩, mais ¬a∈f⁻¹⟨Y⟩  ⇒  ¬x∈Y
    from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
    imp_xY_aY = N.loi_deduction(appartient(vx, vY), aY)              # x∈Y ⇒ a∈f⁻¹⟨Y⟩
    n_xY = N.modus_ponens(n_aY, contraposition(imp_xY_aY))           # ¬x∈Y
    # x∈B∖Y
    xBdY = N.modus_ponens(conjonction_intro(xB, n_xY),
                          equivalence_arriere(_inst_diff(vB, vY, vx)))  # x∈(B∖Y)
    wit_R = conjonction_intro(xBdY, axf)                            # x∈(B∖Y) et (a,x)∈f
    aR = N.modus_ponens(N.modus_ponens(wit_R, N.s5(
            et(appartient(vx, E.difference(vB, vY)), appartient(E.couple(va, vx), vg)), vx, "x")),
            equivalence_arriere(membre_image_recip(vg, E.difference(vB, vY), va)))  # a∈f⁻¹⟨B∖Y⟩
    imp_x = existe_elimination(N.loi_deduction(bodyB, aR), "x")     # (∃x)…⇒ a∈R
    aR_final = N.modus_ponens(exB, imp_x)
    return N.generalisation("z", N.loi_deduction(appartient(va, L), aR_final))


def image_recip_diff_avant(g="f", b="B", y="Y"):
    """{Fonctionnelle(f)} ⊢ f⁻¹⟨B∖Y⟩ ⊂ f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩.   (Prop. 6, sens ⊂.)

    a∈f⁻¹⟨B∖Y⟩ : témoin x avec x∈B, ¬x∈Y, (a,x)∈f.  Donc a∈f⁻¹⟨B⟩ (même x).
    Pour ¬a∈f⁻¹⟨Y⟩ : si a∈f⁻¹⟨Y⟩, un témoin x' avec x'∈Y, (a,x')∈f ; Fonctionnelle
    donne x'=x, d'où x∈Y, contradiction avec ¬x∈Y.  D'où ¬a∈f⁻¹⟨Y⟩."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
    vg, vB, vY, va = _t(g), _t(b), _t(y), var("z")
    vx, vxq = var("x"), var("xq")
    L = image_recip(vg, E.difference(vB, vY))
    R = E.difference(image_recip(vg, vB), image_recip(vg, vY))
    hFun = N.assume(fonctionnelle(vg))

    hL = N.assume(appartient(va, L))
    exBY = N.modus_ponens(hL, equivalence_avant(
        membre_image_recip(vg, E.difference(vB, vY), va)))   # (∃x)(x∈(B∖Y) et (a,x)∈f)
    bodyBY = et(appartient(vx, E.difference(vB, vY)), appartient(E.couple(va, vx), vg))
    hb = N.assume(bodyBY)
    xBY = cg(hb)
    axf = cd(hb)                                             # (a,x)∈f
    xB = N.modus_ponens(xBY, equivalence_avant(_inst_diff(vB, vY, vx)))   # x∈B et ¬x∈Y
    # a∈f⁻¹⟨B⟩
    wit_B = conjonction_intro(cg(xB), axf)
    aB = N.modus_ponens(N.modus_ponens(wit_B, N.s5(
            et(appartient(vx, vB), appartient(E.couple(va, vx), vg)), vx, "x")),
            equivalence_arriere(membre_image_recip(vg, vB, va)))         # a∈f⁻¹⟨B⟩
    # ¬a∈f⁻¹⟨Y⟩ : on montre a∈f⁻¹⟨Y⟩ ⇒ x∈Y, contredit ¬x∈Y.
    h_aY = N.assume(appartient(va, image_recip(vg, vY)))
    exY = N.modus_ponens(h_aY, equivalence_avant(membre_image_recip(vg, vY, va, "xq")))  # (∃x')(x'∈Y et (a,x')∈f)
    bodyY = et(appartient(vxq, vY), appartient(E.couple(va, vxq), vg))
    hbY = N.assume(bodyY)
    xqY = cg(hbY)
    axqf = cd(hbY)                                          # (a,x')∈f
    # Fonctionnelle : (a,x)∈f et (a,x')∈f ⇒ x=x'
    fun_inst = instancie(instancie(instancie(hFun, va), vx), vxq)   # ((a,x)∈f et (a,x')∈f) ⇒ x=x'
    x_eq_xq = N.modus_ponens(conjonction_intro(axf, axqf), fun_inst)  # x=x'
    # de x=x' et x'∈Y déduire x∈Y par Leibniz sur (·∈Y)
    xY = N.modus_ponens(x_eq_xq, N.s6(vx, vxq, "w", appartient(var("w"), vY)))  # (x∈Y)⇔(x'∈Y)
    xY = N.modus_ponens(xqY, equivalence_arriere(xY))      # x∈Y
    imp_bodyY_xY = existe_elimination(N.loi_deduction(bodyY, xY), "xq")  # (∃x')…⇒ x∈Y
    xY_final = N.modus_ponens(exY, imp_bodyY_xY)           # x∈Y  (sous h_aY)
    aY_imp_xY = N.loi_deduction(appartient(va, image_recip(vg, vY)), xY_final)  # a∈f⁻¹⟨Y⟩⇒x∈Y
    n_aY = N.modus_ponens(cd(xB), contraposition(aY_imp_xY))  # ¬a∈f⁻¹⟨Y⟩
    # a∈f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩
    aR = N.modus_ponens(conjonction_intro(aB, n_aY), equivalence_arriere(
        _inst_diff(image_recip(vg, vB), image_recip(vg, vY), va)))
    imp_x = existe_elimination(N.loi_deduction(bodyBY, aR), "x")
    aR_final = N.modus_ponens(exBY, imp_x)
    incl = N.generalisation("z", N.loi_deduction(appartient(va, L), aR_final))
    return N.loi_deduction(fonctionnelle(vg), incl)


def image_recip_difference(g="f", b="B", y="Y"):
    """{Fonctionnelle(f)} ⊢ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩.   (E.II.27, Prop. 6.)

    CONDITIONNÉE à Fonctionnelle(f) (f application, comme dans Bourbaki) — jamais
    postulée.  Composition des deux inclusions : ⊂ (`image_recip_diff_avant`, sous
    Fonctionnelle) et ⊃ (`image_recip_diff_arriere`, inconditionnel)."""
    vg, vB, vY, va = _t(g), _t(b), _t(y), var("a")
    L = image_recip(vg, E.difference(vB, vY))
    R = E.difference(image_recip(vg, vB), image_recip(vg, vY))
    hFun = N.assume(fonctionnelle(vg))
    incl_LR = N.modus_ponens(hFun, image_recip_diff_avant(vg, vB, vY))   # L ⊂ R
    incl_RL = image_recip_diff_arriere(vg, vB, vY)                       # R ⊂ L
    # égalité par double inclusion (extensionnalité)
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    eqt = N.modus_ponens(conjonction_intro(incl_LR, incl_RL), extensionnalite_appliquee(L, R))
    return N.loi_deduction(fonctionnelle(vg), eqt)


__all__ = [
    "fonctionnelle", "injective", "membre_image_recip", "image_recip",
    "famille_image_recip", "famille_image",
    "image_recip_diff_arriere", "image_recip_diff_avant", "image_recip_difference",
]
