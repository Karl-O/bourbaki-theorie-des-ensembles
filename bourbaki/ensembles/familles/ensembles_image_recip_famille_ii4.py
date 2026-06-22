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


# ══════════════════════════════════════════════════════════════════════════════
# Prop. 4 (E.II.25) — IMAGE RÉCIPROQUE d'une INTERSECTION de famille.
#   f⁻¹⟨⋂Y⟩ = ⋂ f⁻¹⟨Y_ι⟩
# ══════════════════════════════════════════════════════════════════════════════
def _membre_fam_recip(g, fam, i, a):
    """⊢ (a ∈ (f⁻¹⟨Y·⟩)_ι) ⇔ (∃x)(x∈Y_ι et (a,x)∈f).

    via (f⁻¹⟨Y·⟩)_ι = f⁻¹⟨Y_ι⟩ (théorie de valeur dédiée) puis membre_image_recip."""
    vg, vfam, vi, va = _t(g), _t(fam), _t(i), _t(a)
    Yi = E.valeur_famille(vfam, vi)
    val_eq = _val_recip(vg, vfam, vi)                       # (f⁻¹⟨Y·⟩)_ι = f⁻¹⟨Y_ι⟩
    membre_eq = _membre_eq(E.valeur_famille(famille_image_recip(vg, vfam), vi),
                           image_recip(vg, Yi), val_eq, va)  # a∈(…)_ι ⇔ a∈f⁻¹⟨Y_ι⟩
    return etr(membre_eq, membre_image_recip(vg, Yi, va))


def image_recip_inter_incluse(g="f", fam="Y", i="I"):
    """⊢ f⁻¹⟨⋂_ι Y_ι⟩ ⊂ ⋂_ι f⁻¹⟨Y_ι⟩.   (Prop. 4, sens ⊂ — INCONDITIONNEL.)

    a∈f⁻¹⟨⋂Y⟩ : témoin x∈⋂Y, (a,x)∈f ; pour i∈I, x∈Y_i, donc x témoigne a∈f⁻¹⟨Y_i⟩,
    et ceci ∀i∈I, soit a∈⋂f⁻¹⟨Y_ι⟩."""
    vg, vfam, vI = _t(g), _t(fam), _t(i)
    va, vx, vi = var("z"), var("x"), var("i")
    inter = E.inter_famille(vfam, vI)
    fam_r = famille_image_recip(vg, vfam)
    L = image_recip(vg, inter)
    R = E.inter_famille(fam_r, vI)

    hL = N.assume(appartient(va, L))
    exX = N.modus_ponens(hL, equivalence_avant(membre_image_recip(vg, inter, va)))  # (∃x)(x∈⋂Y et (a,x)∈f)
    body = et(appartient(vx, inter), appartient(E.couple(va, vx), vg))
    hb = N.assume(body)
    x_inter = cg(hb)
    axf = cd(hb)
    # pour i∈I : x∈Y_i
    hI = N.assume(appartient(vi, vI))
    fa = N.modus_ponens(x_inter, equivalence_avant(_inst_inter(vfam, vI, vx)))  # (∀i)(i∈I⇒x∈Y_i)
    x_Yi = N.modus_ponens(hI, instancie(fa, vi))                                # x∈Y_i
    Yi = E.valeur_famille(vfam, vi)
    wit_i = conjonction_intro(x_Yi, axf)                                        # x∈Y_i et (a,x)∈f
    a_fri = N.modus_ponens(N.modus_ponens(wit_i, N.s5(
        et(appartient(vx, Yi), appartient(E.couple(va, vx), vg)), vx, "x")),
        equivalence_arriere(_membre_fam_recip(vg, vfam, vi, va)))               # a∈(f⁻¹⟨Y·⟩)_i
    # ∀i(i∈I ⇒ a∈(…)_i)  — sous body ; éliminer le témoin x ensuite
    fa_i = N.generalisation("i", N.loi_deduction(appartient(vi, vI), a_fri))
    a_R = N.modus_ponens(fa_i, equivalence_arriere(_inst_inter(fam_r, vI, va)))  # a∈⋂f⁻¹⟨Y·⟩
    imp_x = existe_elimination(N.loi_deduction(body, a_R), "x")
    a_R_final = N.modus_ponens(exX, imp_x)
    return N.generalisation("z", N.loi_deduction(appartient(va, L), a_R_final))


def image_recip_inter_arriere(g="f", fam="Y", i="I", a="alpha"):
    """{Fonctionnelle(f), α∈I} ⊢ ⋂_ι f⁻¹⟨Y_ι⟩ ⊂ f⁻¹⟨⋂_ι Y_ι⟩.   (Prop. 4, sens ⊃.)

    CONDITIONNÉ (fidèlement) : f application (Fonctionnelle) et I≠∅ (via α∈I).
    a∈⋂f⁻¹⟨Y_ι⟩ : pour i=α, témoin x avec x∈Y_α, (a,x)∈f.  Pour tout i∈I, a∈f⁻¹⟨Y_i⟩
    donne un témoin x_i ; Fonctionnelle ⇒ x_i = x ; donc x∈Y_i.  Ainsi x∈⋂Y,
    (a,x)∈f : a∈f⁻¹⟨⋂Y⟩."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
    vg, vfam, vI, valpha = _t(g), _t(fam), _t(i), _t(a)
    va, vx, vxq, vi = var("z"), var("x"), var("xq"), var("i")
    inter = E.inter_famille(vfam, vI)
    fam_r = famille_image_recip(vg, vfam)
    L = E.inter_famille(fam_r, vI)
    R = image_recip(vg, inter)
    hFun = N.assume(fonctionnelle(vg))
    h_aI = N.assume(appartient(valpha, vI))

    hL = N.assume(appartient(va, L))
    fa_L = N.modus_ponens(hL, equivalence_avant(_inst_inter(fam_r, vI, va)))  # (∀i)(i∈I⇒a∈(f⁻¹⟨Y·⟩)_i)
    # témoin x en i=α : a∈(f⁻¹⟨Y·⟩)_α
    a_fr_alpha = N.modus_ponens(h_aI, instancie(fa_L, valpha))               # a∈(…)_α
    exA = N.modus_ponens(a_fr_alpha, equivalence_avant(
        _membre_fam_recip(vg, vfam, valpha, va)))                            # (∃x)(x∈Y_α et (a,x)∈f)
    Yalpha = E.valeur_famille(vfam, valpha)
    bodyA = et(appartient(vx, Yalpha), appartient(E.couple(va, vx), vg))
    hb = N.assume(bodyA)
    axf = cd(hb)                                                             # (a,x)∈f
    # ∀i∈I : x∈Y_i.  Soit i∈I.  a∈(…)_i donne témoin x' avec x'∈Y_i, (a,x')∈f.
    hI = N.assume(appartient(vi, vI))
    a_fr_i = N.modus_ponens(hI, instancie(fa_L, vi))                         # a∈(…)_i
    Yi = E.valeur_famille(vfam, vi)
    bodyI = et(appartient(vxq, Yi), appartient(E.couple(va, vxq), vg))       # binder xq
    exI_xq = N.modus_ponens(a_fr_i, equivalence_avant(_membre_fam_recip_b(vg, vfam, vi, va, "xq")))
    hbI = N.assume(bodyI)
    xqYi = cg(hbI)
    axqf = cd(hbI)                                                           # (a,x')∈f
    fun_inst = instancie(instancie(instancie(hFun, va), vx), vxq)
    x_eq_xq = N.modus_ponens(conjonction_intro(axf, axqf), fun_inst)         # x=x'
    x_Yi = N.modus_ponens(xqYi, equivalence_arriere(
        N.modus_ponens(x_eq_xq, N.s6(vx, vxq, "w", appartient(var("w"), Yi)))))  # x∈Y_i
    imp_bodyI_xYi = existe_elimination(N.loi_deduction(bodyI, x_Yi), "xq")
    x_Yi_final = N.modus_ponens(exI_xq, imp_bodyI_xYi)                       # x∈Y_i (sous hI, body)
    fa_x = N.generalisation("i", N.loi_deduction(appartient(vi, vI), x_Yi_final))  # (∀i)(i∈I⇒x∈Y_i)
    x_inter = N.modus_ponens(fa_x, equivalence_arriere(_inst_inter(vfam, vI, vx)))  # x∈⋂Y
    wit_R = conjonction_intro(x_inter, axf)                                  # x∈⋂Y et (a,x)∈f
    a_R = N.modus_ponens(N.modus_ponens(wit_R, N.s5(
        et(appartient(vx, inter), appartient(E.couple(va, vx), vg)), vx, "x")),
        equivalence_arriere(membre_image_recip(vg, inter, va)))             # a∈f⁻¹⟨⋂Y⟩
    imp_x = existe_elimination(N.loi_deduction(bodyA, a_R), "x")
    a_R_final = N.modus_ponens(exA, imp_x)
    incl = N.generalisation("z", N.loi_deduction(appartient(va, L), a_R_final))
    return N.loi_deduction(fonctionnelle(vg), N.loi_deduction(appartient(valpha, vI), incl))


def image_recip_inter_egal(g="f", fam="Y", i="I", a="alpha"):
    """{Fonctionnelle(f), α∈I} ⊢ f⁻¹⟨⋂_ι Y_ι⟩ = ⋂_ι f⁻¹⟨Y_ι⟩.   (E.II.25, Prop. 4.)

    CONDITIONNÉE (fidèle, Bourbaki : f application, I≠∅) — jamais postulée.
    Double inclusion : ⊂ (`image_recip_inter_incluse`, INCOND.) et ⊃
    (`image_recip_inter_arriere`, sous Fonctionnelle + α∈I)."""
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    vg, vfam, vI, valpha = _t(g), _t(fam), _t(i), _t(a)
    inter = E.inter_famille(vfam, vI)
    fam_r = famille_image_recip(vg, vfam)
    L = image_recip(vg, inter)
    R = E.inter_famille(fam_r, vI)
    hFun = N.assume(fonctionnelle(vg))
    h_aI = N.assume(appartient(valpha, vI))
    incl_LR = image_recip_inter_incluse(vg, vfam, vI)                        # L⊂R (incond.)
    incl_RL = N.modus_ponens(h_aI, N.modus_ponens(hFun,
        image_recip_inter_arriere(vg, vfam, vI, valpha)))                    # R⊂L
    eqt = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                         extensionnalite_appliquee(L, R))
    return N.loi_deduction(fonctionnelle(vg),
                           N.loi_deduction(appartient(valpha, vI), eqt))


def _membre_fam_recip_b(g, fam, i, a, xb):
    """Comme _membre_fam_recip mais avec binder témoin `xb` (α-renommé)."""
    vg, vfam, vi, va = _t(g), _t(fam), _t(i), _t(a)
    Yi = E.valeur_famille(vfam, vi)
    val_eq = _val_recip(vg, vfam, vi)
    membre_eq = _membre_eq(E.valeur_famille(famille_image_recip(vg, vfam), vi),
                           image_recip(vg, Yi), val_eq, va)
    return etr(membre_eq, membre_image_recip(vg, Yi, va, xb))


# ══════════════════════════════════════════════════════════════════════════════
# Prop. 3 (E.II.25) — IMAGE DIRECTE d'une RÉUNION / INTERSECTION de famille.
#   Γ⟨⋃X⟩ = ⋃Γ⟨X_ι⟩  (=, incond.)   ;   Γ⟨⋂X⟩ ⊂ ⋂Γ⟨X_ι⟩  (⊂, incond.)
# ══════════════════════════════════════════════════════════════════════════════
def _membre_fam_image(g, fam, i, y):
    """⊢ (y ∈ (Γ⟨X·⟩)_ι) ⇔ (∃x)(x∈X_ι et (x,y)∈Γ).

    via (Γ⟨X·⟩)_ι = Γ⟨X_ι⟩ (théorie de valeur dédiée) puis AXIOME_IMAGE."""
    vg, vfam, vi, vy = _t(g), _t(fam), _t(i), _t(y)
    Xi = E.valeur_famille(vfam, vi)
    val_eq = _val_image(vg, vfam, vi)                       # (Γ⟨X·⟩)_ι = Γ⟨X_ι⟩
    membre_eq = _membre_eq(E.valeur_famille(famille_image(vg, vfam), vi),
                           E.image(vg, Xi), val_eq, vy)     # y∈(…)_ι ⇔ y∈Γ⟨X_ι⟩
    return etr(membre_eq, _inst_image(vg, Xi, vy))


def image_reunion_egal(g="G", fam="X", i="I"):
    """⊢ Γ⟨⋃_ι X_ι⟩ = ⋃_ι Γ⟨X_ι⟩.   (E.II.25, Prop. 3, 1re formule — INCONDITIONNELLE.)

    y∈Γ⟨⋃X⟩ ⇔ (∃x)(x∈⋃X et (x,y)∈Γ) ⇔ (∃x)((∃i)(i∈I et x∈X_i) et (x,y)∈Γ) ;
    on commute ∃x∃i, réassocie, et tire (∃i)(i∈I et (∃x)(x∈X_i et (x,y)∈Γ))
        = (∃i)(i∈I et y∈Γ⟨X_i⟩) = caractérisation de ⋃Γ⟨X·⟩."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        et_existe_gauche, existe_commute, et_existe_droite)
    vg, vfam, vI = _t(g), _t(fam), _t(i)
    vy, vx, vi = var("y"), var("x"), var("i")
    Xi = E.valeur_famille(vfam, vi)
    reun = E.reunion_famille(vfam, vI)
    fam_im = famille_image(vg, vfam)
    gxy = appartient(E.couple(vx, vy), vg)                  # (x,y)∈Γ

    # ── membre gauche ─────────────────────────────────────────────────────────
    L = _inst_image(vg, reun, vy)                           # ⇔ (∃x)(x∈⋃X et (x,y)∈Γ)
    reun_x = _inst_reunion(vfam, vI, vx)                    # x∈⋃X ⇔ (∃i)(i∈I et x∈X_i)
    L2 = etr(L, congruence_existe(et_congruence_gauche(reun_x, gxy), "x"))
    Pi = et(appartient(vi, vI), appartient(vx, Xi))
    L3 = etr(L2, congruence_existe(et_existe_gauche("i", Pi, gxy), "x"))   # ⇔ (∃x)(∃i)(Pi et (x,y)∈Γ)
    L4 = etr(L3, existe_commute("x", "i", et(Pi, gxy)))                    # ⇔ (∃i)(∃x)(Pi et (x,y)∈Γ)
    # ((i∈I et x∈X_i) et (x,y)∈Γ) ⇔ (i∈I et (x∈X_i et (x,y)∈Γ))
    rearr = _assoc_et_droite(appartient(vi, vI), appartient(vx, Xi), gxy)
    inner_S = et(appartient(vx, Xi), gxy)
    pull_x = esym(et_existe_droite(appartient(vi, vI), "x", inner_S))      # (∃x)(i∈I et S) ⇔ (i∈I et (∃x)S)
    L5 = etr(L4, congruence_existe(etr(congruence_existe(rearr, "x"), pull_x), "i"))
    char_L = N.generalisation("y", L5)

    # ── membre droit ──────────────────────────────────────────────────────────
    R = _inst_reunion(fam_im, vI, vy)                       # ⇔ (∃i)(i∈I et y∈(Γ⟨X·⟩)_i)
    membre_i = _membre_fam_image(vg, vfam, vi, vy)          # y∈(…)_i ⇔ (∃x)(x∈X_i et (x,y)∈Γ)
    R2 = etr(R, congruence_existe(et_congruence_droite(appartient(vi, vI), membre_i), "i"))
    char_R = N.generalisation("y", R2)

    return egalite_par_extension(char_L, char_R, E.image(vg, reun),
                                 E.reunion_famille(fam_im, vI))


def image_inter_incluse(g="G", fam="X", i="I"):
    """⊢ Γ⟨⋂_ι X_ι⟩ ⊂ ⋂_ι Γ⟨X_ι⟩.   (E.II.25, Prop. 3, 2e formule — INCONDITIONNELLE.)

    y∈Γ⟨⋂X⟩ : témoin x∈⋂X, (x,y)∈Γ ; pour i∈I, x∈X_i, donc y∈Γ⟨X_i⟩, ∀i∈I :
    y∈⋂Γ⟨X_ι⟩.  (L'inclusion inverse est FAUSSE en général — note* du PDF.)"""
    vg, vfam, vI = _t(g), _t(fam), _t(i)
    vy, vx, vi = var("z"), var("x"), var("i")
    inter = E.inter_famille(vfam, vI)
    fam_im = famille_image(vg, vfam)
    L = E.image(vg, inter)
    R = E.inter_famille(fam_im, vI)

    hL = N.assume(appartient(vy, L))
    exX = N.modus_ponens(hL, equivalence_avant(_inst_image(vg, inter, vy)))  # (∃x)(x∈⋂X et (x,y)∈Γ)
    body = et(appartient(vx, inter), appartient(E.couple(vx, vy), vg))
    hb = N.assume(body)
    x_inter = cg(hb)
    gxy = cd(hb)
    hI = N.assume(appartient(vi, vI))
    fa = N.modus_ponens(x_inter, equivalence_avant(_inst_inter(vfam, vI, vx)))  # (∀i)(i∈I⇒x∈X_i)
    x_Xi = N.modus_ponens(hI, instancie(fa, vi))                                # x∈X_i
    Xi = E.valeur_famille(vfam, vi)
    wit_i = conjonction_intro(x_Xi, gxy)                                        # x∈X_i et (x,y)∈Γ
    y_GXi = N.modus_ponens(N.modus_ponens(wit_i, N.s5(
        et(appartient(vx, Xi), appartient(E.couple(vx, vy), vg)), vx, "x")),
        equivalence_arriere(_membre_fam_image(vg, vfam, vi, vy)))               # y∈(Γ⟨X·⟩)_i
    fa_i = N.generalisation("i", N.loi_deduction(appartient(vi, vI), y_GXi))
    y_R = N.modus_ponens(fa_i, equivalence_arriere(_inst_inter(fam_im, vI, vy)))  # y∈⋂Γ⟨X·⟩
    imp_x = existe_elimination(N.loi_deduction(body, y_R), "x")
    y_R_final = N.modus_ponens(exX, imp_x)
    return N.generalisation("z", N.loi_deduction(appartient(vy, L), y_R_final))


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


# ══════════════════════════════════════════════════════════════════════════════
# Cor. de la Prop. 4 (E.II.25) — IMAGE DIRECTE d'une INTERSECTION sous INJECTION.
#   {Injective(f)} ⊢ Γ⟨⋂X⟩ = ⋂Γ⟨X_ι⟩
# ══════════════════════════════════════════════════════════════════════════════
def image_inter_arriere_si_inj(g="G", fam="X", i="I", a="alpha"):
    """{Injective(f), α∈I} ⊢ ⋂_ι Γ⟨X_ι⟩ ⊂ Γ⟨⋂_ι X_ι⟩.   (Cor. Prop. 4, sens ⊃.)

    CONDITIONNÉ (fidèle, Bourbaki : f injection, I≠∅).  y∈⋂Γ⟨X_ι⟩ : en i=α, témoin
    x∈X_α, (x,y)∈f.  Pour tout i∈I, y∈Γ⟨X_i⟩ donne un témoin x_i avec (x_i,y)∈f ;
    Injective(f) (f⁻¹ univalent) ⇒ x_i=x ; donc x∈X_i.  Ainsi x∈⋂X, (x,y)∈f :
    y∈Γ⟨⋂X⟩."""
    vg, vfam, vI, valpha = _t(g), _t(fam), _t(i), _t(a)
    vy, vx, vxq, vi = var("z"), var("x"), var("xq"), var("i")
    inter = E.inter_famille(vfam, vI)
    fam_im = famille_image(vg, vfam)
    L = E.inter_famille(fam_im, vI)
    R = E.image(vg, inter)
    hInj = N.assume(injective(vg))
    h_aI = N.assume(appartient(valpha, vI))

    hL = N.assume(appartient(vy, L))
    fa_L = N.modus_ponens(hL, equivalence_avant(_inst_inter(fam_im, vI, vy)))  # (∀i)(i∈I⇒y∈(Γ⟨X·⟩)_i)
    y_GX_alpha = N.modus_ponens(h_aI, instancie(fa_L, valpha))                 # y∈(…)_α
    exA = N.modus_ponens(y_GX_alpha, equivalence_avant(
        _membre_fam_image(vg, vfam, valpha, vy)))                             # (∃x)(x∈X_α et (x,y)∈f)
    Xalpha = E.valeur_famille(vfam, valpha)
    bodyA = et(appartient(vx, Xalpha), appartient(E.couple(vx, vy), vg))
    hb = N.assume(bodyA)
    gxy = cd(hb)                                                              # (x,y)∈f
    hI = N.assume(appartient(vi, vI))
    y_GX_i = N.modus_ponens(hI, instancie(fa_L, vi))                          # y∈(…)_i
    Xi = E.valeur_famille(vfam, vi)
    bodyI = et(appartient(vxq, Xi), appartient(E.couple(vxq, vy), vg))        # binder xq
    exI_xq = N.modus_ponens(y_GX_i, equivalence_avant(
        _membre_fam_image_b(vg, vfam, vi, vy, "xq")))                         # (∃x')(x'∈X_i et (x',y)∈f)
    hbI = N.assume(bodyI)
    xqXi = cg(hbI)
    xqgy = cd(hbI)                                                            # (x',y)∈f
    inj_inst = instancie(instancie(instancie(hInj, vx), vxq), vy)            # ((x,y)∈f et (x',y)∈f)⇒x=x'
    x_eq_xq = N.modus_ponens(conjonction_intro(gxy, xqgy), inj_inst)          # x=x'
    x_Xi = N.modus_ponens(xqXi, equivalence_arriere(
        N.modus_ponens(x_eq_xq, N.s6(vx, vxq, "w", appartient(var("w"), Xi)))))  # x∈X_i
    imp_bodyI = existe_elimination(N.loi_deduction(bodyI, x_Xi), "xq")
    x_Xi_final = N.modus_ponens(exI_xq, imp_bodyI)                            # x∈X_i
    fa_x = N.generalisation("i", N.loi_deduction(appartient(vi, vI), x_Xi_final))
    x_inter = N.modus_ponens(fa_x, equivalence_arriere(_inst_inter(vfam, vI, vx)))  # x∈⋂X
    wit_R = conjonction_intro(x_inter, gxy)
    y_R = N.modus_ponens(N.modus_ponens(wit_R, N.s5(
        et(appartient(vx, inter), appartient(E.couple(vx, vy), vg)), vx, "x")),
        equivalence_arriere(_inst_image(vg, inter, vy)))                     # y∈Γ⟨⋂X⟩
    imp_x = existe_elimination(N.loi_deduction(bodyA, y_R), "x")
    y_R_final = N.modus_ponens(exA, imp_x)
    incl = N.generalisation("z", N.loi_deduction(appartient(vy, L), y_R_final))
    return N.loi_deduction(injective(vg), N.loi_deduction(appartient(valpha, vI), incl))


def _membre_fam_image_b(g, fam, i, y, xb):
    """Comme _membre_fam_image mais avec binder témoin `xb`."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    vg, vfam, vi, vy = _t(g), _t(fam), _t(i), _t(y)
    Xi = E.valeur_famille(vfam, vi)
    base = _membre_fam_image(vg, vfam, vi, vy)             # ⇔ (∃x)(x∈X_i et (x,y)∈Γ)
    if xb == "x":
        return base
    body0 = et(appartient(var("x"), Xi), appartient(E.couple(var("x"), vy), vg))
    return etr(base, alpha_existe("x", xb, body0))


def image_inter_egal_si_injective(g="G", fam="X", i="I", a="alpha"):
    """{Injective(f), α∈I} ⊢ Γ⟨⋂_ι X_ι⟩ = ⋂_ι Γ⟨X_ι⟩.   (E.II.25, Cor. de la Prop. 4.)

    CONDITIONNÉE (fidèle, Bourbaki : f injection, I≠∅) — jamais postulée.
    Double inclusion : ⊂ (`image_inter_incluse`, INCOND.) et ⊃
    (`image_inter_arriere_si_inj`, sous Injective + α∈I)."""
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    vg, vfam, vI, valpha = _t(g), _t(fam), _t(i), _t(a)
    inter = E.inter_famille(vfam, vI)
    fam_im = famille_image(vg, vfam)
    L = E.image(vg, inter)
    R = E.inter_famille(fam_im, vI)
    hInj = N.assume(injective(vg))
    h_aI = N.assume(appartient(valpha, vI))
    incl_LR = image_inter_incluse(vg, vfam, vI)                              # L⊂R (incond.)
    incl_RL = N.modus_ponens(h_aI, N.modus_ponens(hInj,
        image_inter_arriere_si_inj(vg, vfam, vI, valpha)))                   # R⊂L
    eqt = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                         extensionnalite_appliquee(L, R))
    return N.loi_deduction(injective(vg),
                           N.loi_deduction(appartient(valpha, vI), eqt))


# ══════════════════════════════════════════════════════════════════════════════
# Prop. 4 (E.II.25) — IMAGE RÉCIPROQUE d'une RÉUNION de famille.
#   f⁻¹⟨⋃_ι Y_ι⟩ = ⋃_ι f⁻¹⟨Y_ι⟩       (INCONDITIONNELLE).
# ══════════════════════════════════════════════════════════════════════════════
def cible_image_recip_reunion(g="f", fam="Y", i="I"):
    """Énoncé-cible : f⁻¹⟨⋃_ι Y_ι⟩ = ⋃_ι f⁻¹⟨Y_ι⟩."""
    vg, vfam, vI = _t(g), _t(fam), _t(i)
    reun = E.reunion_famille(vfam, vI)
    fam_r = famille_image_recip(vg, vfam)
    return egal(image_recip(vg, reun), E.reunion_famille(fam_r, vI))


def image_recip_reunion_egal(g="f", fam="Y", i="I"):
    """⊢ f⁻¹⟨⋃_ι Y_ι⟩ = ⋃_ι f⁻¹⟨Y_ι⟩.   (E.II.25, Prop. 4, 1re formule — INCONDITIONNELLE.)

    L'univalence n'est PAS requise (contrairement à f⁻¹⟨⋂⟩).  Miroir EXACT de
    `image_reunion_egal` côté image réciproque.  theorie_ensembles() inchangée (22 ax.).

    a∈f⁻¹⟨⋃Y⟩ ⇔ (∃x)(x∈⋃Y et (a,x)∈f) ⇔ (∃x)((∃i)(i∈I et x∈Y_i) et (a,x)∈f) ;
    on commute ∃x∃i, réassocie, et tire (∃i)(i∈I et (∃x)(x∈Y_i et (a,x)∈f))
        = (∃i)(i∈I et a∈f⁻¹⟨Y_i⟩) = caractérisation de ⋃f⁻¹⟨Y·⟩."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        et_existe_gauche, existe_commute, et_existe_droite)
    vg, vfam, vI = _t(g), _t(fam), _t(i)
    va, vx, vi = var("a"), var("x"), var("i")
    Yi = E.valeur_famille(vfam, vi)
    reun = E.reunion_famille(vfam, vI)
    fam_r = famille_image_recip(vg, vfam)
    axc = appartient(E.couple(va, vx), vg)              # (a,x)∈f

    # ── membre gauche ─────────────────────────────────────────────────────────
    L = membre_image_recip(vg, reun, va)               # ⇔ (∃x)(x∈⋃Y et (a,x)∈f)
    reun_x = _inst_reunion(vfam, vI, vx)               # x∈⋃Y ⇔ (∃i)(i∈I et x∈Y_i)
    L2 = etr(L, congruence_existe(et_congruence_gauche(reun_x, axc), "x"))
    Pi = et(appartient(vi, vI), appartient(vx, Yi))
    L3 = etr(L2, congruence_existe(et_existe_gauche("i", Pi, axc), "x"))
    L4 = etr(L3, existe_commute("x", "i", et(Pi, axc)))   # ⇔ (∃i)(∃x)(Pi et (a,x)∈f)
    rearr = _assoc_et_droite(appartient(vi, vI), appartient(vx, Yi), axc)
    inner_S = et(appartient(vx, Yi), axc)
    pull_x = esym(et_existe_droite(appartient(vi, vI), "x", inner_S))
    L5 = etr(L4, congruence_existe(etr(congruence_existe(rearr, "x"), pull_x), "i"))
    char_L = N.generalisation("a", L5)

    # ── membre droit ──────────────────────────────────────────────────────────
    R = _inst_reunion(fam_r, vI, va)                   # ⇔ (∃i)(i∈I et a∈(f⁻¹⟨Y·⟩)_i)
    membre_i = _membre_fam_recip(vg, vfam, vi, va)     # a∈(…)_i ⇔ (∃x)(x∈Y_i et (a,x)∈f)
    R2 = etr(R, congruence_existe(et_congruence_droite(appartient(vi, vI), membre_i), "i"))
    char_R = N.generalisation("a", R2)

    return egalite_par_extension(char_L, char_R, image_recip(vg, reun),
                                 E.reunion_famille(fam_r, vI))


__all__ = [
    "fonctionnelle", "injective", "membre_image_recip", "image_recip",
    "famille_image_recip", "famille_image",
    "image_recip_diff_arriere", "image_recip_diff_avant", "image_recip_difference",
    "image_recip_inter_incluse", "image_recip_inter_arriere", "image_recip_inter_egal",
    "image_reunion_egal", "image_inter_incluse",
    "image_inter_arriere_si_inj", "image_inter_egal_si_injective",
    "image_recip_reunion_egal", "cible_image_recip_reunion",
]
