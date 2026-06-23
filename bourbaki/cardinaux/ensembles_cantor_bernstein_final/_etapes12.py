"""§III.3.2 — CANTOR–BERNSTEIN, CLÔTURE (Corollaire 2 du Théorème 1).

Énoncé (E.III.3.2, Cor. 2, VERBATIM ROADMAP_chap2-4.md) :
    « Deux ensembles tels que chacun soit équipotent à une partie de l'autre
      sont équipotents. »
    Implémentation §III.3.2 : x ≤ y :⇔ (∃f)(f injection de x dans y), donc
        (a ≤ b  et  b ≤ a)  ⇒  Eq(a, b).

CE MODULE — additif, ne redéfinit RIEN — assemble la bijection finale
    h = (f|D) ∪ (g⁻¹|(A∖D))  : A → B
à partir de tout le socle des rounds 28-30 (point fixe φ(D)=D, pivot A∖D=g⟨B∖f⟨D⟩⟩,
morceau f|D, infra recollement).

LES QUATRE ÉTAPES :
  • image_reciproque_image (ÉTAPE 1, LE VERROU) :
        ⊢ est_injection_de(g,b,a) ⇒ ((S⊂b) ⇒ image(g⁻¹, g⟨S⟩) = S).
        (RÉTRACTION g⁻¹∘g = id sur b : tout antécédent de g⟨S⟩ par g⁻¹ revient dans S.)
  • morceau_gI (ÉTAPE 2) :
        ⊢ est_injection_de(g,b,a) ⇒ est_bijection_de(g⁻¹|(A∖D), A∖D, B∖f⟨D⟩).
  • recollement_h (ÉTAPE 3) :
        ⊢ (est_injection_de(f,a,b) et est_injection_de(g,b,a))
              ⇒ est_bijection_de((f|D)∪(g⁻¹|(A∖D)), a, b).
  • cantor_bernstein (ÉTAPE 4, GRAND PRIX) :
        ⊢ (inf_egal_card(a,b) et inf_egal_card(b,a)) ⇒ equipotent(a,b).

Tout sort du noyau (PROUVE == certifie) ; AUCUN axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    instancie, instanciation_en_x, cas,
    et_congruence_droite, et_congruence_gauche)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, congruence_existe, alpha_existe)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension
from bourbaki.cardinaux import ensembles_cantor_bernstein as CB
from bourbaki.cardinaux.ensembles_cardinaux import (est_injection_de,
                                                    est_bijection_de, equipotent,
                                                    inf_egal_card)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — RÉTRACTION  image(g⁻¹, g⟨S⟩) = S   (LE SEUL VERROU)
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_image(g="g", a="A", b="B", s="S"):
    """⊢ est_injection_de(g,b,a) ⇒ ((S⊂b) ⇒ image(g⁻¹, g⟨S⟩) = S).

    g⁻¹⟨g⟨S⟩⟩ = S pour S⊂b, g injective :  z∈g⁻¹⟨g⟨S⟩⟩
        ⇔ (∃y)(y∈g⟨S⟩ et (y,z)∈g⁻¹)                       [AXIOME_IMAGE, binder y]
        ⇔ (∃y)((∃u)(u∈S et (u,y)∈g) et (z,y)∈g)           [image S + couple_reciproque]
      ⇒ : de (u,y)∈g et (z,y)∈g, g⁻¹ fonctionnel (g inj) donne u=z, donc z=u∈S.
      ⇐ : u∈S ⇒ (u,g(u))∈g, g(u)∈g⟨S⟩, (g(u),u)∈g⁻¹ ⇒ u∈g⁻¹⟨g⟨S⟩⟩.
    """
    from bourbaki.cardinaux.ensembles_bijection import reciproque_fonctionnelle
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
    vg, vA, vB, vS = _t(g), _t(a), _t(b), _t(s)
    grec = E.reciproque(vg)
    gS = E.image(vg, vS)                      # g⟨S⟩
    imgrecgS = E.image(grec, gS)              # g⁻¹⟨g⟨S⟩⟩
    vz, vy, vu = var("z"), var("y"), var("u")

    # ── hypothèses tirées de est_injection_de(g,b,a) ──────────────────────────
    hinj = N.assume(est_injection_de(vg, vB, vA))
    g_func = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hinj)))
    g_dom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hinj)))
    g_injB = conjonction_elim_droite(conjonction_elim_gauche(hinj))
    # g⁻¹ fonctionnel  (Prop. 7 : {g func, dom g=b, g inj/b})
    grec_func = _cut(reciproque_fonctionnelle(vg, vB),
                     [(E.est_fonctionnel(vg), g_func),
                      (egal(E.dom(vg), vB), g_dom),
                      (E.injective_dans(vg, vB), g_injB)])     # ⊢ est_fonctionnel(g⁻¹)

    hsub = N.assume(inclus(vS, vB))                            # S⊂b

    # ── caractérisations membre-à-membre ──────────────────────────────────────
    # z∈g⁻¹⟨g⟨S⟩⟩ ⇔ (∃y)(y∈g⟨S⟩ et (y,z)∈g⁻¹)        (binder renommé x→y)
    carOut = _inst_image(grec, gS, vz)
    carOut = equivalence_transitivite(carOut, alpha_existe("x", "y",
        et(appartient(var("x"), gS), appartient(E.couple(var("x"), vz), grec))))
    #   (y,z)∈g⁻¹ ⇔ (z,y)∈g
    crYZ = couple_reciproque(vg, "y", "z")
    carOut = equivalence_transitivite(carOut, congruence_existe(
        et_congruence_droite(appartient(vy, gS), crYZ), "y"))
    #   y∈g⟨S⟩ ⇔ (∃u)(u∈S et (u,y)∈g)              (binder renommé x→u)
    carInner = _inst_image(vg, vS, vy)
    carInner = equivalence_transitivite(carInner, alpha_existe("x", "u",
        et(appartient(var("x"), vS), appartient(E.couple(var("x"), vy), vg))))
    #   y∈g⟨S⟩ et (z,y)∈g ⇔ (∃u)(u∈S et (u,y)∈g) et (z,y)∈g
    carBoth = et_congruence_gauche(carInner, appartient(E.couple(vz, vy), vg))
    carOut = equivalence_transitivite(carOut, congruence_existe(carBoth, "y"))
    #   carOut : z∈g⁻¹⟨g⟨S⟩⟩ ⇔ (∃y)((∃u)(u∈S et (u,y)∈g) et (z,y)∈g)

    body_y = et(existe("u", et(appartient(vu, vS), appartient(E.couple(vu, vy), vg))),
                appartient(E.couple(vz, vy), vg))

    # ── ⇒ : z∈g⁻¹⟨g⟨S⟩⟩ ⇒ z∈S ─────────────────────────────────────────────────
    #   sous body_y : extraire u (témoin), de (u,y)∈g & (z,y)∈g via g⁻¹ func ⇒ u=z ⇒ z∈S.
    hby = N.assume(body_y)
    hzy = conjonction_elim_droite(hby)                        # (z,y)∈g
    body_u = et(appartient(vu, vS), appartient(E.couple(vu, vy), vg))
    hbu = N.assume(body_u)
    huS = conjonction_elim_gauche(hbu)                        # u∈S
    huy = conjonction_elim_droite(hbu)                        # (u,y)∈g
    # (y,u)∈g⁻¹ et (y,z)∈g⁻¹  (couple_reciproque sens arrière)
    yu_rec = N.modus_ponens(huy, equivalence_arriere(couple_reciproque(vg, "y", "u")))  # (y,u)∈g⁻¹
    yz_rec = N.modus_ponens(hzy, equivalence_arriere(couple_reciproque(vg, "y", "z")))  # (y,z)∈g⁻¹
    # g⁻¹ fonctionnel : ((y,u)∈g⁻¹ et (y,z)∈g⁻¹) ⇒ u=z
    func_inst = instancie(instancie(instancie(grec_func, vy), vu), vz)
    u_eq_z = N.modus_ponens(conjonction_intro(yu_rec, yz_rec), func_inst)   # u=z
    # z∈S  : de u∈S et u=z (Leibniz)
    zS = N.modus_ponens(huS, equivalence_avant(N.modus_ponens(
        u_eq_z, N.s6(vu, vz, "w", appartient(var("w"), vS)))))   # z∈S
    imp_u = existe_elimination(N.loi_deduction(body_u, zS), "u")  # (∃u)body_u ⇒ z∈S
    z_in_S = N.modus_ponens(conjonction_elim_gauche(hby), imp_u)  # z∈S  (sous body_y)
    fwd_body = N.loi_deduction(body_y, z_in_S)                    # body_y ⇒ z∈S
    fwd = existe_elimination(fwd_body, "y")                       # (∃y)body_y ⇒ z∈S
    fwd = syllogisme(equivalence_avant(carOut), fwd)             # z∈g⁻¹⟨g⟨S⟩⟩ ⇒ z∈S

    # ── ⇐ : z∈S ⇒ z∈g⁻¹⟨g⟨S⟩⟩ ─────────────────────────────────────────────────
    hzS = N.assume(appartient(vz, vS))                           # z∈S
    # z∈b (S⊂b) → (∃y)(z,y)∈g (z∈dom g=b)
    zB_imp = N.modus_ponens(hsub, instanciation_en_x(            # z∈S ⇒ z∈b
        impl(appartient(vz, vS), appartient(vz, vB)), "z"))
    zB = N.modus_ponens(hzS, zB_imp)                             # z∈b
    b_eq_domg = N.modus_ponens(g_dom, symetrie(E.dom(vg), vB))   # b = dom g
    z_dom = N.modus_ponens(zB, equivalence_avant(N.modus_ponens(
        b_eq_domg, N.s6(vB, E.dom(vg), "w", appartient(vz, var("w"))))))  # z∈dom g
    ex_zy = N.modus_ponens(z_dom, equivalence_avant(_inst_dom(vg, vz)))       # (∃y)(z,y)∈g
    z_gz = N.modus_ponens(ex_zy, N.loi_deduction(
        existe("y", appartient(E.couple(vz, var("y")), vg)),
        valeur_dans_graphe(vg, vz)))                                          # (z, g(z))∈g
    gz = E.valeur(vg, vz)
    # g(z)∈g⟨S⟩ : (∃u)(u∈S et (u,g(z))∈g) avec témoin u:=z
    body_gz = et(appartient(vu, vS), appartient(E.couple(vu, gz), vg))
    in_gS = N.modus_ponens(conjonction_intro(hzS, z_gz),
                           N.s5(body_gz, vz, "u"))                            # (∃u)…  = g(z)∈g⟨S⟩ (post carInner)
    gz_in_gS = N.modus_ponens(in_gS, equivalence_arriere(
        equivalence_transitivite(_inst_image(vg, vS, gz), alpha_existe("x", "u",
            et(appartient(var("x"), vS), appartient(E.couple(var("x"), gz), vg))))))  # g(z)∈g⟨S⟩
    # (g(z),z)∈g⁻¹  (couple_reciproque sens arrière de (z,g(z))∈g)
    gz_z_rec = N.modus_ponens(z_gz, equivalence_arriere(couple_reciproque(vg, gz, vz)))  # (g(z),z)∈g⁻¹
    # z∈g⁻¹⟨g⟨S⟩⟩ : (∃y)(y∈g⟨S⟩ et (y,z)∈g⁻¹) avec témoin y:=g(z)
    body_out = et(appartient(vy, gS), appartient(E.couple(vy, vz), grec))
    in_img = N.modus_ponens(conjonction_intro(gz_in_gS, gz_z_rec),
                            N.s5(body_out, gz, "y"))                          # (∃y)body_out
    z_in_img = N.modus_ponens(in_img, equivalence_arriere(
        equivalence_transitivite(_inst_image(grec, gS, vz), alpha_existe("x", "y",
            et(appartient(var("x"), gS), appartient(E.couple(var("x"), vz), grec))))))  # z∈g⁻¹⟨g⟨S⟩⟩
    bwd = N.loi_deduction(appartient(vz, vS), z_in_img)         # z∈S ⇒ z∈g⁻¹⟨g⟨S⟩⟩

    # ── extensionnalité A1 ────────────────────────────────────────────────────
    incl_LR = N.generalisation("z", fwd)                        # g⁻¹⟨g⟨S⟩⟩ ⊂ S
    incl_RL = N.generalisation("z", bwd)                        # S ⊂ g⁻¹⟨g⟨S⟩⟩
    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), imgrecgS), vS)
    eqset = N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)   # g⁻¹⟨g⟨S⟩⟩ = S
    inner = N.loi_deduction(inclus(vS, vB), eqset)              # (S⊂b) ⇒ (…=S)
    return N.loi_deduction(est_injection_de(vg, vB, vA), inner)


# ════════════════════════════════════════════════════════════════════════════
#  Helpers ÉTAPE 2 : g⁻¹ injective sur une partie W ⊂ dom g⁻¹
# ════════════════════════════════════════════════════════════════════════════
def _reciproque_injective_sur(g, w):
    """{g fonctionnel} ⊢ (W ⊂ dom g⁻¹) ⇒ injective_dans(g⁻¹, W).

    Pour u,u'∈W⊂dom g⁻¹ : (u,g⁻¹(u))∈g⁻¹ → (g⁻¹(u),u)∈g (couple_reciproque) ; idem u' ;
    de g⁻¹(u)=g⁻¹(u') et g fonctionnel (même 1ère coord g⁻¹(u)) ⇒ u=u'."""
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
    vg, vW = _t(g), _t(w)
    grec = E.reciproque(vg)
    vu, vup = var("u"), var("up")
    hfunc = N.assume(E.est_fonctionnel(vg))
    hsub = N.assume(inclus(vW, E.dom(grec)))

    def couple_de(uu):
        """sous uu∈W : ⊢ (g⁻¹(uu), uu) ∈ g."""
        uu_in_dom = N.modus_ponens(N.assume(appartient(uu, vW)),
                                   instancie(hsub, uu))           # uu∈dom g⁻¹
        ex = N.modus_ponens(uu_in_dom, equivalence_avant(_inst_dom(grec, uu)))  # (∃y)(uu,y)∈g⁻¹
        in_grec = N.modus_ponens(ex, N.loi_deduction(
            existe("y", appartient(E.couple(uu, var("y")), grec)),
            valeur_dans_graphe(grec, uu)))                        # (uu,g⁻¹(uu))∈g⁻¹
        guu = E.valeur(grec, uu)
        return N.modus_ponens(in_grec, equivalence_avant(couple_reciproque(vg, uu, guu)))  # (g⁻¹(uu),uu)∈g

    hyp = et(et(appartient(vu, vW), appartient(vup, vW)),
             egal(E.valeur(grec, vu), E.valeur(grec, vup)))
    h = N.assume(hyp)
    uW = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upW = conjonction_elim_droite(conjonction_elim_gauche(h))
    val_eq = conjonction_elim_droite(h)                           # g⁻¹(u)=g⁻¹(u')
    gu, gup = E.valeur(grec, vu), E.valeur(grec, vup)
    # (g⁻¹(u),u)∈g  et  (g⁻¹(u'),u')∈g, sous u,u'∈W
    gu_u = N.modus_ponens(uW, N.loi_deduction(appartient(vu, vW), couple_de(vu)))   # (g⁻¹(u),u)∈g
    gup_up = N.modus_ponens(upW, N.loi_deduction(appartient(vup, vW), couple_de(vup)))  # (g⁻¹(u'),u')∈g
    # réécrire g⁻¹(u')→g⁻¹(u) dans (g⁻¹(u'),u')∈g  → (g⁻¹(u),u')∈g
    gup_eq_gu = N.modus_ponens(val_eq, symetrie(gu, gup))         # g⁻¹(u')=g⁻¹(u)
    gu_up = N.modus_ponens(gup_up, equivalence_avant(N.modus_ponens(
        gup_eq_gu, N.s6(gup, gu, "w", appartient(E.couple(var("w"), vup), vg)))))   # (g⁻¹(u),u')∈g
    inst = instancie(instancie(instancie(hfunc, gu), vu), vup)    # ((g⁻¹(u),u)∈g et (g⁻¹(u),u')∈g)⇒u=u'
    u_eq = N.modus_ponens(conjonction_intro(gu_u, gu_up), inst)   # u=u'
    inner = N.loi_deduction(hyp, u_eq)
    gen = N.generalisation("u", N.generalisation("up", inner))    # injective_dans(g⁻¹, W)
    return N.loi_deduction(inclus(vW, E.dom(grec)), gen)          # (W⊂dom g⁻¹) ⇒ inj


def _img_croiss(g, x, y):
    """⊢ (X ⊂ Y) ⇒ (g⟨X⟩ ⊂ g⟨Y⟩)  pour des TERMES g,x,y."""
    from bourbaki.ensembles.base.ensembles_correspondances import image_croissante
    th = image_croissante("G", "X", "Y")
    th = instancie(N.generalisation("G", th), _t(g))
    th = instancie(N.generalisation("X", th), _t(x))
    th = instancie(N.generalisation("Y", th), _t(y))
    return th


def _image_dans_img_terme(g, x):
    """⊢ g⟨X⟩ ⊂ pr₂(g) = dom(g⁻¹)  pour des TERMES g, x."""
    from bourbaki.ensembles.base.ensembles_correspondances import image_dans_img
    th = image_dans_img("G", "X")
    th = instancie(N.generalisation("G", th), _t(g))
    th = instancie(N.generalisation("X", th), _t(x))
    return th


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — morceau_gI : g⁻¹|(A∖D) bijection de A∖D sur B∖f⟨D⟩
# ════════════════════════════════════════════════════════════════════════════
def morceau_gI(a="A", b="B", f="f", g="g"):
    """{est_injection_de(g,b,a)} ⊢ est_bijection_de(g⁻¹|(A∖D), A∖D, B∖f⟨D⟩).

    gI = restriction(g⁻¹, A∖D).  De est_injection_de(g,b,a) :
      • gI fonctionnel        (restriction_fonctionnelle, g⁻¹ fonctionnel par Prop.7) ;
      • dom(gI)=A∖D           (restriction_dom_sous_inclusion, A∖D⊂dom g⁻¹) ;
      • injective_dans(gI,A∖D) (restriction_injective : g⁻¹ inj sur A∖D⊂dom g⁻¹) ;
      • image(gI,A∖D)=B∖f⟨D⟩  (restriction_image + pivot + ÉTAPE 1, S=B∖f⟨D⟩⊂b).
    """
    from bourbaki.cardinaux.ensembles_bijection import reciproque_fonctionnelle
    from bourbaki.cardinaux.ensembles_cantor_bernstein_bij import (
        restriction_dom_sous_inclusion, restriction_injective,
        restriction_image_egale_image, _restriction_fonctionnelle_terme)
    from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import pivot_AmoinsD
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    grec = E.reciproque(vg)
    dterm = CB.D(vA, vB, vf, vg)
    AmD = E.difference(vA, dterm)                       # A∖D
    BmfD = E.difference(vB, E.image(vf, dterm))         # B∖f⟨D⟩
    gI = E.restriction(grec, AmD)

    hinj = N.assume(est_injection_de(vg, vB, vA))
    g_func = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hinj)))
    g_dom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hinj)))
    g_injB = conjonction_elim_droite(conjonction_elim_gauche(hinj))

    # g⁻¹ fonctionnel (Prop.7)
    grec_func = _cut(reciproque_fonctionnelle(vg, vB),
                     [(E.est_fonctionnel(vg), g_func),
                      (egal(E.dom(vg), vB), g_dom),
                      (E.injective_dans(vg, vB), g_injB)])  # ⊢ est_fonctionnel(g⁻¹)

    # A∖D ⊂ dom g⁻¹ : A∖D = g⟨B∖f⟨D⟩⟩ (pivot) ⊂ pr₂(g) = dom(g⁻¹) (image_dans_img + pr1_reciproque)
    from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import pr1_reciproque
    piv = _cut(pivot_AmoinsD(a, b, f, g), [(est_injection_de(vg, vB, vA), hinj)])  # A∖D = g⟨B∖f⟨D⟩⟩
    gBfD = E.image(vg, BmfD)                            # g⟨B∖f⟨D⟩⟩
    sub_gBfD_img = _image_dans_img_terme(vg, BmfD)      # g⟨B∖f⟨D⟩⟩ ⊂ pr₂(g)
    # dom g⁻¹ = pr₁(g⁻¹) = pr₂(g)  (pr1_reciproque)  ;  réécrire pr₂(g) → dom(g⁻¹)
    pr1rec = pr1_reciproque(vg)                          # pr₁(g⁻¹) = pr₂(g)   (=dom(g⁻¹)=img(g))
    img_eq_domrec = N.modus_ponens(pr1rec, symetrie(E.dom(grec), E.img(vg)))  # pr₂(g)=dom(g⁻¹)
    sub_gBfD_domrec = N.modus_ponens(sub_gBfD_img, equivalence_avant(N.modus_ponens(
        img_eq_domrec, N.s6(E.img(vg), E.dom(grec), "w", inclus(gBfD, var("w"))))))  # g⟨B∖f⟨D⟩⟩⊂dom g⁻¹
    # réécrire g⟨B∖f⟨D⟩⟩ → A∖D  via pivot (sym)
    AmD_eq_gBfD = piv                                    # A∖D = g⟨B∖f⟨D⟩⟩
    sub_AmD_domrec = N.modus_ponens(sub_gBfD_domrec, equivalence_avant(N.modus_ponens(
        N.modus_ponens(AmD_eq_gBfD, symetrie(AmD, gBfD)),
        N.s6(gBfD, AmD, "w", inclus(var("w"), E.dom(grec))))))    # A∖D ⊂ dom g⁻¹

    # ── conjoint 1 : gI fonctionnel ──────────────────────────────────────────
    c_func = N.modus_ponens(grec_func, _restriction_fonctionnelle_terme(grec, AmD))
    # ── conjoint 2 : dom(gI)=A∖D ─────────────────────────────────────────────
    c_dom = N.modus_ponens(sub_AmD_domrec, restriction_dom_sous_inclusion(grec, AmD))
    # ── conjoint 3 : injective_dans(gI, A∖D) ─────────────────────────────────
    inj_imp = _reciproque_injective_sur(vg, AmD)        # {g func} ⊢ (A∖D⊂dom g⁻¹)⇒inj(g⁻¹,A∖D)
    grec_inj_AmD = _cut(N.modus_ponens(sub_AmD_domrec, inj_imp),
                        [(E.est_fonctionnel(vg), g_func)])  # injective_dans(g⁻¹, A∖D)
    ri = restriction_injective(grec, AmD)               # {g⁻¹ func, inj/A∖D, A∖D⊂dom g⁻¹}⊢inj(gI,A∖D)
    c_inj = _cut(ri, [(E.est_fonctionnel(grec), grec_func),
                      (E.injective_dans(grec, AmD), grec_inj_AmD),
                      (inclus(AmD, E.dom(grec)), sub_AmD_domrec)])
    # ── conjoint 4 : image(gI,A∖D)=B∖f⟨D⟩ ────────────────────────────────────
    # image(gI,A∖D)=image(g⁻¹,A∖D)=image(g⁻¹,g⟨B∖f⟨D⟩⟩)=B∖f⟨D⟩
    img_restr = restriction_image_egale_image(grec, AmD)  # image(gI,A∖D)=image(g⁻¹,A∖D)
    # image(g⁻¹,A∖D)=image(g⁻¹,g⟨B∖f⟨D⟩⟩) via congruence (A∖D=g⟨B∖f⟨D⟩⟩)
    img_cong = N.modus_ponens(piv, congruence_terme(AmD, gBfD,
        E.image(grec, var("w"))))                          # image(g⁻¹,A∖D)=image(g⁻¹,g⟨B∖f⟨D⟩⟩)
    # ÉTAPE 1 : image(g⁻¹,g⟨B∖f⟨D⟩⟩)=B∖f⟨D⟩, S=B∖f⟨D⟩⊂b
    sub_BmfD_B = _diff_inclus_terme(vB, E.image(vf, dterm))   # B∖f⟨D⟩ ⊂ b
    retr = image_reciproque_image(vg, vA, vB, BmfD)     # inj(g,b,a)⇒((S⊂b)⇒image(g⁻¹,g⟨S⟩)=S)
    retr = N.modus_ponens(hinj, retr)
    retr = N.modus_ponens(sub_BmfD_B, retr)             # image(g⁻¹,g⟨B∖f⟨D⟩⟩)=B∖f⟨D⟩
    c_img = composer_egalites(composer_egalites(img_restr, img_cong), retr)  # image(gI,A∖D)=B∖f⟨D⟩

    bij = conjonction_intro(conjonction_intro(c_func, c_dom),
                            conjonction_intro(c_inj, c_img))   # est_bijection_de(gI,A∖D,B∖f⟨D⟩)
    return N.loi_deduction(est_injection_de(vg, vB, vA), bij)


def _diff_inclus_terme(e, x):
    """⊢ (E∖X) ⊂ E  pour des TERMES e, x."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import _diff_inclus
    vE, vX = _t(e), _t(x)
    th = _diff_inclus("E", "X")
    th = instancie(N.generalisation("E", th), vE)
    th = instancie(N.generalisation("X", th), vX)
    return th


__all__ = ["image_reciproque_image", "morceau_gI"]
