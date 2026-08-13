"""§II.3.7 / §III.3 — Réciproque d'une bijection : F⁻¹ fonctionnel (Proposition 7).

⊢_{F fonctionnel, dom F=X, F injective sur X}  est_fonctionnel(F⁻¹).
Pont graphe↔valeurs : (u,v)∈F⁻¹ ⇔ (v,u)∈F ; d'une coïncidence (v,u),(z,u)∈F on
tire f(v)=u=f(z) (C46) avec v,z∈X (dom F=X), puis v=z par injectivité gardée.
Premier des quatre conjoints de « F⁻¹ est une bijection Y→X » (symétrie de Eq).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient, existe
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               equivalence_symetrie, projection_gauche,
                               projection_droite, et_congruence_droite, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (congruence_existe, existe_elimination, alpha_existe,
                                      et_existe_droite, existe_commute)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_caracterisation, valeur_dans_graphe
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composee_fonctionnelle, composition_valeur
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee import couple_composee, image_composee
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


def _premier_dans_X(f, x, vt, va):
    """{dom F = X} ⊢ ((vt,va) ∈ F) ⇒ (vt ∈ X).   (le 1er coord d'un couple de F est dans dom F=X.)"""
    vF, vX = _T(f), _T(x)
    h = N.assume(appartient(E.couple(vt, va), vF))
    t_dom = N.modus_ponens(N.modus_ponens(h, N.s5(appartient(E.couple(vt, var("y")), vF), va, "y")),
                           equivalence_arriere(_inst_dom(vF, vt)))             # vt∈dom F
    hdom = N.assume(egal(E.dom(vF), vX))
    t_inX = N.modus_ponens(t_dom, equivalence_avant(N.modus_ponens(
        hdom, N.s6(E.dom(vF), vX, "w", appartient(vt, var("w"))))))            # vt∈X
    return N.loi_deduction(appartient(E.couple(vt, va), vF), t_inX)


def reciproque_domaine(f="F", x="X", y="Y"):
    """⊢_{dom F = X, image(F,X) = Y}  dom(F⁻¹) = Y.   (2e conjoint de la symétrie de Eq.)"""
    vF, vX, vY = _T(f), _T(x), _T(y)
    vz = var("z")
    Frec = E.reciproque(vF)
    # char_dom : (∀z)(z∈dom F⁻¹ ⇔ (∃t)((t,z)∈F))
    dom_ax = _inst_dom(Frec, vz)                                  # z∈dom F⁻¹ ⇔ (∃y)((z,y)∈F⁻¹)
    cr = couple_reciproque(f, "z", "t")                           # ((z,t)∈F⁻¹)⇔((t,z)∈F)
    char1 = equivalence_transitivite(dom_ax, alpha_existe("y", "t",
                appartient(E.couple(vz, var("y")), Frec)))        # z∈dom F⁻¹ ⇔ (∃t)((z,t)∈F⁻¹)
    char1 = equivalence_transitivite(char1, congruence_existe(cr, "t"))   # ⇔ (∃t)((t,z)∈F)
    char_dom = N.generalisation("z", char1)
    # char_Y : (∀z)(z∈Y ⇔ (∃t)((t,z)∈F))
    himg = N.assume(egal(E.image(vF, vX), vY))
    iff1 = N.modus_ponens(N.modus_ponens(himg, symetrie(E.image(vF, vX), vY)),
                          N.s6(vY, E.image(vF, vX), "w", appartient(vz, var("w"))))  # z∈Y ⇔ z∈image
    iff2 = _inst_image(vF, vX, vz)                                # z∈image ⇔ (∃x)(x∈X et (x,z)∈F)
    # redondance de « x∈X » : (∃x)(x∈X et (x,z)∈F) ⇔ (∃x)((x,z)∈F)  (sous dom F=X)
    inner = et(appartient(var("x"), vX), appartient(E.couple(var("x"), vz), vF))
    fwd = N.loi_deduction(inner, conjonction_elim_droite(N.assume(inner)))        # ⇒ (x,z)∈F
    bwd = N.loi_deduction(appartient(E.couple(var("x"), vz), vF), conjonction_intro(
        N.modus_ponens(N.assume(appartient(E.couple(var("x"), vz), vF)), _premier_dans_X(f, x, var("x"), vz)),
        N.assume(appartient(E.couple(var("x"), vz), vF))))                        # ⇐
    redund = congruence_existe(conjonction_intro(fwd, bwd), "x")
    iff3 = equivalence_transitivite(iff2, redund)                 # z∈image ⇔ (∃x)((x,z)∈F)
    align = alpha_existe("x", "t", appartient(E.couple(var("x"), vz), vF))        # (∃x)…⇔(∃t)…
    char2 = equivalence_transitivite(equivalence_transitivite(iff1, iff3), align)
    char_Y = N.generalisation("z", char2)
    return egalite_par_extension(char_dom, char_Y, E.dom(Frec), vY)


def _second_dans_Y(f, x, y, vz, vt):
    """{dom F=X, image(F,X)=Y} ⊢ ((vz,vt)∈F) ⇒ (vt∈Y).   (2e coord d'un couple de F ∈ image=Y.)"""
    vF, vX, vY = _T(f), _T(x), _T(y)
    h = N.assume(appartient(E.couple(vz, vt), vF))
    z_inX = N.modus_ponens(h, _premier_dans_X(f, x, vz, vt))               # vz∈X
    body = et(appartient(var("x"), vX), appartient(E.couple(var("x"), vt), vF))
    t_img = N.modus_ponens(N.modus_ponens(conjonction_intro(z_inX, h), N.s5(body, vz, "x")),
                           equivalence_arriere(_inst_image(vF, vX, vt)))   # vt∈image(F,X)
    himg = N.assume(egal(E.image(vF, vX), vY))
    t_inY = N.modus_ponens(t_img, equivalence_avant(N.modus_ponens(
        himg, N.s6(E.image(vF, vX), vY, "w", appartient(vt, var("w"))))))  # vt∈Y
    return N.loi_deduction(appartient(E.couple(vz, vt), vF), t_inY)


def image_reciproque(f="F", x="X", y="Y"):
    """⊢_{dom F = X, image(F,X) = Y}  image(F⁻¹, Y) = X.   (3e conjoint de la symétrie de Eq.)"""
    vF, vX, vY = _T(f), _T(x), _T(y)
    vz = var("z")
    Frec = E.reciproque(vF)
    # char_img : (∀z)(z∈image(F⁻¹,Y) ⇔ (∃t)((z,t)∈F))
    img_ax = _inst_image(Frec, vY, vz)                            # z∈image(F⁻¹,Y) ⇔ (∃x)(x∈Y et (x,z)∈F⁻¹)
    cr = couple_reciproque(f, "x", "z")                           # ((x,z)∈F⁻¹)⇔((z,x)∈F)
    step_cr = congruence_existe(et_congruence_droite(appartient(var("x"), vY), cr), "x")
    #   (∃x)(x∈Y et (x,z)∈F⁻¹) ⇔ (∃x)(x∈Y et (z,x)∈F)
    ren = alpha_existe("x", "t", et(appartient(var("x"), vY),     # renomme x→t (≠ liant interne image)
                                    appartient(E.couple(vz, var("x")), vF)))
    # redondance « t∈Y » sous {(z,t)∈F ⇒ t∈Y} :
    inn = et(appartient(var("t"), vY), appartient(E.couple(vz, var("t")), vF))
    fwd = N.loi_deduction(inn, conjonction_elim_droite(N.assume(inn)))
    bwd = N.loi_deduction(appartient(E.couple(vz, var("t")), vF), conjonction_intro(
        N.modus_ponens(N.assume(appartient(E.couple(vz, var("t")), vF)),
                       _second_dans_Y(f, x, y, vz, var("t"))),
        N.assume(appartient(E.couple(vz, var("t")), vF))))
    redund = congruence_existe(conjonction_intro(fwd, bwd), "t")   # (∃t)(t∈Y et (z,t)∈F) ⇔ (∃t)((z,t)∈F)
    char1 = equivalence_transitivite(img_ax, equivalence_transitivite(step_cr,
                equivalence_transitivite(ren, redund)))           # z∈image(F⁻¹,Y) ⇔ (∃t)((z,t)∈F)
    char_img = N.generalisation("z", char1)
    # char_X : (∀z)(z∈X ⇔ (∃t)((z,t)∈F))
    hdom = N.assume(egal(E.dom(vF), vX))
    zX = N.modus_ponens(N.modus_ponens(hdom, symetrie(E.dom(vF), vX)),
                        N.s6(vX, E.dom(vF), "w", appartient(vz, var("w"))))   # z∈X ⇔ z∈dom F
    char_X1 = equivalence_transitivite(zX, equivalence_transitivite(_inst_dom(vF, vz),
                alpha_existe("y", "t", appartient(E.couple(vz, var("y")), vF))))
    char_X = N.generalisation("z", char_X1)
    return egalite_par_extension(char_img, char_X, E.image(Frec, vY), vX)


def reciproque_injective(f="F", x="X", y="Y"):
    """⊢_{F fonctionnel, dom F=X, image(F,X)=Y}  injective_dans(F⁻¹, Y).   (4e conjoint, symétrie.)"""
    vF, vX, vY = _T(f), _T(x), _T(y)
    vu, vup = var("u"), var("up")
    Frec = E.reciproque(vF)
    rd = reciproque_domaine(f, x, y)                              # dom F⁻¹ = Y
    hyp = et(et(appartient(vu, vY), appartient(vup, vY)),
             egal(E.valeur(Frec, vu), E.valeur(Frec, vup)))
    h = N.assume(hyp)

    def couple_de(uu, uu_inY):                                   # ⊢ (F⁻¹(uu), uu) ∈ F
        uu_dom = N.modus_ponens(uu_inY, equivalence_arriere(N.modus_ponens(
            rd, N.s6(E.dom(Frec), vY, "w", appartient(uu, var("w"))))))      # uu∈dom F⁻¹
        ex = N.modus_ponens(uu_dom, equivalence_avant(_inst_dom(Frec, uu))) # (∃y)(uu,y)∈F⁻¹
        in_frec = N.modus_ponens(ex, N.loi_deduction(
            existe("y", appartient(E.couple(uu, var("y")), Frec)), valeur_dans_graphe(Frec, uu)))
        fuu = E.valeur(Frec, uu)
        return N.modus_ponens(in_frec, equivalence_avant(couple_reciproque(vF, uu, fuu)))

    fu_u = couple_de(vu, conjonction_elim_gauche(conjonction_elim_gauche(h)))     # (F⁻¹(u),u)∈F
    fup_up = couple_de(vup, conjonction_elim_droite(conjonction_elim_gauche(h)))  # (F⁻¹(u'),u')∈F
    fu, fup = E.valeur(Frec, vu), E.valeur(Frec, vup)
    fup_eq_fu = N.modus_ponens(conjonction_elim_droite(h), symetrie(fu, fup))     # F⁻¹(u')=F⁻¹(u)
    fu_up = N.modus_ponens(fup_up, equivalence_avant(N.modus_ponens(             # (F⁻¹(u),u')∈F
        fup_eq_fu, N.s6(fup, fu, "w", appartient(E.couple(var("w"), vup), vF)))))
    hfunc = N.assume(E.est_fonctionnel(vF))
    inst = instancie(instancie(instancie(hfunc, fu), vu), vup)   # ((F⁻¹(u),u)∈F et (F⁻¹(u),u')∈F)⇒u=u'
    u_eq = N.modus_ponens(conjonction_intro(fu_u, fu_up), inst)  # u=u'
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))


def _cut(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`
    (loi_deduction puis modus_ponens)."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


# @livre Ch.III §3.1 Rem.- | E III.23 L.18-19 | PDF p.126
#   (« Il est clair que les relations Eq(X, Y) et Eq(Y, X) sont équivalentes,
#    autrement dit, la relation Eq(X, Y) est symétrique » — formalisé ici.)
def equipotence_symetrique(f="F", x="X", y="Y"):
    """⊢ Eq(X, Y) ⇒ Eq(Y, X).   (SYMÉTRIE de l'équipotence : F⁻¹ est une bijection Y→X.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
    vF, vX, vY = _T(f), _T(x), _T(y)
    Frec = E.reciproque(vF)
    hbij = N.assume(est_bijection_de(vF, vX, vY))
    g, d = conjonction_elim_gauche(hbij), conjonction_elim_droite(hbij)
    f_func = conjonction_elim_gauche(g)                           # F fonctionnel
    f_dom = conjonction_elim_droite(g)                            # dom F = X
    f_inj = conjonction_elim_gauche(d)                            # injective_dans(F,X)
    f_img = conjonction_elim_droite(d)                            # image(F,X) = Y
    p_func = (E.est_fonctionnel(vF), f_func)
    p_dom = (egal(E.dom(vF), vX), f_dom)
    p_inj = (E.injective_dans(vF, vX), f_inj)
    p_img = (egal(E.image(vF, vX), vY), f_img)
    c1 = _cut(reciproque_fonctionnelle(f, x), [p_func, p_dom, p_inj])    # F⁻¹ fonctionnel
    c2 = _cut(reciproque_domaine(f, x, y), [p_dom, p_img])              # dom F⁻¹ = Y
    c3 = _cut(image_reciproque(f, x, y), [p_dom, p_img])               # image(F⁻¹,Y) = X
    c4 = _cut(reciproque_injective(f, x, y), [p_func, p_dom, p_img])    # injective_dans(F⁻¹,Y)
    bij_rec = conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c4, c3))
    eq_yx = N.modus_ponens(bij_rec, N.s5(est_bijection_de(var("F"), vY, vX), Frec, "F"))  # Eq(Y,X)
    stepA = N.loi_deduction(est_bijection_de(vF, vX, vY), eq_yx)        # est_bijection_de(F,X,Y)⇒Eq(Y,X)
    return existe_elimination(stepA, "F")                              # Eq(X,Y) ⇒ Eq(Y,X)


# ── Composée de bijections (transitivité de Eq) — les 4 conjoints ─────────────
def composee_image(g="G", f="F", x="X", y="Y", z="Z"):
    """⊢_{image(F,X)=Y, image(G,Y)=Z}  image(G∘F, X) = Z.   (4e conjoint, via Prop. 5.)"""
    vG, vF, vX, vY, vZ = _T(g), _T(f), _T(x), _T(y), _T(z)   # g,f,x,y,z acceptent un TERME composé
    ic = image_composee(g, f, x)                                  # image(G∘F,X)=image(G,image(F,X))
    f_img = N.assume(egal(E.image(vF, vX), vY))
    rw = N.modus_ponens(f_img, congruence_terme(E.image(vF, vX), vY, E.image(vG, var("w"))))
    g_img = N.assume(egal(E.image(vG, vY), vZ))
    return composer_egalites(composer_egalites(ic, rw), g_img)   # image(G∘F,X)=Z


def composee_domaine(g="G", f="F", x="X", y="Y"):
    """⊢_{dom F=X, image(F,X)=Y, dom G=Y}  dom(G∘F) = X.   (2e conjoint de la transitivité.)"""
    vG, vF, vX, vY = _T(g), _T(f), _T(x), _T(y)   # g,f,x,y acceptent un TERME composé
    vz, vm = var("z"), var("m")
    comp = E.composee(vG, vF)
    zmF = appartient(E.couple(vz, vm), vF)                        # (z,m)∈F
    # char_dom : (∀z)(z∈dom(G∘F) ⇔ (∃m)((z,m)∈F))
    dom_ax = _inst_dom(comp, vz)                                  # z∈dom(G∘F)⇔(∃y)((z,y)∈G∘F)
    ren1 = alpha_existe("y", "v", appartient(E.couple(vz, var("y")), comp))
    cc = couple_composee(g, f, "z", "v")                          # ((z,v)∈G∘F)⇔(∃y)((z,y)∈F et (y,v)∈G)
    cc_m = equivalence_transitivite(cc, alpha_existe("y", "m",
        et(appartient(E.couple(vz, var("y")), vF), appartient(E.couple(var("y"), var("v")), vG))))
    step1 = congruence_existe(cc_m, "v")                          # (∃v)(z,v)∈G∘F ⇔ (∃v)(∃m)(…)
    P = et(zmF, appartient(E.couple(vm, var("v")), vG))           # (z,m)∈F et (m,v)∈G
    comm = existe_commute("v", "m", P)                           # (∃v)(∃m)P ⇔ (∃m)(∃v)P
    ee = et_existe_droite(zmF, "v", appartient(E.couple(vm, var("v")), vG))
    ee_cong = congruence_existe(equivalence_symetrie(ee), "m")    # (∃m)(∃v)P ⇔ (∃m)((z,m)∈F et (∃v)(m,v)∈G)
    # redondance : ((z,m)∈F et (∃v)(m,v)∈G) ⇔ (z,m)∈F
    exvG = existe("v", appartient(E.couple(vm, var("v")), vG))    # (∃v)(m,v)∈G
    r_fwd = N.loi_deduction(et(zmF, exvG), conjonction_elim_gauche(N.assume(et(zmF, exvG))))
    hm = N.assume(zmF)
    m_inY = N.modus_ponens(hm, _second_dans_Y(f, x, y, vz, vm))   # m∈Y
    hdomG = N.assume(egal(E.dom(vG), vY))
    m_dom = N.modus_ponens(m_inY, equivalence_avant(N.modus_ponens(
        N.modus_ponens(hdomG, symetrie(E.dom(vG), vY)),
        N.s6(vY, E.dom(vG), "w", appartient(vm, var("w"))))))     # m∈dom G
    dm_v = equivalence_transitivite(_inst_dom(vG, vm),
        alpha_existe("y", "v", appartient(E.couple(vm, var("y")), vG)))   # m∈dom G ⇔ (∃v)(m,v)∈G
    ex_v = N.modus_ponens(m_dom, equivalence_avant(dm_v))         # (∃v)(m,v)∈G
    r_bwd = N.loi_deduction(zmF, conjonction_intro(hm, ex_v))
    redund = congruence_existe(conjonction_intro(r_fwd, r_bwd), "m")
    char1 = equivalence_transitivite(dom_ax, equivalence_transitivite(ren1,
        equivalence_transitivite(step1, equivalence_transitivite(comm,
        equivalence_transitivite(ee_cong, redund)))))            # z∈dom(G∘F) ⇔ (∃m)((z,m)∈F)
    char_dom = N.generalisation("z", char1)
    # char_X : (∀z)(z∈X ⇔ (∃m)((z,m)∈F))
    hdomF = N.assume(egal(E.dom(vF), vX))
    zX = N.modus_ponens(N.modus_ponens(hdomF, symetrie(E.dom(vF), vX)),
                        N.s6(vX, E.dom(vF), "w", appartient(vz, var("w"))))   # z∈X ⇔ z∈dom F
    char_X1 = equivalence_transitivite(zX, equivalence_transitivite(_inst_dom(vF, vz),
        alpha_existe("y", "m", appartient(E.couple(vz, var("y")), vF))))
    char_X = N.generalisation("z", char_X1)
    return egalite_par_extension(char_dom, char_X, E.dom(comp), vX)


def _inj_setup(f, vF, vX, vY, uu, uu_inX, hdomF, hdomG):
    """Sous {dom F=X, image(F,X)=Y, dom G=Y} et uu∈X : renvoie
    ((∃y)(uu,y)∈F, F(uu)∈Y, (∃y)(F(uu),y)∈G)."""
    ex = N.modus_ponens(N.modus_ponens(uu_inX, equivalence_arriere(N.modus_ponens(
        hdomF, N.s6(E.dom(vF), vX, "w", appartient(uu, var("w")))))),
        equivalence_avant(_inst_dom(vF, uu)))                    # (∃y)(uu,y)∈F  [via uu∈dom F]
    in_F = N.modus_ponens(ex, N.loi_deduction(
        existe("y", appartient(E.couple(uu, var("y")), vF)), valeur_dans_graphe(vF, uu)))
    fuu = E.valeur(vF, uu)
    fuu_inY = N.modus_ponens(in_F, _second_dans_Y(f, vX.nom, vY.nom, uu, fuu))   # F(uu)∈Y
    fuu_domG = N.modus_ponens(N.modus_ponens(fuu_inY, equivalence_arriere(N.modus_ponens(
        hdomG, N.s6(E.dom(_GG[0]), vY, "w", appartient(fuu, var("w")))))),
        equivalence_avant(_inst_dom(_GG[0], fuu)))               # (∃y)(F(uu),y)∈G
    return ex, fuu_inY, fuu_domG


_GG = [None]   # canal pour passer vG à _inj_setup (évite un long passage d'argument)


def composee_injective(g="G", f="F", x="X", y="Y"):
    """⊢_{F,G fonctionnels, dom F=X, image(F,X)=Y, dom G=Y, F inj/X, G inj/Y}
       injective_dans(G∘F, X).   (3e conjoint de la transitivité.)"""
    vG, vF, vX, vY = _T(g), _T(f), _T(x), _T(y)   # g,f,x,y acceptent un TERME composé
    _GG[0] = vG
    vu, vup = var("u"), var("up")
    comp = E.composee(vG, vF)
    hFfunc, hGfunc = N.assume(E.est_fonctionnel(vF)), N.assume(E.est_fonctionnel(vG))
    hdomF, hdomG = N.assume(egal(E.dom(vF), vX)), N.assume(egal(E.dom(vG), vY))
    hFinj, hGinj = N.assume(E.injective_dans(vF, vX)), N.assume(E.injective_dans(vG, vY))
    hyp = et(et(appartient(vu, vX), appartient(vup, vX)),
             egal(E.valeur(comp, vu), E.valeur(comp, vup)))
    h = N.assume(hyp)
    u_inX = conjonction_elim_gauche(conjonction_elim_gauche(h))
    up_inX = conjonction_elim_droite(conjonction_elim_gauche(h))
    gof_eq = conjonction_elim_droite(h)                          # (G∘F)(u)=(G∘F)(u')

    def compo_val(uu, uu_inX):                                  # ⊢ (G∘F)(uu)=G(F(uu)), F(uu)∈Y
        ex, fuu_inY, fuu_domG = _inj_setup(f, vF, vX, vY, uu, uu_inX, hdomF, hdomG)
        cv = _cut(composition_valeur(g, f, uu.nom),
                  [(existe("y", appartient(E.couple(uu, var("y")), vF)), ex),
                   (existe("y", appartient(E.couple(E.valeur(vF, uu), var("y")), vG)), fuu_domG)])
        return cv, fuu_inY

    cv_u, fu_inY = compo_val(vu, u_inX)
    cv_up, fup_inY = compo_val(vup, up_inX)
    fu, fup = E.valeur(vF, vu), E.valeur(vF, vup)
    gfu_eq = composer_egalites(composer_egalites(_eqsym(cv_u), gof_eq), cv_up)  # G(F(u))=G(F(u'))
    ginj = instancie(instancie(hGinj, fu), fup)
    fu_eq = N.modus_ponens(conjonction_intro(conjonction_intro(fu_inY, fup_inY), gfu_eq), ginj)  # F(u)=F(u')
    finj = instancie(instancie(hFinj, vu), vup)
    u_eq = N.modus_ponens(conjonction_intro(conjonction_intro(u_inX, up_inX), fu_eq), finj)       # u=u'
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))


def _eqsym(thm):
    """⊢ (a=b) ⟹ ⊢ (b=a)  (symétrie appliquée à une preuve d'égalité)."""
    a, b = thm.conclusion.termes
    return N.modus_ponens(thm, symetrie(a, b))


# @livre Ch.III §3.1 Rem.- | E III.23 L.21-21 | PDF p.126
#   (« Enfin la relation Eq(X, Y) est transitive, puisque la composée de deux
#    bijections est une bijection (II, p. 19, th. 1) » — formalisé ici.)
def equipotence_transitive(f="F", g="G", x="X", y="Y", z="Z"):
    """⊢ (Eq(X,Y) et Eq(Y,Z)) ⇒ Eq(X,Z).   (TRANSITIVITÉ : G∘F est une bijection X→Z.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
    vF, vG, vX, vY, vZ = var(f), var(g), var(x), var(y), var(z)
    comp = E.composee(vG, vF)
    hF = N.assume(est_bijection_de(vF, vX, vY))
    hG = N.assume(est_bijection_de(vG, vY, vZ))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(hF))
    Fdom = conjonction_elim_droite(conjonction_elim_gauche(hF))
    Finj = conjonction_elim_gauche(conjonction_elim_droite(hF))
    Fimg = conjonction_elim_droite(conjonction_elim_droite(hF))
    Gfunc = conjonction_elim_gauche(conjonction_elim_gauche(hG))
    Gdom = conjonction_elim_droite(conjonction_elim_gauche(hG))
    Ginj = conjonction_elim_gauche(conjonction_elim_droite(hG))
    Gimg = conjonction_elim_droite(conjonction_elim_droite(hG))
    pFf = (E.est_fonctionnel(vF), Ffunc); pFd = (egal(E.dom(vF), vX), Fdom)
    pFi = (E.injective_dans(vF, vX), Finj); pFm = (egal(E.image(vF, vX), vY), Fimg)
    pGf = (E.est_fonctionnel(vG), Gfunc); pGd = (egal(E.dom(vG), vY), Gdom)
    pGi = (E.injective_dans(vG, vY), Ginj); pGm = (egal(E.image(vG, vY), vZ), Gimg)
    c1 = N.modus_ponens(conjonction_intro(Ffunc, Gfunc), composee_fonctionnelle(g, f))  # comp fonctionnel
    c2 = _cut(composee_domaine(g, f, x, y), [pFd, pGd, pFm])               # dom comp=X
    c3 = _cut(composee_injective(g, f, x, y), [pFi, pGi, pFd, pFf, pFm, pGf, pGd])  # inj comp/X
    c4 = _cut(composee_image(g, f, x, y, z), [pFm, pGm])                   # image comp=Z
    bij_comp = conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))  # bij(comp,X,Z)
    eq_xz = N.modus_ponens(bij_comp, N.s5(est_bijection_de(var("F"), vX, vZ), comp, "F"))  # Eq(X,Z)
    stepG = N.loi_deduction(est_bijection_de(vG, vY, vZ), eq_xz)
    elimG = existe_elimination(stepG, "G")                                 # (∃G)bij(G,Y,Z)⇒Eq(X,Z)
    # equipotent code son ∃ sur « F » ; on convertit (∃G)… en (∃F)… = equipotent(Y,Z)
    alphaG = alpha_existe("G", "F", est_bijection_de(var("G"), vY, vZ))    # (∃G)bij(G,Y,Z) ⇔ equipotent(Y,Z)
    elimG = syllogisme(equivalence_arriere(alphaG), elimG)                 # equipotent(Y,Z)⇒Eq(X,Z)
    stepF = N.loi_deduction(est_bijection_de(vF, vX, vY), elimG)
    elimF = existe_elimination(stepF, "F")                                 # Eq(X,Y)⇒(Eq(Y,Z)⇒Eq(X,Z))
    # importation : A⇒(B⇒C) ⟹ (A et B)⇒C
    hab = N.assume(et(equipotent(vX, vY), equipotent(vY, vZ)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimF))
    return N.loi_deduction(et(equipotent(vX, vY), equipotent(vY, vZ)), c)


def reciproque_fonctionnelle(f="F", x="X"):
    """⊢_{F fonctionnel, dom F = X, F injective sur X}  est_fonctionnel(F⁻¹).  (Prop. 7.)"""
    vF, vX = _T(f), _T(x)
    vu, vv, vz, vy = var("u"), var("v"), var("z"), var("y")
    Frec = E.reciproque(vF)
    hfunc = N.assume(E.est_fonctionnel(vF))
    hdom = N.assume(egal(E.dom(vF), vX))
    hinj = N.assume(E.injective_dans(vF, vX))

    def coord(t, t_in_Frec):
        """De ⊢(t,u)∈F⁻¹, renvoie (t∈X, u=f(t)) sous les hyps globales."""
        tu_inF = N.modus_ponens(t_in_Frec, equivalence_avant(couple_reciproque(f, "u", t.nom)))  # (t,u)∈F
        t_dom = N.modus_ponens(tu_inF, N.s5(appartient(E.couple(t, vy), vF), vu, "y"))  # (∃y)(t,y)∈F
        t_inDom = N.modus_ponens(t_dom, equivalence_arriere(_inst_dom(vF, t)))          # t∈dom F
        t_inX = N.modus_ponens(t_inDom, equivalence_avant(N.modus_ponens(
            hdom, N.s6(E.dom(vF), vX, "w", appartient(t, var("w"))))))                  # t∈X
        vc = instancie(N.generalisation("y", valeur_caracterisation(vF, t)), vu)        # (t,u)∈F⇔u=f(t)
        u_ft0 = N.modus_ponens(tu_inF, equivalence_avant(vc))                           # u=f(t)
        u_ft = N.modus_ponens(t_dom, N.loi_deduction(existe("y", appartient(E.couple(t, vy), vF)), u_ft0))
        return t_inX, u_ft, tu_inF

    h = N.assume(et(appartient(E.couple(vu, vv), Frec), appartient(E.couple(vu, vz), Frec)))
    v_inX, u_fv, _ = coord(vv, conjonction_elim_gauche(h))
    z_inX, u_fz, _ = coord(vz, conjonction_elim_droite(h))
    # f(v) = u = f(z)
    fvz = composer_egalites(N.modus_ponens(u_fv, symetrie(vu, E.valeur(vF, vv))), u_fz)  # f(v)=f(z)
    inj = instancie(instancie(hinj, vv), vz)                  # (v∈X et z∈X et f(v)=f(z)) ⇒ v=z
    v_eq_z = N.modus_ponens(conjonction_intro(conjonction_intro(v_inX, z_inX), fvz), inj)
    inner = N.loi_deduction(h.conclusion, v_eq_z)
    return N.generalisation("u", N.generalisation("v", N.generalisation("z", inner)))


def _conjoints_bijection(hbij, vF, vX, vY):
    """Extrait les 4 conjoints de ⊢ est_bijection_de(F,X,Y) (struct ((func,dom),(inj,img)))."""
    g, d = conjonction_elim_gauche(hbij), conjonction_elim_droite(hbij)
    f_func = conjonction_elim_gauche(g)                           # F fonctionnel
    f_dom = conjonction_elim_droite(g)                            # dom F = X
    f_inj = conjonction_elim_gauche(d)                            # injective_dans(F,X)
    f_img = conjonction_elim_droite(d)                            # image(F,X) = Y
    return ((E.est_fonctionnel(vF), f_func), (egal(E.dom(vF), vX), f_dom),
            (E.injective_dans(vF, vX), f_inj), (egal(E.image(vF, vX), vY), f_img))


def reciproque_est_application(f="F", x="X", y="Y"):
    """⊢ est_bijection_de(F,X,Y) ⇒ (est_fonctionnel(F⁻¹) et dom(F⁻¹)=Y).   (Prop. 7, E.II.3.7.)

    F⁻¹ est une application (graphe fonctionnel, défini sur tout Y) dès que F est
    une bijection de X sur Y.  ASSEMBLAGE direct de reciproque_fonctionnelle
    (F⁻¹ fonctionnel, hyps {F func, dom F=X, F inj/X}) et reciproque_domaine
    (dom F⁻¹=Y, hyps {dom F=X, image(F,X)=Y}) : les 4 conjoints de la bijection
    déchargent toutes les hypothèses des deux lemmes."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
    vF, vX, vY = _T(f), _T(x), _T(y)
    Frec = E.reciproque(vF)
    hbij = N.assume(est_bijection_de(vF, vX, vY))
    p_func, p_dom, p_inj, p_img = _conjoints_bijection(hbij, vF, vX, vY)
    c1 = _cut(reciproque_fonctionnelle(f, x), [p_func, p_dom, p_inj])   # F⁻¹ fonctionnel
    c2 = _cut(reciproque_domaine(f, x, y), [p_dom, p_img])             # dom F⁻¹ = Y
    appli = conjonction_intro(c1, c2)
    return N.loi_deduction(est_bijection_de(vF, vX, vY), appli)


def reciproque_est_bijection(f="F", x="X", y="Y"):
    """⊢ est_bijection_de(F,X,Y) ⇒ est_bijection_de(F⁻¹,Y,X).   (Prop. 7 complète, E.II.3.7.)

    F⁻¹ est elle-même une bijection de Y sur X.  C'est le `bij_rec` interne de
    equipotence_symetrique exposé comme théorème : les 4 conjoints de F⁻¹ bijective
    (reciproque_fonctionnelle/domaine/injective + image_reciproque) déchargés par
    les 4 conjoints de est_bijection_de(F,X,Y)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
    vF, vX, vY = _T(f), _T(x), _T(y)
    Frec = E.reciproque(vF)
    hbij = N.assume(est_bijection_de(vF, vX, vY))
    p_func, p_dom, p_inj, p_img = _conjoints_bijection(hbij, vF, vX, vY)
    c1 = _cut(reciproque_fonctionnelle(f, x), [p_func, p_dom, p_inj])    # F⁻¹ fonctionnel
    c2 = _cut(reciproque_domaine(f, x, y), [p_dom, p_img])              # dom F⁻¹ = Y
    c3 = _cut(image_reciproque(f, x, y), [p_dom, p_img])               # image(F⁻¹,Y) = X
    c4 = _cut(reciproque_injective(f, x, y), [p_func, p_dom, p_img])    # injective_dans(F⁻¹,Y)
    bij_rec = conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c4, c3))
    return N.loi_deduction(est_bijection_de(vF, vX, vY), bij_rec)       # ⇒ est_bijection_de(F⁻¹,Y,X)


__all__ = ["reciproque_fonctionnelle", "reciproque_est_application",
           "reciproque_est_bijection"]
