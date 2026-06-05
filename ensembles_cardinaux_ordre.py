"""§III.3.2 — Ordre ≤ des cardinaux : théorèmes certifiés par le noyau.

Définitions dans ensembles_cardinaux.py (lues verbatim §III.3.2) :
  x ≤ y :⇔ (∃F)(F est le graphe d'une injection de x dans y),
  « F injection de X dans Y » := F fonctionnel ∧ dom F = X ∧ F injective sur X
  ∧ image(F,X) ⊂ Y.

Théorèmes prouvés ici (E.III.3.2) :
  (1) equipotence_implique_inf_egal : Eq(X, Y) ⇒ X ≤ Y.   Une bijection est une
      injection : de est_bijection_de(F,X,Y) on a image(F,X)=Y, donc image(F,X)⊂Y
      (réflexivité de ⊂ + Leibniz), d'où est_injection_de(F,X,Y) ; S5 témoin F.
  (2) inf_egal_transitive : (X ≤ Y et Y ≤ Z) ⇒ X ≤ Z.   La composée G∘F de deux
      injections F:X→Y, G:Y→Z est une injection X→Z.  On REUTILISE
      composee_fonctionnelle, composition_valeur (composée des valeurs) et les
      briques image_composee + image_croissante (monotonie de l'image directe).
      Le seul écart avec la transitivité de l'équipotence (ensembles_bijection) est
      que les hypothèses portent sur image(F,X) ⊂ Y (inclusion, pas égalité) : on
      en dérive des variantes inclusion de « la 2ᵉ coordonnée d'un couple de F est
      dans Y » (_second_dans_Y_incl), réutilisées dans le domaine et l'injectivité
      de la composée.

REPORTÉ honnêtement (anti-faux-résultat) :
  • ANTISYMÉTRIE de ≤ : (X ≤ Y et Y ≤ X) ⇒ Card X = Card Y, c'est-à-dire le
    THÉORÈME DE CANTOR–BERNSTEIN–SCHRÖDER.  Sa démonstration (construction de
    l'ensemble des points de F⟨…⟩ par récurrence / plus petit point fixe d'un
    opérateur monotone sur P(X), réunion d'une famille définie par S8) dépasse de
    loin la machinerie abrégée actuelle (pas de réunion d'une famille indexée, pas
    de récurrence ensembliste disponible au niveau abrégé).  Reportée — voir le
    rapport (champ « reportes »).
"""
from __future__ import annotations

from formule import var, egal, et, appartient, existe, inclus, Terme
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege import inclusion_reflexive, syllogisme
from tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               equivalence_symetrie, instancie, inclusion_transitive)
from tactiques_abrege_egalite import symetrie, composer_egalites
from tactiques_abrege_quantif import (alpha_existe, existe_elimination,
                                      existe_commute, et_existe_droite,
                                      congruence_existe)
from ensembles_cardinaux import (est_bijection_de, equipotent, est_injection_de,
                                 inf_egal_card)
from ensembles_fonctions import valeur_dans_graphe
from ensembles_fonctions_composee import composee_fonctionnelle, composition_valeur
from ensembles_composee import couple_composee, image_composee
from ensembles_theoremes import egalite_par_extension
from ensembles_bijection import _cut, _premier_dans_X


def _T(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_dom(g, x):
    """⊢ (x ∈ dom G) ⇔ (∃y)((x,y) ∈ G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, g), x)


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


# ─────────────────────────────────────────────────────────────────────────────
# (1) Eq(X, Y) ⇒ X ≤ Y   (une bijection est une injection)
# ─────────────────────────────────────────────────────────────────────────────
def equipotence_implique_inf_egal(f="F", x="X", y="Y"):
    """⊢ Eq(X, Y) ⇒ (X ≤ Y).   (E.III.3.2 : toute bijection est une injection.)

    De est_bijection_de(F,X,Y) on extrait F fonctionnel, dom F=X, F injective sur X,
    image(F,X)=Y.  image(F,X)=Y et Y⊂Y (réflexivité) donnent image(F,X)⊂Y par
    Leibniz S6 ; on assemble est_injection_de(F,X,Y) puis S5 témoin F donne X≤Y."""
    vF, vX, vY = _T(f), _T(x), _T(y)
    hbij = N.assume(est_bijection_de(vF, vX, vY))
    g, d = conjonction_elim_gauche(hbij), conjonction_elim_droite(hbij)
    f_func = conjonction_elim_gauche(g)                       # F fonctionnel
    f_dom = conjonction_elim_droite(g)                        # dom F = X
    f_inj = conjonction_elim_gauche(d)                        # injective_dans(F,X)
    f_img = conjonction_elim_droite(d)                        # image(F,X) = Y
    # image(F,X) ⊂ Y :  de Y⊂Y et image(F,X)=Y, réécris le sujet Y↦image(F,X).
    yy = inclusion_reflexive(y)                               # Y ⊂ Y
    eqv = N.modus_ponens(f_img,                               # inclus(image,Y) ⇔ inclus(Y,Y)
        N.s6(E.image(vF, vX), vY, "w", inclus(var("w"), vY)))
    img_sub_Y = N.modus_ponens(yy, equivalence_arriere(eqv))  # image(F,X) ⊂ Y
    inj = conjonction_intro(conjonction_intro(conjonction_intro(
        f_func, f_dom), f_inj), img_sub_Y)                   # est_injection_de(F,X,Y)
    le = N.modus_ponens(inj, N.s5(est_injection_de(var("F"), vX, vY), vF, "F"))  # X ≤ Y
    stepF = N.loi_deduction(est_bijection_de(vF, vX, vY), le)
    return existe_elimination(stepF, "F")                    # Eq(X,Y) ⇒ (X ≤ Y)


# ─────────────────────────────────────────────────────────────────────────────
# (2) Transitivité de ≤  — composée de deux injections est une injection
# ─────────────────────────────────────────────────────────────────────────────
def _second_dans_Y_incl(f, x, y, vz, vt):
    """{dom F=X, image(F,X)⊂Y} ⊢ ((vz,vt)∈F) ⇒ (vt∈Y).

    Variante INCLUSION de _second_dans_Y : la 2ᵉ coordonnée d'un couple de F est
    dans image(F,X) (témoin la 1ʳᵉ coordonnée, ∈ X), donc dans Y par image(F,X)⊂Y."""
    vF, vX, vY = _T(f), _T(x), _T(y)
    h = N.assume(appartient(E.couple(vz, vt), vF))
    z_inX = N.modus_ponens(h, _premier_dans_X(f, x, vz, vt))               # vz∈X
    body = et(appartient(var("x"), vX), appartient(E.couple(var("x"), vt), vF))
    t_img = N.modus_ponens(N.modus_ponens(conjonction_intro(z_inX, h), N.s5(body, vz, "x")),
                           equivalence_arriere(_inst_image(vF, vX, vt)))   # vt∈image(F,X)
    himg = N.assume(inclus(E.image(vF, vX), vY))                          # image(F,X)⊂Y
    t_inY = N.modus_ponens(t_img, instancie(himg, vt))                    # vt∈Y
    return N.loi_deduction(appartient(E.couple(vz, vt), vF), t_inY)


def composee_domaine_incl(g="G", f="F", x="X", y="Y"):
    """⊢_{dom F=X, image(F,X)⊂Y, dom G=Y}  dom(G∘F) = X.

    Variante INCLUSION de composee_domaine (ensembles_bijection) : seule l'étape
    « m∈Y » change (via _second_dans_Y_incl) ; le reste est identique."""
    vG, vF, vX, vY = var(g), var(f), var(x), var(y)
    vz, vm = var("z"), var("m")
    comp = E.composee(vG, vF)
    zmF = appartient(E.couple(vz, vm), vF)
    dom_ax = _inst_dom(comp, vz)
    ren1 = alpha_existe("y", "v", appartient(E.couple(vz, var("y")), comp))
    cc = couple_composee(g, f, "z", "v")
    cc_m = equivalence_transitivite(cc, alpha_existe("y", "m",
        et(appartient(E.couple(vz, var("y")), vF), appartient(E.couple(var("y"), var("v")), vG))))
    step1 = congruence_existe(cc_m, "v")
    P = et(zmF, appartient(E.couple(vm, var("v")), vG))
    comm = existe_commute("v", "m", P)
    ee = et_existe_droite(zmF, "v", appartient(E.couple(vm, var("v")), vG))
    ee_cong = congruence_existe(equivalence_symetrie(ee), "m")
    exvG = existe("v", appartient(E.couple(vm, var("v")), vG))
    r_fwd = N.loi_deduction(et(zmF, exvG), conjonction_elim_gauche(N.assume(et(zmF, exvG))))
    hm = N.assume(zmF)
    m_inY = N.modus_ponens(hm, _second_dans_Y_incl(f, x, y, vz, vm))      # m∈Y  (INCLUSION)
    hdomG = N.assume(egal(E.dom(vG), vY))
    m_dom = N.modus_ponens(m_inY, equivalence_avant(N.modus_ponens(
        N.modus_ponens(hdomG, symetrie(E.dom(vG), vY)),
        N.s6(vY, E.dom(vG), "w", appartient(vm, var("w"))))))             # m∈dom G
    dm_v = equivalence_transitivite(_inst_dom(vG, vm),
        alpha_existe("y", "v", appartient(E.couple(vm, var("y")), vG)))
    ex_v = N.modus_ponens(m_dom, equivalence_avant(dm_v))
    r_bwd = N.loi_deduction(zmF, conjonction_intro(hm, ex_v))
    redund = congruence_existe(conjonction_intro(r_fwd, r_bwd), "m")
    char1 = equivalence_transitivite(dom_ax, equivalence_transitivite(ren1,
        equivalence_transitivite(step1, equivalence_transitivite(comm,
        equivalence_transitivite(ee_cong, redund)))))
    char_dom = N.generalisation("z", char1)
    hdomF = N.assume(egal(E.dom(vF), vX))
    zX = N.modus_ponens(N.modus_ponens(hdomF, symetrie(E.dom(vF), vX)),
                        N.s6(vX, E.dom(vF), "w", appartient(vz, var("w"))))
    char_X1 = equivalence_transitivite(zX, equivalence_transitivite(_inst_dom(vF, vz),
        alpha_existe("y", "m", appartient(E.couple(vz, var("y")), vF))))
    char_X = N.generalisation("z", char_X1)
    return egalite_par_extension(char_dom, char_X, E.dom(comp), vX)


_GG = [None]


def _inj_setup_incl(f, vF, vX, vY, uu, uu_inX, hdomF, hdomG):
    """Sous {dom F=X, image(F,X)⊂Y, dom G=Y} et uu∈X : renvoie
    ((∃y)(uu,y)∈F, F(uu)∈Y, (∃y)(F(uu),y)∈G)."""
    ex = N.modus_ponens(N.modus_ponens(uu_inX, equivalence_arriere(N.modus_ponens(
        hdomF, N.s6(E.dom(vF), vX, "w", appartient(uu, var("w")))))),
        equivalence_avant(_inst_dom(vF, uu)))                # (∃y)(uu,y)∈F  [via uu∈dom F]
    in_F = N.modus_ponens(ex, N.loi_deduction(
        existe("y", appartient(E.couple(uu, var("y")), vF)), valeur_dans_graphe(vF, uu)))
    fuu = E.valeur(vF, uu)
    fuu_inY = N.modus_ponens(in_F, _second_dans_Y_incl(f, vX.nom, vY.nom, uu, fuu))   # F(uu)∈Y
    fuu_domG = N.modus_ponens(N.modus_ponens(fuu_inY, equivalence_arriere(N.modus_ponens(
        hdomG, N.s6(E.dom(_GG[0]), vY, "w", appartient(fuu, var("w")))))),
        equivalence_avant(_inst_dom(_GG[0], fuu)))           # (∃y)(F(uu),y)∈G
    return ex, fuu_inY, fuu_domG


def _eqsym(thm):
    a, b = thm.conclusion.termes
    return N.modus_ponens(thm, symetrie(a, b))


def composee_injective_incl(g="G", f="F", x="X", y="Y"):
    """⊢_{F,G fonctionnels, dom F=X, image(F,X)⊂Y, dom G=Y, F inj/X, G inj/Y}
       injective_dans(G∘F, X).

    Variante INCLUSION de composee_injective : F(uu)∈Y via _second_dans_Y_incl."""
    vG, vF, vX, vY = var(g), var(f), var(x), var(y)
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
    gof_eq = conjonction_elim_droite(h)

    def compo_val(uu, uu_inX):
        ex, fuu_inY, fuu_domG = _inj_setup_incl(f, vF, vX, vY, uu, uu_inX, hdomF, hdomG)
        cv = _cut(composition_valeur(g, f, uu.nom),
                  [(existe("y", appartient(E.couple(uu, var("y")), vF)), ex),
                   (existe("y", appartient(E.couple(E.valeur(vF, uu), var("y")), vG)), fuu_domG)])
        return cv, fuu_inY

    cv_u, fu_inY = compo_val(vu, u_inX)
    cv_up, fup_inY = compo_val(vup, up_inX)
    fu, fup = E.valeur(vF, vu), E.valeur(vF, vup)
    gfu_eq = composer_egalites(composer_egalites(_eqsym(cv_u), gof_eq), cv_up)
    ginj = instancie(instancie(hGinj, fu), fup)
    fu_eq = N.modus_ponens(conjonction_intro(conjonction_intro(fu_inY, fup_inY), gfu_eq), ginj)
    finj = instancie(instancie(hFinj, vu), vup)
    u_eq = N.modus_ponens(conjonction_intro(conjonction_intro(u_inX, up_inX), fu_eq), finj)
    inner = N.loi_deduction(hyp, u_eq)
    return N.generalisation("u", N.generalisation("up", inner))


def composee_image_incl(g="G", f="F", x="X", y="Y", z="Z"):
    """⊢_{image(F,X)⊂Y, image(G,Y)⊂Z}  image(G∘F, X) ⊂ Z.

    image(G∘F,X) = G⟨F⟨X⟩⟩ (image_composee).  F⟨X⟩⊂Y donne G⟨F⟨X⟩⟩⊂G⟨Y⟩ (monotonie
    de l'image directe, image_croissante appliquée aux TERMES F⟨X⟩,Y via
    instance-terme), et G⟨Y⟩⊂Z ; transitivité de ⊂ conclut."""
    from ensembles_correspondances import image_croissante
    vG, vF, vX, vY, vZ = var(g), var(f), var(x), var(y), var(z)
    comp = E.composee(vG, vF)
    fimg = E.image(vF, vX)                                   # F⟨X⟩
    ic = image_composee(g, f, x)                             # image(G∘F,X) = G⟨F⟨X⟩⟩
    # monotonie de l'image directe au TERME F⟨X⟩ :  (F⟨X⟩⊂Y) ⇒ (G⟨F⟨X⟩⟩ ⊂ G⟨Y⟩)
    mono_all = N.generalisation(x, N.generalisation(y, image_croissante(g, x, y)))
    mono = instancie(instancie(mono_all, fimg), vY)         # (F⟨X⟩⊂Y)⇒(G⟨F⟨X⟩⟩⊂G⟨Y⟩)
    hFsub = N.assume(inclus(fimg, vY))                      # F⟨X⟩⊂Y
    gfx_sub_gy = N.modus_ponens(hFsub, mono)               # G⟨F⟨X⟩⟩ ⊂ G⟨Y⟩
    hGsub = N.assume(inclus(E.image(vG, vY), vZ))          # G⟨Y⟩⊂Z
    # G⟨F⟨X⟩⟩ ⊂ Z  par transitivité de ⊂ appliquée aux TERMES G⟨F⟨X⟩⟩, G⟨Y⟩, Z
    trans_all = N.generalisation("a", N.generalisation("b", N.generalisation("c",
        inclusion_transitive("a", "b", "c"))))
    trans = instancie(instancie(instancie(trans_all, E.image(vG, fimg)), E.image(vG, vY)), vZ)
    gfx_sub_Z = N.modus_ponens(conjonction_intro(gfx_sub_gy, hGsub), trans)   # G⟨F⟨X⟩⟩⊂Z
    # réécris  G⟨F⟨X⟩⟩⊂Z  en  image(G∘F,X)⊂Z  via  G⟨F⟨X⟩⟩ = image(G∘F,X)
    img_comp = E.image(comp, vX)
    rw = N.modus_ponens(_eqsym(ic),                        # inclus(G⟨F⟨X⟩⟩,Z) ⇔ inclus(image(G∘F,X),Z)
        N.s6(E.image(vG, fimg), img_comp, "w", inclus(var("w"), vZ)))
    return N.modus_ponens(gfx_sub_Z, equivalence_avant(rw))  # image(G∘F,X) ⊂ Z


def inf_egal_transitive(f="F", g="G", x="X", y="Y", z="Z"):
    """⊢ (X ≤ Y et Y ≤ Z) ⇒ (X ≤ Z).   (TRANSITIVITÉ de ≤ : G∘F injection X→Z.)"""
    vF, vG, vX, vY, vZ = var(f), var(g), var(x), var(y), var(z)
    comp = E.composee(vG, vF)
    hF = N.assume(est_injection_de(vF, vX, vY))
    hG = N.assume(est_injection_de(vG, vY, vZ))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hF)))
    Fdom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hF)))
    Finj = conjonction_elim_droite(conjonction_elim_gauche(hF))
    Fsub = conjonction_elim_droite(hF)                      # image(F,X)⊂Y
    Gfunc = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hG)))
    Gdom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hG)))
    Ginj = conjonction_elim_droite(conjonction_elim_gauche(hG))
    Gsub = conjonction_elim_droite(hG)                      # image(G,Y)⊂Z
    pFf = (E.est_fonctionnel(vF), Ffunc); pFd = (egal(E.dom(vF), vX), Fdom)
    pFi = (E.injective_dans(vF, vX), Finj); pFs = (inclus(E.image(vF, vX), vY), Fsub)
    pGf = (E.est_fonctionnel(vG), Gfunc); pGd = (egal(E.dom(vG), vY), Gdom)
    pGi = (E.injective_dans(vG, vY), Ginj); pGs = (inclus(E.image(vG, vY), vZ), Gsub)
    c1 = N.modus_ponens(conjonction_intro(Ffunc, Gfunc), composee_fonctionnelle(g, f))   # comp fonctionnel
    c2 = _cut(composee_domaine_incl(g, f, x, y), [pFd, pFs, pGd])                         # dom comp=X
    c3 = _cut(composee_injective_incl(g, f, x, y), [pFi, pGi, pFd, pFf, pFs, pGf, pGd])   # inj comp/X
    c4 = _cut(composee_image_incl(g, f, x, y, z), [pFs, pGs])                             # image comp⊂Z
    inj_comp = conjonction_intro(conjonction_intro(conjonction_intro(c1, c2), c3), c4)   # est_injection_de(comp,X,Z)
    le_xz = N.modus_ponens(inj_comp, N.s5(est_injection_de(var("F"), vX, vZ), comp, "F"))  # X≤Z
    stepG = N.loi_deduction(est_injection_de(vG, vY, vZ), le_xz)
    elimG = existe_elimination(stepG, "G")                  # (∃G)inj(G,Y,Z)⇒X≤Z
    alphaG = alpha_existe("G", "F", est_injection_de(var("G"), vY, vZ))  # (∃G)inj⇔(Y≤Z)
    elimG = syllogisme(equivalence_arriere(alphaG), elimG)  # (Y≤Z)⇒X≤Z
    stepF = N.loi_deduction(est_injection_de(vF, vX, vY), elimG)
    elimF = existe_elimination(stepF, "F")                  # (X≤Y)⇒((Y≤Z)⇒X≤Z)
    hab = N.assume(et(inf_egal_card(vX, vY), inf_egal_card(vY, vZ)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimF))
    return N.loi_deduction(et(inf_egal_card(vX, vY), inf_egal_card(vY, vZ)), c)


__all__ = ["equipotence_implique_inf_egal", "inf_egal_transitive"]
