"""§III.3.2 / §III.3.3 — INFRA RECOLLEMENT (valeur / injectivité / image de G∪H).

Suite GÉNÉRALE de ensembles_restriction_somme (R25, qui fournit déjà
reunion_graphes_fonctionnelle, dom_reunion_graphes, membre_reunion_graphes,
antecedent_dans_domaine).  Le RECOLLEMENT de deux graphes fonctionnels G, H à
domaines DISJOINTS est le graphe fonctionnel G∪H ; ce module en décrit la VALEUR,
l'INJECTIVITÉ et l'IMAGE.  Lemmes réutilisables (Cantor–Bernstein ET Prop 9
a^(b+c)=a^b·a^c).

THÉORÈMES CERTIFIÉS (chacun testé en isolé) :
  • valeur_reunion_gauche  {G,H fonct, dom disjoints, u∈dom G}
        ⊢ valeur(G∪H,u) = valeur(G,u)
  • valeur_reunion_droite  {G,H fonct, dom disjoints, u∈dom H}
        ⊢ valeur(G∪H,u) = valeur(H,u)
  • image_reunion_graphes
        ⊢ image(G∪H, domG∪domH) = image(G,domG) ∪ image(H,domH)
  • reunion_graphes_injective  {G,H fonct, dom disjoints, G inj/domG, H inj/domH,
        image(G,domG)∩image(H,domH)=∅}  ⊢ injective_dans(G∪H, domG∪domH)

Tout sort du noyau (PROUVE == certifie) ; AUCUN axiome nouveau (réutilise
AXIOME_REUNION/DOM/IMAGE/INTER/VIDE + valeur_caracterisation/valeur_dans_graphe).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non,
                                       appartient, existe, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import (
    valeur_caracterisation, valeur_dans_graphe)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    membre_reunion_graphes, reunion_graphes_fonctionnelle)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── axiomes instanciés (helpers) ──────────────────────────────────────────────
def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, f), x)


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, g), xset), y)


def _inst_reunion(a, b, z):
    """⊢ (z ∈ A∪B) ⇔ (z∈A ou z∈B)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, a), b), z)


def _inst_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _disjonction(g, h, w="w"):
    """La formule de disjonction des domaines : (∀w)¬(w∈domG et w∈domH).

    (forme exactement attendue par reunion_graphes_fonctionnelle, dont le liant
    par défaut est « u » ; on la pose ici en liant paramétrable w.)"""
    vg, vh, vw = _t(g), _t(h), var(w)
    return pourtout(w, non(et(appartient(vw, E.dom(vg)),
                              appartient(vw, E.dom(vh)))))


def _reunion_fonctionnelle(g, h):
    """{func G, func H, (∀u)¬(u∈domG et u∈domH)} ⊢ est_fonctionnel(G∪H).

    reunion_graphes_fonctionnelle accepte directement des TERMES (ses liants
    internes u,v,z sont fixes) : appel direct sur les arguments-termes."""
    return reunion_graphes_fonctionnelle(_t(g), _t(h))


# ── (a) VALEUR du recollement : G∪H coïncide avec G (resp. H) sur son domaine ──
def _valeur_reunion(g, h, u, cote):
    """Cœur commun de valeur_reunion_gauche / _droite.

    cote='G' : {func G, func H, dom disjoints, u∈dom G} ⊢ valeur(G∪H,u)=valeur(G,u)
    cote='H' : {func G, func H, dom disjoints, u∈dom H} ⊢ valeur(G∪H,u)=valeur(H,u)
    """
    vg, vh, vu = _t(g), _t(h), _t(u)
    GuH = E.reunion(vg, vh)
    src = vg if cote == "G" else vh                       # graphe « propre » de u
    src_dom = E.dom(src)
    fu = E.valeur(src, vu)                                # valeur(G,u) ou valeur(H,u)

    hu = N.assume(appartient(vu, src_dom))               # u∈dom(source)
    funcGuH = _reunion_fonctionnelle(vg, vh)             # {func G,H, disj} ⊢ func(G∪H)
    # (u, fu) ∈ source  (valeur_dans_graphe sous u∈dom source)
    ex_src = N.modus_ponens(hu, equivalence_avant(_inst_dom(src, vu)))   # (∃y)((u,y)∈source)
    u_fu_src = N.modus_ponens(ex_src, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), src)),
        valeur_dans_graphe(src, vu)))                    # (u, fu) ∈ source
    # (u, fu) ∈ G∪H  (membre_reunion_graphes : injection gauche/droite)
    car = membre_reunion_graphes(vg, vh, E.couple(vu, fu))   # (u,fu)∈G∪H ⇔ (…∈G ou …∈H)
    Gpart = appartient(E.couple(vu, fu), vg)
    Hpart = appartient(E.couple(vu, fu), vh)
    if cote == "G":
        disj_in = N.modus_ponens(u_fu_src, N.s2(Gpart, Hpart))          # (u,fu)∈G ou (u,fu)∈H
    else:
        disj_in = N.modus_ponens(u_fu_src, syllogisme(N.s2(Hpart, Gpart),
                                                      N.s3(Hpart, Gpart)))
    u_fu_GuH = N.modus_ponens(disj_in, equivalence_arriere(car))        # (u, fu) ∈ G∪H

    # 4) (∃y)((u,y)∈G∪H)
    ex_GuH = N.modus_ponens(u_fu_GuH, N.s5(appartient(E.couple(vu, var("y")), GuH), fu, "y"))

    # 5) valeur_caracterisation(G∪H, u) : ((u,y)∈G∪H) ⇔ (y = valeur(G∪H,u))
    #    instanciée à y:=fu  →  ((u,fu)∈G∪H) ⇔ (fu = valeur(G∪H,u))
    vc = valeur_caracterisation(GuH, vu)                 # hyps : func(G∪H), (∃y)((u,y)∈G∪H)
    vc_fu = instancie(N.generalisation("y", vc), fu)     # ((u,fu)∈G∪H) ⇔ (fu = valeur(G∪H,u))
    fu_eq = N.modus_ponens(u_fu_GuH, equivalence_avant(vc_fu))          # fu = valeur(G∪H,u)
    # → valeur(G∪H,u) = fu  par symétrie
    res = N.modus_ponens(fu_eq, symetrie(fu, E.valeur(GuH, vu)))        # valeur(G∪H,u) = fu

    # décharge des hypothèses func(G∪H) et (∃y)((u,y)∈G∪H) introduites par
    # valeur_caracterisation : elles sont PROUVÉES (funcGuH, ex_GuH).
    res = N.modus_ponens(funcGuH, N.loi_deduction(E.est_fonctionnel(GuH), res))
    res = N.modus_ponens(ex_GuH, N.loi_deduction(
        existe("y", appartient(E.couple(vu, var("y")), GuH)), res))
    return res


def valeur_reunion_gauche(g="G", h="H", u="u"):
    """{func G, func H, (∀u)¬(u∈domG et u∈domH), u∈dom G}
        ⊢ valeur(G∪H, u) = valeur(G, u).

    Le recollement coïncide avec G sur dom G : G∪H est fonctionnel (domaines
    disjoints), (u,G(u))∈G⊂G∪H, donc par unicité fonctionnelle valeur(G∪H,u)=G(u)."""
    return _valeur_reunion(g, h, u, "G")


def valeur_reunion_droite(g="G", h="H", u="u"):
    """{func G, func H, (∀u)¬(u∈domG et u∈domH), u∈dom H}
        ⊢ valeur(G∪H, u) = valeur(H, u).   (symétrique de valeur_reunion_gauche.)"""
    return _valeur_reunion(g, h, u, "H")


# ── (c) IMAGE du recollement : image(G∪H, domG∪domH)=image(G,domG)∪image(H,domH) ─
def image_reunion_graphes(g="G", h="H"):
    """⊢ image(G∪H, domG∪domH) = image(G, domG) ∪ image(H, domH).

    Double inclusion (membre à membre) via AXIOME_IMAGE + membre_reunion_graphes
    (domaine ET graphe).  Inconditionnel (pur calcul de réunion) : un (x,v)∈G a
    x∈domG (antecedent_dans_domaine), donc les termes croisés se résorbent."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import antecedent_dans_domaine
    vg, vh = _t(g), _t(h)
    vv, vx = var("z"), var("x")     # élément « z » (= liant de inclus/A1), antécédent « x »
    GuH = E.reunion(vg, vh)
    domG, domH = E.dom(vg), E.dom(vh)
    domR = E.reunion(domG, domH)
    imgG, imgH = E.image(vg, domG), E.image(vh, domH)
    imgR = E.reunion(imgG, imgH)

    carL = _inst_image(GuH, domR, vv)       # v∈(G∪H)⟨domR⟩ ⇔ (∃x)(x∈domR et (x,v)∈G∪H)
    carIG = _inst_image(vg, domG, vv)       # v∈G⟨domG⟩ ⇔ (∃x)(x∈domG et (x,v)∈G)
    carIH = _inst_image(vh, domH, vv)       # v∈H⟨domH⟩ ⇔ (∃x)(x∈domH et (x,v)∈H)
    carImgR = _inst_reunion(imgG, imgH, vv) # v∈imgR ⇔ (v∈imgG ou v∈imgH)

    xv_G = appartient(E.couple(vx, vv), vg)
    xv_H = appartient(E.couple(vx, vv), vh)
    x_domG = appartient(vx, domG)
    x_domH = appartient(vx, domH)
    car_couple = membre_reunion_graphes(vg, vh, E.couple(vx, vv))   # (x,v)∈G∪H ⇔ (…∈G ou …∈H)
    car_dom = membre_reunion_graphes(domG, domH, vx)               # x∈domR ⇔ (x∈domG ou x∈domH)
    adG = antecedent_dans_domaine(vx, vv, vg)                       # (x,v)∈G ⇒ x∈domG
    adH = antecedent_dans_domaine(vx, vv, vh)                       # (x,v)∈H ⇒ x∈domH

    # ── ⇒ : v∈(G∪H)⟨domR⟩ ⇒ v∈imgR ──────────────────────────────────────────────
    hL = N.assume(appartient(vv, E.image(GuH, domR)))
    exL = N.modus_ponens(hL, equivalence_avant(carL))             # (∃x)(x∈domR et (x,v)∈G∪H)
    body_L = et(appartient(vx, domR), appartient(E.couple(vx, vv), GuH))
    hbL = N.assume(body_L)
    inGuH = N.modus_ponens(conjonction_elim_droite(hbL), equivalence_avant(car_couple))  # (x,v)∈G ou (x,v)∈H
    # (x,v)∈G ⇒ v∈imgG (x∈domG via antecedent) ⇒ v∈imgR
    hxvG = N.assume(xv_G)
    v_imgG = N.modus_ponens(N.modus_ponens(conjonction_intro(
        N.modus_ponens(hxvG, adG), hxvG), N.s5(et(x_domG, xv_G), vx, "x")),
        equivalence_arriere(carIG))                              # v∈imgG
    v_imgR_G = N.modus_ponens(N.modus_ponens(v_imgG, N.s2(appartient(vv, imgG),
                                                         appartient(vv, imgH))),
                              equivalence_arriere(carImgR))      # v∈imgR
    br_G = N.loi_deduction(xv_G, v_imgR_G)
    # (x,v)∈H ⇒ v∈imgH ⇒ v∈imgR
    hxvH = N.assume(xv_H)
    v_imgH = N.modus_ponens(N.modus_ponens(conjonction_intro(
        N.modus_ponens(hxvH, adH), hxvH), N.s5(et(x_domH, xv_H), vx, "x")),
        equivalence_arriere(carIH))                              # v∈imgH
    v_imgR_H = N.modus_ponens(N.modus_ponens(N.modus_ponens(v_imgH,
        N.s2(appartient(vv, imgH), appartient(vv, imgG))),
        N.s3(appartient(vv, imgH), appartient(vv, imgG))),
        equivalence_arriere(carImgR))                            # v∈imgR
    br_H = N.loi_deduction(xv_H, v_imgR_H)
    v_imgR_body = cas(inGuH, br_G, br_H)                          # v∈imgR (sous body_L)
    impL = existe_elimination(N.loi_deduction(body_L, v_imgR_body), "x")  # (∃x)body_L ⇒ v∈imgR
    fwd = N.loi_deduction(appartient(vv, E.image(GuH, domR)),
                          N.modus_ponens(exL, impL))             # v∈(G∪H)⟨domR⟩ ⇒ v∈imgR
    incl_LR = N.generalisation("z", fwd)

    # ── ⇐ : v∈imgR ⇒ v∈(G∪H)⟨domR⟩ ──────────────────────────────────────────────
    hR = N.assume(appartient(vv, imgR))
    disjImg = N.modus_ponens(hR, equivalence_avant(carImgR))      # v∈imgG ou v∈imgH
    # v∈imgG ⇒ v∈(G∪H)⟨domR⟩
    hImgG = N.assume(appartient(vv, imgG))
    exG = N.modus_ponens(hImgG, equivalence_avant(carIG))         # (∃x)(x∈domG et (x,v)∈G)
    bodyG = et(x_domG, xv_G)
    hbG = N.assume(bodyG)
    xdomR_g = N.modus_ponens(N.modus_ponens(conjonction_elim_gauche(hbG),
        N.s2(x_domG, x_domH)), equivalence_arriere(car_dom))     # x∈domR
    xvGuH_g = N.modus_ponens(N.modus_ponens(conjonction_elim_droite(hbG),
        N.s2(xv_G, xv_H)), equivalence_arriere(car_couple))      # (x,v)∈G∪H
    body_inR_g = conjonction_intro(xdomR_g, xvGuH_g)             # x∈domR et (x,v)∈G∪H
    exR_g = N.modus_ponens(body_inR_g, N.s5(body_L, vx, "x"))    # (∃x)body_L
    vinL_g = N.modus_ponens(exR_g, equivalence_arriere(carL))    # v∈(G∪H)⟨domR⟩
    impG = existe_elimination(N.loi_deduction(bodyG, vinL_g), "x")
    brR_G = N.loi_deduction(appartient(vv, imgG), N.modus_ponens(exG, impG))
    # v∈imgH ⇒ v∈(G∪H)⟨domR⟩
    hImgH = N.assume(appartient(vv, imgH))
    exH = N.modus_ponens(hImgH, equivalence_avant(carIH))         # (∃x)(x∈domH et (x,v)∈H)
    bodyH = et(x_domH, xv_H)
    hbH = N.assume(bodyH)
    xdomR_h = N.modus_ponens(N.modus_ponens(N.modus_ponens(conjonction_elim_gauche(hbH),
        N.s2(x_domH, x_domG)), N.s3(x_domH, x_domG)),
        equivalence_arriere(car_dom))                            # x∈domR
    xvGuH_h = N.modus_ponens(N.modus_ponens(N.modus_ponens(conjonction_elim_droite(hbH),
        N.s2(xv_H, xv_G)), N.s3(xv_H, xv_G)),
        equivalence_arriere(car_couple))                         # (x,v)∈G∪H
    body_inR_h = conjonction_intro(xdomR_h, xvGuH_h)
    exR_h = N.modus_ponens(body_inR_h, N.s5(body_L, vx, "x"))
    vinL_h = N.modus_ponens(exR_h, equivalence_arriere(carL))    # v∈(G∪H)⟨domR⟩
    impH = existe_elimination(N.loi_deduction(bodyH, vinL_h), "x")
    brR_H = N.loi_deduction(appartient(vv, imgH), N.modus_ponens(exH, impH))
    vinL = cas(disjImg, brR_G, brR_H)                            # v∈(G∪H)⟨domR⟩
    bwd = N.loi_deduction(appartient(vv, imgR), vinL)
    incl_RL = N.generalisation("z", bwd)

    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1),
                              E.image(GuH, domR)), imgR)
    return N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)   # image(G∪H,domR)=imgR


# ── (b) INJECTIVITÉ du recollement (images disjointes) ────────────────────────
def reunion_graphes_injective(g="G", h="H"):
    """{func G, func H, (∀u)¬(u∈domG et u∈domH), injective_dans(G,domG),
        injective_dans(H,domH), image(G,domG)∩image(H,domH)=∅}
        ⊢ injective_dans(G∪H, domG∪domH).

    Pour u,u'∈domG∪domH avec (G∪H)(u)=(G∪H)(u'), cas sur domG/domH : même côté ⇒
    (G∪H) coïncide avec G (ou H) + injectivité du côté ⇒ u=u' ; côtés différents ⇒
    valeur commune dans image(G,domG)∩image(H,domH)=∅ ⇒ ex falso."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import antecedent_dans_domaine
    vg, vh = _t(g), _t(h)
    vu, vup = var("u"), var("up")
    GuH = E.reunion(vg, vh)
    domG, domH = E.dom(vg), E.dom(vh)
    domR = E.reunion(domG, domH)
    imgG, imgH = E.image(vg, domG), E.image(vh, domH)

    # hyps globales utilisées directement (func/func/disj entrent via valeur_reunion_*)
    hinjG = N.assume(E.injective_dans(vg, domG))
    hinjH = N.assume(E.injective_dans(vh, domH))
    hinterVide = N.assume(egal(E.intersection(imgG, imgH), E.VIDE))

    # caractérisations réunion des domaines pour u et u'
    car_u = membre_reunion_graphes(domG, domH, vu)     # u∈domR ⇔ (u∈domG ou u∈domH)
    car_up = membre_reunion_graphes(domG, domH, vup)   # u'∈domR ⇔ (u'∈domG ou u'∈domH)

    # hypothèse principale de injective_dans(G∪H, domR)
    GuHu, GuHup = E.valeur(GuH, vu), E.valeur(GuH, vup)
    hyp = et(et(appartient(vu, domR), appartient(vup, domR)), egal(GuHu, GuHup))
    h = N.assume(hyp)
    u_inR = conjonction_elim_gauche(conjonction_elim_gauche(h))
    up_inR = conjonction_elim_droite(conjonction_elim_gauche(h))
    val_eq = conjonction_elim_droite(h)                # (G∪H)(u)=(G∪H)(u')
    cible = egal(vu, vup)

    u_disj = N.modus_ponens(u_inR, equivalence_avant(car_u))    # u∈domG ou u∈domH
    up_disj = N.modus_ponens(up_inR, equivalence_avant(car_up)) # u'∈domG ou u'∈domH

    # valeur de u via G (sous u∈domG) : ⊢ (G∪H)(u)∈imgG (resp. via H : ∈imgH)
    def gu_eq_imgG(t, t_inDomG):
        """sous t∈domG : ⊢ (G∪H)(t) ∈ imgG.  (=(G∪H)(t)=G(t) et G(t)∈image(G,domG).)"""
        # (G∪H)(t)=G(t)
        gv = valeur_reunion_gauche(vg, vh, t)
        gv = N.modus_ponens(t_inDomG, N.loi_deduction(appartient(t, domG), gv))  # décharge t∈domG
        # G(t)∈imgG : (t,G(t))∈G (valeur_dans_graphe sous t∈domG) puis AXIOME_IMAGE
        ex_t = N.modus_ponens(t_inDomG, equivalence_avant(_inst_dom(vg, t)))     # (∃y)(t,y)∈G
        t_gt = N.modus_ponens(ex_t, N.loi_deduction(
            existe("y", appartient(E.couple(t, var("y")), vg)), valeur_dans_graphe(vg, t)))  # (t,G(t))∈G
        gt = E.valeur(vg, t)
        body = et(appartient(t, domG), appartient(E.couple(t, gt), vg))
        gt_img = N.modus_ponens(N.modus_ponens(conjonction_intro(t_inDomG, t_gt),
            N.s5(et(appartient(var("x"), domG), appartient(E.couple(var("x"), gt), vg)), t, "x")),
            equivalence_arriere(_inst_image(vg, domG, gt)))    # G(t)∈imgG
        # (G∪H)(t)=G(t) et G(t)∈imgG → (G∪H)(t)∈imgG  (sens arrière de l'équiv. s6)
        return N.modus_ponens(gt_img, equivalence_arriere(N.modus_ponens(
            gv, N.s6(E.valeur(GuH, t), gt, "w", appartient(var("w"), imgG)))))

    def hu_eq_imgH(t, t_inDomH):
        """sous t∈domH : ⊢ (G∪H)(t) ∈ imgH."""
        hv = valeur_reunion_droite(vg, vh, t)
        hv = N.modus_ponens(t_inDomH, N.loi_deduction(appartient(t, domH), hv))
        ex_t = N.modus_ponens(t_inDomH, equivalence_avant(_inst_dom(vh, t)))
        t_ht = N.modus_ponens(ex_t, N.loi_deduction(
            existe("y", appartient(E.couple(t, var("y")), vh)), valeur_dans_graphe(vh, t)))
        ht = E.valeur(vh, t)
        ht_img = N.modus_ponens(N.modus_ponens(conjonction_intro(t_inDomH, t_ht),
            N.s5(et(appartient(var("x"), domH), appartient(E.couple(var("x"), ht), vh)), t, "x")),
            equivalence_arriere(_inst_image(vh, domH, ht)))    # H(t)∈imgH
        return N.modus_ponens(ht_img, equivalence_arriere(N.modus_ponens(
            hv, N.s6(E.valeur(GuH, t), ht, "w", appartient(var("w"), imgH)))))

    # ── les 4 branches du double cas ────────────────────────────────────────────
    # br_GG : u∈domG ⇒ (u'∈domG ⇒ u=u') et (u'∈domH ⇒ ⊥→u=u')
    def branche(side_u):
        """side_u ∈ {'G','H'} : retourne (u∈dom side_u) ⇒ ((u'∈domG ou u'∈domH) ⇒ u=u')."""
        # même côté
        def meme(side_up):
            h_u = N.assume(appartient(vu, domG if side_u == "G" else domH))
            h_up = N.assume(appartient(vup, domG if side_up == "G" else domH))
            if side_u == "G":
                vu_val = valeur_reunion_gauche(vg, vh, vu)
                vu_val = N.modus_ponens(h_u, N.loi_deduction(appartient(vu, domG), vu_val))  # (G∪H)(u)=G(u)
            else:
                vu_val = valeur_reunion_droite(vg, vh, vu)
                vu_val = N.modus_ponens(h_u, N.loi_deduction(appartient(vu, domH), vu_val))  # (G∪H)(u)=H(u)
            if side_up == "G":
                vup_val = valeur_reunion_gauche(vg, vh, vup)
                vup_val = N.modus_ponens(h_up, N.loi_deduction(appartient(vup, domG), vup_val))
            else:
                vup_val = valeur_reunion_droite(vg, vh, vup)
                vup_val = N.modus_ponens(h_up, N.loi_deduction(appartient(vup, domH), vup_val))
            srcG = vg if side_u == "G" else vh
            # side(u)=(G∪H)(u)=(G∪H)(u')=side(u')  ; même côté ⇒ injectivité
            chain = composer_egalites(composer_egalites(
                N.modus_ponens(vu_val, symetrie(E.valeur(GuH, vu), E.valeur(srcG, vu))),
                val_eq), vup_val)                                          # side(u)=side(u')
            hinj = hinjG if side_u == "G" else hinjH
            inj = instancie(instancie(hinj, vu), vup)   # (u∈sd et u'∈sd et side(u)=side(u'))⇒u=u'
            ueq = N.modus_ponens(conjonction_intro(conjonction_intro(h_u, h_up), chain), inj)
            return N.loi_deduction(appartient(vup, domG if side_up == "G" else domH), ueq)

        def croise(side_up):
            # u∈side_u, u'∈side_up, side_u≠side_up : la valeur commune (G∪H)(u) est
            # dans imgG ET imgH (via val_eq) → dans imgG∩imgH=∅ → ex falso.
            h_u = N.assume(appartient(vu, domG if side_u == "G" else domH))
            h_up = N.assume(appartient(vup, domG if side_up == "G" else domH))
            second_img = imgH if side_u == "G" else imgG     # image de l'autre côté
            if side_u == "G":
                u_img = gu_eq_imgG(vu, h_u)               # (G∪H)(u)∈imgG
                up_img = hu_eq_imgH(vup, h_up)            # (G∪H)(u')∈imgH
            else:
                u_img = hu_eq_imgH(vu, h_u)               # (G∪H)(u)∈imgH
                up_img = gu_eq_imgG(vup, h_up)            # (G∪H)(u')∈imgG
            # (G∪H)(u) ∈ second_img  (via (G∪H)(u)=(G∪H)(u') et up_img)
            u_in_second = N.modus_ponens(up_img, equivalence_avant(N.modus_ponens(
                N.modus_ponens(val_eq, symetrie(GuHu, GuHup)),
                N.s6(GuHup, GuHu, "w", appartient(var("w"), second_img)))))
            in_inter = (conjonction_intro(u_img, u_in_second) if side_u == "G"
                        else conjonction_intro(u_in_second, u_img))   # ∈imgG et ∈imgH
            v_inter = N.modus_ponens(in_inter, equivalence_arriere(
                _inst_inter(imgG, imgH, GuHu)))           # (G∪H)(u)∈imgG∩imgH
            v_in_vide = N.modus_ponens(v_inter, equivalence_avant(N.modus_ponens(
                hinterVide, N.s6(E.intersection(imgG, imgH), E.VIDE, "w",
                                 appartient(GuHu, var("w"))))))   # (G∪H)(u)∈∅
            n_vide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), GuHu)  # ¬(·∈∅)
            ueq = N.modus_ponens(v_in_vide, N.modus_ponens(n_vide,
                N.s2(non(appartient(GuHu, E.VIDE)), cible)))   # u=u' (ex falso)
            return N.loi_deduction(appartient(vup, domG if side_up == "G" else domH), ueq)

        br_left = meme("G") if side_u == "G" else croise("G")
        br_right = croise("H") if side_u == "G" else meme("H")
        inner = cas(up_disj, br_left, br_right)          # u=u'  (sous u∈dom side_u)
        return N.loi_deduction(appartient(vu, domG if side_u == "G" else domH), inner)

    br_uG = branche("G")     # u∈domG ⇒ ((u'∈domG ou u'∈domH) ⇒ u=u')
    br_uH = branche("H")     # u∈domH ⇒ ...
    u_eq_up = cas(u_disj, br_uG, br_uH)
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))


__all__ = ["valeur_reunion_gauche", "valeur_reunion_droite",
           "image_reunion_graphes", "reunion_graphes_injective"]
