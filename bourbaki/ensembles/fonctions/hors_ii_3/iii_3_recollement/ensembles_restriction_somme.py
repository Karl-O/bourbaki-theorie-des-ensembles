"""§III.3.3 — RECOLLEMENT le long de la somme disjointe (infra pour Prop 9
a^(b+c) = a^b · a^c).

Une application f définie sur la somme disjointe B⊔C = (B×{0})∪(C×{1}) se
DÉCOUPE en f|gauche et f|droite ; inversement, deux applications (g, h) à
domaines DISJOINTS se RECOLLENT en G∪H.  Le cœur ensembliste du recollement
est le fait que la RÉUNION de deux graphes fonctionnels à domaines disjoints
reste fonctionnelle (aucun conflit de valeur).

THÉORÈMES CERTIFIÉS (chacun testé, cf. test_restriction_somme.py) :
  • membre_reunion_graphes        (clos) — z∈G∪H ⇔ ((z∈G) ou (z∈H)) ;
  • antecedent_dans_domaine       (clos) — (u,v)∈F ⇒ u∈dom F ;
  • domaines_disjoints_si_marques (clos) — si dom G⊂B×{0} et dom H⊂C×{1}
        (donc 0≠1 sépare les copies) alors ¬(u∈dom G et u∈dom H) ;
  • reunion_graphes_fonctionnelle (clos, PIVOT) — G,H fonctionnels à domaines
        DISJOINTS (∀u ¬(u∈dom G et u∈dom H)) ⇒ G∪H fonctionnel ;
  • dom_reunion_graphes           (clos) — dom(G∪H) = dom G ∪ dom H.

Le terme « recollement » est simplement la réunion des deux graphes G∪H.
Tout est posé au niveau GÉNÉRAL (graphes fonctionnels G, H quelconques), donc
réutilisable hors de la somme disjointe.  La spécialisation aux copies marquées
(B×{0}, C×{1}) n'intervient que dans domaines_disjoints_si_marques, qui FOURNIT
l'hypothèse de disjonction au pivot.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, impl,
                                       appartient, existe, pourtout, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, antecedent_consequent
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── recollement = réunion des deux graphes ────────────────────────────────────
def recollement(g, h):
    """Le recollement de deux graphes G, H := G ∪ H  (terme dérivé).

    Si les domaines de G et H sont disjoints, G∪H est le graphe fonctionnel qui
    coïncide avec G sur dom G et avec H sur dom H."""
    return E.reunion(_t(g), _t(h))


# ── ex falso (réutilisé) ──────────────────────────────────────────────────────
def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.   (¬A ⇒ (A ⇒ Z), S2 puis MP.)"""
    a = thm_a.conclusion
    a_imp_z = N.modus_ponens(thm_na, N.s2(non(a), z))
    return N.modus_ponens(thm_a, a_imp_z)


# ── membership de la réunion de deux graphes ──────────────────────────────────
def membre_reunion_graphes(g="G", h="H", z="z"):
    """⊢ (z ∈ G∪H) ⇔ ((z ∈ G) ou (z ∈ H)).   (AXIOME_REUNION ; z nom ou terme.)"""
    vg, vh, vz = _t(g), _t(h), _t(z)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, vg), vh), vz)


# ── (u,v)∈F ⇒ u∈dom F ─────────────────────────────────────────────────────────
def antecedent_dans_domaine(u="u", v="v", f="F", y="y"):
    """⊢ ((u,v) ∈ F) ⇒ (u ∈ dom F).   (un couple de F atteste l'antécédent dans le
    domaine ; u,v,f noms ou termes.  Liant interne du domaine — paramétrable via `y`.)

    Avec le défaut `y="y"`, le pas S5 produit directement `(∃y)((u,y)∈F)`, la forme
    EXACTE du membre droit de AXIOME_DOM (qui fixe le liant « y ») : aucun pont, build
    BYTE-IDENTIQUE à l'historique.  Avec un liant FRAIS (`y≠"y"`, choisi par l'appelant
    pour éviter une τ-capture du témoin/liant dans F), on α-convertit le `(∃frais)…`
    obtenu vers le `(∃y)…` requis par AXIOME_DOM (`alpha_bridge`, renommage de liant ∃
    DÉRIVÉ) — la conclusion reste la même."""
    vu, vv, vf = _t(u), _t(v), _t(f)
    cpl = E.couple(vu, vv)
    huv = N.assume(appartient(cpl, vf))                       # (u,v)∈F
    # (∃y)((u,y)∈F) par S5, témoin y:=v, sur le liant (paramétrable) `y`
    body = appartient(E.couple(vu, var(y)), vf)              # (u,y)∈F
    ex = N.modus_ponens(huv, N.s5(body, vv, y))             # (∃<y>)((u,<y>)∈F)
    # AXIOME_DOM : u∈dom F ⇔ (∃y)((u,y)∈F)   (liant FIXÉ « y »)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vf), vu)               # u∈dom F ⇔ (∃y)((u,y)∈F)
    car_exists = antecedent_consequent(equivalence_arriere(car).conclusion)[0]  # (∃y)((u,y)∈F)
    # si le liant fourni n'est pas « y », α-convertir vers la forme de AXIOME_DOM
    if ex.conclusion != car_exists:
        from bourbaki.logique.tactiques.ensembles_alpha_bridge import alpha_bridge
        ex = alpha_bridge(ex, car_exists)                    # (∃y)((u,y)∈F)
    u_in_dom = N.modus_ponens(ex, equivalence_arriere(car))  # u∈dom F
    return N.loi_deduction(appartient(cpl, vf), u_in_dom)


# ── LEMME PIVOT : réunion de graphes fonctionnels à domaines disjoints ─────────
def reunion_graphes_fonctionnelle(g="G", h="H", u="u", v="v", z="z", y="y"):
    """{est_fonctionnel(G), est_fonctionnel(H), (∀u)¬(u∈dom G et u∈dom H)}
        ⊢ est_fonctionnel(G∪H).

    PIVOT DU RECOLLEMENT.  Si G et H sont fonctionnels et leurs domaines
    disjoints (aucun antécédent commun), alors G∪H ne crée aucun conflit de
    valeur : pour (u,v),(u,z)∈G∪H, soit les deux sont dans G (fonctionnalité de
    G), soit les deux dans H (fonctionnalité de H), soit l'un dans G et l'autre
    dans H — mais alors u∈dom G ET u∈dom H, contraire à la disjonction (ex
    falso).  Liants u,v,z (= ceux de est_fonctionnel, ≠ w,y)."""
    vg, vh = _t(g), _t(h)
    vu, vv, vz = var(u), var(v), var(z)
    GuH = E.reunion(vg, vh)
    cplv, cplz = E.couple(vu, vv), E.couple(vu, vz)

    hG = N.assume(E.est_fonctionnel(vg))                      # G fonctionnel
    hH = N.assume(E.est_fonctionnel(vh))                      # H fonctionnel
    # disjonction des domaines : (∀u)¬(u∈dom G et u∈dom H)
    disj_axiom = pourtout(u, non(et(appartient(vu, E.dom(vg)),
                                    appartient(vu, E.dom(vh)))))
    hD = N.assume(disj_axiom)
    ndisj = instancie(hD, vu)                                 # ¬(u∈dom G et u∈dom H)

    # G fonctionnel instancié : ((u,v)∈G et (u,z)∈G) ⇒ v=z
    fG = instancie(instancie(instancie(hG, vu), vv), vz)
    fH = instancie(instancie(instancie(hH, vu), vv), vz)

    # caractérisations réunion pour les deux couples
    carV = membre_reunion_graphes(vg, vh, cplv)              # (u,v)∈G∪H ⇔ ((u,v)∈G ou (u,v)∈H)
    carZ = membre_reunion_graphes(vg, vh, cplz)              # (u,z)∈G∪H ⇔ ((u,z)∈G ou (u,z)∈H)

    # antécédents dans les domaines
    adG_v = antecedent_dans_domaine(vu, vv, vg, y)         # (u,v)∈G ⇒ u∈dom G
    adH_v = antecedent_dans_domaine(vu, vv, vh, y)         # (u,v)∈H ⇒ u∈dom H
    adG_z = antecedent_dans_domaine(vu, vz, vg, y)         # (u,z)∈G ⇒ u∈dom G
    adH_z = antecedent_dans_domaine(vu, vz, vh, y)         # (u,z)∈H ⇒ u∈dom H

    cible = egal(vv, vz)

    # Sous l'hypothèse principale (u,v)∈G∪H et (u,z)∈G∪H :
    hyp = N.assume(et(appartient(cplv, GuH), appartient(cplz, GuH)))
    in_v = N.modus_ponens(conjonction_elim_gauche(hyp), equivalence_avant(carV))  # (u,v)∈G ou (u,v)∈H
    in_z = N.modus_ponens(conjonction_elim_droite(hyp), equivalence_avant(carZ))  # (u,z)∈G ou (u,z)∈H

    Gv = appartient(cplv, vg)
    Hv = appartient(cplv, vh)
    Gz = appartient(cplz, vg)
    Hz = appartient(cplz, vh)

    # branche : (u,v)∈G ⇒ [ (u,z)∈G ou (u,z)∈H ⇒ v=z ]
    def branche_v_dans_G():
        hGv = N.assume(Gv)
        # sous (u,z)∈G : fonctionnalité de G
        hGz = N.assume(Gz)
        vz_GG = N.modus_ponens(conjonction_intro(hGv, hGz), fG)        # v=z
        br_GG = N.loi_deduction(Gz, vz_GG)
        # sous (u,z)∈H : u∈dom G (de Gv) et u∈dom H (de Hz) → ¬disj → ex falso
        hHz = N.assume(Hz)
        udG = N.modus_ponens(hGv, adG_v)                              # u∈dom G
        udH = N.modus_ponens(hHz, adH_z)                             # u∈dom H
        contra = _ex_falso(conjonction_intro(udG, udH), ndisj, cible)  # v=z
        br_GH = N.loi_deduction(Hz, contra)
        return N.loi_deduction(Gv, cas(in_z, br_GG, br_GH))           # Gv ⇒ (v=z)

    # branche : (u,v)∈H ⇒ [ (u,z)∈G ou (u,z)∈H ⇒ v=z ]
    def branche_v_dans_H():
        hHv = N.assume(Hv)
        # sous (u,z)∈G : u∈dom H (Hv) et u∈dom G (Gz) → ex falso
        hGz = N.assume(Gz)
        udH = N.modus_ponens(hHv, adH_v)                            # u∈dom H
        udG = N.modus_ponens(hGz, adG_z)                            # u∈dom G
        contra = _ex_falso(conjonction_intro(udG, udH), ndisj, cible)
        br_HG = N.loi_deduction(Gz, contra)
        # sous (u,z)∈H : fonctionnalité de H
        hHz = N.assume(Hz)
        vz_HH = N.modus_ponens(conjonction_intro(hHv, hHz), fH)      # v=z
        br_HH = N.loi_deduction(Hz, vz_HH)
        return N.loi_deduction(Hv, cas(in_z, br_HG, br_HH))         # Hv ⇒ (v=z)

    vz_eq = cas(in_v, branche_v_dans_G(), branche_v_dans_H())        # v=z
    impl_uvz = N.loi_deduction(et(appartient(cplv, GuH), appartient(cplz, GuH)), vz_eq)
    gen = N.generalisation(u, N.generalisation(v, N.generalisation(z, impl_uvz)))
    return gen                                                       # est_fonctionnel(G∪H)


# ── dom(G∪H) = dom G ∪ dom H ──────────────────────────────────────────────────
def dom_reunion_graphes(g="G", h="H"):
    """⊢ (dom(G∪H)) = ((dom G) ∪ (dom H)).   (le domaine d'une réunion de graphes
    est la réunion des domaines ; double inclusion + extensionnalité A1.)

    u∈dom(G∪H) ⇔ (∃y)((u,y)∈G∪H) ⇔ (∃y)((u,y)∈G ou (u,y)∈H)
              ⇔ ((∃y)(u,y)∈G ou (∃y)(u,y)∈H) ⇔ (u∈dom G ou u∈dom H) ⇔ u∈domG∪domH.
    """
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    vg, vh = _t(g), _t(h)
    # variable courante = "z" (= liant de inclus, pour s'apparier à A1/extensionnalité)
    vu, vy = var("z"), var("y")
    GuH = E.reunion(vg, vh)
    domGuH = E.dom(GuH)
    domG, domH = E.dom(vg), E.dom(vh)
    reunDom = E.reunion(domG, domH)

    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_GuH = instancie(instancie(ax_dom, GuH), vu)   # u∈dom(G∪H) ⇔ (∃y)((u,y)∈G∪H)
    car_G = instancie(instancie(ax_dom, vg), vu)      # u∈dom G ⇔ (∃y)((u,y)∈G)
    car_H = instancie(instancie(ax_dom, vh), vu)      # u∈dom H ⇔ (∃y)((u,y)∈H)
    car_reun = membre_reunion_graphes(domG, domH, vu) # u∈domG∪domH ⇔ (u∈domG ou u∈domH)

    cplGuH = appartient(E.couple(vu, vy), GuH)
    cplG = appartient(E.couple(vu, vy), vg)
    cplH = appartient(E.couple(vu, vy), vh)
    car_couple = membre_reunion_graphes(vg, vh, E.couple(vu, vy))  # (u,y)∈G∪H ⇔ ((u,y)∈G ou (u,y)∈H)

    # ── ⇒ : u∈dom(G∪H) ⇒ u∈domG∪domH ─────────────────────────────────────────
    hL = N.assume(appartient(vu, domGuH))
    ex_GuH = N.modus_ponens(hL, equivalence_avant(car_GuH))    # (∃y)((u,y)∈G∪H)
    # sous (u,y)∈G∪H : ((u,y)∈G ou (u,y)∈H) → (u∈domG ou u∈domH) → u∈domG∪domH
    hbody = N.assume(cplGuH)
    disj_y = N.modus_ponens(hbody, equivalence_avant(car_couple))  # (u,y)∈G ou (u,y)∈H
    # (u,y)∈G ⇒ u∈domG∪domH
    hgy = N.assume(cplG)
    uG = N.modus_ponens(N.modus_ponens(hgy, N.s5(cplG, vy, "y")),
                        equivalence_arriere(car_G))            # u∈domG
    uG_reun = N.modus_ponens(
        N.modus_ponens(uG, N.s2(appartient(vu, domG), appartient(vu, domH))),
        equivalence_arriere(car_reun))                         # u∈domG∪domH
    br_G = N.loi_deduction(cplG, uG_reun)
    # (u,y)∈H ⇒ u∈domG∪domH
    hhy = N.assume(cplH)
    uH = N.modus_ponens(N.modus_ponens(hhy, N.s5(cplH, vy, "y")),
                        equivalence_arriere(car_H))            # u∈domH
    uH_reun = N.modus_ponens(
        N.modus_ponens(N.modus_ponens(uH, N.s2(appartient(vu, domH), appartient(vu, domG))),
                       N.s3(appartient(vu, domH), appartient(vu, domG))),
        equivalence_arriere(car_reun))                         # u∈domG∪domH
    br_H = N.loi_deduction(cplH, uH_reun)
    inreun_body = cas(disj_y, br_G, br_H)                      # u∈domG∪domH (sous (u,y)∈G∪H)
    ex_imp = existe_elimination(N.loi_deduction(cplGuH, inreun_body), "y")  # (∃y)((u,y)∈G∪H) ⇒ u∈domG∪domH
    fwd = N.loi_deduction(appartient(vu, domGuH),
                          N.modus_ponens(ex_GuH, ex_imp))      # u∈dom(G∪H) ⇒ u∈domG∪domH
    incl_LR = N.generalisation("z", fwd)                       # dom(G∪H) ⊂ domG∪domH

    # ── ⇐ : u∈domG∪domH ⇒ u∈dom(G∪H) ─────────────────────────────────────────
    hR = N.assume(appartient(vu, reunDom))
    disj_dom = N.modus_ponens(hR, equivalence_avant(car_reun))  # u∈domG ou u∈domH
    # u∈domG ⇒ u∈dom(G∪H)
    hdg = N.assume(appartient(vu, domG))
    exG = N.modus_ponens(hdg, equivalence_avant(car_G))        # (∃y)((u,y)∈G)
    # sous (u,y)∈G : (u,y)∈G∪H, donc (∃y)((u,y)∈G∪H)
    hgy2 = N.assume(cplG)
    inGuH_g = N.modus_ponens(
        N.modus_ponens(hgy2, N.s2(cplG, cplH)),
        equivalence_arriere(car_couple))                       # (u,y)∈G∪H
    exGuH_g = N.modus_ponens(inGuH_g, N.s5(cplGuH, vy, "y"))   # (∃y)((u,y)∈G∪H)
    impG = existe_elimination(N.loi_deduction(cplG, exGuH_g), "y")  # (∃y)(u,y)∈G ⇒ (∃y)(u,y)∈G∪H
    uG_dom = N.modus_ponens(N.modus_ponens(exG, impG), equivalence_arriere(car_GuH))  # u∈dom(G∪H)
    brR_G = N.loi_deduction(appartient(vu, domG), uG_dom)
    # u∈domH ⇒ u∈dom(G∪H)
    hdh = N.assume(appartient(vu, domH))
    exH = N.modus_ponens(hdh, equivalence_avant(car_H))        # (∃y)((u,y)∈H)
    hhy2 = N.assume(cplH)
    inGuH_h = N.modus_ponens(
        N.modus_ponens(N.modus_ponens(hhy2, N.s2(cplH, cplG)), N.s3(cplH, cplG)),
        equivalence_arriere(car_couple))                       # (u,y)∈G∪H
    exGuH_h = N.modus_ponens(inGuH_h, N.s5(cplGuH, vy, "y"))   # (∃y)((u,y)∈G∪H)
    impH = existe_elimination(N.loi_deduction(cplH, exGuH_h), "y")
    uH_dom = N.modus_ponens(N.modus_ponens(exH, impH), equivalence_arriere(car_GuH))  # u∈dom(G∪H)
    brR_H = N.loi_deduction(appartient(vu, domH), uH_dom)
    indom = cas(disj_dom, brR_G, brR_H)                        # u∈dom(G∪H)
    bwd = N.loi_deduction(appartient(vu, reunDom), indom)
    incl_RL = N.generalisation("z", bwd)                       # domG∪domH ⊂ dom(G∪H)

    ext = extensionnalite_appliquee(domGuH, reunDom)
    return N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)


# ── disjonction des domaines déduite de la STRUCTURE marquée (copies 0/1) ─────
def domaines_disjoints_si_marques(g="G", h="H", b="B", c="C", u="u"):
    """{dom G ⊂ B×{0}, dom H ⊂ C×{1}}  ⊢  ¬((u ∈ dom G) et (u ∈ dom H)).

    Les copies marquées sont disjointes car 0 ≠ 1 : si u∈dom G alors u∈B×{0}
    (donc 2ᵉ coordonnée = 0), si u∈dom H alors u∈C×{1} (2ᵉ coordonnée = 1) ;
    or de u=(p,0) et u=(p',1) on tire 0=1 par projection, contredisant 0≠1
    (vide_distinct_singleton).  Fournit l'hypothèse de disjonction du PIVOT.

    NB : la conclusion est instanciée à un u quelconque ; généraliser sur u
    (puis brancher reunion_graphes_fonctionnelle) est immédiat — laissé à
    l'appelant qui maîtrise la fraîcheur de u dans son contexte."""
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN
    from bourbaki.cardinaux.ensembles_vide_singleton import vide_distinct_singleton
    from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
    vg, vh, vb, vc = _t(g), _t(h), _t(b), _t(c)
    vu = _t(u)
    B0 = E.produit(vb, E.singleton(ZERO))
    C1 = E.produit(vc, E.singleton(UN))
    domG, domH = E.dom(vg), E.dom(vh)

    hG_sub = N.assume(E.inclus(domG, B0))   # dom G ⊂ B×{0} = (∀z)(z∈domG⇒z∈B×{0})
    hH_sub = N.assume(E.inclus(domH, C1))   # dom H ⊂ C×{1}

    # extraction de la 2ᵉ coordonnée marquée (= 0 à gauche, = 1 à droite)
    secondB = _seconde_coord_marquee(vu, vb, ZERO)    # (u∈B×{0}) ⇒ (∃p)(u=(p,0))
    secondC = _seconde_coord_marquee(vu, vc, UN)      # (u∈C×{1}) ⇒ (∃p)(u=(p,1))

    # ── sous (u∈domG et u∈domH) on dérive 0=1, contradiction avec 0≠1 ─────────
    hboth = N.assume(et(appartient(vu, domG), appartient(vu, domH)))
    uG = conjonction_elim_gauche(hboth)                # u∈domG
    uH = conjonction_elim_droite(hboth)                # u∈domH
    inB0 = N.modus_ponens(uG, instancie(hG_sub, vu))   # u∈B×{0}
    inC1 = N.modus_ponens(uH, instancie(hH_sub, vu))   # u∈C×{1}
    exB = N.modus_ponens(inB0, secondB)                # (∃p)(u=(p,0))
    exC = N.modus_ponens(inC1, secondC)                # (∃p)(u=(p,1))

    n01 = vide_distinct_singleton()                    # ¬(∅={∅}) = ¬(0=1)
    zero_eq_un = _zero_egal_un_de_temoins(vu, exB, exC)   # 0=1   (sous hboth, hG_sub, hH_sub)
    # both ⇒ 0=1 (décharge hboth) ; contraposée + ¬(0=1) → ¬both
    imp_both_01 = N.loi_deduction(et(appartient(vu, domG), appartient(vu, domH)),
                                  zero_eq_un)            # both ⇒ 0=1
    return N.modus_ponens(n01, contraposition(imp_both_01))   # ¬(u∈domG et u∈domH)


def _seconde_coord_marquee(u, a, c, p="p", q="q"):
    """⊢ (u ∈ A×{c}) ⇒ (∃p)(u = (p, c)).   (extraction de la forme (p,c) ; la 2ᵉ
    coordonnée d'un couple de A×{c} vaut c.  Liants p,q internes.)"""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import (composer_egalites,
                                                                     congruence_terme)
    vu, va, vc = _t(u), _t(a), _t(c)
    vp, vq = var(p), var(q)
    Sc = E.singleton(vc)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    inst = instancie(instancie(instancie(ax, va), Sc), vu)   # u∈A×{c} ⇔ (∃p∃q)(u=(p,q) et p∈A et q∈{c})
    body = et(et(egal(vu, E.couple(vp, vq)), appartient(vp, va)), appartient(vq, Sc))
    ax_p = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)

    hb = N.assume(body)
    u_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # u=(p,q)
    q_in = conjonction_elim_droite(hb)                           # q∈{c}
    car_q = instancie(instancie(instancie(ax_p, vc), vc), vq)    # q∈{c,c} ⇔ (q=c ou q=c)
    q_or = N.modus_ponens(q_in, equivalence_avant(car_q))       # q=c ou q=c
    # idempotence du ou → q=c
    eqc = egal(vq, vc)
    q_eq_c = N.modus_ponens(q_or, N.loi_deduction(ou(eqc, eqc),
        cas(N.assume(ou(eqc, eqc)),
            N.loi_deduction(eqc, N.assume(eqc)),
            N.loi_deduction(eqc, N.assume(eqc)))))             # q=c
    # u=(p,q)=(p,c)
    pq_pc = N.modus_ponens(q_eq_c, congruence_terme(vq, vc, E.couple(vp, var("w"))))  # (p,q)=(p,c)
    u_pc = composer_egalites(u_pq, pq_pc)                       # u=(p,c)
    ex = N.modus_ponens(u_pc, N.s5(egal(vu, E.couple(vp, vc)), vp, p))   # (∃p)(u=(p,c))
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(body, ex), q), p)                      # (∃p∃q)body ⇒ (∃p)(u=(p,c))
    return syllogisme(equivalence_avant(inst), avant)          # u∈A×{c} ⇒ (∃p)(u=(p,c))


def _zero_egal_un_de_temoins(u, exB, exC):
    """De ⊢ (∃p)(u=(p,0)) et ⊢ (∃p)(u=(p,1)), tire ⊢ 0=1.

    Sous témoins (u=(p,0), u=(pp,1)) : (p,0)=(pp,1) par transitivité, d'où la 2ᵉ
    coordonnée 0=1 (couple_egal_implique_composantes), via ∃-élimination.  Les deux
    existentielles ont le même liant 'p' ; on renomme celui de exC en 'pp'
    (alpha_existe) pour que les deux témoins soient distincts."""
    from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                                                                     composer_egalites)
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    vu = _t(u)
    vp, vpp = var("p"), var("pp")
    # renommage du liant de exC : (∃p)(u=(p,1)) → (∃pp)(u=(pp,1))
    corpsC = egal(vu, E.couple(vp, UN))                          # u=(p,1)
    exC_pp = N.modus_ponens(exC, equivalence_avant(alpha_existe("p", "pp", corpsC)))
    eqB = egal(vu, E.couple(vp, ZERO))     # u=(p,0)
    eqC = egal(vu, E.couple(vpp, UN))      # u=(pp,1)
    hB = N.assume(eqB)
    hC = N.assume(eqC)
    # (p,0)=u et u=(pp,1) → (p,0)=(pp,1)
    p0_u = N.modus_ponens(hB, symetrie(vu, E.couple(vp, ZERO)))   # (p,0)=u
    p0_p1 = composer_egalites(p0_u, hC)                           # (p,0)=(pp,1)
    # couple_egal_implique_composantes : (a,b)=(c,d) ⇒ (a=c et b=d)
    comp = couple_egal_implique_composantes(vp, ZERO, vpp, UN)    # (p,0)=(pp,1) ⇒ (p=pp et 0=1)
    zero_un = conjonction_elim_droite(N.modus_ponens(p0_p1, comp))  # 0=1   (sous hB,hC)
    # décharger les témoins par ∃-élimination (0=1 ne contient ni p ni pp)
    imp_C = existe_elimination(N.loi_deduction(eqC, zero_un), "pp")  # (∃pp)(u=(pp,1)) ⇒ 0=1
    z1_underB = N.modus_ponens(exC_pp, imp_C)                    # 0=1   (sous hB + ctx)
    imp_B = existe_elimination(N.loi_deduction(eqB, z1_underB), "p")  # (∃p)(u=(p,0)) ⇒ 0=1
    return N.modus_ponens(exB, imp_B)                            # 0=1


__all__ = ["recollement", "membre_reunion_graphes", "antecedent_dans_domaine",
           "reunion_graphes_fonctionnelle", "dom_reunion_graphes",
           "domaines_disjoints_si_marques"]
