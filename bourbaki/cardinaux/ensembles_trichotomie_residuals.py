"""§III.2 — Théorème 3 (TRICHOTOMIE) : DÉCHARGE des RÉSIDUS STRUCTURELS.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  L'assemblage `trichotomie_ordinaux_canon_prouve_min`
(ensembles_trichotomie_assemble) conclut `trichotomie_ordinaux_canon(E,R,F,Rp)`
sous EXACTEMENT 6 hypothèses :

    { bo(R,E), bo(Rp,F),                                  [ 2 = la prémisse du Th3 ]
      residu_univ_app,                                    [ R1 ]
      ( dom h = E  ou  pr₂ h = F ),                       [ MAXIMALITÉ ]
      est_segment(pr₂ h, Rp, F)[x,w],                     [ R4 ]
      val_dans_F }.                                       [ R2 ]

Ce module fournit les LEMMES GÉOMÉTRIQUES MANQUANTS qui DÉCHARGENT ces résidus
STRUCTURELS, ramenant l'assemblage vers { bo(R,E), bo(Rp,F) } = la prémisse propre
du théorème (= CLOS).  Le cœur mathématique (coïncidence, maximalité) est DÉJÀ prouvé
ailleurs ; ce qui restait n'était que de la BONNE-FORMATION géométrique.

────────────────────────────────────────────────────────────────────────────────
LE LEMME CŒUR (R1, partie #8 ; et R4) :

  🎯 `image_segment_est_segment(φ,S,T,S0,E,F,R,Rp)` :
        { iso(φ,S,T,R,Rp)[px,pw],  func φ,  dom φ=S,
          est_segment(S0,R,E),  est_segment(T,Rp,F),  inclus(S0,S),  bo(R,E) }
        ⊢ est_segment( image(φ,S0), Rp, F ).
     « L'IMAGE d'un sous-segment par un iso d'ordre est un segment du codomaine. »
     C'est LE lemme géométrique : image(φ,S0) est CLOS VERS LE BAS dans F.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout DÉRIVE des axiomes
IMAGE/DOM, de est_segment (Déf. 2), de compatible_ordre (sens arrière) et de la
surjectivité (image=but).  NON vacueux.  NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.cardinaux.ensembles_cantor_bernstein import inclusion_transitive_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.ensembles.base.ensembles_correspondances import (
    image_croissante, _inst_image,
)
from bourbaki.ensembles.fonctions.ensembles_valeur_codomaine import couple_valeur_dans_graphe
from bourbaki.ordre.ensembles_valeur_bridge import valeur_y_egal_j


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _image_croissante_terme(g, X, Y):
    """⊢ (X ⊂ Y) ⇒ (G⟨X⟩ ⊂ G⟨Y⟩)  pour des TERMES g, X, Y  (Prop 2, E.II.40).

    `image_croissante` ne travaille que sur des NOMS (var(g)) ; on instancie le schéma
    à lettres g,X,Y vers les TERMES (motif inclusion_transitive_terme)."""
    th = image_croissante("g", "X", "Y")
    for nm, tm in (("g", _t(g)), ("X", _t(X)), ("Y", _t(Y))):
        th = instancie(N.generalisation(nm, th), tm)
    return th


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LEMME CŒUR — image(φ,S0) est un SEGMENT de F.
# ════════════════════════════════════════════════════════════════════════════
def image_segment_est_segment(phi="phi", S="S", T="T", S0="S0",
                              E_set="E", F_set="F", R="R", Rp="Rp",
                              px="px", pw="pw"):
    """⊢ { est_isomorphisme_ordre(φ,S,T,R,Rp)[px,pw],  est_fonctionnel(φ),  dom φ=S,
           est_segment(S0,R,E),  est_segment(T,Rp,F),  inclus(S0,S),  bo(R,E) }
          ⊢ est_segment( image(φ,S0), Rp, F ).

    🎯 L'IMAGE d'un SOUS-SEGMENT S0 (⊆ le domaine S) par un iso d'ordre φ:S≅T est un
    SEGMENT du codomaine F (T étant lui-même un segment de F).

    PREUVE (clôture-bas de image(φ,S0) dans F).
      • inclus(image(φ,S0),F) : image(φ,S0)⊂image(φ,S)=T⊂F (image_croissante + surj + seg T).
      • INITIALITÉ : soit y∈image(φ,S0) (y=φ(x), x∈S0) et z∈F avec z≤y (Rp{z,y}).
          – y∈image(φ,S0)⊂T (déjà) ; T segment de F + z∈F + z≤y ⇒ z∈T.
          – z∈T=image(φ,S) ⇒ z=φ(x'), x'∈S.
          – Rp{z,y}=Rp{φ(x'),φ(x)} ⇒ (compat, sens ARRIÈRE) R{x',x}.
          – x'∈E (bo(R,E) : R{x',x}⇒R{x',x'}⇒x'∈E), x∈S0, R{x',x} ⇒ (init S0) x'∈S0.
          – donc z=φ(x')∈image(φ,S0).

    Liants d'ordre (px,pw) PARAMÉTRÉS pour s'aligner sur le témoin du résidu.
    Points FRAIS (xa,xb,yv,zv) ≠ x,y,z,j,px,pw — évite toute capture (τ_j de
    valeur / liants internes de compatible_ordre / binders de est_segment).
    theorie=22 ; rien postulé ; NON vacueux."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vphi, vS, vT, vS0 = _t(phi), _t(S), _t(T), _t(S0)
    vE, vF = _t(E_set), _t(F_set)
    img0 = E.image(vphi, vS0)                          # image(φ, S0)
    imgS = E.image(vphi, vS)                           # image(φ, S)

    # ── HYPOTHÈSES (assumées) ──────────────────────────────────────────────────
    H_iso = N.assume(V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, px, pw))
    H_func = N.assume(E.est_fonctionnel(vphi))
    H_dom = N.assume(egal(E.dom(vphi), vS))
    H_seg_S0 = N.assume(E.est_segment(vS0, Rf, vE))
    H_seg_T = N.assume(E.est_segment(vT, Rpf, vF))
    H_incl_S0_S = N.assume(inclus(vS0, vS))
    H_bo = N.assume(E.est_bien_ordonne(Rf, vE))

    bij = conjonction_elim_gauche(H_iso)               # est_bijective(φ,S,T)
    compat = conjonction_elim_droite(H_iso)            # compatible_ordre(φ,S,R,Rp)[px,pw]
    surj = conjonction_elim_droite(bij)                # image(φ,S)=T
    surj_sym = N.modus_ponens(surj, symetrie(imgS, vT))  # T = image(φ,S)

    incl_T_F = conjonction_elim_gauche(H_seg_T)        # T ⊂ F
    init_T = conjonction_elim_droite(H_seg_T)          # (∀x)(∀y)((x∈T et y∈F et Rp{y,x})⇒y∈T)
    incl_S0_E = conjonction_elim_gauche(H_seg_S0)      # S0 ⊂ E
    init_S0 = conjonction_elim_droite(H_seg_S0)        # init de S0

    # ── borne : image(φ,S0) ⊂ T  (= ⊂ image(φ,S) = T) ────────────────────────────
    img0_in_imgS = N.modus_ponens(H_incl_S0_S, _image_croissante_terme(vphi, vS0, vS))  # img0⊂imgS
    #   img0⊂imgS et imgS=T ⇒ img0⊂T (Leibniz S6, slot frais)
    img0_in_T = N.modus_ponens(img0_in_imgS,
        equivalence_avant(N.modus_ponens(surj,
            N.s6(imgS, vT, "rslotT", inclus(img0, var("rslotT"))))))             # img0⊂T

    # ── borne : image(φ,S0) ⊂ F  (transitivité img0⊂T⊂F) ─────────────────────────
    incl_img0_F = N.modus_ponens(conjonction_intro(img0_in_T, incl_T_F),
                                 inclusion_transitive_terme(img0, vT, vF))       # img0⊂F

    # ════════ INITIALITÉ : (∀yv)(∀zv)((yv∈img0 et zv∈F et Rp{zv,yv}) ⇒ zv∈img0) ════════
    vyv, vzv = var("yv"), var("zv")
    Hyv = N.assume(appartient(vyv, img0))              # yv ∈ image(φ,S0)
    Hzv = N.assume(appartient(vzv, vF))                # zv ∈ F
    HRp = N.assume(Rpf(vzv, vyv))                      # Rp{zv,yv}  i.e. zv ≤ yv

    # ── (a) yv∈img0 ⇒ (∃xa)(xa∈S0 et (xa,yv)∈φ) ; on extrait le témoin xa ──────────
    img0_car = _inst_image(vphi, vS0, vyv)             # yv∈img0 ⇔ (∃x)(x∈S0 et (x,yv)∈φ)
    ex_xa = N.modus_ponens(Hyv, equivalence_avant(img0_car))      # (∃x)(x∈S0 et (x,yv)∈φ)
    #   le liant de _inst_image est « x » ; on travaille SOUS ∃ avec le corps, et on
    #   refermera l'existentielle à la fin (existe_elimination).
    body_xa = et(appartient(var("x"), vS0), appartient(E.couple(var("x"), vyv), vphi))

    # ── (b) yv∈T  (img0⊂T instancié en yv) ───────────────────────────────────────
    yv_in_T = N.modus_ponens(Hyv, instancie(img0_in_T, vyv))     # yv ∈ T

    # ── (c) zv∈T  (T segment de F : zv∈F, yv∈T, Rp{zv,yv} ⇒ zv∈T) ─────────────────
    init_T_inst = instancie(instancie(init_T, vyv), vzv)         # (yv∈T et zv∈F et Rp{zv,yv})⇒zv∈T
    zv_in_T = N.modus_ponens(
        conjonction_intro(conjonction_intro(yv_in_T, Hzv), HRp), init_T_inst)   # zv∈T

    # ── (d) zv∈T=image(φ,S) ⇒ (∃xb)(xb∈S et (xb,zv)∈φ) ───────────────────────────
    zv_in_imgS = N.modus_ponens(zv_in_T,
        equivalence_avant(N.modus_ponens(surj_sym,
            N.s6(vT, imgS, "rslotI", appartient(vzv, var("rslotI"))))))          # zv∈image(φ,S)
    imgS_car = _inst_image(vphi, vS, vzv)              # zv∈imgS ⇔ (∃x)(x∈S et (x,zv)∈φ)
    ex_xb = N.modus_ponens(zv_in_imgS, equivalence_avant(imgS_car))  # (∃x)(x∈S et (x,zv)∈φ)
    body_xb = et(appartient(var("x"), vS), appartient(E.couple(var("x"), vzv), vphi))

    # ════════ SOUS LES DEUX TÉMOINS (xa pour yv, xb pour zv), prouver zv∈img0 ════════
    #   On élimine d'abord ∃ pour xb (liant « xb »), puis ∃ pour xa (liant « xa »), en
    #   α-renommant les deux existentielles (liant natif « x ») vers xa / xb distincts.
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    vxa, vxb = var("xa"), var("xb")
    # α : (∃x)(x∈S0 et (x,yv)∈φ) ⇔ (∃xa)(xa∈S0 et (xa,yv)∈φ)
    ren_a = alpha_existe("x", "xa", body_xa)
    ex_xa = N.modus_ponens(ex_xa, equivalence_avant(ren_a))      # (∃xa)…
    # α : (∃x)(x∈S et (x,zv)∈φ) ⇔ (∃xb)(xb∈S et (xb,zv)∈φ)
    ren_b = alpha_existe("x", "xb", body_xb)
    ex_xb = N.modus_ponens(ex_xb, equivalence_avant(ren_b))      # (∃xb)…

    body_xa_r = et(appartient(vxa, vS0), appartient(E.couple(vxa, vyv), vphi))
    body_xb_r = et(appartient(vxb, vS), appartient(E.couple(vxb, vzv), vphi))
    Hxa = N.assume(body_xa_r)
    Hxb = N.assume(body_xb_r)
    xa_in_S0 = conjonction_elim_gauche(Hxa)            # xa ∈ S0
    cpl_a = conjonction_elim_droite(Hxa)               # (xa, yv) ∈ φ
    xb_in_S = conjonction_elim_gauche(Hxb)             # xb ∈ S
    cpl_b = conjonction_elim_droite(Hxb)               # (xb, zv) ∈ φ
    xa_in_S = N.modus_ponens(xa_in_S0, instancie(H_incl_S0_S, vxa))   # xa ∈ S

    # ── yv = φ(xa)  (b='j', via func + couple_valeur) ────────────────────────────
    #   φ_j(xa) = valeur(φ,xa,b='j').  De (xa,yv)∈φ et (xa,φ_y(xa))∈φ + func : yv=φ_y(xa) ;
    #   pont y→j : φ_y(xa)=φ_j(xa).  D'où yv=φ_j(xa).
    yv_eq = _couple_donne_valeur_j(vphi, vS, vxa, vyv, cpl_a, H_func, H_dom, xa_in_S)
    zv_eq = _couple_donne_valeur_j(vphi, vS, vxb, vzv, cpl_b, H_func, H_dom, xb_in_S)
    phi_j_xa = E.valeur(vphi, vxa, b="j")
    phi_j_xb = E.valeur(vphi, vxb, b="j")

    # ── Rp{zv,yv} ⇒ Rp{φ_j(xb), φ_j(xa)}  (Leibniz, deux sites) ──────────────────
    #   réécrit zv → φ_j(xb) puis yv → φ_j(xa) dans HRp.
    Rp_z_to = N.modus_ponens(HRp, equivalence_avant(N.modus_ponens(zv_eq,
        N.s6(vzv, phi_j_xb, "rsz", Rpf(var("rsz"), vyv)))))      # Rp{φ_j(xb), yv}
    Rp_zy = N.modus_ponens(Rp_z_to, equivalence_avant(N.modus_ponens(yv_eq,
        N.s6(vyv, phi_j_xa, "rsy", Rpf(phi_j_xb, var("rsy"))))))  # Rp{φ_j(xb), φ_j(xa)}

    # ── compat (sens ARRIÈRE) : (xb∈S et xa∈S) ⇒ (R{xb,xa} ⇔ Rp{φ_j(xb),φ_j(xa)}) ─
    compat_inst = instancie(instancie(compat, vxb), vxa)         # (xb∈S et xa∈S)⇒(R{xb,xa}⇔Rp{…})
    equiv_ord = N.modus_ponens(conjonction_intro(xb_in_S, xa_in_S), compat_inst)
    R_xb_xa = N.modus_ponens(Rp_zy, equivalence_arriere(equiv_ord))   # R{xb, xa}

    # ── xb∈E  (bo(R,E) : R{xb,xa}⇒R{xb,xb} ; reflexive_dans : R{xb,xb}⇒xb∈E) ──────
    ord_dans = conjonction_elim_gauche(H_bo)           # est_relation_ordre_dans(R,E)
    rel_ordre = conjonction_elim_gauche(ord_dans)      # est_relation_ordre(R)
    refl_dans = conjonction_elim_droite(ord_dans)      # est_reflexive_dans_ordre(R,E)
    refl_impl = conjonction_elim_droite(rel_ordre)     # ordre_reflexif_implicite(R)
    refl_inst = instancie(instancie(refl_impl, vxb), vxa)        # R{xb,xa}⇒(R{xb,xb} et R{xa,xa})
    Rxbxb = conjonction_elim_gauche(N.modus_ponens(R_xb_xa, refl_inst))   # R{xb,xb}
    xb_in_E = N.modus_ponens(Rxbxb,
        equivalence_avant(instancie(refl_dans, vxb)))            # xb ∈ E

    # ── init S0 : (xa∈S0 et xb∈E et R{xb,xa}) ⇒ xb∈S0 ────────────────────────────
    init_S0_inst = instancie(instancie(init_S0, vxa), vxb)       # (xa∈S0 et xb∈E et R{xb,xa})⇒xb∈S0
    xb_in_S0 = N.modus_ponens(
        conjonction_intro(conjonction_intro(xa_in_S0, xb_in_E), R_xb_xa), init_S0_inst)  # xb∈S0

    # ── zv = φ(xb) ⇒ zv ∈ image(φ,S0)  (témoin xb∈S0, (xb,zv)∈φ) ──────────────────
    img0_car_z = _inst_image(vphi, vS0, vzv)           # zv∈img0 ⇔ (∃x)(x∈S0 et (x,zv)∈φ)
    body_img0_z = et(appartient(var("x"), vS0), appartient(E.couple(var("x"), vzv), vphi))
    wit_z = conjonction_intro(xb_in_S0, cpl_b)         # xb∈S0 et (xb,zv)∈φ  = (xb|x)body
    ex_img0_z = N.modus_ponens(wit_z, N.s5(body_img0_z, vxb, "x"))   # (∃x)(x∈S0 et (x,zv)∈φ)
    zv_in_img0 = N.modus_ponens(ex_img0_z, equivalence_arriere(img0_car_z))   # zv∈img0

    # ════════ refermer les deux existentielles (xb puis xa) ════════
    #   zv_in_img0 dépend de {body_xb_r, body_xa_r, yv∈img0, zv∈F, Rp{zv,yv}, hyps}.
    imp_xb = N.loi_deduction(body_xb_r, zv_in_img0)    # body_xb_r ⇒ zv∈img0
    imp_xb = existe_elimination(imp_xb, "xb")          # (∃xb)body_xb_r ⇒ zv∈img0
    zv_in_img0 = N.modus_ponens(ex_xb, imp_xb)         # zv∈img0  [body_xa_r, …]
    imp_xa = N.loi_deduction(body_xa_r, zv_in_img0)    # body_xa_r ⇒ zv∈img0
    imp_xa = existe_elimination(imp_xa, "xa")          # (∃xa)body_xa_r ⇒ zv∈img0
    zv_in_img0 = N.modus_ponens(ex_xa, imp_xa)         # zv∈img0  [yv∈img0, zv∈F, Rp{zv,yv}, hyps]

    # ── assembler la prémisse triple de est_segment, généraliser ─────────────────
    premisse = et(et(appartient(vyv, img0), appartient(vzv, vF)), Rpf(vzv, vyv))
    Hprem = N.assume(premisse)
    Hyv2 = conjonction_elim_gauche(conjonction_elim_gauche(Hprem))   # yv∈img0
    Hzv2 = conjonction_elim_droite(conjonction_elim_gauche(Hprem))   # zv∈F
    HRp2 = conjonction_elim_droite(Hprem)                            # Rp{zv,yv}
    #   reconstruire zv_in_img0 sous Hprem en déchargeant Hyv, Hzv, HRp
    step = zv_in_img0
    step = N.modus_ponens(HRp2, N.loi_deduction(Rpf(vzv, vyv), step))
    step = N.modus_ponens(Hzv2, N.loi_deduction(appartient(vzv, vF), step))
    step = N.modus_ponens(Hyv2, N.loi_deduction(appartient(vyv, img0), step))
    body_init = N.loi_deduction(premisse, step)        # premisse ⇒ zv∈img0
    init_clause = N.generalisation("yv", N.generalisation("zv", body_init))
    #   α-renommer (∀yv)(∀zv) → (∀x)(∀y) : forme canonique de est_segment (binders x,y).
    #   inner zv→y (sous ∀yv), puis outer yv→x.
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        alpha_pour_tout, congruence_pour_tout,
    )
    _, body_yv = _peler_pourtout(init_clause.conclusion)         # (∀zv)(corps)
    _, body_in = _peler_pourtout(body_yv)                        # corps interne (sous ∀zv)
    eqv_in = alpha_pour_tout("zv", "y", body_in)                 # (∀zv corps) ⇔ (∀y corps')
    eqv_lift = congruence_pour_tout(eqv_in, "yv")               # remonté sous ∀yv
    init_clause = N.modus_ponens(init_clause, equivalence_avant(eqv_lift))   # (∀yv)(∀y)(…)
    _, body_outer = _peler_pourtout(init_clause.conclusion)     # (∀y)(…)  (corps sous ∀yv)
    eqv_out = alpha_pour_tout("yv", "x", body_outer)            # (∀yv …) ⇔ (∀x …)
    init_clause = N.modus_ponens(init_clause, equivalence_avant(eqv_out))    # (∀x)(∀y)(…)

    return conjonction_intro(incl_img0_F, init_clause)   # est_segment(image(φ,S0),Rp,F)


def _couple_donne_valeur_j(vphi, vS, vx, vy_t, cpl, H_func, H_dom, x_in_S):
    """⊢ vy_t = valeur(φ, vx, b='j').

    De (vx,vy_t)∈φ [cpl], func φ [H_func], dom φ=S [H_dom], vx∈S [x_in_S] :
      (vx,φ_y(vx))∈φ [couple_valeur_dans_graphe] ; func ⇒ vy_t=φ_y(vx) ;
      pont y→j (valeur_y_egal_j) ⇒ vy_t=φ_j(vx).
    Tous les TERMES sont déjà résolus.  Liant-valeur τ_y puis pont vers τ_j."""
    phi_y = E.valeur(vphi, vx, b="y")                  # φ_y(vx)
    phi_j = E.valeur(vphi, vx, b="j")                  # φ_j(vx)
    # (vx, φ_y(vx)) ∈ φ   [dom φ=S, vx∈S]
    cvg = couple_valeur_dans_graphe(vphi, vS, vx)      # {dom φ=S, vx∈S} ⊢ (vx,φ_y(vx))∈φ
    cvg = N.modus_ponens(H_dom, N.loi_deduction(egal(E.dom(vphi), vS), cvg))
    cvg = N.modus_ponens(x_in_S, N.loi_deduction(appartient(vx, vS), cvg))
    # func : ((vx,vy_t)∈φ et (vx,φ_y(vx))∈φ) ⇒ vy_t=φ_y(vx)
    func_inst = instancie(instancie(instancie(H_func, vx), vy_t), phi_y)
    vy_eq_phiy = N.modus_ponens(conjonction_intro(cpl, cvg), func_inst)   # vy_t=φ_y(vx)
    # pont φ_y(vx)=φ_j(vx)
    bridge = valeur_y_egal_j(vphi, vx)                 # φ_y(vx)=φ_j(vx)
    return composer_egalites(vy_eq_phiy, bridge)       # vy_t = φ_j(vx)


def image_segment_est_segment_cible(phi="phi", S0="S0", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : est_segment(image(φ,S0), Rp, F)  (binders x,y)."""
    Rpf = _R_de(Rp)
    vphi, vS0, vF = _t(phi), _t(S0), _t(F_set)
    return E.est_segment(E.image(vphi, vS0), Rpf, vF)


__all__ = [
    "image_segment_est_segment", "image_segment_est_segment_cible",
]
