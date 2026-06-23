"""§III.2 — Théorème 3 (TRICHOTOMIE) : DÉCHARGE structurelle de pr₂h-SEGMENT et
h-GRAPHE (réduction de `trichotomie_ordinaux_canon_close` vers {bo,bo,residu}).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `trichotomie_ordinaux_canon_close` (ensembles_trichotomie_residuals) conclut
`trichotomie_ordinaux_canon(E,R,F,Rp)` (== maillon_final_cible) sous 5 hypothèses :

    { bo(R,E), bo(Rp,F), residu_univ_app,
      ( dom h = E  ou  pr₂ h = F ),                       [ MAXIMALITÉ ]
      est_segment(pr₂ h, Rp, F)[x,w] }.                   [ R4 ]

Ce module DÉCHARGE deux résidus STRUCTURELS :

  🎯 TARGET 2 — `pr2_h_est_segment` : est_segment(pr₂h, Rp, F) PROUVÉ CLOS.
     L'objection antérieure (circularité de image_segment_est_segment avec T=pr₂h
     son propre codomaine) est CONTOURNÉE par une preuve de clôture-bas AUTONOME :
     pour v∈pr₂h on a v=φ(u) (u∈S, témoin iso de h) ; pour w∈F avec Rp{w,v},
     l'INITIALITÉ du segment T (porté par le témoin) donne w∈T, la SURJECTIVITÉ de
     φ:S≅T (image(φ,S)=T) donne w=φ(u') pour u'∈S, et couple_iso_dans_h replace
     (u',w) dans h ⇒ w∈pr₂h.  AUCUNE hypothèse de codomaine (val_dans_F) : v∈T est
     DÉRIVÉ de la surjectivité, pas postulé.  CLOS.

  🎯 TARGET 1 — `h_inclus_dom_pr2` : inclus(h, dom h × pr₂h) (= h_graphe_hyp).
     De est_un_graphe(h) (tout z∈h est un couple) + h_inclus_produit (couple-form,
     CLOS) on dérive inclus(h, dom h × pr₂h) (AXIOME_DOM/AXIOME_IMG/PRODUIT).
     ⚠️ est_un_graphe(h) reste l'unique RÉSIDU OPAQUE irréductible : l'axiome de h
     (axiome_h, theorie_h) caractérise SEULEMENT les couples (u,v)∈h ⇔ corps — il ne
     dit RIEN d'un z ARBITRAIRE ∈ h, donc « tout z∈h est un couple » N'EST PAS
     dérivable de l'axiome opaque couple-only.  TARGET 1 RAMÈNE donc h_graphe_hyp à
     est_un_graphe(h), STRICTEMENT plus faible et plus fidèle (Déf. 1 « h est un
     graphe », E.II.37) que inclus(h, dom h × pr₂h) ; ce dernier IMPLIQUE le premier
     (tout produit est fait de couples).

  🎯🎯 `trichotomie_ordinaux_canon_close_v2` : trichotomie_ordinaux_canon SOUS
     { bo(R,E), bo(Rp,F), residu_univ_app, est_un_graphe(h) }.  La MAXIMALITÉ est
     déchargée (maximalite_donne_trichotomie_close), ses 3 hyps structurelles étant
     réglées : est_segment(dom h) ← dom_h_est_segment_sans_val (CLOS) ; est_segment(
     pr₂h) ← TARGET 2 (CLOS) ; inclus(h,dom h×pr₂h) ← TARGET 1 (sous est_un_graphe).
     Le résidu STRUCTUREL est_segment(pr₂h)[x,w] de close-v1 est aussi déchargé.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout DÉRIVE de l'axiome de h
(scaffold), AXIOME_DOM/IMG/IMAGE/PRODUIT, est_segment (Déf. 2), est_surjective,
compatible_ordre, couple_iso_dans_h, et ponts CLOS du dépôt.  NON vacueux.  NE
MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.ensembles.ii_3_correspondances.ensembles_correspondances import _inst_image, _inst_img
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import (
    _instance_produit, couple_dans_produit_ssi,
)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_valeur_codomaine import couple_valeur_dans_graphe
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_y_egal_j
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux import ensembles_maximalite_close as MAX
from bourbaki.cardinaux import ensembles_trichotomie_dom_segment as DS


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _inst_dom(g, x):
    """⊢ (x ∈ dom G) ⇔ (∃y)((x,y) ∈ G).   (le ∃ natif est sur le liant « y ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _t(g)), _t(x))


def _couple_donne_valeur_j(vphi, vS, vx, vy_t, cpl, H_func, H_dom, x_in_S):
    """⊢ vy_t = valeur(φ, vx, b='j').   (motif residuals._couple_donne_valeur_j.)

    De (vx,vy_t)∈φ [cpl], func φ [H_func], dom φ=S [H_dom], vx∈S [x_in_S] :
      (vx,φ_y(vx))∈φ [couple_valeur_dans_graphe] ; func ⇒ vy_t=φ_y(vx) ;
      pont y→j (valeur_y_egal_j) ⇒ vy_t=φ_j(vx)."""
    phi_y = E.valeur(vphi, vx, b="y")
    cvg = couple_valeur_dans_graphe(vphi, vS, vx)
    cvg = N.modus_ponens(H_dom, N.loi_deduction(egal(E.dom(vphi), vS), cvg))
    cvg = N.modus_ponens(x_in_S, N.loi_deduction(appartient(vx, vS), cvg))
    func_inst = instancie(instancie(instancie(H_func, vx), vy_t), phi_y)
    vy_eq_phiy = N.modus_ponens(conjonction_intro(cpl, cvg), func_inst)   # vy_t=φ_y(vx)
    bridge = valeur_y_egal_j(vphi, vx)                                    # φ_y(vx)=φ_j(vx)
    return composer_egalites(vy_eq_phiy, bridge)                          # vy_t=φ_j(vx)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 2 — pr₂h est un SEGMENT de F  (clôture-bas AUTONOME, CLOS).
# ════════════════════════════════════════════════════════════════════════════
def _pr2_h_initial(E_set="E", R="R", F_set="F", Rp="Rp", S="S", T="T", phi="phi"):
    """⊢ (∀x)(∀y)( (x∈pr₂h et y∈F et Rp{y,x}) ⇒ y∈pr₂h ).   (CLOS, theorie=22.)

    Clause d'INITIALITÉ (clôture-bas) de pr₂h, MIROIR F-côté de
    DS.dom_h_initial_sous_val mais SANS hypothèse de codomaine (val_dans_F) :

      x∈pr₂h ⇒ (∃u)((u,x)∈h) ⇒ (h_membre_donne_temoin) (∃S)(∃T)(∃φ) coeur :
        S seg E, T seg F, φ:S≅T, u∈S, x=φ(u), func φ, dom φ=S, φ⊂S×T.
      • SURJECTIVITÉ image(φ,S)=T (de l'iso) + (u,x)∈φ (couple_valeur + x=φ(u))
        ⇒ x∈image(φ,S)=T.
      • INITIALITÉ de T (T seg F) : y∈F, x∈T, Rp{y,x} ⇒ y∈T=image(φ,S)
        ⇒ (∃u')(u'∈S et (u',y)∈φ).
      • (u',y)∈φ, func, dom φ=S, u'∈S ⇒ y=φ(u') ; u'∈S⊂E ; y∈F
        ⇒ (u',y)∈h (couple_iso_dans_h) ⇒ y∈pr₂h (AXIOME_IMG, témoin u').

    Liants : universels « x » (∈pr₂h), « y » (∈F, = binders de est_segment) ; témoin
    préimage de x via AXIOME_IMG sur liant natif « x » → α-renommé « ux » (distinct
    des universels) ; préimage de y via image(φ,S) sur liant frais « up ».  CLOS."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    imgh = E.img(h)
    # universels FRAIS (≠ binders « x » de AXIOME_IMAGE/AXIOME_IMG, « y » de valeur,
    # « up »/« ux »/« vv » des témoins) ; α-renommés vers x,y de est_segment à la fin.
    vx, vy = var("xs"), var("ys")
    vS, vT, vphi = var(S), var(T), var(phi)

    # ════ sous le cœur témoin (S,T,φ ; u=ux, x), démontrer y∈pr₂h ════
    #   ux = préimage de x (liant ∃ de AXIOME_IMG côté x — natif « x » → renommé ux,
    #   ≠ universels x,y et ≠ binder « y » de valeur).
    ux = "ux"
    vux = var(ux)
    coeur = DS._coeur_temoin(E_set, R, F_set, Rp, vux, vx, S, T, phi)   # coeur(S,T,φ; ux, x)
    Hcoeur = N.assume(coeur)
    Hgraph = conjonction_elim_droite(Hcoeur)                   # φ⊂S×T
    r_app = conjonction_elim_gauche(Hcoeur)
    Hdom = conjonction_elim_droite(r_app)                      # dom(φ)=S
    r_app = conjonction_elim_gauche(r_app)
    Hfunc = conjonction_elim_droite(r_app)                     # est_fonctionnel(φ)
    Hc5 = conjonction_elim_gauche(r_app)
    Hx_eq = conjonction_elim_droite(Hc5)                       # x = valeur(φ, ux)
    c4 = conjonction_elim_gauche(Hc5)
    Hux_in_S = conjonction_elim_droite(c4)                     # ux∈S
    c3 = conjonction_elim_gauche(c4)
    Hiso = conjonction_elim_droite(c3)                         # iso(φ,S,T)[px,pw]
    c2 = conjonction_elim_gauche(c3)
    Hseg_T = conjonction_elim_droite(c2)                       # est_segment(T,Rp,F)
    Hseg_S = conjonction_elim_gauche(c2)                       # est_segment(S,R,E)

    # iso ⇒ bijective ⇒ surjective : image(φ,S)=T
    bij = conjonction_elim_gauche(Hiso)                        # est_bijective(φ,S,T)
    surj = conjonction_elim_droite(bij)                        # image(φ,S)=T
    imgphiS = E.image(vphi, vS)
    incl_S_E = conjonction_elim_gauche(Hseg_S)                 # S⊂E
    incl_T_F = conjonction_elim_gauche(Hseg_T)                 # T⊂F
    init_T = conjonction_elim_droite(Hseg_T)                   # (∀a)(∀b)((a∈T et b∈F et Rp{b,a})⇒b∈T)

    Hy_in_F = N.assume(appartient(vy, vF))                     # y∈F
    HRp = N.assume(Rpf(vy, vx))                                # Rp{y,x}  (y≤x)

    # ── (a) x∈T  : x=φ(ux)∈image(φ,S)=T  via (ux,x)∈φ ────────────────────────────
    #   (ux, x)∈φ : x=φ(ux)=φ_y(ux) [pont y→j absent ici : x=valeur(φ,ux,b='y')] ;
    #   couple_valeur_dans_graphe donne (ux,φ_y(ux))∈φ ; réécrire φ_y(ux)→x via Hx_eq.
    phi_y_ux = E.valeur(vphi, vux, b="y")                      # φ_y(ux) = valeur(φ,ux)
    cvg_ux = couple_valeur_dans_graphe(vphi, vS, vux)          # (ux,φ_y(ux))∈φ [domφ=S, ux∈S]
    cvg_ux = N.modus_ponens(Hdom, N.loi_deduction(egal(E.dom(vphi), vS), cvg_ux))
    cvg_ux = N.modus_ponens(Hux_in_S, N.loi_deduction(appartient(vux, vS), cvg_ux))
    #   x=φ_y(ux) ⇒ (ux,x)∈φ  (Leibniz : réécrire φ_y(ux)→x dans (ux,φ_y(ux))∈φ)
    ux_x_in_phi = N.modus_ponens(cvg_ux, equivalence_avant(N.modus_ponens(
        N.modus_ponens(Hx_eq, symetrie(vx, phi_y_ux)),         # φ_y(ux)=x
        N.s6(phi_y_ux, vx, "rs1", appartient(E.couple(vux, var("rs1")), vphi)))))   # (ux,x)∈φ
    #   x∈image(φ,S) : témoin ux∈S et (ux,x)∈φ  (AXIOME_IMAGE, liant natif « x »)
    img_car_x = _inst_image(vphi, vS, vx)                      # x∈img(φ,S) ⇔ (∃a)(a∈S et (a,x)∈φ)
    body_imgx = et(appartient(var("x"), vS), appartient(E.couple(var("x"), vx), vphi))
    #   ⚠️ le liant natif de _inst_image est « x » (= notre universel) → α-renommer en « ux »
    ren_imgx = alpha_existe("x", ux, body_imgx)                # (∃x)… ⇔ (∃ux)…
    img_car_x = _equiv_transit(img_car_x, ren_imgx)
    wit_x = conjonction_intro(Hux_in_S, ux_x_in_phi)           # ux∈S et (ux,x)∈φ
    ex_imgx = N.modus_ponens(wit_x, N.s5(
        et(appartient(vux, vS), appartient(E.couple(vux, vx), vphi)), vux, ux))   # (∃ux)…
    x_in_imgphiS = N.modus_ponens(ex_imgx, equivalence_arriere(img_car_x))   # x∈image(φ,S)
    #   image(φ,S)=T ⇒ x∈T
    x_in_T = N.modus_ponens(x_in_imgphiS, equivalence_avant(N.modus_ponens(
        surj, N.s6(imgphiS, vT, "rs2", appartient(vx, var("rs2"))))))           # x∈T

    # ── (b) y∈T  : T segment de F, x∈T, y∈F, Rp{y,x} ⇒ y∈T ───────────────────────
    init_T_inst = instancie(instancie(init_T, vx), vy)         # (x∈T et y∈F et Rp{y,x})⇒y∈T
    y_in_T = N.modus_ponens(
        conjonction_intro(conjonction_intro(x_in_T, Hy_in_F), HRp), init_T_inst)   # y∈T

    # ── (c) y∈T=image(φ,S) ⇒ (∃up)(up∈S et (up,y)∈φ) ─────────────────────────────
    surj_sym = N.modus_ponens(surj, symetrie(imgphiS, vT))     # T=image(φ,S)
    y_in_imgphiS = N.modus_ponens(y_in_T, equivalence_avant(N.modus_ponens(
        surj_sym, N.s6(vT, imgphiS, "rs3", appartient(vy, var("rs3"))))))         # y∈image(φ,S)
    img_car_y = _inst_image(vphi, vS, vy)                      # y∈img(φ,S) ⇔ (∃a)(a∈S et (a,y)∈φ)
    body_imgy = et(appartient(var("x"), vS), appartient(E.couple(var("x"), vy), vphi))
    up = "up"
    vup = var(up)
    ren_imgy = alpha_existe("x", up, body_imgy)                # (∃x)… ⇔ (∃up)…
    img_car_y = _equiv_transit(img_car_y, ren_imgy)
    ex_imgy = N.modus_ponens(y_in_imgphiS, equivalence_avant(img_car_y))   # (∃up)(up∈S et (up,y)∈φ)
    body_up = et(appartient(vup, vS), appartient(E.couple(vup, vy), vphi))

    # ════ sous le témoin up (préimage de y), démontrer y∈pr₂h ════
    Hup = N.assume(body_up)
    up_in_S = conjonction_elim_gauche(Hup)                     # up∈S
    up_y_phi = conjonction_elim_droite(Hup)                    # (up,y)∈φ
    up_in_E = N.modus_ponens(up_in_S, instancie(incl_S_E, vup))   # up∈E

    # y=φ(up)=valeur(φ,up,b='j')  (func + couple_valeur + pont y→j)
    y_eq_j = _couple_donne_valeur_j(vphi, vS, vup, vy, up_y_phi, Hfunc, Hdom, up_in_S)
    phi_j_up = E.valeur(vphi, vup, b="j")                      # = valeur(φ,up) attendu par couple_iso_dans_h ?

    # ── (up, vv) ∈ h  via couple_iso_dans_h (vv FRAÎCHE, vv∈F et vv=valeur(φ,up)) ──
    #   couple_iso_dans_h attend v = valeur(φ, u) (b='y' par défaut).  On donne donc
    #   vv=valeur(φ,up,b='y') = phi_y_up, dérivé de (up,y)∈φ comme y_eq_phiy.
    phi_y_up = E.valeur(vphi, vup, b="y")
    cvg_up = couple_valeur_dans_graphe(vphi, vS, vup)          # (up,φ_y(up))∈φ
    cvg_up = N.modus_ponens(Hdom, N.loi_deduction(egal(E.dom(vphi), vS), cvg_up))
    cvg_up = N.modus_ponens(up_in_S, N.loi_deduction(appartient(vup, vS), cvg_up))
    func_up = instancie(instancie(instancie(Hfunc, vup), vy), phi_y_up)
    y_eq_phiy_up = N.modus_ponens(conjonction_intro(up_y_phi, cvg_up), func_up)   # y=φ_y(up)

    vv_name = "vv"
    vvv = var(vv_name)
    cid = TS.couple_iso_dans_h(E_set, R, F_set, Rp, S, T, phi, up, vv_name)
    Hvv_F = N.assume(appartient(vvv, vF))
    Hvv_eq = N.assume(egal(vvv, phi_y_up))                     # vv=valeur(φ,up)
    preuves = [
        (E.est_segment(vS, Rf, vE), Hseg_S),
        (E.est_segment(vT, Rpf, vF), Hseg_T),
        (V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw"), Hiso),
        (appartient(vup, vS), up_in_S),
        (appartient(vup, vE), up_in_E),
        (appartient(vvv, vF), Hvv_F),
        (egal(vvv, phi_y_up), Hvv_eq),
        (E.est_fonctionnel(vphi), Hfunc),
        (egal(E.dom(vphi), vS), Hdom),
        (inclus(vphi, E.produit(vS, vT)), Hgraph),
    ]
    couple_in_h = cid
    for hyp_f, preuve in preuves:
        couple_in_h = N.modus_ponens(preuve, N.loi_deduction(hyp_f, couple_in_h))
    # couple_in_h : {coeur, y∈F, Rp{y,x}, up-body, vv∈F, vv=φ(up)} ⊢ (up, vv)∈h

    # ── (up,vv)∈h ⇒ y∈pr₂h : (∃a)((a,vv)∈h) donne vv∈pr₂h ; mais on veut y∈pr₂h.
    #   On élimine vv via vv=φ(up) et y=φ(up) ⇒ vv=y ; replace vv→y dans (up,vv)∈h.
    prem_vv = et(appartient(vvv, vF), egal(vvv, phi_y_up))
    Hprem_vv = N.assume(prem_vv)
    vv_eq_phi = conjonction_elim_droite(Hprem_vv)              # vv=φ(up)
    #   vv=φ(up) et y=φ(up) ⇒ vv=y
    vv_eq_y = composer_egalites(vv_eq_phi, N.modus_ponens(y_eq_phiy_up, symetrie(vy, phi_y_up)))
    couple_in_h_2 = N.modus_ponens(
        conjonction_elim_gauche(Hprem_vv),
        N.modus_ponens(conjonction_elim_droite(Hprem_vv),
                       N.loi_deduction(egal(vvv, phi_y_up),
                           N.loi_deduction(appartient(vvv, vF), couple_in_h))))
    #   (up,vv)∈h et vv=y ⇒ (up,y)∈h  (Leibniz : vv→y)
    up_y_in_h = N.modus_ponens(couple_in_h_2, equivalence_avant(N.modus_ponens(
        vv_eq_y, N.s6(vvv, vy, "rs4", appartient(E.couple(vup, var("rs4")), h)))))   # (up,y)∈h
    #   y∈pr₂h : (∃a)((a,y)∈h)  (AXIOME_IMG, liant natif « x » → on prend témoin up)
    img_h_car = _inst_img(h, vy)                               # y∈pr₂h ⇔ (∃a)((a,y)∈h)
    bd = _find_exists_binder(img_h_car.conclusion)
    ex_h = N.modus_ponens(up_y_in_h, N.s5(appartient(E.couple(var(bd), vy), h), vup, bd))
    y_in_imgh = N.modus_ponens(ex_h, equivalence_arriere(img_h_car))   # y∈pr₂h  [.., prem_vv]

    # ── éliminer vv (∃vv) puis le témoin up (∃up) ──
    imp_vv = N.loi_deduction(prem_vv, y_in_imgh)               # prem_vv ⇒ y∈pr₂h
    ex_vv_to = existe_elimination(imp_vv, vv_name)             # (∃vv)prem_vv ⇒ y∈pr₂h
    #   (∃vv)(vv∈F et vv=φ(up)) depuis φ(up)∈F.  φ(up)∈F : φ(up)=y (y_eq_phiy_up
    #   ⇒ φ_y(up)=y) ... mais y∈F est une HYP ; donc φ_y(up)∈F par réécriture y→φ_y(up).
    phiy_up_in_F = N.modus_ponens(Hy_in_F, equivalence_avant(N.modus_ponens(
        y_eq_phiy_up, N.s6(vy, phi_y_up, "rs5", appartient(var("rs5"), vF)))))   # φ_y(up)∈F
    refl = N.reflexivite(phi_y_up)
    ex_vv = N.modus_ponens(conjonction_intro(phiy_up_in_F, refl),
                           N.s5(prem_vv, phi_y_up, vv_name))   # (∃vv)(vv∈F et vv=φ(up))
    y_in_imgh = N.modus_ponens(ex_vv, ex_vv_to)                # y∈pr₂h  [coeur,y∈F,Rp,up-body]
    #   éliminer le témoin up
    imp_up = N.loi_deduction(body_up, y_in_imgh)               # up-body ⇒ y∈pr₂h
    ex_up_to = existe_elimination(imp_up, up)                  # (∃up)up-body ⇒ y∈pr₂h
    y_in_imgh = N.modus_ponens(ex_imgy, ex_up_to)              # y∈pr₂h  [coeur,y∈F,Rp]

    # ── éliminer le cœur (∃S,T,φ) puis raccorder à x∈pr₂h ──
    imp_coeur = N.loi_deduction(coeur, y_in_imgh)
    imp_phi = existe_elimination(imp_coeur, phi)
    imp_T = existe_elimination(imp_phi, T)
    imp_S = existe_elimination(imp_T, S)                       # (∃S)(∃T)(∃φ)coeur ⇒ y∈pr₂h

    #   x∈pr₂h ⇒ (∃ux)((ux,x)∈h) ; h_membre_donne_temoin ⇒ (∃S)(∃T)(∃φ)coeur(;ux,x)
    hdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    couple_imp = instancie(instancie(hdt, vux), vx)            # (ux,x)∈h ⇒ (∃S)(∃T)(∃φ)coeur(;ux,x)
    cz_to = syllogisme(couple_imp, imp_S)                      # (ux,x)∈h ⇒ y∈pr₂h
    ex_ux_to = existe_elimination(cz_to, ux)                   # (∃ux)((ux,x)∈h) ⇒ y∈pr₂h
    #   x∈pr₂h ⇔ (∃a)((a,x)∈h) [AXIOME_IMG, liant natif « x » → α-renommer « ux »]
    img_h_car_x = _inst_img(h, vx)                             # x∈pr₂h ⇔ (∃x)((x,x)∈h)  liant « x »
    bdx = _find_exists_binder(img_h_car_x.conclusion)
    body_x_native = appartient(E.couple(var(bdx), vx), h)
    ren_x = alpha_existe(bdx, ux, body_x_native)               # (∃x)((x,x)∈h) ⇔ (∃ux)((ux,x)∈h)
    x_imgh_to_ex = syllogisme(equivalence_avant(img_h_car_x), equivalence_avant(ren_x))
    x_to = syllogisme(x_imgh_to_ex, ex_ux_to)                  # x∈pr₂h ⇒ y∈pr₂h  [y∈F, Rp]

    # ── assembler la prémisse triple de est_segment, généraliser sur x,y ──
    imp1 = N.loi_deduction(Rpf(vy, vx), x_to)
    imp2 = N.loi_deduction(appartient(vy, vF), imp1)
    premisse = et(et(appartient(vx, imgh), appartient(vy, vF)), Rpf(vy, vx))
    Hprem = N.assume(premisse)
    Hx_img = conjonction_elim_gauche(conjonction_elim_gauche(Hprem))
    Hy_F2 = conjonction_elim_droite(conjonction_elim_gauche(Hprem))
    HRp2 = conjonction_elim_droite(Hprem)
    step = N.modus_ponens(HRp2, N.modus_ponens(Hy_F2, imp2))
    y_in_imgh_final = N.modus_ponens(Hx_img, step)
    body = N.loi_deduction(premisse, y_in_imgh_final)
    init_clause = N.generalisation("xs", N.generalisation("ys", body))   # (∀xs)(∀ys)(…)
    #   α-renommer (∀xs)(∀ys) → (∀x)(∀y) : forme canonique de est_segment (binders x,y).
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        alpha_pour_tout, congruence_pour_tout,
    )
    _, body_xs = _peler_pourtout(init_clause.conclusion)        # (∀ys)(corps)
    _, body_in = _peler_pourtout(body_xs)                       # corps interne (sous ∀ys)
    eqv_in = alpha_pour_tout("ys", "y", body_in)                # (∀ys corps) ⇔ (∀y corps')
    eqv_lift = congruence_pour_tout(eqv_in, "xs")
    init_clause = N.modus_ponens(init_clause, equivalence_avant(eqv_lift))   # (∀xs)(∀y)(…)
    _, body_outer = _peler_pourtout(init_clause.conclusion)     # (∀y)(…)  (corps sous ∀xs)
    eqv_out = alpha_pour_tout("xs", "x", body_outer)            # (∀xs …) ⇔ (∀x …)
    init_clause = N.modus_ponens(init_clause, equivalence_avant(eqv_out))    # (∀x)(∀y)(…)
    return init_clause                                          # initialité de pr₂h  (CLOS)


def _find_exists_binder(f):
    """Renvoie le nom du PREMIER liant ∃ rencontré dans f (parcours préfixe)."""
    if f.tag == "exists":
        return f.lieur
    for s in f.sous:
        r = _find_exists_binder(s)
        if r:
            return r
    return None


def _equiv_transit(*equivs):
    """Chaîne d'équivalences A⇔B, B⇔C, … en A⇔Z."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_transitivite
    acc = equivs[0]
    for e in equivs[1:]:
        acc = equivalence_transitivite(acc, e)
    return acc


def pr2_h_est_segment(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ est_segment(pr₂h, Rp, F).   (CLOS, theorie=22 — TARGET 2.)

    🎯 Conjonction de la borne pr₂h⊂F (INCONDITIONNELLE, M.h_img_inclus_F) et de
    l'initialité `_pr2_h_initial` (clôture-bas AUTONOME via surjectivité de l'iso
    témoin, SANS hypothèse de codomaine).  Déchargeur du résidu est_segment(pr₂h,Rp,F)
    de `trichotomie_ordinaux_canon_close`.  NON vacueux."""
    incl = M.h_img_inclus_F(E_set, R, F_set, Rp)               # pr₂h⊂F  (INCOND.)
    init = _pr2_h_initial(E_set, R, F_set, Rp)
    return conjonction_intro(incl, init)


def pr2_h_est_segment_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : est_segment(pr₂h, Rp, F)  [binders x,y]."""
    Rpf = _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_segment(E.img(h), Rpf, _t(F_set))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 1 — inclus(h, dom h × pr₂h)  (= h_graphe_hyp), SOUS est_un_graphe(h).
#
#  ⚠️ est_un_graphe(h) = (∀z)(z∈h ⇒ z couple) est l'UNIQUE résidu OPAQUE : l'axiome
#  de h (couple-only) ne dit RIEN d'un z arbitraire ∈ h.  De est_un_graphe(h) +
#  h_inclus_produit (couple-form, CLOS), on dérive inclus(h, dom h × pr₂h) :
#  STRICTEMENT plus faible que cette dernière (qui IMPLIQUE est_un_graphe(h)).
# ════════════════════════════════════════════════════════════════════════════
def h_inclus_dom_pr2(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { est_un_graphe(h) } ⊢ inclus( h, dom h × pr₂h ).   (== M.h_graphe_hyp.)

    🎯 TARGET 1.  z∈h ⇒ (est_un_graphe(h)) z=(p,q) est un couple ; témoins p,q :
      (p,q)∈h (Leibniz z→(p,q)) ; p∈dom h (AXIOME_DOM, témoin q) ; q∈pr₂h (AXIOME_IMG,
      témoin p) ; (p,q)∈dom h×pr₂h (couple_dans_produit_ssi) ; z=(p,q) ⇒ z∈dom h×pr₂h.
      ∃-élim de p,q (la conclusion z∈dom h×pr₂h ne contient ni p ni q).

    L'UNIQUE hypothèse `est_un_graphe(h)` est l'opacité IRRÉDUCTIBLE (l'axiome de h,
    couple-only, ne la donne pas pour un z arbitraire) — mais elle est STRICTEMENT
    plus faible que h_graphe_hyp = inclus(h, dom h × pr₂h) (qui l'implique : tout
    élément d'un produit est un couple).  theorie=22, NON vacueux."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    prod = E.produit(domh, imgh)
    vz = var("z")
    #   ⚠️ témoins kp,kq DISTINCTS des binders internes p,q de couple_dans_produit_ssi
    #   et x,y de est_un_couple / AXIOME_DOM(y) / AXIOME_IMG(x).
    vp, vq = var("kp"), var("kq")

    # ── est_un_graphe(h) : z∈h ⇒ est_un_couple(z) ──
    H_graphe = N.assume(E.est_un_graphe(h))                    # (∀z)(z∈h ⇒ z couple)
    Hz = N.assume(appartient(vz, h))                           # z∈h
    z_couple = N.modus_ponens(Hz, instancie(H_graphe, vz))     # (∃x)(∃y)(z=(x,y))  binders x,y
    #   α-renommer (∃x)(∃y)(z=(x,y)) → (∃kp)(∃kq)(z=(kp,kq))  (binders frais kp,kq)
    inner_xy = egal(vz, E.couple(var("x"), var("y")))
    ren_y = alpha_existe("y", "kq", inner_xy)                  # (∃y)(z=(x,y)) ⇔ (∃kq)(z=(x,kq))
    eqv_y_lift = _congruence_existe(ren_y, "x")               # (∃x)(∃y)… ⇔ (∃x)(∃kq)…
    from bourbaki.logique.formule import subst_f
    body_x2 = existe("kq", subst_f(vq, "y", inner_xy))         # (∃kq)(z=(x,kq))
    ren_x = alpha_existe("x", "kp", body_x2)                   # (∃x)(∃kq)… ⇔ (∃kp)(∃kq)…
    z_couple_pq = N.modus_ponens(z_couple, equivalence_avant(
        _equiv_transit(eqv_y_lift, ren_x)))                    # (∃kp)(∃kq)(z=(kp,kq))

    # ── sous les témoins p,q : z=(p,q) ⇒ z∈dom h×pr₂h ──
    body_pq = egal(vz, E.couple(vp, vq))
    Hpq = N.assume(body_pq)                                    # z=(p,q)
    #   (p,q)∈h : z∈h et z=(p,q) ⇒ (p,q)∈h  (Leibniz z→(p,q) dans z∈h)
    pq_in_h = N.modus_ponens(Hz, equivalence_avant(N.modus_ponens(
        Hpq, N.s6(vz, E.couple(vp, vq), "rsz", appartient(var("rsz"), h)))))   # (p,q)∈h
    #   p∈dom h : (∃a)((p,a)∈h)  (AXIOME_DOM, liant natif « y » → témoin q)
    dom_car = _inst_dom(h, vp)                                 # p∈dom h ⇔ (∃y)((p,y)∈h)
    bd_d = _find_exists_binder(dom_car.conclusion)
    ex_d = N.modus_ponens(pq_in_h, N.s5(appartient(E.couple(vp, var(bd_d)), h), vq, bd_d))
    p_in_dom = N.modus_ponens(ex_d, equivalence_arriere(dom_car))   # p∈dom h
    #   q∈pr₂h : (∃a)((a,q)∈h)  (AXIOME_IMG, liant natif « x » → témoin p)
    img_car = _inst_img(h, vq)                                 # q∈pr₂h ⇔ (∃x)((x,q)∈h)
    bd_i = _find_exists_binder(img_car.conclusion)
    ex_i = N.modus_ponens(pq_in_h, N.s5(appartient(E.couple(var(bd_i), vq), h), vp, bd_i))
    q_in_img = N.modus_ponens(ex_i, equivalence_arriere(img_car))   # q∈pr₂h
    #   (p,q)∈dom h×pr₂h  (couple_dans_produit_ssi)
    ssi = couple_dans_produit_ssi(vp, vq, domh, imgh)          # ((p,q)∈domh×imgh)⇔(p∈domh et q∈imgh)
    pq_in_prod = N.modus_ponens(conjonction_intro(p_in_dom, q_in_img),
                                equivalence_arriere(ssi))      # (p,q)∈domh×imgh
    #   z=(p,q) ⇒ z∈domh×imgh  (Leibniz (p,q)→z)
    z_in_prod = N.modus_ponens(pq_in_prod, equivalence_arriere(N.modus_ponens(
        Hpq, N.s6(vz, E.couple(vp, vq), "rsp", appartient(var("rsp"), prod)))))   # z∈domh×imgh

    # ── ∃-élim de kq, kp ──
    z_in_prod = N.modus_ponens(z_couple_pq, existe_elimination(existe_elimination(
        N.loi_deduction(body_pq, z_in_prod), "kq"), "kp"))     # z∈domh×imgh  [z∈h, est_un_graphe]
    #   décharger z∈h (en antécédent), généraliser sur z
    z_imp = N.loi_deduction(appartient(vz, h), z_in_prod)      # z∈h ⇒ z∈domh×imgh  [est_un_graphe]
    return N.generalisation("z", z_imp)                        # h ⊂ domh×imgh  [est_un_graphe]


def h_inclus_dom_pr2_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : inclus(h, dom h × pr₂h)  (== M.h_graphe_hyp)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return inclus(h, E.produit(E.dom(h), E.img(h)))


def _congruence_existe(thm_eq, x):
    """⊢ (R⇔S) (x non libre dans Γ) ⟹ Γ ⊢ (∃x)R ⇔ (∃x)S."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import monotonie_existe
    avant = monotonie_existe(equivalence_avant(thm_eq), x)
    arriere = monotonie_existe(equivalence_arriere(thm_eq), x)
    return conjonction_intro(avant, arriere)


def _pr2_seg_binders(E_set, R, F_set, Rp, xb, yb):
    """⊢ est_segment(pr₂h, Rp, F)  aux binders (xb,yb) ARBITRAIRES — CLOS.

    `pr2_h_est_segment` (binders x,y) α-renommé vers (xb,yb), motif
    RES._seg_dom_sans_val_binders."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche as cg, conjonction_elim_droite as cd, _peler_pourtout,
    )
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        alpha_pour_tout, congruence_pour_tout,
    )
    ps = pr2_h_est_segment(E_set, R, F_set, Rp)       # binders x,y
    borne = cg(ps)                                    # pr₂h ⊂ F
    init = cd(ps)                                     # (∀x)(∀y)(…)
    if xb != "x":                                     # α-renommer le binder externe x→xb
        _, body_x = _peler_pourtout(init.conclusion)  # (∀y)(…)
        eqv_ext = alpha_pour_tout("x", xb, body_x)
        init = N.modus_ponens(init, equivalence_avant(eqv_ext))   # (∀xb)(∀y)(…)
    if yb != "y":                                     # α-renommer le binder interne y→yb
        outer_b, body_xb = _peler_pourtout(init.conclusion)
        _, body_in = _peler_pourtout(body_xb)
        eqv_in = alpha_pour_tout("y", yb, body_in)
        eqv_lift = congruence_pour_tout(eqv_in, outer_b)
        init = N.modus_ponens(init, equivalence_avant(eqv_lift))   # (∀xb)(∀yb)(…)
    return conjonction_intro(borne, init)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 ASSEMBLAGE v2 — pr₂h-segment + maximalité (via h-graphe) DÉCHARGÉS.
# ════════════════════════════════════════════════════════════════════════════
def maximalite_close_via_est_un_graphe(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { bo(R,E), bo(Rp,F), est_un_graphe(h) }
          ⊢ ( dom h = E ) ou ( pr₂ h = F ).

    `MAX.maximalite_donne_trichotomie_close` (5 hyps) dont les 3 structurelles sont
    déchargées : est_segment(dom h) ← _seg_dom_sans_val_binders [x,y] (CLOS) ;
    est_segment(pr₂h) ← pr2_h_est_segment (TARGET 2, CLOS) ; inclus(h,dom h×pr₂h)
    ← h_inclus_dom_pr2 (TARGET 1, sous est_un_graphe(h)).  Restent {bo,bo,
    est_un_graphe(h)}  (residu_univ_app ÉLIMINÉ)."""
    from bourbaki.cardinaux import ensembles_trichotomie_residuals as RES
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    mdc = MAX.maximalite_donne_trichotomie_close(E_set, R, F_set, Rp)
    seg_dom = E.est_segment(E.dom(h), Rf, vE)
    seg_img = E.est_segment(E.img(h), Rpf, vF)
    hgr = MAX.h_graphe_hyp(E_set, R, F_set, Rp)
    paires = [
        (seg_dom, RES._seg_dom_sans_val_binders(E_set, R, F_set, Rp, "x", "y")),
        (seg_img, pr2_h_est_segment(E_set, R, F_set, Rp)),
        (hgr, h_inclus_dom_pr2(E_set, R, F_set, Rp)),
    ]
    for hyp_f, preuve in paires:
        if hyp_f in set(mdc.hypotheses):
            assert preuve.conclusion == hyp_f, "discharge maximalité mismatch"
            mdc = N.modus_ponens(preuve, N.loi_deduction(hyp_f, mdc))
    return mdc


def maximalite_close_via_est_un_graphe_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : ( dom h = E ) ou ( pr₂ h = F )."""
    return MAX.maximalite_donne_trichotomie_close_cible(E_set, R, F_set, Rp)


def trichotomie_ordinaux_canon_close_v2(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp)  (== maillon_final_cible) SOUS
    { bo(R,E), bo(Rp,F), est_un_graphe(h) }.

    🎯🎯 RÉDUCTION vs `RES.trichotomie_ordinaux_canon_close` (4 hyps) : DEUX résidus
    structurels DÉCHARGÉS.

      • est_segment(pr₂h,Rp,F)[x,w]  ← TARGET 2 (`_pr2_seg_binders`, CLOS) ;
      • MAXIMALITÉ (dom h=E ∨ pr₂h=F)  ← `maximalite_close_via_est_un_graphe` qui,
        DANS la décharge, règle ses 3 hyps structurelles (seg dom CLOS, seg pr₂h CLOS
        via TARGET 2, h_graphe via TARGET 1) en N'INTRODUISANT que est_un_graphe(h).

    HYPOTHÈSES SURVIVANTES (3) : { bo(R,E), bo(Rp,F), est_un_graphe(h) }.  Soit, vs le
    séquent BUT {bo,bo}, l'UNIQUE résidu STRUCTUREL est_un_graphe(h) — l'opacité
    couple-only IRRÉDUCTIBLE de l'axiome de h (cf. h_inclus_dom_pr2), STRICTEMENT plus
    faible que l'ancien h_graphe_hyp.

    🔬 RÉSIDU SUBSISTANT (rapporté, JAMAIS postulé) :
      • est_un_graphe(h) = (∀z)(z∈h ⇒ z couple) : l'axiome de h (axiome_h, theorie_h)
        caractérise UNIQUEMENT (u,v)∈h ⇔ corps — il ne dit RIEN d'un z ARBITRAIRE ∈ h ;
        « tout z∈h est un couple » n'en est PAS dérivable.  C'est l'ex-résidu h_graphe_hyp
        ABAISSÉ à sa forme la plus faible et la plus fidèle (Déf. 1, E.II.37).
      • residu_univ_app est désormais ÉLIMINÉ : son CONTENU géométrique (#8 ∧ #13) est
        DÉRIVÉ de `RES.residu_univ_app_renforce` (CLOS) dès la fusion (cœurs portant
        seg(Sp,R,E)+seg(Tg,Rp,F)).  Il ne reste donc QUE est_un_graphe(h) en sus de {bo,bo}.

    INVARIANT : theorie_ensembles() = 22.  RIEN POSTULÉ.  NON vacueux.  Noms ambiants
    CANONIQUES E,F,R,Rp.  Conclusion == trichotomie_ordinaux_canon.  NE MODIFIE AUCUN
    fichier."""
    from bourbaki.cardinaux import ensembles_trichotomie_residuals as RES
    from bourbaki.cardinaux import ensembles_trichotomie_assemble as A
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis"
    mf = RES.trichotomie_ordinaux_canon_close(E_set, R, F_set, Rp)   # 5 hyps
    # ── DÉCHARGE est_segment(pr₂h,Rp,F)[x,w] (TARGET 2, binders x,w) ──
    seg_img_xw = A._seg_img_form(E_set, R, F_set, Rp, "x", "w")
    if seg_img_xw in set(mf.hypotheses):
        preuve = _pr2_seg_binders(E_set, R, F_set, Rp, "x", "w")
        assert preuve.conclusion == seg_img_xw, "seg(pr₂h)[x,w] ≠ hypothèse de close"
        mf = N.modus_ponens(preuve, N.loi_deduction(seg_img_xw, mf))
    # ── DÉCHARGE la MAXIMALITÉ (dom h=E ∨ pr₂h=F) via le théorème dédié ──
    maxform = A._maximalite_form(E_set, R, F_set, Rp)
    if maxform in set(mf.hypotheses):
        preuve = maximalite_close_via_est_un_graphe(E_set, R, F_set, Rp)
        assert preuve.conclusion == maxform, "maximalité ≠ hypothèse de close"
        mf = N.modus_ponens(preuve, N.loi_deduction(maxform, mf))
    return mf


def trichotomie_ordinaux_canon_close_v2_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : trichotomie_ordinaux_canon(E,R,F,Rp)
    (== maillon_final_cible)."""
    from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP
    return MCP.maillon_final_h_plus3_cible(E_set, R, F_set, Rp)


def trichotomie_ordinaux_canon_close_v2_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 3 HYPOTHÈSES SURVIVANTES ATTENDUES (documentation / test miroir) :
       { bo(R,E), bo(Rp,F), est_un_graphe(h) }.  (residu_univ_app ÉLIMINÉ.)"""
    from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    honnetes = list(FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp))
    return honnetes + [E.est_un_graphe(h)]


__all__ = [
    "pr2_h_est_segment", "pr2_h_est_segment_cible",
    "h_inclus_dom_pr2", "h_inclus_dom_pr2_cible",
    "maximalite_close_via_est_un_graphe", "maximalite_close_via_est_un_graphe_cible",
    "trichotomie_ordinaux_canon_close_v2", "trichotomie_ordinaux_canon_close_v2_cible",
    "trichotomie_ordinaux_canon_close_v2_hypotheses",
]
