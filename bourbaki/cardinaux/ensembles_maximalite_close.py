"""§III.2 — Théorème 3 (TRICHOTOMIE) : MAXIMALITÉ SUBSTANTIELLE — CLÔTURE par
VARIABLE FRAÎCHE (déblocage de la collision τ).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  CLORE `maximalite_donne_trichotomie` (dom h=E ∨ pr₂h=F) jusqu'aux hypothèses
HONNÊTES { bo(R,E), bo(Rp,F), residu_univ_app }.

La preuve antérieure `maximalite_donne_trichotomie_prouve`
(ensembles_maximalite_substantielle) prouvait la conclusion mais laissait 4 RÉSIDU
au TÉMOIN τ a*=τx(min(E∖dom h)), b*=τx(min(F∖pr₂h)).  Le RÉSIDU (3) — l'iso de h⁺*
pour R/Rp — restait OUVERT parce que `iso_hplus_pour_R_majorants_discharges`
(ensembles_maximalite_adjoint_bridge) NE SE CONSTRUIT PAS au témoin τ : le liant
interne x de a*=τx(…) ENTRE EN COLLISION avec les binders fixes du recollement
(extension_iso_depuis_iso_h / image_reunion_graphes / couples).

🔑 LE FIX (cœur de ce module).  On introduit a,b par ÉLIMINATION de ∃ (existe_
elimination) sur l'existence du minimum (Prop 1) — a,b sont alors des variables
ATOMIQUES, SANS liant interne ⇒ AUCUNE collision.  Le pont adjoint↔R se construit
alors à la variable fraîche ; le RÉSIDU (3) est DÉRIVÉ (plus une hypothèse).

Vérifié dans ce module :  iso_hplus_pour_R_majorants_discharges se CONSTRUIT à la
variable fraîche « a » mais LÈVE « modus ponens : mineure ≠ antécédent » au témoin
τ — la collision documentée.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (theorie=22, rien postulé — NE MODIFIE AUCUN fichier existant) :

  🎯🎯 `maximalite_donne_trichotomie_close(E,R,F,Rp)` :
        { bo(R,E), bo(Rp,F), residu_univ_app,                  [ 3 HONNÊTES ]
          est_segment(dom h,R,E), est_segment(pr₂h,Rp,F),      [ Prop 1 ]
          inclus(h, dom h × pr₂h) }                            [ « h graphe », S8 ]
          ⊢  ( dom h = E ) ou ( pr₂ h = F )   ( == maximalite_donne_trichotomie ).

  Les 3 hypothèses structurelles supplémentaires sont TOUTES a,b-INDÉPENDANTES (elles
  survivent à existe_elimination).  Le point décisif : le RÉSIDU (3) (iso de h⁺ pour
  R/Rp), τ-bloqué dans maximalite_donne_trichotomie_prouve, est ici DÉRIVÉ.

  En DÉRIVANT, à la variable FRAÎCHE a (puis b), TOUS les faits structurels
  (« h iso de SEGMENTS », « a,b SOMMETS ») depuis Prop 1 + h_est_iso_prouve + bo :
     • dom h = seg(R,E,a)        ← Prop 1 (a=min(E∖dom h)) ;
     • pr₂ h = seg(Rp,F,b)       ← Prop 1 (b=min(F∖pr₂h)) ;
     • iso(h, seg a, seg b, R, Rp) [capture-free]  ← h_est_iso_prouve + réécriture ;
     • func h                    ← fonctionnel_h_prouve ;
     • a∉dom h, b∉pr₂h, a∈E, b∈F ← min(E∖dom h)/min(F∖pr₂h) ;
     • a sommet de seg a, b sommet de seg b  ← antisymétrie (bo) ;
     • h⟨seg a⟩⊂seg b, seg a⊂dom h, images disjointes  ← valeur/image + b∉pr₂h ;
     • ]←,a], ]←,b] sont des SEGMENTS (clôture-bas, transitivité de bo) ;
     • h⁺ ⊂ ]←,a]×]←,b]          ← h⊂dom h×pr₂h + (a,b).
  Puis RÉSIDU (3) DÉRIVÉ par iso_hplus_pour_R_majorants_discharges (à a,b FRAIS),
  (a,b)∈h par couple_ab_dans_h_residu, a∈dom h par couple_dans_h_donne_antecedent,
  CONTRADICTION avec a∉dom h.  existe_elimination retire b puis a.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Hypothèses HONNÊTES
{bo(R,E), bo(Rp,F), residu_univ_app}.  NON vacueux : la conclusion n'est aucune
hypothèse.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas, tiers_exclu,
    _peler_pourtout, contraposition, dni, dne,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe, alpha_pour_tout, congruence_pour_tout,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux import ensembles_trichotomie_prop1 as P1
from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP
from bourbaki.cardinaux import ensembles_maximalite_substantielle as MS
from bourbaki.cardinaux import ensembles_maximalite_adjoint_bridge as ADJB
from bourbaki.cardinaux import ensembles_trichotomie_extension_iso as EXT
from bourbaki.cardinaux import ensembles_trichotomie_maximalite_preuve as MP
from bourbaki.cardinaux import ensembles_trichotomie_temoin_adjonction as ADJ
from bourbaki.cardinaux.ensembles_segments_construction import seg as _seg, membre_segment
from bourbaki.ensembles.base.ensembles_couples import (
    singleton_membre, couple_egal_implique_composantes,
)
from bourbaki.ensembles.fonctions.ensembles_restriction_somme import membre_reunion_graphes
from bourbaki.ensembles.fonctions.ensembles_valeur_codomaine import couple_valeur_dans_graphe
from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ensembles.ensembles_theoremes import egalite_par_extension


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_maxclose"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b et ⊢ Φ[a] déduit ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.  (ex falso quodlibet, S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P  (via S1)."""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _efq(notP_thm, q):
    """De ⊢¬P, déduire ⊢ (P ⇒ Q)   (ex falso quodlibet ; P⇒¬¬P⇒¬¬Q⇒Q)."""
    P = notP_thm.conclusion.sous[0]
    h = N.loi_deduction(non(q), notP_thm)
    return syllogisme(syllogisme(dni(P), contraposition(h)), dne(q))


def _diff_ssi(e, d, z):
    """⊢ ( z ∈ E∖D ) ⇔ ( z∈E et ¬(z∈D) ).   (AXIOME_DIFF instancié.)"""
    ve, vd, vz = _t(e), _t(d), _t(z)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, ve), vd), vz)


def _find_exists_binder(f):
    """Renvoie le nom du PREMIER liant ∃ rencontré dans la formule f (parcours
    préfixe).  Sert à apparier le liant interne (canonique) des axiomes DOM/IMG."""
    if f.tag == "exists":
        return f.lieur
    for s in f.sous:
        r = _find_exists_binder(s)
        if r:
            return r
    return None


def _de_morgan_ou(thm_neg_ou):
    """De ⊢ ¬(A ∨ B) déduit (⊢ ¬A , ⊢ ¬B)."""
    A, B = thm_neg_ou.conclusion.sous[0].sous
    notA = N.modus_ponens(thm_neg_ou, contraposition(N.s2(A, B)))
    B_imp = syllogisme(N.s2(B, A), N.s3(B, A))
    notB = N.modus_ponens(thm_neg_ou, contraposition(B_imp))
    return notA, notB


# ════════════════════════════════════════════════════════════════════════════
#  DÉRIVATION (à VARIABLE FRAÎCHE) des 9 faits structurels de extension_iso.
#  Chacun est conditionnel à des données NOMMÉES (dom h=seg, pr₂h=seg, b∉pr₂h,
#  a∈E, bo) déchargées dans le théorème final.
# ════════════════════════════════════════════════════════════════════════════
def _iso_capture_free_derive(E_set, R, F_set, Rp, a, b):
    """⊢ { 3 honnêtes,  dom h = seg(R,E,a),  pr₂h = seg(Rp,F,b) }
          ⊢ iso(h, seg(R,E,a), seg(Rp,F,b), R, Rp)  [binders xc,yc].

    RÉÉCRIT h_est_iso_prouve (iso de dom h sur pr₂h, binders x,w) : substitue
    dom h→seg a, pr₂h→seg b (Leibniz) et α-renomme x,w→xc,yc."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    S = _seg(R, E_set, a)
    T = _seg(Rp, F_set, b)

    iso = MS.h_est_iso_prouve(E_set, R, F_set, Rp)        # iso(h, dom h, pr₂h, R,Rp) [3 honnêtes]
    bij = conjonction_elim_gauche(iso)                    # est_bijective(h, dom h, pr₂h)
    co = conjonction_elim_droite(iso)                     # compatible_ordre(h, dom h, R,Rp, x, w)

    Hds = N.assume(egal(domh, S))                         # dom h = seg(R,E,a)
    Hit = N.assume(egal(imgh, T))                         # pr₂h = seg(Rp,F,b)

    bij2 = _leib(domh, S, Hds, lambda w: E.est_bijective(h, w, imgh), bij)
    bij3 = _leib(imgh, T, Hit, lambda w: E.est_bijective(h, S, w), bij2)

    co2 = _leib(domh, S, Hds,
                lambda w: V.compatible_ordre(h, w, Rf, Rpf, x="x", y="w"), co)
    # α-rename binders x,w → xc,yc
    nx, Rx = _peler_pourtout(co2.conclusion)              # nx='x', Rx = ∀w(...)
    nw, body = _peler_pourtout(Rx)                        # nw='w'
    eq_w = alpha_pour_tout("w", "yc", body)
    eq_lift = congruence_pour_tout(eq_w, "x")
    co3 = N.modus_ponens(co2, equivalence_avant(eq_lift)) # compatible(x, yc)
    nx2, Rx2 = _peler_pourtout(co3.conclusion)
    eq_x = alpha_pour_tout("x", "xc", Rx2)
    co4 = N.modus_ponens(co3, equivalence_avant(eq_x))    # compatible(xc, yc)

    res = conjonction_intro(bij3, co4)
    assert res.conclusion == EXT.iso_segments_capture_free(E_set, R, F_set, Rp, a, b)
    return res


def _sommet_de_S_derive(R, E_set, a, y):
    """⊢ { bo(R,E) } ⊢ (∀y)( y∈seg(R,E,a) ⇒ ¬R{a,y} )  [liant y paramétré].

    GÉNÉRIQUE : avec (R,E,a,'ys_') donne hyp_a_sommet_de_S ; avec (Rp,F,b,'qt_')
    donne hyp_b_sommet_de_T (mêmes preuve, binders distincts).

    Pour y∈seg a : R{y,a} et y≠a ; si R{a,y} alors antisym ⇒ a=y, contradiction."""
    Rf = _R_de(R)
    va, vE = _t(a), _t(E_set)
    S = _seg(R, E_set, a)
    vy = var(y)
    Hbo = N.assume(E.est_bien_ordonne(Rf, vE))
    ord_dans = conjonction_elim_gauche(Hbo)
    rel_ordre = conjonction_elim_gauche(ord_dans)
    trans_anti = conjonction_elim_gauche(rel_ordre)
    h_anti = conjonction_elim_droite(trans_anti)          # ordre_antisymetrique(R)
    Hy = N.assume(appartient(vy, S))
    corps = N.modus_ponens(Hy, equivalence_avant(membre_segment(R, E_set, a, y)))
    Rya = conjonction_elim_droite(conjonction_elim_gauche(corps))   # R{y,a}
    y_ne_a = conjonction_elim_droite(corps)               # y≠a
    HRay = N.assume(Rf(va, vy))                           # R{a,y}
    anti = instancie(instancie(h_anti, va), vy)           # (R{a,y} et R{y,a}) ⇒ a=y
    a_eq_y = N.modus_ponens(conjonction_intro(HRay, Rya), anti)
    y_eq_a = N.modus_ponens(a_eq_y, symetrie(va, vy))     # y=a
    falso = _ex_falso(y_eq_a, y_ne_a, non(Rf(va, vy)))
    not_Ray = _refute_self(N.loi_deduction(Rf(va, vy), falso))   # ¬R{a,y}
    res = N.generalisation(y, N.loi_deduction(appartient(vy, S), not_Ray))
    return res


def _a_sommet_de_S_derive(R, E_set, a):
    """⊢ { bo(R,E) } ⊢ hyp_a_sommet_de_S(R,E,a)  (liant « ys_ »)."""
    res = _sommet_de_S_derive(R, E_set, a, "ys_")
    assert res.conclusion == EXT.hyp_a_sommet_de_S(R, E_set, a)
    return res


def _b_sommet_de_T_derive(Rp, F_set, b):
    """⊢ { bo(Rp,F) } ⊢ hyp_b_sommet_de_T(Rp,F,b)  (liant « qt_ »)."""
    res = _sommet_de_S_derive(Rp, F_set, b, "qt_")
    assert res.conclusion == EXT.hyp_b_sommet_de_T(Rp, F_set, b)
    return res


def _S_inclus_dom_h_derive(E_set, R, F_set, Rp, a):
    """⊢ { dom h = seg(R,E,a) } ⊢ (∀x)( x∈seg(R,E,a) ⇒ x∈dom h ).  ( = hyp_S_inclus_dom_h )"""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh = E.dom(h)
    S = _seg(R, E_set, a)
    vx = var("x")
    Hds = N.assume(egal(domh, S))
    Hsd = N.modus_ponens(Hds, symetrie(domh, S))          # S = dom h
    HxS = N.assume(appartient(vx, S))
    x_in_domh = _leib(S, domh, Hsd, lambda w: appartient(vx, w), HxS)
    res = N.generalisation("x", N.loi_deduction(appartient(vx, S), x_in_domh))
    assert res.conclusion == EXT.hyp_S_inclus_dom_h(E_set, R, F_set, Rp, a)
    return res


def _h_envoie_S_dans_T_derive(E_set, R, F_set, Rp, a, b):
    """⊢ { dom h = seg(R,E,a),  pr₂h = seg(Rp,F,b) }
          ⊢ (∀x)( x∈seg(R,E,a) ⇒ h(x)∈seg(Rp,F,b) ).  ( = hyp_h_envoie_S_dans_T )

    Pour x∈S=dom h : (x,h(x))∈h (couple_valeur_dans_graphe) ⇒ h(x)∈pr₂h (AXIOME_IMG)
    = seg b (pr₂h=seg b).  Le liant interne de AXIOME_IMG est apparié par lecture
    (_find_exists_binder) pour éviter la collision avec le τ de valeur(h,x)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    S = _seg(R, E_set, a)
    T = _seg(Rp, F_set, b)
    vx = var("x")
    hx = E.valeur(h, vx)
    HxS = N.assume(appartient(vx, S))
    Hds = N.assume(egal(domh, S))
    Hsd = N.modus_ponens(Hds, symetrie(domh, S))
    x_in_domh = _leib(S, domh, Hsd, lambda w: appartient(vx, w), HxS)
    cvg = couple_valeur_dans_graphe(h, domh, vx)          # (x,h(x))∈h [dom h=dom h, x∈dom h]
    cvg = N.modus_ponens(N.reflexivite(domh), N.loi_deduction(egal(domh, domh), cvg))
    cvg = N.modus_ponens(x_in_domh, N.loi_deduction(appartient(vx, domh), cvg))
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    imgeq = instancie(instancie(ax_img, h), hx)           # h(x)∈pr₂h ⇔ (∃·)((·,h(x))∈h)
    bd = _find_exists_binder(imgeq.conclusion)
    ex = N.modus_ponens(cvg, N.s5(appartient(E.couple(var(bd), hx), h), vx, bd))
    hx_in_img = N.modus_ponens(ex, equivalence_arriere(imgeq))   # h(x)∈pr₂h
    Hit = N.assume(egal(imgh, T))
    hx_in_T = _leib(imgh, T, Hit, lambda w: appartient(hx, w), hx_in_img)   # h(x)∈seg b
    res = N.generalisation("x", N.loi_deduction(appartient(vx, S), hx_in_T))
    assert res.conclusion == EXT.hyp_h_envoie_S_dans_T(E_set, R, F_set, Rp, a, b)
    return res


def _images_disjointes_derive(E_set, R, F_set, Rp, a, b):
    """⊢ { b∉pr₂h }
          ⊢ image(h, dom h) ∩ image({(a,b)}, dom{(a,b)}) = ∅.  ( = hyp_images_disjointes )

    image(h,dom h)=pr₂h, image({(a,b)},dom{(a,b)})=pr₂{(a,b)} (image_dom_egale_img) ;
    un z commun est dans pr₂{(a,b)} ⇒ z=b ⇒ b∈pr₂h, contredisant b∉pr₂h ⇒ ∅."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh = E.dom(h)
    G = ADJ.graphe_point(a, b)
    domG = E.dom(G)
    va, vb = _t(a), _t(b)
    ab = E.couple(va, vb)
    A = E.image(h, domh)
    B = E.image(G, domG)
    inter = E.intersection(A, B)
    vz = var("z")
    Hb_notin = N.assume(non(appartient(vb, E.img(h))))    # b∉pr₂h
    A_eq = MS.image_dom_egale_img(h)                      # image(h,dom h)=pr₂h
    B_eq = MS.image_dom_egale_img(G)                      # image(G,dom G)=pr₂G
    ax_inter = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    inter_eq = instancie(instancie(instancie(ax_inter, A), B), vz)
    Hz = N.assume(appartient(vz, inter))
    zAB = N.modus_ponens(Hz, equivalence_avant(inter_eq))
    zA = conjonction_elim_gauche(zAB)
    zB = conjonction_elim_droite(zAB)
    z_in_prh = _leib(A, E.img(h), A_eq, lambda w: appartient(vz, w), zA)    # z∈pr₂h
    z_in_prG = _leib(B, E.img(G), B_eq, lambda w: appartient(vz, w), zB)    # z∈pr₂G
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    imgGeq = instancie(instancie(ax_img, G), vz)
    ex_xz = N.modus_ponens(z_in_prG, equivalence_avant(imgGeq))             # (∃·)((·,z)∈G)
    bd = _find_exists_binder(imgGeq.conclusion)
    vw = var(bd)
    body = appartient(E.couple(vw, vz), G)
    Hbody = N.assume(body)
    wz_eq_ab = N.modus_ponens(Hbody, equivalence_avant(singleton_membre(E.couple(vw, vz), ab)))
    z_eq_b = conjonction_elim_droite(N.modus_ponens(
        wz_eq_ab, couple_egal_implique_composantes(vw, vz, va, vb)))        # z=b
    b_in_prh = _leib(vz, vb, z_eq_b, lambda u: appartient(u, E.img(h)), z_in_prh)   # b∈pr₂h
    falso = _ex_falso(b_in_prh, Hb_notin, appartient(vz, E.VIDE))
    imp_body = existe_elimination(N.loi_deduction(body, falso), bd)
    z_in_vide = N.modus_ponens(ex_xz, imp_body)
    fwd = N.loi_deduction(appartient(vz, inter), z_in_vide)
    notzV = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)
    bwd = _efq(notzV, appartient(vz, inter))
    char_inter = N.generalisation("z", conjonction_intro(fwd, bwd))
    char_v = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, E.VIDE)), a_implique_a(appartient(vz, E.VIDE))))
    res = egalite_par_extension(char_inter, char_v, inter, E.VIDE)
    assert res.conclusion == EXT.hyp_images_disjointes(E_set, R, F_set, Rp, a, b)
    return res


# ════════════════════════════════════════════════════════════════════════════
#  RÉSIDUS (1)(2) — ]←,a], ]←,b] sont des SEGMENTS  (clôture-bas, transitivité).
# ════════════════════════════════════════════════════════════════════════════
def _segment_ferme_derive(R, E_set, a):
    """⊢ { bo(R,E),  a∈E }  ⊢ est_segment( seg(R,E,a)∪{a}, R, E ).

    ]←,a] = seg(R,E,a)∪{a} est un segment de E :
      • ⊂E : seg⊂E (membre_segment) et a∈E ;
      • clôture-bas : x∈]←,a] (⇒ R{x,a} ou x=a, donc R{x,a}), y∈E, R{y,x}
        ⇒ R{y,a} (transitivité) ⇒ y∈seg (si y≠a) ou y=a ⇒ y∈]←,a]."""
    Rf = _R_de(R)
    va, vE = _t(a), _t(E_set)
    S = _seg(R, E_set, a)
    SaA = V.ensemble_adjoint(S, va)
    sing = E.singleton(va)

    Hbo = N.assume(E.est_bien_ordonne(Rf, vE))
    ord_dans = conjonction_elim_gauche(Hbo)
    rel_ordre = conjonction_elim_gauche(ord_dans)
    trans_anti = conjonction_elim_gauche(rel_ordre)
    h_trans = conjonction_elim_gauche(trans_anti)         # ordre_transitif(R)
    Ha_E = N.assume(appartient(va, vE))

    def car_SaA(z):
        return membre_reunion_graphes(S, sing, z)         # z∈SaA ⇔ (z∈S ou z∈{a})

    # ── (i) SaA ⊂ E ──────────────────────────────────────────────────────────
    zn, _ = _peler_pourtout(inclus(SaA, vE))
    vz = var(zn)
    Hz = N.assume(appartient(vz, SaA))
    disj_z = N.modus_ponens(Hz, equivalence_avant(car_SaA(vz)))
    HzS = N.assume(appartient(vz, S))
    z_in_E_S = conjonction_elim_gauche(conjonction_elim_gauche(
        N.modus_ponens(HzS, equivalence_avant(membre_segment(R, E_set, a, zn)))))
    br1 = N.loi_deduction(appartient(vz, S), z_in_E_S)
    Hza = N.assume(appartient(vz, sing))
    z_eq_a = N.modus_ponens(Hza, equivalence_avant(singleton_membre(vz, va)))
    z_in_E_a = _leib(va, vz, N.modus_ponens(z_eq_a, symetrie(vz, va)),
                     lambda w: appartient(w, vE), Ha_E)
    br2 = N.loi_deduction(appartient(vz, sing), z_in_E_a)
    z_in_E = cas(disj_z, br1, br2)
    incl = N.generalisation(zn, N.loi_deduction(appartient(vz, SaA), z_in_E))   # SaA⊂E

    # ── (ii) clôture-bas : (∀x)(∀y)((x∈SaA et y∈E et R{y,x}) ⇒ y∈SaA) ──────────
    # binders « x », « y » de est_segment
    vx, vy = var("x"), var("y")
    Hpre = N.assume(et(et(appartient(vx, SaA), appartient(vy, vE)), Rf(vy, vx)))
    x_in_SaA = conjonction_elim_gauche(conjonction_elim_gauche(Hpre))
    y_in_E = conjonction_elim_droite(conjonction_elim_gauche(Hpre))
    Ryx = conjonction_elim_droite(Hpre)                   # R{y,x}

    # R{x,a} : x∈seg ⇒ R{x,a} ; x=a ⇒ R{x,a} via réflexivité? non — on a x∈SaA.
    #   x∈seg(R,E,a) ⇒ R{x,a} (membre_segment 2ᵉ conjoint) ;
    #   x=a ⇒ R{x,a}=R{a,a} : réflexivité (bo) sur a∈E.
    refl = conjonction_elim_droite(ord_dans)              # est_reflexive_dans_ordre(R,E)
    Raa = N.modus_ponens(Ha_E, equivalence_arriere(instancie(refl, va)))   # R{a,a}
    disj_x = N.modus_ponens(x_in_SaA, equivalence_avant(car_SaA(vx)))
    HxS = N.assume(appartient(vx, S))
    Rxa_S = conjonction_elim_droite(conjonction_elim_gauche(
        N.modus_ponens(HxS, equivalence_avant(membre_segment(R, E_set, a, "x")))))  # R{x,a}
    br_xS = N.loi_deduction(appartient(vx, S), Rxa_S)
    Hxa = N.assume(appartient(vx, sing))
    x_eq_a = N.modus_ponens(Hxa, equivalence_avant(singleton_membre(vx, va)))
    Rxa_a = _leib(va, vx, N.modus_ponens(x_eq_a, symetrie(vx, va)),
                  lambda w: Rf(w, va), Raa)               # R{x,a}
    br_xa = N.loi_deduction(appartient(vx, sing), Rxa_a)
    Rxa = cas(disj_x, br_xS, br_xa)                       # R{x,a}

    # R{y,a} : transitivité (R{y,x} et R{x,a}) ⇒ R{y,a}
    trans = instancie(instancie(instancie(h_trans, vy), vx), va)
    Rya = N.modus_ponens(conjonction_intro(Ryx, Rxa), trans)   # R{y,a}

    # y∈SaA : cas y=a ⇒ y∈{a}⊂SaA ; y≠a ⇒ y∈seg (y∈E, R{y,a}, y≠a) ⊂ SaA
    def y_in_SaA_from(branch_in_S_or_sing):
        return N.modus_ponens(branch_in_S_or_sing, equivalence_arriere(car_SaA(vy)))
    Hyne = N.assume(non(egal(vy, va)))                    # y≠a
    y_corps = conjonction_intro(conjonction_intro(y_in_E, Rya), Hyne)
    y_in_seg = N.modus_ponens(y_corps, equivalence_arriere(membre_segment(R, E_set, a, "y")))
    y_in_SaA_ne = y_in_SaA_from(N.modus_ponens(y_in_seg,
        N.s2(appartient(vy, S), appartient(vy, sing))))   # y∈(S ou {a})
    br_yne = N.loi_deduction(non(egal(vy, va)), y_in_SaA_ne)
    Hye = N.assume(egal(vy, va))                          # y=a
    y_in_sing = N.modus_ponens(Hye,
                               equivalence_arriere(singleton_membre(vy, va)))   # y∈{a}
    y_in_SaA_e = y_in_SaA_from(N.modus_ponens(y_in_sing,
        syllogisme(N.s2(appartient(vy, sing), appartient(vy, S)),
                   N.s3(appartient(vy, sing), appartient(vy, S)))))     # (S ou {a})
    br_ye = N.loi_deduction(egal(vy, va), y_in_SaA_e)
    y_in_SaA = cas(tiers_exclu(egal(vy, va)), br_ye, br_yne)
    closure_body = N.loi_deduction(
        et(et(appartient(vx, SaA), appartient(vy, vE)), Rf(vy, vx)), y_in_SaA)
    closure = N.generalisation("x", N.generalisation("y", closure_body))

    res = conjonction_intro(incl, closure)
    assert res.conclusion == E.est_segment(SaA, Rf, vE)
    return res


# ════════════════════════════════════════════════════════════════════════════
#  RÉSIDU (10) — h⁺ ⊂ ]←,a]×]←,b],  DÉRIVÉ depuis « h graphe » (inclus(h,dom×img)).
#
#  ⚠️ inclus(h, dom h × pr₂ h) — « h est un graphe » — N'EST PAS dérivable de
#  l'axiome opaque de h (qui ne caractérise QUE les couples (u,v)∈h, jamais un z
#  ARBITRAIRE).  C'est une limitation PRÉ-EXISTANTE, INDÉPENDANTE de la collision
#  τ.  On la PORTE en hypothèse STRUCTURELLE HONNÊTE (a,b-INDÉPENDANTE : elle
#  survit à existe_elimination), JAMAIS postulée.
# ════════════════════════════════════════════════════════════════════════════
def h_graphe_hyp(E_set="E", R="R", F_set="F", Rp="Rp"):
    """La formule « h est un graphe » :  inclus( h, dom h × pr₂ h ).

    HYPOTHÈSE STRUCTURELLE HONNÊTE (a,b-indépendante), fidèle à h={(u,v)∈E×F|…} de
    Bourbaki (S8) mais NON extractible de l'axiome opaque couple-only de h."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return inclus(h, E.produit(E.dom(h), E.img(h)))


def _SxT_inclus_SaA_TbB(R, E_set, Rp, F_set, a, b):
    """⊢ seg(R,E,a)×seg(Rp,F,b) ⊂ (seg(R,E,a)∪{a})×(seg(Rp,F,b)∪{b}).  (INCOND.)

    Monotonie du produit : seg a ⊂ ]←,a], seg b ⊂ ]←,b] (injection gauche de la
    réunion-adjoint), z=(p,q) transporté."""
    from bourbaki.ensembles.familles.ensembles_produit import _instance_produit
    from bourbaki.ensembles.fonctions.ensembles_restriction_somme import membre_reunion_graphes
    va, vb = _t(a), _t(b)
    S = _seg(R, E_set, a)
    T = _seg(Rp, F_set, b)
    SaA = V.ensemble_adjoint(S, va)
    TbB = V.ensemble_adjoint(T, vb)
    vz, vp, vq = var("z"), var("p"), var("q")

    def pt_sub_adjoint(X, x, p):
        car = membre_reunion_graphes(X, E.singleton(x), p)
        return syllogisme(N.s2(appartient(p, X), appartient(p, E.singleton(x))),
                          equivalence_arriere(car))

    instST = _instance_produit(S, T, vz)
    instSaTb = _instance_produit(SaA, TbB, vz)
    bodyST = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, S)), appartient(vq, T))
    Hb = N.assume(bodyST)
    zpq = conjonction_elim_gauche(conjonction_elim_gauche(Hb))
    pS = conjonction_elim_droite(conjonction_elim_gauche(Hb))
    qT = conjonction_elim_droite(Hb)
    pSaA = N.modus_ponens(pS, pt_sub_adjoint(S, va, vp))
    qTbB = N.modus_ponens(qT, pt_sub_adjoint(T, vb, vq))
    conc = conjonction_intro(conjonction_intro(zpq, pSaA), qTbB)
    inner = N.loi_deduction(bodyST, conc)
    mono = monotonie_existe(monotonie_existe(inner, "q"), "p")
    z_imp = syllogisme(equivalence_avant(instST),
                       syllogisme(mono, equivalence_arriere(instSaTb)))
    return N.generalisation("z", z_imp)


def _hplus_inclus_produit_derive(E_set, R, F_set, Rp, a, b):
    """⊢ { inclus(h, dom h × pr₂h),  dom h=seg(R,E,a),  pr₂h=seg(Rp,F,b) }
          ⊢ h⁺ ⊂ (seg(R,E,a)∪{a})×(seg(Rp,F,b)∪{b}).   ( = RÉSIDU (10) )

    z∈h⁺=h∪{(a,b)} ⇒ (z∈h ou z=(a,b)).
      • z∈h : z∈dom h×pr₂h (h graphe) = seg a×seg b (dom h=seg, pr₂h=seg)
              ⊂ ]←,a]×]←,b] (monotonie produit) ;
      • z=(a,b) : (a,b)∈]←,a]×]←,b] (a∈{a}⊂]←,a], b∈{b}⊂]←,b])."""
    from bourbaki.ensembles.fonctions.ensembles_restriction_somme import membre_reunion_graphes
    from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    G = ADJ.graphe_point(a, b)
    hplus = E.reunion(h, G)
    S = _seg(R, E_set, a)
    T = _seg(Rp, F_set, b)
    SaA = V.ensemble_adjoint(S, va)
    TbB = V.ensemble_adjoint(T, vb)
    ab = E.couple(va, vb)
    sing_a, sing_b = E.singleton(va), E.singleton(vb)
    prod_SaTb = E.produit(SaA, TbB)

    H_graph = N.assume(inclus(h, E.produit(domh, imgh)))   # h ⊂ dom h × pr₂h
    Hds = N.assume(egal(domh, S))
    Hit = N.assume(egal(imgh, T))
    h_in_SxT = _leib(domh, S, Hds, lambda w: inclus(h, E.produit(w, imgh)), H_graph)
    h_in_SxT = _leib(imgh, T, Hit, lambda w: inclus(h, E.produit(S, w)), h_in_SxT)   # h⊂seg a×seg b

    SxT_in = _SxT_inclus_SaA_TbB(R, E_set, Rp, F_set, a, b)    # seg a×seg b ⊂ ]←,a]×]←,b]

    zn, _ = _peler_pourtout(inclus(hplus, prod_SaTb))
    vz = var(zn)
    h_to_prod = syllogisme(instancie(h_in_SxT, vz), instancie(SxT_in, vz))   # z∈h ⇒ z∈]←,a]×]←,b]

    # z=(a,b) ⇒ z∈]←,a]×]←,b]
    a_in_sing = N.modus_ponens(N.reflexivite(va), equivalence_arriere(singleton_membre(va, va)))
    a_in_SaA = N.modus_ponens(
        N.modus_ponens(a_in_sing, N.s2(appartient(va, sing_a), appartient(va, S))),
        syllogisme(N.s3(appartient(va, sing_a), appartient(va, S)),
                   equivalence_arriere(membre_reunion_graphes(S, sing_a, va))))
    b_in_sing = N.modus_ponens(N.reflexivite(vb), equivalence_arriere(singleton_membre(vb, vb)))
    b_in_TbB = N.modus_ponens(
        N.modus_ponens(b_in_sing, N.s2(appartient(vb, sing_b), appartient(vb, T))),
        syllogisme(N.s3(appartient(vb, sing_b), appartient(vb, T)),
                   equivalence_arriere(membre_reunion_graphes(T, sing_b, vb))))
    ssi_ab = couple_dans_produit_ssi(va, vb, SaA, TbB)
    ab_in_prod = N.modus_ponens(conjonction_intro(a_in_SaA, b_in_TbB), equivalence_arriere(ssi_ab))
    HzG = N.assume(appartient(vz, G))
    z_eq_ab = N.modus_ponens(HzG, equivalence_avant(singleton_membre(vz, ab)))
    z_in_prod_G = _leib(ab, vz, N.modus_ponens(z_eq_ab, symetrie(vz, ab)),
                        lambda w: appartient(w, prod_SaTb), ab_in_prod)
    G_to_prod = N.loi_deduction(appartient(vz, G), z_in_prod_G)

    car = membre_reunion_graphes(h, G, vz)
    Hz = N.assume(appartient(vz, hplus))
    disj = N.modus_ponens(Hz, equivalence_avant(car))
    z_in_prod = cas(disj, h_to_prod, G_to_prod)
    res = N.generalisation(zn, N.loi_deduction(appartient(vz, hplus), z_in_prod))
    assert res.conclusion == inclus(hplus, prod_SaTb)
    return res


# ════════════════════════════════════════════════════════════════════════════
#  RÉSIDU (3) — l'iso de h⁺ pour R/Rp, DÉRIVÉ à la VARIABLE FRAÎCHE a,b.
#  (Le pont adjoint↔R — iso_hplus_pour_R_majorants_discharges — se CONSTRUIT à
#   variable fraîche ; il LÈVE au témoin τ.  C'est le déblocage de ce module.)
# ════════════════════════════════════════════════════════════════════════════
def _residu3_derive(E_set, R, F_set, Rp, a, b):
    """⊢ { 3 honnêtes,  dom h=seg(R,E,a),  pr₂h=seg(Rp,F,b),  b∉pr₂h,  a∉dom h,
           a∈E,  b∈F,  bo(R,E),  bo(Rp,F),  h⁺⊂]←,a]×]←,b],  dom h⁺=]←,a] }
          ⊢ iso( h⁺, ]←,a], ]←,b], R, Rp )  [binders px,pw]  ( = RÉSIDU (3) ).

    DÉRIVE iso_hplus_pour_R_majorants_discharges (à a,b FRAIS) en DÉCHARGEANT ses
    9 faits structurels d'extension par les preuves de ce module."""
    out = ADJB.iso_hplus_pour_R_majorants_discharges(E_set, R, F_set, Rp, a, b)
    discharges = [
        (EXT.iso_segments_capture_free(E_set, R, F_set, Rp, a, b),
         _iso_capture_free_derive(E_set, R, F_set, Rp, a, b)),
        (E.est_fonctionnel(TS.h_iso_max(E_set, R, F_set, Rp)),
         MCP.fonctionnel_h_prouve(E_set, R, F_set, Rp)),
        (EXT.hyp_h_envoie_S_dans_T(E_set, R, F_set, Rp, a, b),
         _h_envoie_S_dans_T_derive(E_set, R, F_set, Rp, a, b)),
        (EXT.hyp_S_inclus_dom_h(E_set, R, F_set, Rp, a),
         _S_inclus_dom_h_derive(E_set, R, F_set, Rp, a)),
        (EXT.hyp_images_disjointes(E_set, R, F_set, Rp, a, b),
         _images_disjointes_derive(E_set, R, F_set, Rp, a, b)),
        (EXT.hyp_a_sommet_de_S(R, E_set, a),
         _a_sommet_de_S_derive(R, E_set, a)),
        (EXT.hyp_b_sommet_de_T(Rp, F_set, b),
         _b_sommet_de_T_derive(Rp, F_set, b)),
    ]
    for form, preuve in discharges:
        assert preuve.conclusion == form, "discharge ext mismatch"
        out = N.modus_ponens(preuve, N.loi_deduction(form, out))
    return out


# ════════════════════════════════════════════════════════════════════════════
#  EXTRACTION du MINIMUM à VARIABLE FRAÎCHE (cœur du fix : a atomique, sans τ).
# ════════════════════════════════════════════════════════════════════════════
def _corps_min(R, e_set, d_term, a, w="w"):
    """Le corps de Prop 1 au LIANT a (variable fraîche) :
        est_plus_petit_element(R, E∖D, a)  et  D = seg(R,E,a)."""
    Rf = _R_de(R)
    ve, vd, va = _t(e_set), _t(d_term), var(a)
    DmD = E.difference(ve, vd)
    petit = et(appartient(va, DmD),
               pourtout(w, impl(appartient(var(w), DmD), Rf(va, var(w)))))
    return et(petit, egal(vd, _seg(R, e_set, var(a))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 LE THÉORÈME — maximalité substantielle CLOSE par variable fraîche.
# ════════════════════════════════════════════════════════════════════════════
def maximalite_donne_trichotomie_close(E_set="E", R="R", F_set="F", Rp="Rp"):
    """🎯🎯 ⊢ { bo(R,E), bo(Rp,F), residu_univ_app           [ 3 HONNÊTES ]
               est_segment(dom h, R, E), est_segment(pr₂h, Rp, F),
               inclus(h, dom h × pr₂h)                       [ 3 STRUCTURELS a,b-INDÉP. ] }
          ⊢ ( dom h = E )  ou  ( pr₂ h = F )   ( == maximalite_donne_trichotomie ).

    🔑 FIX par VARIABLE FRAÎCHE.  PAR L'ABSURDE : ¬(dom h=E ∨ pr₂h=F) ⇒ dom h≠E ∧
    pr₂h≠F.  Prop 1 donne ∃a(a=min(E∖dom h) ∧ dom h=seg(R,E,a)) ; existe_elimination
    introduit a comme variable ATOMIQUE (sans liant interne ⇒ AUCUNE collision avec
    les binders du recollement — contrairement au témoin τx(…)).  Idem b.

    À a,b FRAIS, on DÉRIVE le RÉSIDU (3) (iso de h⁺ pour R/Rp) par le pont adjoint↔R,
    puis (a,b)∈h, a∈dom h — CONTREDIT a∉dom h.  existe_elimination retire b puis a.

    🎯 RÉSOLUTION τ (le cœur de ce module) : iso_hplus_pour_R_majorants_discharges
    se CONSTRUIT ici à la variable a fraîche, là où il LÈVE « modus ponens : mineure ≠
    antécédent » au témoin τx(…) (collision documentée dans
    ensembles_maximalite_adjoint_bridge).  Le RÉSIDU (3), qui restait OUVERT dans
    maximalite_donne_trichotomie_prouve (4 RÉSIDU au témoin τ, (3) τ-bloqué), est ici
    DÉRIVÉ.  Les RÉSIDU (1),(2) (segments fermés ]←,a],]←,b]) et (10) (h⁺⊂]←,a]×]←,b])
    sont AUSSI dérivés (les deux derniers depuis « h graphe »).

    HYPOTHÈSES SURVIVANTES (6, toutes a,b-INDÉPENDANTES) :
      • 3 HONNÊTES : bo(R,E), bo(Rp,F), residu_univ_app (portées par func h /
        h_est_iso_prouve / Prop 1) ;
      • est_segment(dom h, R, E), est_segment(pr₂h, Rp, F) : « dom h, pr₂h sont des
        segments » (Prop 1 ; déjà résidus de maximalite_donne_trichotomie_prouve) ;
      • inclus(h, dom h × pr₂h) : « h est un graphe » (= h_graphe_hyp), fidèle à
        h={(u,v)∈E×F|…} (S8) mais NON extractible de l'axiome opaque couple-only de h.
        C'est l'ex-RÉSIDU (10), abaissé à cette UNIQUE structurelle a,b-indépendante
        (au lieu d'une formule h⁺⊂]←,a]×]←,b] au témoin, qui bloquait l'élimination).

    INVARIANT : theorie_ensembles() = 22.  Rien postulé.  NON vacueux : la conclusion
    n'est aucune hypothèse."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis"
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    D = ou(egal(domh, vE), egal(imgh, vF))

    Hneg = N.assume(non(D))
    not_dom_E, not_img_F = _de_morgan_ou(Hneg)

    p1a = P1.prop1_segment_propre(R, E_set, domh, x="a", w="w")
    p1a = N.modus_ponens(not_dom_E, N.loi_deduction(non(egal(domh, vE)), p1a))
    body_a = _corps_min(R, E_set, domh, "a")
    va = var("a")

    Ha = N.assume(body_a)
    petit_a = conjonction_elim_gauche(Ha)
    dom_eq_seg = conjonction_elim_droite(Ha)
    a_in_diff = conjonction_elim_gauche(petit_a)
    a_split = N.modus_ponens(a_in_diff, equivalence_avant(_diff_ssi(vE, domh, va)))
    a_in_E = conjonction_elim_gauche(a_split)
    a_not_dom = conjonction_elim_droite(a_split)

    p1b = P1.prop1_segment_propre(Rp, F_set, imgh, x="b", w="w")
    p1b = N.modus_ponens(not_img_F, N.loi_deduction(non(egal(imgh, vF)), p1b))
    body_b = _corps_min(Rp, F_set, imgh, "b")
    vb = var("b")

    Hb = N.assume(body_b)
    petit_b = conjonction_elim_gauche(Hb)
    img_eq_seg = conjonction_elim_droite(Hb)
    b_in_diff = conjonction_elim_gauche(petit_b)
    b_split = N.modus_ponens(b_in_diff, equivalence_avant(_diff_ssi(vF, imgh, vb)))
    b_in_F = conjonction_elim_gauche(b_split)
    b_not_img = conjonction_elim_droite(b_split)

    couple_in_h = MS.couple_ab_dans_h_residu(E_set, R, F_set, Rp, "a", "b")

    S = _seg(R, E_set, "a")
    T = _seg(Rp, F_set, "b")
    SaA = V.ensemble_adjoint(S, va)
    TbB = V.ensemble_adjoint(T, vb)
    seg1 = _segment_ferme_derive(R, E_set, "a")
    seg2 = _segment_ferme_derive(Rp, F_set, "b")
    couple_in_h = N.modus_ponens(seg1,
        N.loi_deduction(E.est_segment(SaA, Rf, vE), couple_in_h))
    couple_in_h = N.modus_ponens(seg2,
        N.loi_deduction(E.est_segment(TbB, Rpf, vF), couple_in_h))

    res3 = _residu3_derive(E_set, R, F_set, Rp, "a", "b")
    iso3_form = V.est_isomorphisme_ordre(
        EXT._hplus(E_set, R, F_set, Rp, "a", "b"), SaA, TbB, Rf, Rpf, x="px", y="pw")
    assert res3.conclusion == iso3_form
    couple_in_h = N.modus_ponens(res3, N.loi_deduction(iso3_form, couple_in_h))

    func_h = MCP.fonctionnel_h_prouve(E_set, R, F_set, Rp)
    couple_in_h = N.modus_ponens(dom_eq_seg,
        N.loi_deduction(egal(domh, S), couple_in_h))
    couple_in_h = N.modus_ponens(a_in_E, N.loi_deduction(appartient(va, vE), couple_in_h))
    couple_in_h = N.modus_ponens(b_in_F, N.loi_deduction(appartient(vb, vF), couple_in_h))
    couple_in_h = N.modus_ponens(func_h, N.loi_deduction(E.est_fonctionnel(h), couple_in_h))
    couple_in_h = N.modus_ponens(a_not_dom,
        N.loi_deduction(non(appartient(va, domh)), couple_in_h))
    # — DÉCHARGE des hyps de RÉSIDU (3) hissées : pr₂h=seg b, b∉pr₂h, dom h⁺=]←,a] —
    couple_in_h = N.modus_ponens(img_eq_seg,
        N.loi_deduction(egal(imgh, T), couple_in_h))           # pr₂h = seg(Rp,F,b)
    couple_in_h = N.modus_ponens(b_not_img,
        N.loi_deduction(non(appartient(vb, imgh)), couple_in_h))   # b∉pr₂h
    #   dom h⁺=]←,a] DÉRIVÉ de dom h=seg(R,E,a) (Prop 1) par _dom_hplus_eq_Saa
    dom_hplus = MS._dom_hplus_eq_Saa(E_set, R, F_set, Rp, "a", "b")   # [dom h=seg(R,E,a)]
    dom_hplus = N.modus_ponens(dom_eq_seg,
        N.loi_deduction(egal(domh, S), dom_hplus))             # dom h⁺=]←,a]  (sans hyp dom=seg)
    dom_hplus_form = egal(E.dom(EXT._hplus(E_set, R, F_set, Rp, "a", "b")), SaA)
    assert dom_hplus.conclusion == dom_hplus_form
    couple_in_h = N.modus_ponens(dom_hplus,
        N.loi_deduction(dom_hplus_form, couple_in_h))          # décharge dom h⁺=]←,a]
    # — DÉCHARGE (10) — h⁺⊂]←,a]×]←,b], DÉRIVÉ de « h graphe » (inclus(h,dom×img)) —
    #   APRÈS res3 (qui ré-introduit (10) parmi les hyps du pont) : MP décharge TOUTES
    #   les occurrences.  L'hypothèse h-graphe restante est a,b-INDÉPENDANTE ⇒ SURVIT à
    #   existe_elimination (c'est le RÉSIDU honnête final, h={(u,v)∈E×F|…} de Bourbaki).
    res10 = _hplus_inclus_produit_derive(E_set, R, F_set, Rp, "a", "b")
    res10_form = inclus(EXT._hplus(E_set, R, F_set, Rp, "a", "b"), E.produit(SaA, TbB))
    assert res10.conclusion == res10_form
    couple_in_h = N.modus_ponens(res10, N.loi_deduction(res10_form, couple_in_h))
    #   res10 hisse aussi dom h=seg, pr₂h=seg : les redécharger
    couple_in_h = N.modus_ponens(dom_eq_seg,
        N.loi_deduction(egal(domh, S), couple_in_h))
    couple_in_h = N.modus_ponens(img_eq_seg,
        N.loi_deduction(egal(imgh, T), couple_in_h))

    ab_in_h_form = appartient(E.couple(va, vb), h)
    a_in_dom = MP.couple_dans_h_donne_antecedent(E_set, R, F_set, Rp, "a", "b")
    a_in_dom = N.modus_ponens(couple_in_h, N.loi_deduction(ab_in_h_form, a_in_dom))
    D_falso = _ex_falso(a_in_dom, a_not_dom, D)

    imp_b = N.loi_deduction(body_b, D_falso)
    elim_b = existe_elimination(imp_b, "b")
    D_after_b = N.modus_ponens(p1b, elim_b)
    imp_a = N.loi_deduction(body_a, D_after_b)
    elim_a = existe_elimination(imp_a, "a")
    D_after_a = N.modus_ponens(p1a, elim_a)

    from bourbaki.logique.tactiques.tactiques_abrege2 import dne, mono_gauche
    imp = N.loi_deduction(non(D), D_after_a)
    return N.modus_ponens(imp, syllogisme(mono_gauche(dne(D), D), N.s1(D)))


def maximalite_donne_trichotomie_close_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : ( dom h = E ) ou ( pr₂ h = F )."""
    return M.maximalite_donne_trichotomie(E_set, R, F_set, Rp)


def maximalite_donne_trichotomie_close_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 6 HYPOTHÈSES SURVIVANTES (documentation / test miroir) :
       3 HONNÊTES + est_segment(dom h,R,E) + est_segment(pr₂h,Rp,F) + h_graphe_hyp.
       Toutes a,b-INDÉPENDANTES."""
    from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    honnetes = FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp)
    return list(honnetes) + [
        E.est_segment(E.dom(h), Rf, vE),
        E.est_segment(E.img(h), Rpf, vF),
        h_graphe_hyp(E_set, R, F_set, Rp),
    ]


__all__ = [
    "h_graphe_hyp",
    "maximalite_donne_trichotomie_close",
    "maximalite_donne_trichotomie_close_cible",
    "maximalite_donne_trichotomie_close_hypotheses",
]
