"""§III.2 — Théorème 3 (TRICHOTOMIE) : pr₂(h) est un SEGMENT de F (initialité).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  MIROIR de `ensembles_trichotomie_dom_segment` côté IMAGE : l'iso MAXIMAL h
a pour image T₀ := pr₂(h) ; la borne pr₂(h)⊂F est INCONDITIONNELLE
(M.h_img_inclus_F) ; ce module fournit la clause d'INITIALITÉ manquante, qui,
conjointe à la borne, DONNE est_segment(pr₂ h, R', F).

IDÉE (fidèle Bourbaki, image).  t∈pr₂h ⇒ (∃x)((x,t)∈h) ⇒ (h_membre_donne_temoin)
il existe un segment S de E, un segment T de F, un iso φ:S≅T avec x∈S, t=φ(x).
Si u∈F et u≤'t, alors t=φ(x)∈T, par INITIALITÉ de T (T segment de F) u∈T, et par
SURJECTIVITÉ de φ il existe p∈S avec φ(p)=u.  Alors (p,u)∈h (couple_iso_dans_h),
donc u∈pr₂h.

LE MAILLON NON PORTÉ par le scaffold — même philosophie que `val_dans_F` du
modèle : les pas « t=φ(x)∈T » (structure de graphe de φ), « u∈T » (initialité de
T appliquée) et « ∃p∈S⊂E, φ(p)=u » (surjectivité de la bijection φ:S→T) sont
ABSORBÉS d'un bloc dans UNE hypothèse explicite ∀-close, VRAIE, JAMAIS postulée :

    temoin_dans_S(E,R,F,Rp) :=
      (∀u)(∀t)(∀xt)(∀S)(∀T)(∀φ)(
          ( u∈F et est_segment(S,R,E) et est_segment(T,Rp,F)
            et est_isomorphisme_ordre(φ,S,T,R,Rp) et xt∈S
            et t=valeur(φ,xt) et Rp{u,t} )
        ⇒ (∃pz)( (pz∈S et pz∈E) et valeur(φ,pz)=u ) ).

C'est VRAI : t=φ(xt)∈T (φ⊂S×T), u∈T par initialité du segment T (u∈F, u≤'t∈T),
p:=φ⁻¹(u)∈S par surjectivité de la bijection φ:S→T, et p∈E par S⊂E.  Dérivable
plus tard de la décomposition de est_bijective (même sort que val_dans_F / pont
R2 renforcé) — reporté comme hypothèse, jamais comme théorème.

CE MODULE LIVRE (conditionnel, honnête, theorie=22) :
  • img_h_initial_sous_temoin    : sous {temoin_dans_S} ⊢ initialité de pr₂(h).
  • img_h_est_segment_sous_temoin: sous {temoin_dans_S} ⊢ est_segment(pr₂h,R',F).
    (la borne pr₂(h)⊂F est INCONDITIONNELLE, M.h_img_inclus_F.)

⚠️ LIANTS (hérités du modèle) : le ∃ natif de AXIOME_IMG est sur « x » — le
témoin première-coordonnée s'appelle donc « x » (coïncidence obligatoire, cf.
h_img_inclus_F) ; le ∃-témoin de surjectivité s'appelle « pz » (≠ « y » τ-liant de valeur, ≠ « pw » liant interne d'iso) ; universelles exotiques (ta, ua).
INVARIANT : theorie_ensembles() = 22.  Rien postulé.  NON vacueux.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.maximalite import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_dom_segment import _coeur_temoin


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _inst_img(g, y):
    """⊢ (y ∈ pr₂ G) ⇔ (∃x)((x,y) ∈ G).   (le ∃ natif est sur le liant « x ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, g), y)


# ════════════════════════════════════════════════════════════════════════════
#  HYPOTHÈSE DE SURJECTIVITÉ-TÉMOIN (EXPLICITE) — le maillon non porté, côté image.
# ════════════════════════════════════════════════════════════════════════════
def temoin_dans_S(E_set="E", R="R", F_set="F", Rp="Rp",
                  u="u", t="t", xt="xt", S="S", T="T", phi="phi", pw="pz"):
    """FORMULE de SURJECTIVITÉ-TÉMOIN des isos témoins de h (cf. en-tête) :

        (∀u)(∀t)(∀xt)(∀S)(∀T)(∀φ)( ( u∈F et seg(S,R,E) et seg(T,Rp,F)
            et iso(φ,S,T) et xt∈S et t=valeur(φ,xt) et Rp{u,t} )
          ⇒ (∃pz)( (pz∈S et pz∈E) et valeur(φ,pz)=u ) )."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vu, vt, vxt = var(u), var(t), var(xt)
    vS, vT, vphi, vpw = var(S), var(T), var(phi), var(pw)
    premisse = et(et(et(et(et(et(
        appartient(vu, vF),
        E.est_segment(vS, Rf, vE)),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw")),
        appartient(vxt, vS)),
        egal(vt, E.valeur(vphi, vxt))),
        Rpf(vu, vt))
    corps = et(et(appartient(vpw, vS), appartient(vpw, vE)),
               egal(E.valeur(vphi, vpw), vu))
    return pourtout(u, pourtout(t, pourtout(xt, pourtout(S, pourtout(T, pourtout(phi,
        impl(premisse, existe(pw, corps))))))))


# ════════════════════════════════════════════════════════════════════════════
#  Clause d'INITIALITÉ de pr₂(h)  —  CONDITIONNEL à temoin_dans_S.
# ════════════════════════════════════════════════════════════════════════════
def img_h_initial_sous_temoin(E_set="E", R="R", F_set="F", Rp="Rp",
                              t="ta", u="ua", S="S", T="T", phi="phi",
                              via_pont=False):
    """⊢ { temoin_dans_S } ⊢ (∀t)(∀u)( (t∈pr₂h et u∈F et R'{u,t}) ⇒ u∈pr₂h ).

    MIROIR de dom_h_initial_sous_val : t∈pr₂h ⇒ (∃x)((x,t)∈h) ⇒ témoin
    (S,T,φ;x,t) ; temoin_dans_S fournit p∈S⊂E avec φ(p)=u ; couple_iso_dans_h
    donne (p,u)∈h, d'où u∈pr₂h.  CONDITIONNEL, theorie=22, NON vacueux.

    via_pont=True : le ∃-témoin est DÉRIVÉ (temoin_surjectif_dans_S, pont_val)
    et coupé contre les 8 conjoints déjà pelés du coeur — temoin_dans_S ne
    figure plus au séquent ; le théorème devient CLOS."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vt, vu = var(t), var(u)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    # témoin première coordonnée : « x » = liant NATIF du ∃ de AXIOME_IMG.
    xw = "x"
    vxw = var(xw)

    # ════════ sous le coeur témoin (S,T,φ ; x, t), démontrer u∈pr₂h ════════
    coeur = _coeur_temoin(E_set, R, F_set, Rp, vxw, vt, S, T, phi)
    Hcoeur = N.assume(coeur)
    Hgraph = conjonction_elim_droite(Hcoeur)                   # φ⊂S×T
    r_app = conjonction_elim_gauche(Hcoeur)
    Hdom = conjonction_elim_droite(r_app)                      # dom(φ)=S
    r_app = conjonction_elim_gauche(r_app)
    Hfunc = conjonction_elim_droite(r_app)                     # est_fonctionnel(φ)
    Hc5 = conjonction_elim_gauche(r_app)
    c4 = conjonction_elim_gauche(Hc5)
    Hx_in_S = conjonction_elim_droite(c4)                      # x∈S
    c3 = conjonction_elim_gauche(c4)
    Hiso = conjonction_elim_droite(c3)                         # iso(φ,S,T)
    c2 = conjonction_elim_gauche(c3)
    Hseg_T = conjonction_elim_droite(c2)                       # est_segment(T,Rp,F)
    Hseg_S = conjonction_elim_gauche(c2)                       # est_segment(S,R,E)
    Ht_eq = conjonction_elim_droite(Hc5)                       # t = valeur(φ,x)

    vS, vT, vphi = var(S), var(T), var(phi)
    Hu_in_F = N.assume(appartient(vu, vF))                     # u∈F
    HRut = N.assume(Rpf(vu, vt))                               # R'{u,t}

    # ── ∃pw((pw∈S et pw∈E) et φ(pw)=u) : DÉRIVÉ (pont) ou temoin_dans_S ──
    if via_pont:
        from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_pont_val import temoin_surjectif_dans_S
        Hex_p = temoin_surjectif_dans_S(E_set, R, F_set, Rp, u, t, xw, S, T, phi)
        for hyp_f, preuve_h in [                    # coupes contre le coeur pelé
            (inclus(vphi, E.produit(vS, vT)), Hgraph),
            (egal(E.dom(vphi), vS), Hdom),
            (E.est_fonctionnel(vphi), Hfunc),
            (appartient(vxw, vS), Hx_in_S),
            (egal(vt, E.valeur(vphi, vxw)), Ht_eq),
            (E.est_segment(vS, Rf, vE), Hseg_S),
            (E.est_segment(vT, Rpf, vF), Hseg_T),
            (V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw"), Hiso),
        ]:
            Hex_p = N.modus_ponens(preuve_h, N.loi_deduction(hyp_f, Hex_p))
        # Hex_p : {coeur, u∈F, R'{u,t}} ⊢ (∃pz)(corps) — temoin_dans_S ABSENTE
    else:
        Htem = N.assume(temoin_dans_S(E_set, R, F_set, Rp))
        tem_inst = instancie(instancie(instancie(instancie(instancie(instancie(
            Htem, vu), vt), vxw), vS), vT), vphi)
        premisse_tem = conjonction_intro(conjonction_intro(conjonction_intro(
            conjonction_intro(conjonction_intro(conjonction_intro(
                Hu_in_F, Hseg_S), Hseg_T), Hiso), Hx_in_S), Ht_eq), HRut)
        Hex_p = N.modus_ponens(premisse_tem, tem_inst)         # (∃pw)(corps)

    # ── sous le corps témoin pw, (pw,u)∈h puis u∈pr₂h ──
    vpw = var("pz")
    corps_pw = et(et(appartient(vpw, vS), appartient(vpw, vE)),
                  egal(E.valeur(vphi, vpw), vu))
    Hcorps = N.assume(corps_pw)
    Hp_in_S = conjonction_elim_gauche(conjonction_elim_gauche(Hcorps))   # pw∈S
    Hp_in_E = conjonction_elim_droite(conjonction_elim_gauche(Hcorps))   # pw∈E
    Hphi_p_eq_u = conjonction_elim_droite(Hcorps)                        # φ(pw)=u
    # u = φ(pw)  (couple_iso_dans_h attend la valeur à droite)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
    Hu_eq = N.modus_ponens(Hphi_p_eq_u, symetrie(E.valeur(vphi, vpw), vu))  # u=φ(pw)

    cid = TS.couple_iso_dans_h(E_set, R, F_set, Rp, S, T, phi, "pz", u)
    preuves = [
        (E.est_segment(vS, Rf, vE), Hseg_S),
        (E.est_segment(vT, Rpf, vF), Hseg_T),
        (V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw"), Hiso),
        (appartient(vpw, vS), Hp_in_S),
        (appartient(vpw, vE), Hp_in_E),
        (appartient(vu, vF), Hu_in_F),
        (egal(vu, E.valeur(vphi, vpw)), Hu_eq),
        (E.est_fonctionnel(vphi), Hfunc),
        (egal(E.dom(vphi), vS), Hdom),
        (inclus(vphi, E.produit(vS, vT)), Hgraph),
    ]
    couple_in_h = cid
    for hyp_f, preuve in preuves:
        couple_in_h = N.modus_ponens(preuve, N.loi_deduction(hyp_f, couple_in_h))
    # couple_in_h : {coeur, u∈F, R'{u,t}, corps_pw, temoin} ⊢ (pw, u) ∈ h

    # ── (∃x)((x,u)∈h)  (liant natif « x »)  puis  u∈pr₂h ──
    body_ex = appartient(E.couple(vxw, vu), h)                 # (x,u)∈h  (x liant)
    ex_x = N.modus_ponens(couple_in_h, N.s5(body_ex, vpw, xw)) # (∃x)((x,u)∈h)
    img_eq_u = _inst_img(h, vu)                                # u∈pr₂h ⇔ (∃x)((x,u)∈h)
    u_in_img_pw = N.modus_ponens(ex_x, equivalence_arriere(img_eq_u))    # u∈pr₂h [corps_pw,…]

    # ── éliminer pw : corps_pw ⇒ u∈pr₂h, puis (∃pw)corps ⇒ u∈pr₂h, MP avec Hex_p ──
    imp_pw = N.loi_deduction(corps_pw, u_in_img_pw)
    ex_pw_to_img = existe_elimination(imp_pw, "pz")
    u_in_img = N.modus_ponens(Hex_p, ex_pw_to_img)             # u∈pr₂h [coeur,u∈F,R',tem]

    # ════════ décharger le coeur, puis éliminer φ, T, S ════════
    imp_coeur = N.loi_deduction(coeur, u_in_img)
    imp_phi = existe_elimination(imp_coeur, phi)
    imp_T = existe_elimination(imp_phi, T)
    imp_S = existe_elimination(imp_T, S)                       # (∃S∃T∃φ)coeur ⇒ u∈pr₂h

    # ════════ raccord à (x,t)∈h via h_membre_donne_temoin, puis (∃x)((x,t)∈h) ════════
    hdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    couple_imp = instancie(instancie(hdt, vxw), vt)            # (x,t)∈h ⇒ (∃S∃T∃φ)coeur(…;x,t)
    cx_to_img = syllogisme(couple_imp, imp_S)                  # (x,t)∈h ⇒ u∈pr₂h
    ex_x_to_img = existe_elimination(cx_to_img, xw)            # (∃x)((x,t)∈h) ⇒ u∈pr₂h
    img_eq_t = _inst_img(h, vt)                                # t∈pr₂h ⇔ (∃x)((x,t)∈h)
    t_to_img = syllogisme(equivalence_avant(img_eq_t), ex_x_to_img)   # t∈pr₂h ⇒ u∈pr₂h

    # ════════ assembler la prémisse de est_segment : (t∈pr₂h et u∈F) et R'{u,t} ════════
    imp1 = N.loi_deduction(Rpf(vu, vt), t_to_img)
    imp2 = N.loi_deduction(appartient(vu, vF), imp1)
    premisse_seg = et(et(appartient(vt, E.img(h)), appartient(vu, vF)), Rpf(vu, vt))
    Hprem = N.assume(premisse_seg)
    Ht_img = conjonction_elim_gauche(conjonction_elim_gauche(Hprem))
    Hu_F2 = conjonction_elim_droite(conjonction_elim_gauche(Hprem))
    HRut2 = conjonction_elim_droite(Hprem)
    step = N.modus_ponens(HRut2, N.modus_ponens(Hu_F2, imp2))  # t∈pr₂h ⇒ u∈pr₂h
    u_in_img_final = N.modus_ponens(Ht_img, step)              # u∈pr₂h
    body = N.loi_deduction(premisse_seg, u_in_img_final)
    return N.generalisation(t, N.generalisation(u, body))


def img_h_initial_cible(E_set="E", R="R", F_set="F", Rp="Rp", t="ta", u="ua"):
    """ÉNONCÉ-cible (test miroir) de la clause d'initialité de pr₂(h)."""
    Rpf = _R_de(Rp)
    vF = _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vt, vu = var(t), var(u)
    return pourtout(t, pourtout(u,
        impl(et(et(appartient(vt, E.img(h)), appartient(vu, vF)), Rpf(vu, vt)),
             appartient(vu, E.img(h)))))


# ════════════════════════════════════════════════════════════════════════════
#  pr₂(h) est un SEGMENT de F  —  CONDITIONNEL à temoin_dans_S.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.26-29 | PDF p.124  (démonstration du Th. 3 : l'image de l'iso maximal est un segment de F — le pendant image du « S est un segment de E »)
def img_h_est_segment_sous_temoin(E_set="E", R="R", F_set="F", Rp="Rp",
                                  t="ta", u="ua", S="S", T="T", phi="phi"):
    """⊢ { temoin_dans_S } ⊢ est_segment(pr₂ h, R', F).

    Conjonction de la borne pr₂(h)⊂F (INCONDITIONNELLE, M.h_img_inclus_F) et de
    la clause d'initialité (conditionnelle à temoin_dans_S).  theorie=22."""
    incl = M.h_img_inclus_F(E_set, R, F_set, Rp)               # pr₂(h) ⊂ F (INCOND.)
    init = img_h_initial_sous_temoin(E_set, R, F_set, Rp, t, u, S, T, phi)
    return conjonction_intro(incl, init)


def img_h_est_segment_cible(E_set="E", R="R", F_set="F", Rp="Rp", t="ta", u="ua"):
    """ÉNONCÉ-cible (test miroir) : est_segment(pr₂ h, R', F) avec binders (t,u)."""
    Rpf = _R_de(Rp)
    vF = _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_segment(E.img(h), Rpf, vF, t, u)


# ════════════════════════════════════════════════════════════════════════════
#  Versions PROUVÉES (pont) — temoin_dans_S DÉRIVÉE, théorèmes CLOS.
# ════════════════════════════════════════════════════════════════════════════
def img_h_initial_prouve(E_set="E", R="R", F_set="F", Rp="Rp",
                         t="ta", u="ua", S="S", T="T", phi="phi"):
    """⊢ (∀t)(∀u)( (t∈pr₂h et u∈F et R'{u,t}) ⇒ u∈pr₂h ).            [CLOS]"""
    res = img_h_initial_sous_temoin(E_set, R, F_set, Rp, t, u, S, T, phi,
                                    via_pont=True)
    assert res.conclusion == img_h_initial_cible(E_set, R, F_set, Rp, t, u), \
        "img_h_initial_prouve : conclusion inattendue"
    assert res.est_clos, "img_h_initial_prouve : hypothèses résiduelles"
    return res


def img_h_est_segment_prouve(E_set="E", R="R", F_set="F", Rp="Rp",
                             t="ta", u="ua", S="S", T="T", phi="phi"):
    """⊢ est_segment(pr₂ h, R', F).                                   [CLOS]"""
    incl = M.h_img_inclus_F(E_set, R, F_set, Rp)
    init = img_h_initial_prouve(E_set, R, F_set, Rp, t, u, S, T, phi)
    res = conjonction_intro(incl, init)
    assert res.conclusion == img_h_est_segment_cible(E_set, R, F_set, Rp, t, u), \
        "img_h_est_segment_prouve : conclusion inattendue"
    assert res.est_clos, "img_h_est_segment_prouve : hypothèses résiduelles"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 LA COUPE — le segment-image de _min REMPLACÉ par temoin_dans_S.
# ════════════════════════════════════════════════════════════════════════════
def trichotomie_ordinaux_canon_prouve_min2(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp) sous les 5 hypothèses
       { bo(R,E), bo(Rp,F), (dom h=E ou pr₂h=F), val_dans_F, temoin_dans_S }.

    _min avec l'hypothèse de CONSTRUCTION est_segment(pr₂h,Rp,F)[x,w] DÉCHARGÉE
    sur la preuve du présent module — TROC d'une hypothèse de construction contre
    une ∀-close générale VRAIE (temoin_dans_S), même sort que val_dans_F.
    RE-LIANT : la preuve est aux binders (ta,ua), la cible aux (x,w) —
    instancie+generalisation (licite : x/w non libres dans temoin_dans_S)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_assemble import (
        trichotomie_ordinaux_canon_prouve_min, _seg_img_form, _decharge,
    )
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis"
    mf = trichotomie_ordinaux_canon_prouve_min(E_set, R, F_set, Rp)   # 5 hyps

    # preuve du segment-image, RE-LIÉE aux binders (x,w) de la cible
    incl = M.h_img_inclus_F(E_set, R, F_set, Rp)                      # pr₂h⊂F (INCOND.)
    init = img_h_initial_sous_temoin(E_set, R, F_set, Rp)             # ∀ta∀ua(…)
    init_xw = N.generalisation("x", N.generalisation("w",
        instancie(instancie(init, var("x")), var("w"))))              # ∀x∀w(…)
    seg_preuve = conjonction_intro(incl, init_xw)
    seg_cible = _seg_img_form(E_set, R, F_set, Rp, "x", "w")
    assert seg_preuve.conclusion == seg_cible, \
        "min2 : preuve α-alignée ≠ est_segment(pr₂h)[x,w] de la cible"

    assert seg_cible in set(mf.hypotheses), \
        "min2 : l'hypothèse segment-image attendue est absente de _min"
    res = _decharge(mf, seg_cible, seg_preuve)
    assert seg_cible not in res.hypotheses, "min2 : segment-image NON déchargé"
    assert temoin_dans_S(E_set, R, F_set, Rp) in res.hypotheses, \
        "min2 : temoin_dans_S absente (la coupe n'a pas apporté l'hypothèse)"
    assert len(res.hypotheses) == 5, \
        "min2 : hyps ≠ 5 (%d)" % len(res.hypotheses)
    assert res.conclusion == mf.conclusion, "min2 : conclusion altérée"
    assert res.conclusion not in res.hypotheses, "min2 : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 LE THÉORÈME AUX HYPOTHÈSES DU LIVRE — les DEUX segments DÉRIVÉS.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Th.3 | E III.21 L.18-22 | PDF p.124  (Théorème 3, trichotomie des ensembles bien ordonnés — assemblage aux seules hypothèses { bo(R,E), bo(Rp,F), maximalité de h })
def trichotomie_ordinaux_canon_prouve_min3(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp) sous LES 3 HYPOTHÈSES
       { bo(R,E), bo(Rp,F), ( dom h=E ou pr₂h=F ) }.

    Le maillon+3 (5 hyps) avec ses DEUX segments DÉRIVÉS par les ponts :
      • seg_dom[x,w] ← dom_h_est_segment_prouve (CLOS, α-renommé xx/ww→x/w) ;
      • seg_img[x,w] ← img_h_est_segment_prouve (CLOS, re-lié ta/ua→x/w).
    val_dans_F ET temoin_dans_S ont DISPARU du séquent : il ne reste que les
    deux bons ordres (honnêtes) et la MAXIMALITÉ de h (le lemme de Zorn)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_assemble import (
        _dom_segment_aux_binders, _seg_dom_form, _seg_img_form, _decharge,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_maillon_coherences_prouvees as MCP
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis"
    mf = MCP.maillon_final_h_plus3(E_set, R, F_set, Rp)
    conclusion_attendue = mf.conclusion

    # ── segment dom[x,w] ← version PROUVÉE (0 hyp), α-renommée (xx,ww)→(x,w) ──
    seg_d = _seg_dom_form(E_set, R, F_set, Rp, "x", "w")
    assert seg_d in set(mf.hypotheses), "min3 : seg_dom[x,w] absent du maillon"
    mf = _decharge(mf, seg_d,
                   _dom_segment_aux_binders(E_set, R, F_set, Rp, "x", "w",
                                            via_pont=True))

    # ── segment img[x,w] ← version PROUVÉE (0 hyp), re-liée (ta,ua)→(x,w) ──
    incl = M.h_img_inclus_F(E_set, R, F_set, Rp)
    init = img_h_initial_prouve(E_set, R, F_set, Rp)
    init_xw = N.generalisation("x", N.generalisation("w",
        instancie(instancie(init, var("x")), var("w"))))
    seg_preuve = conjonction_intro(incl, init_xw)
    seg_i = _seg_img_form(E_set, R, F_set, Rp, "x", "w")
    assert seg_preuve.conclusion == seg_i, "min3 : preuve α-alignée ≠ seg_img[x,w]"
    assert seg_i in set(mf.hypotheses), "min3 : seg_img[x,w] absent du maillon"
    mf = _decharge(mf, seg_i, seg_preuve)

    assert len(mf.hypotheses) == 3, "min3 : hyps ≠ 3 (%d)" % len(mf.hypotheses)
    assert mf.conclusion == conclusion_attendue, "min3 : conclusion altérée"
    assert mf.conclusion not in mf.hypotheses, "min3 : VACUOUS"
    return mf


__all__ = [
    "temoin_dans_S",
    "img_h_initial_sous_temoin", "img_h_initial_cible",
    "img_h_est_segment_sous_temoin", "img_h_est_segment_cible",
    "img_h_initial_prouve", "img_h_est_segment_prouve",
    "trichotomie_ordinaux_canon_prouve_min2",
    "trichotomie_ordinaux_canon_prouve_min3",
]
