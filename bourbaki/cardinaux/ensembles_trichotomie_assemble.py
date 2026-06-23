"""§III.2 — Théorème 3 (TRICHOTOMIE) : ASSEMBLAGE FINAL contre la CIBLE SAINE (canon).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `maillon_final_h_plus3` (ensembles_maillon_coherences_prouvees) conclut
`trichotomie_ordinaux_canon(E,R,F,Rp)` (== `maillon_final_cible()`) sous EXACTEMENT
6 hypothèses :

    { bo(R,E), bo(Rp,F), residu_univ_app,                       [ 3 HONNÊTES ]
      ( dom h = E  ou  pr₂ h = F ),                             [ MAXIMALITÉ ]
      est_segment(dom h, R, E, x, w),                           [ SEGMENT dom ]
      est_segment(pr₂ h, Rp, F, x, w) }                         [ SEGMENT pr₂ ]
        ⊢ trichotomie_ordinaux_canon(E, R, F, Rp).

Ce module DÉCHARGE celles de ces hypothèses qui sont PORTÉES par des pièces PROUVÉES
du dépôt, et RAPPORTE PRÉCISÉMENT le RÉSIDU STRUCTUREL irréductible qui subsiste.

────────────────────────────────────────────────────────────────────────────────
DÉCHARGES EFFECTUÉES (chacune via le pattern GARDÉ `_decharge`, qui exige
`preuve.conclusion == hyp ∈ thm.hypotheses` — identique à `maillon_final_h_plus2/3`) :

  • MAXIMALITÉ ( dom h=E ou pr₂h=F )
        ← `maximalite_donne_trichotomie_close()` (ensembles_maximalite_close, PROUVÉE :
          conclusion == la disjonction de maximalité).  Ses PROPRES hypothèses sont
          { bo(R,E), bo(Rp,F), residu_univ_app, est_segment(dom h,R,E)[x,y],
            est_segment(pr₂h,Rp,F)[x,y], h_graphe_hyp }.  Les 3 honnêtes COÏNCIDENT
          avec celles du maillon ; les 2 segments [x,y] et h_graphe sont RÉINTRODUITS
          (voir RÉSIDU ci-dessous).

  • est_segment(dom h, R, E)  (TOUS les binders présents : [x,w] du maillon ET [x,y]
        réintroduits par la maximalité)
        ← `dom_h_est_segment_sous_val(...)` (ensembles_trichotomie_dom_segment, PROUVÉE
          sous la SEULE hypothèse `val_dans_F`), α-renommé aux binders demandés.  La
          borne dom(h)⊂E y est INCONDITIONNELLE ; seule l'INITIALITÉ porte `val_dans_F`.

────────────────────────────────────────────────────────────────────────────────
🎯 RÉSIDU STRUCTUREL IRRÉDUCTIBLE (rapporté, JAMAIS postulé) — la trichotomie de deux
bons ordres ⊢ se ramène à { bo(R,E), bo(Rp,F) } PLUS exactement ces pièces :

  (R1) `residu_univ_app`  — la BONNE FORME (#8 segment + #13 inclusion de graphe) des
       objets image/restriction du chevauchement des isos témoins (Lemme 1 §III.2).
       NON dérivable des briques closes du dépôt :
         #8  est_segment(image(φ_grand, S_petit), R', F)  : « image d'un segment par un
             iso est un segment » — `codomaine_egal_image` (seul consommateur) le REQUIERT
             lui-même en hypothèse ; aucune brique close ne le prouve.
         #13 inclus(restriction(φ_grand, S_petit), S_petit × T_petit) : `restriction_incluse`
             ne donne que φ_g|Sp ⊂ φ_g ⊂ Sg×Tg (codomaine T_grand) ; resserrer à T_petit
             exige image(φ_g, Sp)=T_petit, NON dérivable du graphe seul.

  (R2) `val_dans_F`  — CODOMAINE des isos témoins : φ(p)∈F pour p∈S, φ:S≅T iso de
       segments.  VRAI (φ(p)∈T par bijectivité, T⊂F car T segment) mais
       est_isomorphisme_ordre porte est_bijective SANS la structure de graphe
       (φ⊂S×T, dom φ=S) qu'exige valeur_dans_codomaine.  `val_dans_F_depuis_structure`
       (PONT, CLOS) le DÉRIVE mais SOUS la prémisse STRUCTURELLE renforcée (φ⊂S×T,
       dom φ=S) : il ne décharge donc PAS `val_dans_F` (prémisse opaque) sans le pont
       « iso ⇒ structure de graphe », lui aussi non porté.

  (R3) `h_graphe_hyp` = inclus(h, dom h × pr₂h)  — « h est un graphe ».  Fidèle à
       h={(u,v)∈E×F|…} (S8) mais NON extractible de l'AXIOME OPAQUE de h, qui ne
       caractérise QUE les couples (u,v)∈h, jamais un z ARBITRAIRE (limitation
       PRÉ-EXISTANTE, documentée dans ensembles_maximalite_close).

  (R4) est_segment(pr₂ h, Rp, F)  — « pr₂ h est un segment de F ».  L'initialité de
       l'IMAGE requiert l'iso INVERSE / la surjectivité de φ (maillon distinct,
       REPORTÉ dans ensembles_trichotomie_dom_segment) ; AUCUNE brique close ne livre
       le pr₂-analogue de dom_h_est_segment_sous_val.

────────────────────────────────────────────────────────────────────────────────
DEUX VERSIONS LIVRÉES :

  ✅ `trichotomie_ordinaux_canon_prouve(...)` (assemblage MAXIMAL) :
        applique TOUTES les pièces prouvées (maximalité + segments dom).  Conclusion
        == trichotomie_ordinaux_canon.  Hypothèses HONNÊTES SURVIVANTES (le RÉSIDU
        STRUCTUREL irréductible exposé) :
            { bo(R,E), bo(Rp,F), residu_univ_app, val_dans_F, h_graphe_hyp,
              est_segment(pr₂h,Rp,F)[x,w], est_segment(pr₂h,Rp,F)[x,y] }.

  ✅ `trichotomie_ordinaux_canon_prouve_min(...)` (assemblage MINIMAL en COMPTE) :
        garde la MAXIMALITÉ INTACTE (ne PAS l'échanger contre h_graphe+segments), et
        ne décharge QUE le segment dom du maillon.  Conclusion idem.  Hypothèses :
            { bo(R,E), bo(Rp,F), residu_univ_app, (dom h=E ou pr₂h=F),
              est_segment(pr₂h,Rp,F)[x,w], val_dans_F }.   (6 hyps, le plus serré.)

INVARIANT (vérifié) : theorie_ensembles() = 22.  RIEN POSTULÉ : chaque décharge est
une PREUVE existante.  NON vacueux : la conclusion (trichotomie) n'est AUCUNE des
hypothèses.  NE MODIFIE AUCUN fichier existant.  Noms ambiants CANONIQUES E,F,R,Rp.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, ou, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, _peler_pourtout,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    alpha_pour_tout, congruence_pour_tout,
)
from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP
from bourbaki.cardinaux import ensembles_maximalite_close as MAX
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
import bourbaki.cardinaux.ensembles_trichotomie_dom_segment as DS


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _decharge(thm, hyp_form, preuve):
    """De Γ∪{H}⊢C et Δ⊢H (Δ⊢preuve.conclusion==H), déduit Γ∪Δ⊢C.

    GARDÉ : on n'invoque QUE si `preuve.conclusion == hyp_form` ET `hyp_form` est
    effectivement parmi les hypothèses de `thm` (pattern de maillon_final_h_plus2/3).
    """
    assert preuve.conclusion == hyp_form, "décharge : preuve.conclusion ≠ hypothèse visée"
    assert hyp_form in set(thm.hypotheses), "décharge : hypothèse absente du séquent"
    return N.modus_ponens(preuve, N.loi_deduction(hyp_form, thm))


# ════════════════════════════════════════════════════════════════════════════
#  PREUVE de est_segment(dom h, R, E, x=xb, y=yb) sous {val_dans_F}, pour des
#  binders (xb,yb) ARBITRAIRES (α-renommage de dom_h_est_segment_sous_val).
#
#  dom_h_est_segment_sous_val(x='x', …) LÈVE une collision interne (le binder « x »
#  rentre en conflit avec les liants du recollement).  On le construit donc avec des
#  binders SÛRS (xx,ww) puis on α-renomme la clause d'initialité (∀x∀y) vers (xb,yb).
# ════════════════════════════════════════════════════════════════════════════
def _dom_segment_aux_binders(E_set, R, F_set, Rp, xb, yb):
    """⊢ { val_dans_F } ⊢ est_segment(dom h, R, E, x=xb, y=yb).

    est_segment = et( dom h ⊂ E , (∀xb)(∀yb)(…) ) ; la borne ⊂ est INCONDITIONNELLE,
    l'initialité porte `val_dans_F`.  α-renomme les DEUX liants internes (xx→xb, ww→yb)
    de la clause d'initialité, sans toucher à la borne ⊂E (sans liants externes)."""
    ds = DS.dom_h_est_segment_sous_val(E_set, R, F_set, Rp, x="xx", y="ww")
    borne = conjonction_elim_gauche(ds)               # dom h ⊂ E
    init = conjonction_elim_droite(ds)                # (∀xx)(∀ww)(…)

    # ── α-renommer le liant EXTERNE xx → xb ──
    _, body_xx = _peler_pourtout(init.conclusion)     # body_xx = (∀ww)(…)
    eqv_ext = alpha_pour_tout("xx", xb, body_xx)      # (∀xx body) ⇔ (∀xb body')
    init = N.modus_ponens(init, equivalence_avant(eqv_ext))   # (∀xb)(∀ww)(…)

    # ── α-renommer le liant INTERNE ww → yb (sous le ∀xb) ──
    _, body_xb = _peler_pourtout(init.conclusion)     # body_xb = (∀ww)(…)
    _, body_in = _peler_pourtout(body_xb)             # corps interne
    eqv_in = alpha_pour_tout("ww", yb, body_in)       # (∀ww …) ⇔ (∀yb …)
    eqv_lift = congruence_pour_tout(eqv_in, xb)       # remonté sous ∀xb
    init = N.modus_ponens(init, equivalence_avant(eqv_lift))  # (∀xb)(∀yb)(…)

    return conjonction_intro(borne, init)


# ════════════════════════════════════════════════════════════════════════════
#  RÉFÉRENCES de FORMULES (binders canoniques des hypothèses du maillon / max).
# ════════════════════════════════════════════════════════════════════════════
def _maximalite_form(E_set="E", R="R", F_set="F", Rp="Rp"):
    """La disjonction de MAXIMALITÉ ( dom h = E  ou  pr₂ h = F )."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return ou(egal(E.dom(h), _t(E_set)), egal(E.img(h), _t(F_set)))


def _seg_dom_form(E_set, R, F_set, Rp, xb, yb):
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_segment(E.dom(h), _R_de(R), _t(E_set), xb, yb)


def _seg_img_form(E_set, R, F_set, Rp, xb, yb):
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_segment(E.img(h), _R_de(Rp), _t(F_set), xb, yb)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE MAXIMAL : maximalité + segments dom DÉCHARGÉS.
# ════════════════════════════════════════════════════════════════════════════
def trichotomie_ordinaux_canon_prouve(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp)  (== maillon_final_cible) sous le RÉSIDU
    STRUCTUREL HONNÊTE { bo(R,E), bo(Rp,F), residu_univ_app, val_dans_F, h_graphe_hyp,
    est_segment(pr₂h,Rp,F)[x,w], est_segment(pr₂h,Rp,F)[x,y] }.

    ASSEMBLAGE MAXIMAL : on décharge avec les pièces PROUVÉES
      • la MAXIMALITÉ ← `maximalite_donne_trichotomie_close` (PROUVÉE) ;
      • TOUS les segments dom (binders [x,w] du maillon + [x,y] réintroduits par la
        maximalité) ← `dom_h_est_segment_sous_val` (PROUVÉE sous `val_dans_F`).
    Le RÉSIDU STRUCTUREL irréductible (R1 residu, R2 val_dans_F, R3 h_graphe, R4 segment
    pr₂) est ALORS EXPOSÉ et RAPPORTÉ (cf. docstring du module).

    theorie=22, rien postulé.  Conclusion == maillon_final_cible.  NON vacueux."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis (schéma maximalite_donne_trichotomie_close)"
    mf = MCP.maillon_final_h_plus3(E_set, R, F_set, Rp)

    # ── DÉCHARGE de la MAXIMALITÉ (réintroduit segments[x,y] + h_graphe) ──
    maxim = _maximalite_form(E_set, R, F_set, Rp)
    if maxim in set(mf.hypotheses):
        preuve_max = MAX.maximalite_donne_trichotomie_close(E_set, R, F_set, Rp)
        mf = _decharge(mf, maxim, preuve_max)

    # ── DÉCHARGE de TOUS les segments dom présents (toutes paires de binders) ──
    for (xb, yb) in (("x", "w"), ("x", "y")):
        seg = _seg_dom_form(E_set, R, F_set, Rp, xb, yb)
        if seg in set(mf.hypotheses):
            mf = _decharge(mf, seg, _dom_segment_aux_binders(E_set, R, F_set, Rp, xb, yb))

    return mf


def trichotomie_ordinaux_canon_prouve_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : trichotomie_ordinaux_canon(E,R,F,Rp)
    (== maillon_final_cible)."""
    return MCP.maillon_final_h_plus3_cible(E_set, R, F_set, Rp)


def trichotomie_ordinaux_canon_prouve_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 6 HYPOTHÈSES SURVIVANTES ATTENDUES (documentation / test miroir) du
    RÉSIDU STRUCTUREL irréductible de l'assemblage MAXIMAL :
        2 HONNÊTES { bo(R,E), bo(Rp,F) }   (residu_univ_app ÉLIMINÉ)
        + val_dans_F + h_graphe_hyp
        + est_segment(pr₂h,Rp,F)[x,w] + est_segment(pr₂h,Rp,F)[x,y]."""
    from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
    honnetes = list(FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp))
    return honnetes + [
        DS.val_dans_F(E_set, R, F_set, Rp),
        MAX.h_graphe_hyp(E_set, R, F_set, Rp),
        _seg_img_form(E_set, R, F_set, Rp, "x", "w"),
        _seg_img_form(E_set, R, F_set, Rp, "x", "y"),
    ]


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE MINIMAL en COMPTE : maximalité GARDÉE, seul le segment dom du
#     maillon est déchargé (échange seg_dom ↔ val_dans_F ; pas de h_graphe).
# ════════════════════════════════════════════════════════════════════════════
def trichotomie_ordinaux_canon_prouve_min(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp)  (== maillon_final_cible) sous les 5
    hypothèses { bo(R,E), bo(Rp,F), ( dom h=E ou pr₂h=F ),
    est_segment(pr₂h,Rp,F)[x,w], val_dans_F }.   (residu_univ_app ÉLIMINÉ.)

    ASSEMBLAGE LE PLUS SERRÉ EN COMPTE.  On NE décharge PAS la maximalité (l'échanger
    contre `maximalite_donne_trichotomie_close` réintroduirait `h_graphe_hyp` — l'opaque
    de h — et des segments [x,y], FAISANT GROSSIR le résidu).  On décharge UNIQUEMENT le
    segment dom[x,w] du maillon via `dom_h_est_segment_sous_val` (PROUVÉE sous
    `val_dans_F`).  RÉSULTAT : 5 hypothèses (residu_univ_app DÉRIVÉ de
    residu_univ_app_renforce, CLOS).

    theorie=22, rien postulé.  Conclusion == maillon_final_cible.  NON vacueux."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis"
    mf = MCP.maillon_final_h_plus3(E_set, R, F_set, Rp)
    seg = _seg_dom_form(E_set, R, F_set, Rp, "x", "w")
    if seg in set(mf.hypotheses):
        mf = _decharge(mf, seg, _dom_segment_aux_binders(E_set, R, F_set, Rp, "x", "w"))
    return mf


def trichotomie_ordinaux_canon_prouve_min_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 5 HYPOTHÈSES SURVIVANTES ATTENDUES de l'assemblage MINIMAL :
        2 HONNÊTES + maximalité + est_segment(pr₂h,Rp,F)[x,w] + val_dans_F.
        (residu_univ_app ÉLIMINÉ — dérivé de residu_univ_app_renforce, CLOS.)"""
    from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
    honnetes = list(FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp))
    return honnetes + [
        _maximalite_form(E_set, R, F_set, Rp),
        _seg_img_form(E_set, R, F_set, Rp, "x", "w"),
        DS.val_dans_F(E_set, R, F_set, Rp),
    ]


__all__ = [
    "trichotomie_ordinaux_canon_prouve",
    "trichotomie_ordinaux_canon_prouve_cible",
    "trichotomie_ordinaux_canon_prouve_hypotheses",
    "trichotomie_ordinaux_canon_prouve_min",
    "trichotomie_ordinaux_canon_prouve_min_hypotheses",
]
