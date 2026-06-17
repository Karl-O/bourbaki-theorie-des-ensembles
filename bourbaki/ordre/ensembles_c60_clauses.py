"""§III.2 — RÉCURRENCE TRANSFINIE (Critère C60), EXISTENCE : LES 3 CLAUSES RÉSIDUELLES.

Suite DIRECTE de `ensembles_c60_realisation` (qui CONSTRUIT par S8 la famille concrète
`Dfam_real(x) = { p∈𝔓(E×V) | (∃y∈seg(R,E,x)) est_essai(p,vh,R,E,y) }` et DÉCHARGE par
construction les clauses (P1) `membres_fonctionnels_realise` et (P5)
`equation_au_point_realise`, RÉDUISANT `realisation_famille` à ses TROIS clauses
substantielles (P2),(P3),(P4)).  Ce module ATTAQUE ces TROIS clauses pour la famille
CONCRÈTE Dfam_real, afin de COMPLÉTER l'existence C60 sous { bon ordre } seul.

────────────────────────────────────────────────────────────────────────────────
LES TROIS CLAUSES.

  (P2) coincidence_membres(Dfam_real(x)) :
        (∀p)(∀q)(∀a)( (p∈D ∧ q∈D ∧ a∈dom p ∧ a∈dom q) ⇒ valeur(p,a)=valeur(q,a) ).
        🎯 CLOSE INCONDITIONNELLEMENT (0 hyp).  Chaque membre p de Dfam_real(x) est, par
        l'axiome S8, un essai d'un y<x : est_essai(p,vh,R,E,y) CONTIENT l'ÉQUATION DE
        RÉCURSION (∀z)(z∈dom p ⇒ valeur(p,z)=vh(z)).  Donc, pour a∈dom p, valeur(p,a)=vh(a) ;
        de même valeur(q,a)=vh(a).  D'où valeur(p,a)=vh(a)=valeur(q,a).  Les valeurs des
        essais sont TOUTES épinglées sur la même règle vh — la coïncidence est DIRECTE,
        SANS recours à `solutions_coincident` (l'équation de récursion suffit).  Les deux
        témoins existentiels y (pour p) et y' (pour q) sont ÉLIMINÉS (non libres dans la
        conclusion valeur(p,a)=valeur(q,a)).

  (P3) dom(⋃Dfam_real(x)) = seg(R,E,x) :  voir le RAPPORT en bas — RÉSIDU HONNÊTE.
  (P4) recursion_sur_segment(Dfam_real(x),vh,…) :  voir le RAPPORT en bas — RÉSIDU.

INVARIANT : theorie_ensembles() = 22.  Tout DÉRIVÉ, rien postulé.  vh OPAQUE.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.ordre.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.ensembles_c60_existence_close import est_essai, couvert_essai
from bourbaki.ordre.ensembles_c60_coeur import (
    union_famille, famille_compatible, valeur_union_famille,
)
from bourbaki.ordre.ensembles_c60_final import (
    membres_fonctionnels, coincidence_membres, recursion_sur_segment,
    famille_compatible_depuis_coincidence,
)
from bourbaki.ordre.ensembles_c60_realisation import (
    Dfam_real, _inst_Dfam_real, membre_Dfam_real, ambiant,
    membres_fonctionnels_realise,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE — l'équation de récursion d'un membre de Dfam_real(x) en un antécédent.
#  Pour p∈Dfam_real(x) et a∈dom(p) :  valeur(p,a) = vh(a)   [via S8 + est_essai].
# ════════════════════════════════════════════════════════════════════════════
def valeur_membre_egale_regle(vh, e="E", G="G", x="x0", V="Vval",
                              p="pmv", a="amv", y="yD", z="zess"):
    """{ p∈Dfam_real(x), a∈dom(p) } ⊢ valeur(p,a) = vh(a)             [2 hyps honnêtes].

    Tout membre p de la famille concrète Dfam_real(x) est, par l'axiome S8, un essai
    d'un y<x : est_essai(p,vh,R,E,y) CONTIENT l'équation de récursion
    (∀z)(z∈dom p ⇒ valeur(p,z)=vh(z)).  Donc en a∈dom(p), valeur(p,a)=vh(a).  Le témoin
    existentiel y (du segment) est ÉLIMINÉ (non libre dans valeur(p,a)=vh(a)).

    ⚠️ DEUX hypothèses HONNÊTES : p∈Dfam_real(x), a∈dom(p).  Non vacuous."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    vp, va, vy = var(p), var(a), var(y)
    seg = E.segment_extremite(R, ve, vx)

    # p∈Dx ⇒ (p∈𝔓(E×V) et (∃y∈seg)est_essai(p,y))   [axiome S8]
    ax = _inst_Dfam_real(vh, e, G, vx, vp, V, y)
    h_pin = N.assume(appartient(vp, Dx))                        # p∈Dx   [HONNÊTE]
    corps = N.modus_ponens(h_pin, equivalence_avant(ax))        # amb et (∃y∈seg)essai
    sel = conjonction_elim_droite(corps)                        # (∃y)( y∈seg et est_essai(p,y) )

    h_a = N.assume(appartient(va, E.dom(vp)))                   # a∈dom(p)   [HONNÊTE]

    # corps du témoin :  y∈seg et est_essai(p,y)  ⇒  valeur(p,a)=vh(a)
    corps_y = et(appartient(vy, seg), est_essai(vp, vh, R, ve, vy, z))
    h_corps_y = N.assume(corps_y)
    essai_y = conjonction_elim_droite(h_corps_y)                # est_essai(p,y)
    eq_rec = conjonction_elim_droite(essai_y)                   # (∀z)(z∈dom p ⇒ valeur(p,z)=vh(z))
    eq_a = N.modus_ponens(h_a, instancie(eq_rec, va))           # valeur(p,a)=vh(a)
    assert eq_a.conclusion == egal(E.valeur(vp, va), vh(va)), \
        "valeur_membre_egale_regle : équation ≠ valeur(p,a)=vh(a)"

    # élimine le témoin y (y∉valeur(p,a)=vh(a) ni dans Γ\{h_corps_y})
    imp_y = N.loi_deduction(corps_y, eq_a)                      # corps_y ⇒ valeur(p,a)=vh(a)
    ex_imp = existe_elimination(imp_y, y)                       # (∃y)corps_y ⇒ valeur(p,a)=vh(a)
    res = N.modus_ponens(sel, ex_imp)                           # valeur(p,a)=vh(a)   [p∈Dx, a∈dom p]

    cible = egal(E.valeur(vp, va), vh(va))
    assert res.conclusion == cible, "valeur_membre_egale_regle : ≠ valeur(p,a)=vh(a)"
    assert appartient(vp, Dx) in res.hypotheses, "valeur_membre_egale_regle : p∈Dx absente"
    assert appartient(va, E.dom(vp)) in res.hypotheses, "valeur_membre_egale_regle : a∈dom p absente"
    assert res.conclusion not in res.hypotheses, "valeur_membre_egale_regle : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSE (P2) — coincidence_membres(Dfam_real(x))  [CLOS, 0 hyp].
# ════════════════════════════════════════════════════════════════════════════
def coincidence_membres_realise(vh, e="E", G="G", x="x0", V="Vval",
                                y="yD", z="zess"):
    """⊢ coincidence_membres( Dfam_real(x) )                          [CLOS, 0 hyp].

    🎯 LA CLAUSE (P2) DÉCHARGÉE INCONDITIONNELLEMENT.  Deux membres p,q quelconques de
    la famille concrète Dfam_real(x) COÏNCIDENT en valeur sur tout antécédent commun a :
      • p∈Dfam_real(x), a∈dom(p)  ⇒  valeur(p,a)=vh(a)   [`valeur_membre_egale_regle`] ;
      • q∈Dfam_real(x), a∈dom(q)  ⇒  valeur(q,a)=vh(a)   [idem] ;
      • chaîne :  valeur(p,a) = vh(a) = valeur(q,a).
    Les VALEURS des essais sont TOUTES épinglées sur la même règle vh (l'équation de
    récursion de est_essai), donc la coïncidence est DIRECTE — sans `solutions_coincident`.

    coincidence_membres(Dfam_real(x)) =
      (∀p)(∀q)(∀a)( (p∈D ∧ q∈D ∧ a∈dom p ∧ a∈dom q) ⇒ valeur(p,a)=valeur(q,a) )
    est donc un THÉORÈME CLOS pour la famille concrète.  Aucune hypothèse, non vacuous."""
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    # binders de coincidence_membres : pcm, qcm, acm
    p, q, a = "pcm", "qcm", "acm"
    vp, vq, va = var(p), var(q), var(a)

    prem_form = et(et(appartient(vp, Dx), appartient(vq, Dx)),
                   et(appartient(va, E.dom(vp)), appartient(va, E.dom(vq))))
    prem = N.assume(prem_form)
    pD = conjonction_elim_gauche(conjonction_elim_gauche(prem))    # p∈D
    qD = conjonction_elim_droite(conjonction_elim_gauche(prem))    # q∈D
    a_dp = conjonction_elim_gauche(conjonction_elim_droite(prem))  # a∈dom p
    a_dq = conjonction_elim_droite(conjonction_elim_droite(prem))  # a∈dom q

    # valeur(p,a)=vh(a)   (décharge p∈D et a∈dom p)
    vpa = valeur_membre_egale_regle(vh, e, G, vx, V, p, a, y, z)
    vpa = N.modus_ponens(pD, N.loi_deduction(appartient(vp, Dx), vpa))
    vpa = N.modus_ponens(a_dp, N.loi_deduction(appartient(va, E.dom(vp)), vpa))   # valeur(p,a)=vh(a)
    # valeur(q,a)=vh(a)
    vqa = valeur_membre_egale_regle(vh, e, G, vx, V, q, a, y, z)
    vqa = N.modus_ponens(qD, N.loi_deduction(appartient(vq, Dx), vqa))
    vqa = N.modus_ponens(a_dq, N.loi_deduction(appartient(va, E.dom(vq)), vqa))   # valeur(q,a)=vh(a)

    # chaîne :  valeur(p,a) = vh(a) = valeur(q,a)
    vha_eq_vqa = N.modus_ponens(vqa, symetrie(E.valeur(vq, va), vh(va)))  # vh(a)=valeur(q,a)
    val_eq = composer_egalites(vpa, vha_eq_vqa)                          # valeur(p,a)=valeur(q,a)
    assert val_eq.conclusion == egal(E.valeur(vp, va), E.valeur(vq, va)), \
        "coincidence_membres_realise : chaîne ≠ valeur(p,a)=valeur(q,a)"

    imp = N.loi_deduction(prem_form, val_eq)
    res = N.generalisation(p, N.generalisation(q, N.generalisation(a, imp)))

    cible = coincidence_membres(Dx, p, q, a)
    assert res.conclusion == cible, "coincidence_membres_realise : ≠ coincidence_membres(Dfam_real(x))"
    assert res.est_clos, "coincidence_membres_realise : non clos (devrait être 0 hyp)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 COROLLAIRE — famille_compatible(Dfam_real(x))  [CLOS, 0 hyp].
#  (P1)+(P2) closes ⇒ le PONT solutions_coincident→famille_compatible se décharge.
# ════════════════════════════════════════════════════════════════════════════
def famille_compatible_realise(vh, e="E", G="G", x="x0", V="Vval",
                               y="yD", z="zess"):
    """⊢ famille_compatible( Dfam_real(x) )                           [CLOS, 0 hyp].

    🎯 La famille concrète Dfam_real(x) est COMPATIBLE PAR PAIRES, INCONDITIONNELLEMENT.
    Le PONT `famille_compatible_depuis_coincidence` (c60_final) DÉRIVE famille_compatible
    de { membres_fonctionnels(D), coincidence_membres(D) } ; ces DEUX hypothèses sont
    désormais des THÉORÈMES CLOS pour la famille concrète :
      • membres_fonctionnels(D)  ⇐ `membres_fonctionnels_realise` (P1, CLOS) ;
      • coincidence_membres(D)   ⇐ `coincidence_membres_realise`  (P2, CLOS).
    Donc famille_compatible(D) est CLOS — ce qui débloque `union_famille_fonctionnelle`,
    `valeur_union_famille` et tout le recollement de la famille concrète SANS hypothèse."""
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)

    pont = famille_compatible_depuis_coincidence(Dx)            # {mf(D), cm(D)} ⊢ compat(D)
    p1 = membres_fonctionnels_realise(vh, e, G, vx, V)          # ⊢ membres_fonctionnels(D)  [CLOS]
    p2 = coincidence_membres_realise(vh, e, G, vx, V, y, z)     # ⊢ coincidence_membres(D)   [CLOS]

    res = N.modus_ponens(p1, N.loi_deduction(membres_fonctionnels(Dx), pont))
    res = N.modus_ponens(p2, N.loi_deduction(coincidence_membres(Dx), res))

    cible = famille_compatible(Dx)
    assert res.conclusion == cible, "famille_compatible_realise : ≠ famille_compatible(Dfam_real(x))"
    assert res.est_clos, "famille_compatible_realise : non clos (devrait être 0 hyp)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 BRIQUE — valeur(⋃Dfam_real(x), u) = vh(u)  pour u dans le domaine d'un membre.
#  (la valeur de la réunion HÉRITE de la règle vh ; famille_compatible déchargée.)
# ════════════════════════════════════════════════════════════════════════════
def valeur_union_egale_regle(vh, e="E", G="G", x="x0", V="Vval",
                             p="pcf", u="u", q="qcf", y="yD", z="zess"):
    """{ p∈Dfam_real(x), u∈dom(p) } ⊢ valeur( ⋃Dfam_real(x), u ) = vh(u)
                                                                    [2 hyps honnêtes].

    🎯 La VALEUR DE LA RÉUNION ⋃Dfam_real(x) en u COÏNCIDE avec la règle vh(u), dès que
    u est dans le domaine d'un membre p de la famille.  PREUVE (chaîne) :
      • valeur(⋃D,u) = valeur(p,u)  ⇐ `valeur_union_famille` (c60_coeur), dont la
        3ᵉ hypothèse famille_compatible(D) est DÉCHARGÉE par `famille_compatible_realise`
        (CLOS) ; ne restent que p∈D et u∈dom p ;
      • valeur(p,u) = vh(u)         ⇐ `valeur_membre_egale_regle` (P2-brique), sous p∈D,
        u∈dom p.
      • chaîne :  valeur(⋃D,u) = valeur(p,u) = vh(u).

    ⚠️ DEUX hypothèses HONNÊTES : p∈Dfam_real(x), u∈dom(p).  Non vacuous.  C'est la
    BRIQUE de l'équation de récursion sur le segment (P4)."""
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    U = union_famille(Dx)
    vp, vu = var(p), var(u)

    # valeur(⋃D,u)=valeur(p,u)  ; décharge famille_compatible(D) par le corollaire CLOS
    vuf = valeur_union_famille(Dx, p, u, q)                     # {compat(D), p∈D, u∈dom p}
    compat = famille_compatible_realise(vh, e, G, vx, V, y, z)  # ⊢ famille_compatible(D)  [CLOS]
    vuf = N.modus_ponens(compat, N.loi_deduction(famille_compatible(Dx), vuf))   # {p∈D, u∈dom p}
    assert vuf.conclusion == egal(E.valeur(U, vu), E.valeur(vp, vu)), \
        "valeur_union_egale_regle : ≠ valeur(⋃D,u)=valeur(p,u)"

    # valeur(p,u)=vh(u)  (P2-brique)
    vpu = valeur_membre_egale_regle(vh, e, G, vx, V, p, u, y, z)   # {p∈D, u∈dom p}

    res = composer_egalites(vuf, vpu)                          # valeur(⋃D,u)=vh(u)

    cible = egal(E.valeur(U, vu), vh(vu))
    assert res.conclusion == cible, "valeur_union_egale_regle : ≠ valeur(⋃D,u)=vh(u)"
    assert appartient(vp, Dx) in res.hypotheses, "valeur_union_egale_regle : p∈D absente"
    assert appartient(vu, E.dom(vp)) in res.hypotheses, "valeur_union_egale_regle : u∈dom p absente"
    assert res.conclusion not in res.hypotheses, "valeur_union_egale_regle : VACUOUS"
    return res


__all__ = [
    # brique : l'équation de récursion d'un membre en un antécédent
    "valeur_membre_egale_regle",
    # 🎯 clause (P2) CLOSE par construction
    "coincidence_membres_realise",
    # 🎯 corollaire : famille_compatible(Dfam_real(x)) CLOS (débloque le recollement)
    "famille_compatible_realise",
    # 🎯 brique : valeur de la réunion en un point du domaine d'un membre = vh
    "valeur_union_egale_regle",
]
