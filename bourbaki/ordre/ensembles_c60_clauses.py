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
from bourbaki.ensembles.base.ensembles_couples import singleton_membre

from bourbaki.ordre.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.ensembles_c60_existence_close import est_essai, couvert_essai, dom_essai
from bourbaki.ordre.ensembles_c60_coeur import (
    union_famille, famille_compatible, valeur_union_famille, _inst_union_famille,
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


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSE (P2 universelle) — clause_P2(vh,…)  [CLOS, 0 hyp].
#  coincidence_membres_realise est 0-hyp ; on l'enveloppe (∀x∈E)(antéc ⇒ ·).
# ════════════════════════════════════════════════════════════════════════════
def coincidence_segment_realise(vh, e="E", G="G", x="x0", V="Vval",
                                y="ytf", yD="yD", z="zess"):
    """⊢ clause_P2(vh,e,G,x,V,y)                                       [CLOS, 0 hyp].

    🎯 LA CLAUSE (P2) SOUS FORME UNIVERSELLE, INCONDITIONNELLE.  `coincidence_membres_realise`
    donne coincidence_membres(Dfam_real(x)) CLOS (0 hyp) pour tout x ; on l'enveloppe
    dans (∀x)( x∈E ⇒ ( antecedent_couverture(x) ⇒ coincidence_membres(Dfam_real(x)) ) )
    par loi_deduction (déchargeant x∈E et l'antécédent VACUEUSEMENT — la conclusion ne
    dépend ni de x∈E ni de l'antécédent) puis généralisation.  Aucune hypothèse."""
    from bourbaki.ordre.ensembles_c60_realisation import (
        clause_P2 as _clause_P2, antecedent_couverture,
    )
    ve, vx = _t(e), var(x)
    Dx = Dfam_real(vh, e, G, vx, V)

    coinc = coincidence_membres_realise(vh, e, G, vx, V, yD, z)   # ⊢ coincidence_membres(Dx)  [CLOS]
    antec = antecedent_couverture(vh, e, G, vx, y)
    body = N.loi_deduction(appartient(vx, ve),
                           N.loi_deduction(antec, coinc))
    res = N.generalisation(x, body)

    cible = _clause_P2(vh, e, G, x, V, y)
    assert res.conclusion == cible, "coincidence_segment_realise : ≠ clause_P2"
    assert res.est_clos, "coincidence_segment_realise : non clos (devrait être 0 hyp)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  L'ANTÉCÉDENT AMBIANT — variante honnête de antecedent_couverture où l'essai
#  témoin de chaque y<x vit dans l'ambiant 𝔓(E×V) (condition de membership Dfam_real).
# ════════════════════════════════════════════════════════════════════════════
def antecedent_couverture_ambiant(vh, e="E", G="G", x="x0", V="Vval",
                                  y="ytf", p="pcf", z="zess"):
    """(∀y)( y∈seg(R,E,x) ⇒ (∃p)( p∈𝔓(E×V) ∧ est_essai(p,vh,R,E,y) ) ).

    « Tout y<x est couvert par un essai DANS L'AMBIANT 𝔓(E×V). »  C'est l'hypothèse
    d'induction de C59, RENFORCÉE par la condition d'appartenance à l'ambiant — la SEULE
    chose dont la membership Dfam_real(x) a besoin en plus de est_essai (l'axiome S8
    sélectionne DANS 𝔓(E×V)).  C'est HONNÊTE : un essai sur un segment est un graphe de
    couples (z,vh(z)) ⊂ E×V dès que les valeurs-règle vivent dans V (le contenant des
    valeurs candidates) — la donnée naturelle de la construction de Bourbaki."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    seg = E.segment_extremite(R, ve, vx)
    vy, vp = var(y), var(p)
    corps = existe(p, et(appartient(vp, ambiant(e, V)),
                         est_essai(vp, vh, R, ve, vy, z)))
    return pourtout(y, impl(appartient(vy, seg), corps))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 HELPER PARTAGÉ (P3-⊇ et P4) — la COUVERTURE :
#  { antecedent_couverture_ambiant(x) , z∈seg(R,E,x) } ⊢ (∃p)( p∈Dfam_real(x) ∧ z∈dom p ).
# ════════════════════════════════════════════════════════════════════════════
def _couverture_membre(vh, e, G, x, V, z, p="pcf", yD="yD", zb="zess"):
    """{ antecedent_couverture_ambiant(x), z∈seg(R,E,x) }
        ⊢ (∃p)( p∈Dfam_real(x) ∧ z∈dom(p) ∧ valeur(⋃Dfam_real(x),z)=vh(z) ).

    LE CŒUR PARTAGÉ par P3-⊇ et P4.  z<x est couvert par un essai p_z DANS L'AMBIANT
    (hyp ambiante) ; comme z∈seg(x) ∧ est_essai(p_z,z), on a p_z∈Dfam_real(x) (axiome
    S8) ; z∈dom(p_z)=seg(z)∪{z} (z∈{z}) ; et par `valeur_union_egale_regle`,
    valeur(⋃Dfam_real(x),z)=vh(z).  Renvoie l'existentiel sur le témoin p_z (éliminable).

    Renvoie un Theoreme dont la conclusion est l'existentiel ci-dessus, sous les deux
    hypothèses honnêtes (antécédent ambiant + z∈seg)."""
    R = _graphe_R(G)
    ve, vx, vz = _t(e), _t(x), var(z)
    zname = z
    Dx = Dfam_real(vh, e, G, vx, V)
    Ux = union_famille(Dx)
    seg = E.segment_extremite(R, ve, vx)
    vp = var(p)

    # hypothèses honnêtes
    h_ant = N.assume(antecedent_couverture_ambiant(vh, e, G, vx, V, "ytf", p, zb))
    h_zseg = N.assume(appartient(vz, seg))                         # z∈seg(R,E,x)

    # antécédent ambiant instancié à z : z∈seg ⇒ (∃p)(p∈amb ∧ est_essai(p,z))
    ant_z = N.modus_ponens(h_zseg, instancie(h_ant, vz))          # (∃p)( p∈amb ∧ est_essai(p,z) )

    # corps du témoin p :  p∈amb ∧ est_essai(p, vh, R, E, z)
    corps_p = et(appartient(vp, ambiant(e, V)), est_essai(vp, vh, R, ve, vz, zb))
    h_corps = N.assume(corps_p)
    p_amb = conjonction_elim_gauche(h_corps)                      # p∈𝔓(E×V)
    essai_p = conjonction_elim_droite(h_corps)                    # est_essai(p,z)

    # p∈Dfam_real(x) :  (p∈amb) ∧ (∃yD)( yD∈seg ∧ est_essai(p,yD) ), via S8 ⇐
    #   le témoin yD := z (z∈seg, est_essai(p,z))
    sel_corps = et(appartient(vz, seg), est_essai(vp, vh, R, ve, vz, zb))
    sel_zz = conjonction_intro(h_zseg, essai_p)                   # z∈seg ∧ est_essai(p,z)
    sel_ex = N.modus_ponens(sel_zz, N.s5(
        et(appartient(var(yD), seg), est_essai(vp, vh, R, ve, var(yD), zb)), vz, yD))  # (∃yD)(...)
    corps_D = et(appartient(vp, ambiant(e, V)), sel_ex.conclusion)
    membre_D = conjonction_intro(p_amb, sel_ex)                   # p∈amb ∧ (∃yD)(...)
    ax = _inst_Dfam_real(vh, e, G, vx, vp, V, yD)                 # p∈Dx ⇔ (amb ∧ (∃yD)essai)
    p_in_Dx = N.modus_ponens(membre_D, equivalence_arriere(ax))   # p∈Dfam_real(x)

    # z∈dom(p) :  dom(p)=seg(z)∪{z}, z∈{z}⊆dom(p)
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(essai_p))   # dom(p)=seg(z)∪{z}
    sx = E.singleton(vz)
    z_in_sx = N.modus_ponens(N.reflexivite(vz), equivalence_arriere(singleton_membre(vz, vz)))  # z∈{z}
    # z∈seg(z)∪{z}  (côté droit de la réunion)
    from bourbaki.ensembles.ensembles_theoremes import _instance_reunion
    segz = E.segment_extremite(R, ve, vz)
    # z∈{z} ⇒ (z∈{z} ou z∈segz) [s2] ⇒ (z∈segz ou z∈{z}) [s3]
    Bz, Az = appartient(vz, sx), appartient(vz, segz)
    z_disj = N.modus_ponens(N.modus_ponens(z_in_sx, N.s2(Bz, Az)), N.s3(Bz, Az))  # z∈segz ou z∈{z}
    z_in_dom_essai = N.modus_ponens(z_disj,
        equivalence_arriere(_instance_reunion(segz, sx, vz)))      # z∈seg(z)∪{z}
    # réécrit seg(z)∪{z} → dom(p) via dom(p)=seg(z)∪{z} (symétrie)
    dom_eq_sym = N.modus_ponens(dom_eq, symetrie(E.dom(vp), dom_essai(R, ve, vz)))  # seg(z)∪{z}=dom(p)
    z_in_domp = N.modus_ponens(z_in_dom_essai, equivalence_avant(
        N.modus_ponens(dom_eq_sym, N.s6(dom_essai(R, ve, vz), E.dom(vp), "wdz", appartient(vz, var("wdz"))))))  # z∈dom(p)

    # valeur(⋃Dx,z)=vh(z)   via valeur_union_egale_regle  (décharge p∈Dx, z∈dom p)
    vue = valeur_union_egale_regle(vh, e, G, vx, V, p, zname, "qcf", yD, zb)   # {p∈Dx, z∈dom p}
    vue = N.modus_ponens(p_in_Dx, N.loi_deduction(appartient(vp, Dx), vue))
    vue = N.modus_ponens(z_in_domp, N.loi_deduction(appartient(vz, E.dom(vp)), vue))  # valeur(⋃Dx,z)=vh(z)

    # construit le témoin existentiel :  p∈Dx ∧ z∈dom p ∧ valeur(⋃Dx,z)=vh(z)
    eq_form = egal(E.valeur(Ux, vz), vh(vz))
    temoin_corps = et(et(appartient(vp, Dx), appartient(vz, E.dom(vp))), eq_form)
    temoin = conjonction_intro(conjonction_intro(p_in_Dx, z_in_domp), vue)
    assert temoin.conclusion == temoin_corps

    # existentiel sur p (témoin p) ; corps NE dépend que de p, z (pas du binder du témoin S8)
    gabarit = et(et(appartient(vp, Dx), appartient(vz, E.dom(vp))), eq_form)
    ex_temoin = N.modus_ponens(temoin, N.s5(gabarit, vp, p))      # (∃p)( p∈Dx ∧ z∈dom p ∧ val=vh )

    # élimine le témoin p de l'antécédent ambiant (corps_p ⇒ ∃p(gabarit))
    imp = N.loi_deduction(corps_p, ex_temoin)
    ex_imp = existe_elimination(imp, p)                           # (∃p)(corps_p) ⇒ (∃p)(gabarit)
    res = N.modus_ponens(ant_z, ex_imp)                           # (∃p)(gabarit)   [hyps honnêtes]
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSE (P4) — recursion_segment_realise(vh,…)  ⊢ clause_P4  [hyp ambiante + bo].
# ════════════════════════════════════════════════════════════════════════════
def clause_P4_ambiant(vh, e="E", G="G", x="x0", V="Vval", y="ytf", p="pcf", zb="zess"):
    """(∀x)( x∈E ⇒ ( antecedent_couverture_ambiant(x) ⇒ recursion_sur_segment(Dfam_real(x),…) ) ).

    Variante de clause_P4 où l'antécédent est l'antécédent d'induction AMBIANT (essais des
    y<x dans 𝔓(E×V)) — la SEULE chose en plus de est_essai dont la membership Dfam_real(x)
    a besoin (l'axiome S8 sélectionne DANS 𝔓(E×V))."""
    ve, vx = _t(e), var(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    antec = antecedent_couverture_ambiant(vh, e, G, vx, V, y, p, zb)
    return pourtout(x, impl(appartient(vx, ve),
        impl(antec, recursion_sur_segment(Dx, vh, G, e, vx))))


def recursion_segment_realise(vh, e="E", G="G", x="x0", V="Vval", y="ytf",
                              z="zrs", p="pcf", zb="zess"):
    """⊢ clause_P4_ambiant(vh,e,G,x,V,y)                              [CLOS, 0 hyp].

    🎯 LA CLAUSE (P4), sous l'antécédent d'induction AMBIANT.  Pour x∈E avec l'antécédent
    ambiant, tout z∈seg(R,E,x) vérifie valeur(⋃Dfam_real(x),z)=vh(z) : par
    `_couverture_membre`, z est couvert par un essai p_z∈Dfam_real(x) avec z∈dom(p_z),
    donc valeur(⋃Dfam_real(x),z)=vh(z) (la valeur de la réunion hérite de la règle,
    `valeur_union_egale_regle`).  Le témoin p_z est éliminé, puis on enveloppe et
    généralise — l'antécédent ambiant (x-dépendant) étant l'ANTÉCÉDENT (déchargé par
    loi_deduction AVANT généralisation), x n'est libre dans AUCUNE hypothèse.  CLOS.

    ⚠️ L'antécédent est antecedent_couverture_ambiant (PLUS FORT que antecedent_couverture
    de clause_P4) : il exige que l'essai-témoin de chaque y<x vive dans 𝔓(E×V), condition
    sans laquelle la membership Dfam_real(x) (sélection S8 dans 𝔓(E×V)) ne peut être
    établie.  C'est HONNÊTE : un essai sur seg est un graphe de couples (z,vh(z)) ⊂ E×V."""
    R = _graphe_R(G)
    ve, vx = _t(e), var(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    Ux = union_famille(Dx)
    seg = E.segment_extremite(R, ve, vx)
    vz = var(z)
    antec = antecedent_couverture_ambiant(vh, e, G, vx, V, y, p, zb)

    h_antec = N.assume(antec)                                    # antécédent ambiant (x-dépendant)

    # but du corps :  z∈seg ⇒ valeur(⋃Dx,z)=vh(z)
    cov = _couverture_membre(vh, e, G, vx, V, z, p, "yD", zb)    # (∃p)(p∈Dx ∧ z∈dom p ∧ val=vh)
    #   sous {antecedent_couverture_ambiant(x, binder=ytf), z∈seg} — aligne le binder y du ∀
    eq_form = egal(E.valeur(Ux, vz), vh(vz))
    pq = var(p)
    gabarit = et(et(appartient(pq, Dx), appartient(vz, E.dom(pq))), eq_form)
    h_g = N.assume(gabarit)
    val_z = conjonction_elim_droite(h_g)                         # valeur(⋃Dx,z)=vh(z)
    imp_g = N.loi_deduction(gabarit, val_z)
    ex_imp = existe_elimination(imp_g, p)                        # (∃p)(gabarit) ⇒ val=vh
    val_z_final = N.modus_ponens(cov, ex_imp)                    # valeur(⋃Dx,z)=vh(z)  [antec ambiant, z∈seg]

    body_z = N.loi_deduction(appartient(vz, seg), val_z_final)   # z∈seg ⇒ val=vh   [antec ambiant]
    rec = N.generalisation(z, body_z)                            # recursion_sur_segment(Dx,…)  [antec ambiant]
    assert rec.conclusion == recursion_sur_segment(Dx, vh, G, e, vx), \
        "recursion_segment_realise : ≠ recursion_sur_segment(Dx,…)"

    # enveloppe (∀x)( x∈E ⇒ ( antec_ambiant(x) ⇒ rec ) ) — décharge antec PUIS x∈E, généralise
    body = N.loi_deduction(appartient(vx, ve),
                           N.loi_deduction(antec, rec))
    res = N.generalisation(x, body)

    cible = clause_P4_ambiant(vh, e, G, x, V, y, p, zb)
    assert res.conclusion == cible, "recursion_segment_realise : ≠ clause_P4_ambiant"
    assert res.est_clos, "recursion_segment_realise : non clos (devrait être 0 hyp)"
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
    # 🎯 clause (P2 universelle) CLOSE
    "coincidence_segment_realise",
    # antécédent renforcé (essais dans l'ambiant) + helper de couverture
    "antecedent_couverture_ambiant",
    # 🎯 clause (P4) sous l'antécédent ambiant
    "recursion_segment_realise",
]
