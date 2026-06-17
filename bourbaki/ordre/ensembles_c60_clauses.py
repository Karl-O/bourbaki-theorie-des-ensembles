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
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, alpha_pour_tout,
)
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


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSE (P3) — couverture_segment_realise(vh,…)  ⊢ clause_P3_ambiant  [1 hyp : bo].
#  dom(⋃Dfam_real(x)) = seg(R,E,x), par double inclusion + extensionnalité.
# ════════════════════════════════════════════════════════════════════════════
def clause_P3_ambiant(vh, e="E", G="G", x="x0", V="Vval", y="ytf", p="pcf", zb="zess"):
    """(∀x)( x∈E ⇒ ( antecedent_couverture_ambiant(x) ⇒ dom(⋃Dfam_real(x)) = seg(R,E,x) ) ).

    Variante de clause_P3 où l'antécédent est l'antécédent d'induction AMBIANT (essais des
    y<x dans 𝔓(E×V)) — nécessaire pour la membership Dfam_real(x) dans l'inclusion ⊇."""
    R = _graphe_R(G)
    ve, vx = _t(e), var(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    Ux = union_famille(Dx)
    seg = E.segment_extremite(R, ve, vx)
    antec = antecedent_couverture_ambiant(vh, e, G, vx, V, y, p, zb)
    return pourtout(x, impl(appartient(vx, ve),
        impl(antec, egal(E.dom(Ux), seg))))


def couverture_segment_realise(vh, e="E", G="G", x="x0", V="Vval", y="ytf",
                               p="pcf", zb="zess", w="wseg", zz="zseg"):
    """{ est_bien_ordonne(R,E) }  ⊢  clause_P3_ambiant(vh,e,G,x,V,y)   [1 hyp : bon ordre].

    🎯 LA CLAUSE (P3), sous l'antécédent d'induction AMBIANT.  Les domaines des essais des
    y<x RECOUVRENT EXACTEMENT le segment seg(R,E,x).  Double inclusion + extensionnalité :

      (⊆)  z∈dom(⋃Dfam_real(x)) ⇒ (∃w)((z,w)∈⋃D) ⇒ (∃p∈D)((z,w)∈p) ⇒ z∈dom(p).  p∈D ⇒
           (∃y∈seg(x))est_essai(p,y) ⇒ dom(p)=seg(y)∪{y}.  Donc z∈seg(y)∪{y} :
             • z∈seg(y) : z≤y∧z≠y, y≤x∧y≠x → z≤x (TRANSITIVITÉ) et z≠x (ANTISYMÉTRIE :
               z=x ⇒ x≤y∧y≤x ⇒ x=y, contredisant y≠x) → z∈seg(x) ;
             • z∈{y}    : z=y∈seg(x).
           TRANSITIVITÉ + ANTISYMÉTRIE proviennent du BON ORDRE (est_bien_ordonne ⊃ est_ordre).

      (⊇)  z∈seg(x) ⇒ z couvert par un essai p_z∈Dfam_real(x), z∈dom(p_z) (`_couverture_membre`)
           ⇒ (z,valeur(p_z,z))∈p_z ⇒ ∈⋃D ⇒ z∈dom(⋃D).

    ⚠️ UNE hypothèse HONNÊTE : est_bien_ordonne(R,E) (le bon ordre, pour la transitivité
    et l'antisymétrie de ⊆).  L'antécédent ambiant (⊇) est l'ANTÉCÉDENT de la clause.
    Conclusion == clause_P3_ambiant."""
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    from bourbaki.logique.formule import inclus, non, ou
    from bourbaki.ensembles.ensembles_theoremes import _instance_reunion
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas, antecedent_consequent
    R = _graphe_R(G)
    ve, vx = _t(e), var(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    Ux = union_famille(Dx)
    seg = E.segment_extremite(R, ve, vx)
    dU = E.dom(Ux)

    antec = antecedent_couverture_ambiant(vh, e, G, vx, V, y, p, zb)
    h_antec = N.assume(antec)
    bo = E.est_bien_ordonne(R, ve)
    h_bo = N.assume(bo)                                          # bon ordre   [HONNÊTE]

    # extrait transitivité + antisymétrie de est_bien_ordonne
    #   bo = et( est_relation_ordre_dans(R,E), petit )
    #   est_relation_ordre_dans = et( est_relation_ordre, est_reflexive_dans_ordre )
    #   est_relation_ordre = et( et(ordre_transitif, ordre_antisymetrique), ordre_refl_implicite )
    ord_dans = conjonction_elim_gauche(h_bo)                    # est_relation_ordre_dans
    rel_ordre = conjonction_elim_gauche(ord_dans)               # est_relation_ordre
    trans_antisym = conjonction_elim_gauche(rel_ordre)          # et(transitif, antisym)
    trans = conjonction_elim_gauche(trans_antisym)              # ordre_transitif(R)
    antisym = conjonction_elim_droite(trans_antisym)            # ordre_antisymetrique(R)

    vw, vz = var(w), var(zz)

    # axiome dom :  z∈dom(⋃D) ⇔ (∃w)((z,w)∈⋃D)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car_dom = instancie(instancie(ax_dom, Ux), vz)              # z∈dom⋃D ⇔ (∃w)((z,w)∈⋃D)

    # ── (⊆) inclus(dom(⋃D), seg) :  z∈dom(⋃D) ⇒ z∈seg(x) ────────────────────────
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    h_z_dU = N.assume(appartient(vz, dU))                       # z∈dom(⋃D)
    ex_w0 = N.modus_ponens(h_z_dU, equivalence_avant(car_dom))  # (∃y)((z,y)∈⋃D)
    ex_w = N.modus_ponens(ex_w0, equivalence_avant(alpha_existe(
        "y", w, appartient(E.couple(vz, var("y")), Ux))))       # (∃w)((z,w)∈⋃D)  [renommé]
    # corps témoin w :  (z,w)∈⋃D ⇒ z∈seg(x)
    h_zw_U = N.assume(appartient(E.couple(vz, vw), Ux))         # (z,w)∈⋃D
    ex_pq = N.modus_ponens(h_zw_U, equivalence_avant(_inst_union_famille(Dx, E.couple(vz, vw))))
    #   ex_pq : (∃punion)( punion∈D ∧ (z,w)∈punion )
    pun = "punion"
    vpun = var(pun)
    corps_pun = et(appartient(vpun, Dx), appartient(E.couple(vz, vw), vpun))
    h_pun = N.assume(corps_pun)
    pun_in_D = conjonction_elim_gauche(h_pun)                   # punion∈D
    zw_in_pun = conjonction_elim_droite(h_pun)                  # (z,w)∈punion
    # z∈dom(punion)  via axiome dom + S5
    ex_w2 = N.modus_ponens(zw_in_pun, N.s5(appartient(E.couple(vz, var("y")), vpun), vw, "y"))
    car_dom_pun = instancie(instancie(ax_dom, vpun), vz)        # z∈dom(punion) ⇔ (∃y)((z,y)∈punion)
    z_in_dpun = N.modus_ponens(ex_w2, equivalence_arriere(car_dom_pun))  # z∈dom(punion)
    # punion∈D ⇒ (∃yseg∈seg(x)) est_essai(punion, yseg)   [axiome S8]
    axS8 = _inst_Dfam_real(vh, e, G, vx, vpun, V, "yseg")
    corpsS8 = N.modus_ponens(pun_in_D, equivalence_avant(axS8))  # amb ∧ (∃yseg)(...)
    selS8 = conjonction_elim_droite(corpsS8)                    # (∃yseg)( yseg∈seg(x) ∧ est_essai(punion,yseg) )
    # corps témoin yseg :  yseg∈seg(x) ∧ est_essai(punion,yseg) ⇒ z∈seg(x)
    vys = var("yseg")
    corps_ys = et(appartient(vys, seg), est_essai(vpun, vh, R, ve, vys, zb))
    h_ys = N.assume(corps_ys)
    ys_in_seg = conjonction_elim_gauche(h_ys)                   # yseg∈seg(x)
    essai_ys = conjonction_elim_droite(h_ys)                    # est_essai(punion,yseg)
    dom_pun_eq = conjonction_elim_droite(conjonction_elim_gauche(essai_ys))  # dom(punion)=seg(yseg)∪{yseg}
    # z∈seg(yseg)∪{yseg}  (réécrire dom(punion))
    segys = E.segment_extremite(R, ve, vys)
    sys = E.singleton(vys)
    z_in_segys_union = N.modus_ponens(z_in_dpun, equivalence_avant(
        N.modus_ponens(dom_pun_eq, N.s6(E.dom(vpun), dom_essai(R, ve, vys), "wdz", appartient(vz, var("wdz"))))))
    z_disj = N.modus_ponens(z_in_segys_union, equivalence_avant(_instance_reunion(segys, sys, vz)))  # z∈seg(yseg) ou z∈{yseg}

    # segment membership instances (binder order E, x, y) :
    th_seg = E.theorie_segment_extremite(R)
    ax_seg = N.axiome(th_seg, E.axiome_segment_extremite(R))
    # yseg∈seg(x) ⇔ ((yseg∈E ∧ yseg≤x) ∧ yseg≠x)
    ys_seg_mem = instancie(instancie(instancie(ax_seg, ve), vx), vys)
    ys_body = N.modus_ponens(ys_in_seg, equivalence_avant(ys_seg_mem))   # (yseg∈E ∧ yseg≤x) ∧ yseg≠x
    ys_le_x = conjonction_elim_droite(conjonction_elim_gauche(ys_body))  # yseg≤x = (yseg,x)∈G
    ys_ne_x = conjonction_elim_droite(ys_body)                          # yseg≠x

    # CASE A : z∈seg(yseg) ⇒ z∈seg(x)
    h_zsegys = N.assume(appartient(vz, segys))
    # z∈seg(yseg) ⇔ ((z∈E ∧ z≤yseg) ∧ z≠yseg)
    z_segys_mem = instancie(instancie(instancie(ax_seg, ve), vys), vz)
    z_body = N.modus_ponens(h_zsegys, equivalence_avant(z_segys_mem))
    z_in_E = conjonction_elim_gauche(conjonction_elim_gauche(z_body))    # z∈E
    z_le_ys = conjonction_elim_droite(conjonction_elim_gauche(z_body))   # z≤yseg = (z,yseg)∈G
    # transitivité : (z≤yseg ∧ yseg≤x) ⇒ z≤x
    trans_inst = instancie(instancie(instancie(trans, vz), vys), vx)     # ((z,yseg)∈G ∧ (yseg,x)∈G)⇒(z,x)∈G
    z_le_x = N.modus_ponens(conjonction_intro(z_le_ys, ys_le_x), trans_inst)  # (z,x)∈G
    # z≠x  (antisymétrie) : si z=x alors (x,yseg)∈G et (yseg,x)∈G ⇒ x=yseg, contredisant yseg≠x
    #   ¬(z=x) prouvé par : assume z=x, dérive yseg=x via antisym appliqué, contredire yseg≠x
    h_z_eq_x = N.assume(egal(vz, vx))
    # réécrit z→x dans z≤yseg : (x,yseg)∈G
    x_le_ys = N.modus_ponens(z_le_ys, equivalence_avant(
        N.modus_ponens(h_z_eq_x, N.s6(vz, vx, "wzx", appartient(E.couple(var("wzx"), vys), _t(G))))))  # (x,yseg)∈G
    # antisym (x,yseg) : ((x,yseg)∈G ∧ (yseg,x)∈G) ⇒ x=yseg
    antisym_inst = instancie(instancie(antisym, vx), vys)
    x_eq_ys = N.modus_ponens(conjonction_intro(x_le_ys, ys_le_x), antisym_inst)  # x=yseg
    ys_eq_x = N.modus_ponens(x_eq_ys, symetrie(vx, vys))                 # yseg=x
    faux = N.modus_ponens(ys_eq_x, N.modus_ponens(ys_ne_x, N.s2(non(egal(vys, vx)), egal(vz, vx) and non(egal(vz, vx)))))
    # construire ¬(z=x) proprement : (z=x) ⇒ FAUX, donc ¬(z=x)
    z_ne_x_cibleA = non(egal(vz, vx))
    inner = N.modus_ponens(ys_eq_x, N.modus_ponens(ys_ne_x, N.s2(non(egal(vys, vx)), z_ne_x_cibleA)))
    impA_neg = N.loi_deduction(egal(vz, vx), inner)                     # (z=x) ⇒ ¬(z=x)
    _, notP = antecedent_consequent(impA_neg.conclusion)
    z_ne_x = N.modus_ponens(impA_neg, N.s1(notP))                       # ¬(z=x)
    # z∈seg(x) ⇐ ((z∈E ∧ z≤x) ∧ z≠x)
    z_seg_mem = instancie(instancie(instancie(ax_seg, ve), vx), vz)     # z∈seg(x) ⇔ ((z∈E ∧ z≤x)∧z≠x)
    z_in_segx_A = N.modus_ponens(
        conjonction_intro(conjonction_intro(z_in_E, z_le_x), z_ne_x),
        equivalence_arriere(z_seg_mem))                                 # z∈seg(x)
    impA = N.loi_deduction(appartient(vz, segys), z_in_segx_A)

    # CASE B : z∈{yseg} ⇒ z∈seg(x)  (z=yseg, yseg∈seg(x))
    h_zsys = N.assume(appartient(vz, sys))
    z_eq_ys = N.modus_ponens(h_zsys, equivalence_avant(singleton_membre(vz, vys)))  # z=yseg
    ys_eq_z = N.modus_ponens(z_eq_ys, symetrie(vz, vys))               # yseg=z
    z_in_segx_B = N.modus_ponens(ys_in_seg, equivalence_avant(
        N.modus_ponens(ys_eq_z, N.s6(vys, vz, "wyz", appartient(var("wyz"), seg)))))  # z∈seg(x)
    impB = N.loi_deduction(appartient(vz, sys), z_in_segx_B)

    z_in_segx = cas(z_disj, impA, impB)                                # z∈seg(x)   [sous corps_ys, …]
    # élimine témoin yseg
    imp_ys = N.loi_deduction(corps_ys, z_in_segx)
    ex_ys = existe_elimination(imp_ys, "yseg")
    z_in_segx_2 = N.modus_ponens(selS8, ex_ys)                         # z∈seg(x)   [corps_pun, …]
    # élimine témoin punion
    imp_pun = N.loi_deduction(corps_pun, z_in_segx_2)
    ex_pun = existe_elimination(imp_pun, pun)
    z_in_segx_3 = N.modus_ponens(ex_pq, ex_pun)                        # z∈seg(x)   [(z,w)∈⋃D, …]
    # élimine témoin w
    imp_w = N.loi_deduction(appartient(E.couple(vz, vw), Ux), z_in_segx_3)
    ex_w_imp = existe_elimination(imp_w, w)
    z_in_segx_4 = N.modus_ponens(ex_w, ex_w_imp)                       # z∈seg(x)   [z∈dom⋃D, bo]
    incl_sub0 = N.generalisation(zz, N.loi_deduction(appartient(vz, dU), z_in_segx_4))  # (∀zseg)(z∈dU⇒z∈seg)
    incl_sub = N.modus_ponens(incl_sub0, equivalence_avant(alpha_pour_tout(
        zz, "z", impl(appartient(vz, dU), appartient(vz, seg)))))      # dom⋃D ⊂ seg

    # ── (⊇) inclus(seg, dom(⋃D)) :  z∈seg(x) ⇒ z∈dom(⋃D) ────────────────────────
    cov = _couverture_membre(vh, e, G, vx, V, zz, p, "yD", zb)          # (∃p)(p∈D ∧ z∈dom p ∧ val=vh)  [antec, z∈seg]
    vpc = var(p)
    gab = et(et(appartient(vpc, Dx), appartient(vz, E.dom(vpc))), egal(E.valeur(Ux, vz), vh(vz)))
    h_gab = N.assume(gab)
    pc_in_D = conjonction_elim_gauche(conjonction_elim_gauche(h_gab))   # p∈D
    z_in_dpc = conjonction_elim_droite(conjonction_elim_gauche(h_gab))  # z∈dom(p)
    # z∈dom(p) ⇒ (∃y)((z,y)∈p) ⇒ (z, valeur(p,z))∈p
    car_dom_pc = instancie(instancie(ax_dom, vpc), vz)                 # z∈dom p ⇔ (∃y)((z,y)∈p)
    ex_y_pc = N.modus_ponens(z_in_dpc, equivalence_avant(car_dom_pc))  # (∃y)((z,y)∈p)
    from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_dans_graphe
    zvz_in_pc = N.modus_ponens(ex_y_pc, N.loi_deduction(
        existe("y", appartient(E.couple(vz, var("y")), vpc)),
        valeur_dans_graphe(vpc, vz)))                                  # (z,valeur(p,z))∈p
    # (z,valeur(p,z))∈⋃D  via _membre_dans_union pattern
    cple = E.couple(vz, E.valeur(vpc, vz))
    Rform = et(appartient(var("punion"), Dx), appartient(cple, var("punion")))
    ex_intro = N.modus_ponens(conjonction_intro(pc_in_D, zvz_in_pc), N.s5(Rform, vpc, "punion"))  # (∃punion)(...)
    cple_in_U = N.modus_ponens(ex_intro, equivalence_arriere(_inst_union_famille(Dx, cple)))      # (z,val)∈⋃D
    # z∈dom(⋃D)  via axiome dom + S5
    ex_w_U = N.modus_ponens(cple_in_U, N.s5(appartient(E.couple(vz, var("y")), Ux), E.valeur(vpc, vz), "y"))
    z_in_dU = N.modus_ponens(ex_w_U, equivalence_arriere(car_dom))     # z∈dom(⋃D)   [gab]
    # élimine témoin p de cov
    imp_gab = N.loi_deduction(gab, z_in_dU)
    ex_gab = existe_elimination(imp_gab, p)
    z_in_dU_2 = N.modus_ponens(cov, ex_gab)                            # z∈dom(⋃D)   [antec, z∈seg]
    incl_sup0 = N.generalisation(zz, N.loi_deduction(appartient(vz, seg), z_in_dU_2))  # (∀zseg)(z∈seg⇒z∈dU)
    incl_sup = N.modus_ponens(incl_sup0, equivalence_avant(alpha_pour_tout(
        zz, "z", impl(appartient(vz, seg), appartient(vz, dU)))))      # seg ⊂ dom⋃D

    # extensionnalité : (dom⋃D⊂seg ∧ seg⊂dom⋃D) ⇒ dom⋃D=seg
    dom_eq = N.modus_ponens(conjonction_intro(incl_sub, incl_sup),
                            extensionnalite_appliquee(dU, seg))         # dom(⋃D)=seg   [antec, bo]
    assert dom_eq.conclusion == egal(dU, seg), "couverture_segment_realise : ≠ dom(⋃D)=seg"

    # enveloppe (∀x)( x∈E ⇒ ( antec_ambiant(x) ⇒ dom⋃D=seg ) ) ; bo reste libre
    body = N.loi_deduction(appartient(vx, ve),
                           N.loi_deduction(antec, dom_eq))
    res = N.generalisation(x, body)

    cible = clause_P3_ambiant(vh, e, G, x, V, y, p, zb)
    assert res.conclusion == cible, "couverture_segment_realise : ≠ clause_P3_ambiant"
    assert bo in res.hypotheses, "couverture_segment_realise : bon ordre absent"
    assert len(res.hypotheses) == 1, "couverture_segment_realise : hyps ≠ 1 (devrait être {bo})"
    assert res.conclusion not in res.hypotheses, "couverture_segment_realise : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — EXISTENCE C60 avec (P2) DÉCHARGÉE ; (P3),(P4) restantes (bare).
# ════════════════════════════════════════════════════════════════════════════
def recursion_transfinie_existence_complet(vh, e="E", G="G", V="Vval",
                                           x="x0tf", y="ytf"):
    """🎯 EXISTENCE C60 (§III.2) pour la famille CONCRÈTE Dfam_real, (P2) DÉCHARGÉE :

      { est_bien_ordonne(R,E),  clause_P3,  clause_P4 }
        ⊢ (∀x)( x∈E ⇒ (∃p)( est_essai(p, vh, R, E, x) ) ).

    On part de `recursion_transfinie_existence_reduite` (= existence sous {bo,P2,P3,P4})
    et on DÉCHARGE la clause (P2) par `coincidence_segment_realise` (CLOS, 0 hyp).  Ne
    restent que { bon ordre, clause_P3, clause_P4 } — trois hypothèses honnêtes.

    ⚠️ HONNÊTETÉ DU RÉSIDU.  Les clauses (P3),(P4) restantes sont ici prises sous leur
    forme NOMINALE `clause_P3` / `clause_P4` (antécédent d'induction BARE de C59, i.e.
    « tout y<x est couvert par un essai »).  Ce module CLÔT (P3),(P4) sous leur forme
    AMBIANTE `clause_P3_ambiant` / `clause_P4_ambiant` (`couverture_segment_realise` sous
    {bo} ; `recursion_segment_realise` CLOS), où l'antécédent EXIGE EN PLUS que les
    essais-témoins des y<x vivent dans 𝔓(E×V) (`antecedent_couverture_ambiant`) — la
    SEULE chose dont la membership Dfam_real(x) (sélection S8 dans 𝔓(E×V)) a besoin.
    Le PONT bare→ambiant (montrer qu'un essai sur un segment est ipso facto ⊂E×V, donc
    ∈𝔓(E×V)) demande de relier les valeurs-règle vh(z) à V — un chunk à part NON clos
    ici (vh est OPAQUE, sans contrainte vh(z)∈V).  C'est pourquoi (P3),(P4) BARE
    restent des hypothèses honnêtes de l'assemblage, tandis que leurs variantes AMBIANTES
    sont des THÉORÈMES (closes/sous bo).  Conclusion ∉ hypothèses (non vacuous)."""
    from bourbaki.ordre.ensembles_c60_realisation import (
        recursion_transfinie_existence_reduite, clause_P2 as _clause_P2,
        clause_P3 as _clause_P3, clause_P4 as _clause_P4,
    )
    from bourbaki.ordre.ensembles_recursion_transfinie_existence import couverture_totale
    R = _graphe_R(G)
    ve = _t(e)
    couvert = couvert_essai(vh, R, ve)

    base = recursion_transfinie_existence_reduite(vh, e, G, V, x, y)   # {bo,P2,P3,P4}
    p2 = coincidence_segment_realise(vh, e, G, x, V, y)               # ⊢ clause_P2  [CLOS]
    p2_form = _clause_P2(vh, e, G, x, V, y)
    assert p2.conclusion == p2_form, "existence_complet : ≠ clause_P2"
    res = N.modus_ponens(p2, N.loi_deduction(p2_form, base))          # {bo,P3,P4}

    cible = couverture_totale(couvert, ve, x)
    assert res.conclusion == cible, "existence_complet : ≠ couverture totale (existence)"
    W = E.est_bien_ordonne(R, ve)
    assert W in res.hypotheses, "existence_complet : bon ordre absent"
    assert _clause_P3(vh, e, G, x, V, y) in res.hypotheses, "existence_complet : P3 absente"
    assert _clause_P4(vh, e, G, x, V, y) in res.hypotheses, "existence_complet : P4 absente"
    assert p2_form not in res.hypotheses, "existence_complet : P2 PAS déchargée"
    assert len(res.hypotheses) == 3, "existence_complet : hyps ≠ 3 (devrait être {bo,P3,P4})"
    assert res.conclusion not in res.hypotheses, "existence_complet : VACUOUS"
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
    "clause_P4_ambiant", "recursion_segment_realise",
    # 🎯 clause (P3) sous l'antécédent ambiant (sous bon ordre)
    "clause_P3_ambiant", "couverture_segment_realise",
    # 🎯 assemblage : existence C60 avec (P2) déchargée, {bo,P3,P4} restantes
    "recursion_transfinie_existence_complet",
]
