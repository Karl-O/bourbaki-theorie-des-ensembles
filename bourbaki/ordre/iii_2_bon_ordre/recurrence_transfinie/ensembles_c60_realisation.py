"""§III.2 — RÉCURRENCE TRANSFINIE (Critère C60), EXISTENCE : RÉALISATION DE LA FAMILLE.

Suite DIRECTE de `ensembles_c60_final` (qui CLOSE l'existence C60 sous
{ est_bien_ordonne(R,E), realisation_famille } via `couvert_essai_depuis_famille`,
`heredite_couverture_realisee` et `recursion_transfinie_existence`).  Ce module
ATTAQUE le dernier verrou honnête `realisation_famille` en CONSTRUISANT, par S8, la
famille CONCRÈTE des essais des y<x et en DÉCHARGEANT autant de ses 5 clauses que la
construction le permet PROPREMENT.

────────────────────────────────────────────────────────────────────────────────
CE QUE `realisation_famille` PAQUETTE (cf. `_proprietes_famille` de c60_final).

  realisation_famille(Dfam, vval, vh, R, E) =
    (∀x)( x∈E ⇒ ( (∀y)(y∈seg(R,E,x) ⇒ couvert_essai[y]) ⇒ proprietes(Dfam(x)) ) ),
  où proprietes(Dfam(x)) est la CONJONCTION DE 5 CLAUSES :
    (P1) membres_fonctionnels(Dfam(x))   — chaque membre de la famille est fonctionnel ;
    (P2) coincidence_membres(Dfam(x))    — deux membres coïncident en valeur sur tout
                                           antécédent commun (⇐ solutions_coincident) ;
    (P3) dom(⋃Dfam(x)) = seg(R,E,x)      — les domaines des essais des y<x RECOUVRENT
                                           exactement le segment ;
    (P4) recursion_sur_segment(Dfam(x),…)— ⋃Dfam(x) satisfait l'équation de récursion
                                           sur le segment ;
    (P5) vval(x) = vh(x)                  — la valeur posée au nouveau point.

────────────────────────────────────────────────────────────────────────────────
LA CONSTRUCTION (S8) — la FAMILLE CONCRÈTE des essais des y<x.

  Dfam_real(x) := { p ∈ 𝔓(E×V) | (∃y)( y∈seg(R,E,x) ∧ est_essai(p, vh, R, E, y) ) }

  C'EST exactement « l'ensemble des essais des points y<x » : un graphe p est membre
  ssi il est dans l'ambiant 𝔓(E×V) (parties du produit, A3+produit — EXISTANTS) ET
  c'est un essai pour UN point y du segment.  La collectivisation est LÉGITIME par S8
  (sélection dans l'EXISTANT 𝔓(E×V)) + unicité A1, isolée dans une THÉORIE DÉDIÉE
  paramétrée `theorie_Dfam_real` — EXACTEMENT le motif `Ncol` / `union_famille` /
  `lim_proj`.  theorie_ensembles() reste = 22.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST CLOS ICI (par CONSTRUCTION, theorie=22, tout DÉRIVÉ).

  (P1) `membres_fonctionnels_realise`  ⊢ membres_fonctionnels(Dfam_real(x))   [CLOS, 0 hyp].
       Tout membre p de Dfam_real(x) est fonctionnel : par l'axiome S8, p est un essai
       d'un y<x, et est_essai(p,y) CONTIENT est_fonctionnel(p) (1er conjoint).  Le
       témoin y de la sélection est éliminé (existe_elimination, y∉est_fonctionnel(p)).
       ⟹ La clause (P1) est INCONDITIONNELLE pour la famille concrète.

  (P5) `equation_au_point_realise`  ⊢ vh(x) = vh(x)   [CLOS, 0 hyp].
       En posant vval := vh, la clause (P5) `vval(x)=vh(x)` devient vh(x)=vh(x),
       VRAIE par réflexivité.  C'est le CHOIX NATUREL : la valeur posée au nouveau
       point EST la valeur-règle.  ⟹ La clause (P5) est INCONDITIONNELLE.

  `realisation_famille_reduite`  (l'ASSEMBLAGE)
       ⊢ { (P2)_universel, (P3)_universel, (P4)_universel }
         ⊢ realisation_famille(Dfam_real, vh, vh, R, E)                  [3 hyps honnêtes].
       On INSTANCIE realisation_famille à la famille CONCRÈTE Dfam_real et à vval:=vh.
       Les 5 clauses : (P1),(P5) sont DÉCHARGÉES PAR CONSTRUCTION (closes ci-dessus) ;
       (P2),(P3),(P4) restent — prises sous forme UNIVERSELLE (∀x∈E)(antéc ⇒ clause)
       (les hypothèses HONNÊTES résiduelles).  La RÉALISATION est ainsi RÉDUITE de
       5 à 3 clauses : exactement (P2)+(P3)+(P4).

────────────────────────────────────────────────────────────────────────────────
LE RÉSIDU HONNÊTE EXACT (reporté, cf. rapport en bas).

  Ne restent que les TROIS clauses substantielles du contenu transfini :
    (P2) coincidence_membres(Dfam_real(x)) — DEMANDE `solutions_coincident` appliqué
         aux essais des y<x (cohérence par C60-unicité : deux essais coïncident sur
         leur recouvrement).  C'est le PONT niveau-valeur → niveau-graphe sur la
         famille CONCRÈTE (le pont générique `famille_compatible_depuis_coincidence`
         est clos, mais SA prémisse coincidence_membres(Dfam_real) sur la famille
         concrète exige d'extraire les deux essais témoins et de leur appliquer
         solutions_coincident — chunk distinct).
    (P3) dom(⋃Dfam_real(x)) = seg(R,E,x) — DEMANDE la double inclusion : tout point
         z<x est dans le domaine d'un essai (⇐ couverture des y<x, l'antécédent), et
         réciproquement tout antécédent d'un essai des y<x est <x.  C'est la COUVERTURE
         des segments par les essais.
    (P4) recursion_sur_segment(Dfam_real(x),…) — DEMANDE le TRANSFERT de l'équation de
         récursion de chaque essai à la réunion (⇐ `valeur_union_famille` (c60_coeur)
         + l'équation de chaque essai sur son domaine).

  Ces trois clauses sont le CONTENU INDUCTIF non trivial de la construction de
  Bourbaki.  Elles sont HONNÊTES, NON VACUOUS, NON FAUSSES (ce sont des théorèmes
  vrais du cadre, conséquences de couvert_essai[y] pour y<x + C60-unicité).

INVARIANT : theorie_ensembles() = 22.  L'unique axiome introduit est celui de
Dfam_real (sélection S8 dans 𝔓(E×V)), dans la THÉORIE DÉDIÉE `theorie_Dfam_real` —
JAMAIS la réalisation elle-même.  (P1),(P5) DÉRIVÉES, jamais postulées.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination

from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    est_essai, couvert_essai,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_final import (
    membres_fonctionnels, coincidence_membres, recursion_sur_segment,
    equation_au_point, realisation_famille, _proprietes_famille,
    recursion_transfinie_existence,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import couverture_totale


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  LA CONSTRUCTION S8 — Dfam_real(x) = { p∈𝔓(E×V) | (∃y∈seg(R,E,x)) est_essai(p,y) }.
#  Terme opaque + axiome DÉFINITIONNEL (sélection S8 dans l'EXISTANT 𝔓(E×V), A1).
#  theorie_ensembles() reste = 22 (axiome en THÉORIE DÉDIÉE paramétrée).
# ════════════════════════════════════════════════════════════════════════════
def ambiant(e, V="Vval"):
    """L'AMBIANT 𝔓(E×V) — parties du produit E×V (A3 + produit, EXISTANTS).

    V (par défaut « Vval ») = l'ensemble des valeurs candidates ; E×V EXISTE
    (produit de deux ensembles), donc 𝔓(E×V) EXISTE (axiome des parties A3).  C'est
    le CONTENANT légitime de la séparation S8 (tout graphe-essai p⊂E×V y vit)."""
    return E.parties(E.produit(_t(e), _t(V)))


def Dfam_real(vh, e="E", G="G", x="x0", V="Vval"):
    """Dfam_real(x) := { p ∈ 𝔓(E×V) | (∃y)( y∈seg(R,E,x) ∧ est_essai(p, vh, R, E, y) ) }.

    La FAMILLE CONCRÈTE des essais des points y<x (sélection S8 dans l'EXISTANT
    𝔓(E×V)).  Un graphe p en est membre ssi p est un essai pour UN point y du
    segment seg(R,E,x).  Terme opaque (motif `Ncol`/`union_famille`).

    vh : règle Terme→Terme (lue dans est_essai).  Le terme INDEX ne porte que E, x, V
    (comme `Ncol(a)` n'embarque pas l'ordre — la relation R=(·,·)∈G et la règle vh
    sont CAPTURÉES dans le sélecteur de l'axiome ci-dessous, pas dans le terme index ;
    le segment lui-même est seg_ext(E,x), indépendant de G au niveau terme)."""
    return app("c60_Dfam_real", _t(e), _t(x), _t(V))


def _corps_Dfam_real(vh, e, G, x, p, V="Vval", y="yD"):
    """Corps de Dfam_real(x) en p :  p∈𝔓(E×V)  et  (∃y)( y∈seg(R,E,x) ∧ est_essai(p,y) )."""
    R = _graphe_R(G)
    vp, vy = _t(p), var(y)
    seg = E.segment_extremite(R, _t(e), _t(x))
    amb = appartient(vp, ambiant(e, V))
    sel = existe(y, et(appartient(vy, seg), est_essai(vp, vh, R, _t(e), vy)))
    return et(amb, sel)


def axiome_Dfam_real(vh, e="E", G="G", x="x0", V="Vval", p="pD", y="yD"):
    """⊢-schéma  (∀x)(∀p)( p∈Dfam_real(x) ⇔ ( p∈𝔓(E×V) ∧ (∃y∈seg)( est_essai(p,y) ) ) ).

    Axiome DÉFINITIONNEL de la séparation S8 des essais DANS l'ensemble EXISTANT
    𝔓(E×V) (sélection légitime, unicité A1) — motif `Ncol` / `difference`.  N'altère
    PAS theorie_ensembles() (=22).  Le test sélecteur est « p est un essai d'un y<x » ;
    le contenant 𝔓(E×V) EXISTE (A3 + produit)."""
    vx, vp = var(x), var(p)
    return pourtout(x, pourtout(p,
        equiv(appartient(vp, Dfam_real(vh, e, G, vx, V)),
              _corps_Dfam_real(vh, e, G, vx, vp, V, y))))


def theorie_Dfam_real(vh, e="E", G="G", x="x0", V="Vval", p="pD", y="yD"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Dfam_real (C60-existence, S8).

    Schéma identique à `theorie_Ncol` / `theorie_union_famille` : l'axiome référence
    le segment, le produit et est_essai, donc théorie dédiée — JAMAIS dans
    theorie_ensembles() (=22)."""
    return N.Theorie("Dfam-real-C60", [axiome_Dfam_real(vh, e, G, x, V, p, y)])


def _inst_Dfam_real(vh, e, G, x, p, V="Vval", y="yD"):
    """⊢ ( p∈Dfam_real(x) ⇔ (p∈𝔓(E×V) et (∃y∈seg)est_essai(p,y)) )  (axiome instancié)."""
    ax = N.axiome(theorie_Dfam_real(vh, e, G, V=V, p=p, y=y),
                  axiome_Dfam_real(vh, e, G, V=V, p=p, y=y))
    ax = instancie(ax, _t(x))                                    # x := x
    ax = instancie(ax, _t(p))                                    # p := p
    return ax


def membre_Dfam_real(vh, e="E", G="G", x="x0", p="pD", V="Vval", y="yD"):
    """⊢ ( p∈Dfam_real(x) ) ⇔ ( p∈𝔓(E×V) et (∃y∈seg(R,E,x))( est_essai(p,y) ) )."""
    return _inst_Dfam_real(vh, e, G, var(x), var(p), V, y)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSE (P1) — membres_fonctionnels(Dfam_real(x))  [CLOS PAR CONSTRUCTION].
# ════════════════════════════════════════════════════════════════════════════
def membres_fonctionnels_realise(vh, e="E", G="G", x="x0", V="Vval",
                                 p="pmf", y="yD"):
    """⊢ membres_fonctionnels( Dfam_real(x) )                        [CLOS, 0 hyp].

    🎯 LA CLAUSE (P1) DÉCHARGÉE PAR CONSTRUCTION.  Tout membre p de la famille
    concrète Dfam_real(x) est FONCTIONNEL — INCONDITIONNELLEMENT :
      • p∈Dfam_real(x) ⇒ (p∈𝔓(E×V) et (∃y∈seg)est_essai(p,y))   [axiome S8] ;
      • (∃y∈seg)est_essai(p,y) ⇒ est_fonctionnel(p)             [est_essai contient
        est_fonctionnel(p) en 1er conjoint ; témoin y éliminé, y∉est_fonctionnel(p)].

    membres_fonctionnels(Dfam_real(x)) = (∀p)( p∈Dfam_real(x) ⇒ est_fonctionnel(p) )
    est donc un THÉORÈME CLOS pour la famille concrète.  Aucune hypothèse.  Non
    vacuous (la conclusion n'est pas une hypothèse — il n'y a pas d'hypothèse)."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    # binder de membres_fonctionnels(Dx) : 'pmf'
    vp = var(p)
    seg = E.segment_extremite(R, ve, vx)

    ax = _inst_Dfam_real(vh, e, G, vx, vp, V, y)                 # p∈Dx ⇔ (amb et (∃y∈seg)essai)
    h_pin = N.assume(appartient(vp, Dx))                        # p∈Dx
    corps = N.modus_ponens(h_pin, equivalence_avant(ax))        # amb et (∃y∈seg)essai
    sel = conjonction_elim_droite(corps)                        # (∃y)( y∈seg et est_essai(p,y) )

    # y∈seg et est_essai(p,y) ⇒ est_fonctionnel(p)   (1er conjoint de est_essai)
    vy = var(y)
    corps_y = et(appartient(vy, seg), est_essai(vp, vh, R, ve, vy))
    h_corps_y = N.assume(corps_y)
    essai_y = conjonction_elim_droite(h_corps_y)                # est_essai(p,y)
    func_p = conjonction_elim_gauche(conjonction_elim_gauche(essai_y))   # est_fonctionnel(p)
    assert func_p.conclusion == E.est_fonctionnel(vp), \
        "membres_fonctionnels_realise : ≠ est_fonctionnel(p)"

    # élimine le témoin y (y∉est_fonctionnel(p) ni dans Γ)
    imp_y = N.loi_deduction(corps_y, func_p)                    # corps_y ⇒ func(p)
    ex_imp = existe_elimination(imp_y, y)                       # (∃y)corps_y ⇒ func(p)
    func_from_sel = N.modus_ponens(sel, ex_imp)                 # func(p)   [p∈Dx]

    # p∈Dx ⇒ func(p), généralise (∀p)
    body = N.loi_deduction(appartient(vp, Dx), func_from_sel)   # p∈Dx ⇒ func(p)
    res = N.generalisation(p, body)

    cible = membres_fonctionnels(Dx, p)
    assert res.conclusion == cible, "membres_fonctionnels_realise : ≠ membres_fonctionnels(Dfam_real(x))"
    assert res.est_clos, "membres_fonctionnels_realise : non clos (devrait être 0 hyp)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSE (P5) — equation_au_point(vh(x), vh, x)  [CLOS PAR CHOIX vval:=vh].
# ════════════════════════════════════════════════════════════════════════════
def equation_au_point_realise(vh, x="x0"):
    """⊢ vh(x) = vh(x)   ( = equation_au_point(vh(x), vh, x) )           [CLOS, 0 hyp].

    🎯 LA CLAUSE (P5) DÉCHARGÉE PAR CHOIX.  En posant vval := vh (la valeur posée au
    nouveau point EST la valeur-règle vh(x)), la clause (P5) `vval(x)=vh(x)` devient
    vh(x)=vh(x), VRAIE par réflexivité.  C'est le choix CANONIQUE de la construction
    de Bourbaki (f(x)=h(x,f|seg))."""
    vx = _t(x)
    res = N.reflexivite(vh(vx))                                 # vh(x)=vh(x)

    cible = equation_au_point(vh(vx), vh, vx)
    assert res.conclusion == cible, "equation_au_point_realise : ≠ vh(x)=vh(x)"
    assert res.est_clos, "equation_au_point_realise : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS — les TROIS clauses RÉSIDUELLES (P2),(P3),(P4) sous forme UNIVERSELLE.
#  (hypothèses HONNÊTES : le contenu inductif non trivial de la construction.)
# ════════════════════════════════════════════════════════════════════════════
def _vval_canon(vh):
    """vval := vh  (le choix canonique : la valeur posée au point EST la valeur-règle)."""
    return vh


def antecedent_couverture(vh, e, G, x, y="ytf"):
    """L'ANTÉCÉDENT de l'hérédité :  (∀y)( y∈seg(R,E,x) ⇒ couvert_essai[y] ).

    « Tout y<x est couvert par un essai. »  C'est l'hypothèse d'induction de C59
    (le contexte sous lequel la famille Dfam_real(x) est réalisée)."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    couvert = couvert_essai(vh, R, ve)
    seg = E.segment_extremite(R, ve, vx)
    return pourtout(y, impl(appartient(var(y), seg), couvert(var(y))))


def clause_P2(vh, e="E", G="G", x="x0", V="Vval", y="ytf"):
    """(∀x)( x∈E ⇒ ( antéc(x) ⇒ coincidence_membres(Dfam_real(x)) ) )  [P2 universelle].

    « Pour tout x∈E dont les y<x sont couverts, deux membres quelconques de
    Dfam_real(x) coïncident en valeur sur tout antécédent commun. »  C'est la
    cohérence des essais des y<x (⇐ solutions_coincident / C60-unicité), portée à la
    famille concrète.  HYPOTHÈSE HONNÊTE (résidu)."""
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    return pourtout(x, impl(appartient(vx, ve),
        impl(antecedent_couverture(vh, e, G, vx, y), coincidence_membres(Dx))))


def clause_P3(vh, e="E", G="G", x="x0", V="Vval", y="ytf"):
    """(∀x)( x∈E ⇒ ( antéc(x) ⇒ dom(⋃Dfam_real(x)) = seg(R,E,x) ) )  [P3 universelle].

    « Pour tout x∈E dont les y<x sont couverts, les domaines des essais des y<x
    RECOUVRENT exactement le segment seg(R,E,x). »  C'est la COUVERTURE des segments.
    HYPOTHÈSE HONNÊTE (résidu)."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    Ux = union_famille(Dx)
    seg = E.segment_extremite(R, ve, vx)
    return pourtout(x, impl(appartient(vx, ve),
        impl(antecedent_couverture(vh, e, G, vx, y), egal(E.dom(Ux), seg))))


def clause_P4(vh, e="E", G="G", x="x0", V="Vval", y="ytf"):
    """(∀x)( x∈E ⇒ ( antéc(x) ⇒ recursion_sur_segment(Dfam_real(x),…) ) )  [P4 universelle].

    « Pour tout x∈E dont les y<x sont couverts, ⋃Dfam_real(x) satisfait l'équation de
    récursion sur seg(R,E,x). »  C'est le TRANSFERT de l'équation de chaque essai à la
    réunion (⇐ valeur_union_famille).  HYPOTHÈSE HONNÊTE (résidu)."""
    ve, vx = _t(e), _t(x)
    Dx = Dfam_real(vh, e, G, vx, V)
    return pourtout(x, impl(appartient(vx, ve),
        impl(antecedent_couverture(vh, e, G, vx, y),
             recursion_sur_segment(Dx, vh, G, e, vx))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — realisation_famille(Dfam_real, vh, vh, R, E) RÉDUITE de 5 à 3 clauses.
# ════════════════════════════════════════════════════════════════════════════
def realisation_famille_reduite(vh, e="E", G="G", x="x0", V="Vval", y="ytf"):
    """🎯 { clause_P2, clause_P3, clause_P4 } ⊢ realisation_famille(Dfam_real, vh, vh, R, E)
                                                                    [3 hyps honnêtes].

    L'ASSEMBLAGE de la RÉALISATION pour la famille CONCRÈTE Dfam_real et vval:=vh.
    realisation_famille INSTANCIÉE à (Dfam_real, vh, vh) est, pour chaque x∈E avec
    tous les y<x couverts, la conjonction des 5 clauses (P1..P5) de Dfam_real(x) :
      • (P1) membres_fonctionnels(Dfam_real(x))   ⇐ `membres_fonctionnels_realise` [CLOS] ;
      • (P2) coincidence_membres(Dfam_real(x))    ⇐ clause_P2(x)   [HONNÊTE, résidu] ;
      • (P3) dom(⋃Dfam_real(x))=seg(R,E,x)        ⇐ clause_P3(x)   [HONNÊTE, résidu] ;
      • (P4) recursion_sur_segment(Dfam_real(x),…)⇐ clause_P4(x)   [HONNÊTE, résidu] ;
      • (P5) vh(x)=vh(x)                           ⇐ `equation_au_point_realise` [CLOS].

    Les clauses (P1),(P5) sont DÉCHARGÉES PAR CONSTRUCTION ; (P2),(P3),(P4) restent
    sous leurs formes UNIVERSELLES (∀x∈E)(antéc⇒clause).  La RÉALISATION est ainsi
    RÉDUITE de 5 clauses à EXACTEMENT 3 — le contenu inductif non trivial.

    ⚠️ TROIS hypothèses HONNÊTES (theorie=22), déchargées par loi_deduction.  Conclusion
    ∉ hypothèses (non vacuous)."""
    R = _graphe_R(G)
    ve = _t(e)
    Dfam = lambda t: Dfam_real(vh, e, G, t, V)                  # famille concrète (Terme→Terme)
    vval = _vval_canon(vh)                                      # vval := vh
    vx = var(x)
    couvert = couvert_essai(vh, R, ve)
    seg = E.segment_extremite(R, ve, vx)
    antec = pourtout(y, impl(appartient(var(y), seg), couvert(var(y))))

    # hypothèses (P2),(P3),(P4) sous forme universelle
    hP2 = N.assume(clause_P2(vh, e, G, x, V, y))
    hP3 = N.assume(clause_P3(vh, e, G, x, V, y))
    hP4 = N.assume(clause_P4(vh, e, G, x, V, y))

    h_xE = N.assume(appartient(vx, ve))                         # x∈E
    h_antec = N.assume(antec)                                   # (∀y<x) couvert[y]

    Dx = Dfam(vx)
    Ux = union_famille(Dx)

    # (P1) PAR CONSTRUCTION
    c1 = membres_fonctionnels_realise(vh, e, G, vx, V)          # CLOS
    # (P2),(P3),(P4) : instancie l'hypothèse universelle à x, décharge x∈E puis antéc
    c2 = N.modus_ponens(h_antec, N.modus_ponens(h_xE, instancie(hP2, vx)))
    c3 = N.modus_ponens(h_antec, N.modus_ponens(h_xE, instancie(hP3, vx)))
    c4 = N.modus_ponens(h_antec, N.modus_ponens(h_xE, instancie(hP4, vx)))
    # (P5) PAR CHOIX vval:=vh
    c5 = equation_au_point_realise(vh, vx)                      # CLOS

    # proprietes(Dfam_real(x)) = ((((P1 et P2) et P3) et P4) et P5)
    props = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(c1, c2), c3), c4), c5)
    cible_props = _proprietes_famille(Dfam, vval, vh, G, e, vx)
    assert props.conclusion == cible_props, \
        "realisation_famille_reduite : ≠ proprietes(Dfam_real(x))"

    # x∈E ⇒ ( antéc ⇒ proprietes ), généralise (∀x)
    body = N.loi_deduction(appartient(vx, ve), N.loi_deduction(antec, props))
    res = N.generalisation(x, body)

    cible = realisation_famille(Dfam, vval, vh, G, e, x, y)
    assert res.conclusion == cible, "realisation_famille_reduite : ≠ realisation_famille(Dfam_real,vh,vh)"
    assert clause_P2(vh, e, G, x, V, y) in res.hypotheses, "realisation_famille_reduite : P2 absente"
    assert clause_P3(vh, e, G, x, V, y) in res.hypotheses, "realisation_famille_reduite : P3 absente"
    assert clause_P4(vh, e, G, x, V, y) in res.hypotheses, "realisation_famille_reduite : P4 absente"
    assert len(res.hypotheses) == 3, "realisation_famille_reduite : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "realisation_famille_reduite : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 CAPSTONE — EXISTENCE C60 sous { bon ordre, P2, P3, P4 } (famille CONCRÈTE).
# ════════════════════════════════════════════════════════════════════════════
def recursion_transfinie_existence_reduite(vh, e="E", G="G", V="Vval",
                                           x="x0tf", y="ytf"):
    """🎯🎯 EXISTENCE C60 (§III.2) pour la FAMILLE CONCRÈTE Dfam_real, vval:=vh :

      { est_bien_ordonne(R,E),  clause_P2,  clause_P3,  clause_P4 }
        ⊢ (∀x)( x∈E ⇒ (∃p)( est_essai(p, vh, R, E, x) ) ).

    L'EXISTENCE C60, le résidu `realisation_famille` étant DÉCONSTRUIT par la
    construction S8 : on RÉDUIT le bundle monolithique `realisation_famille` à ses
    TROIS clauses substantielles (P2),(P3),(P4) — les clauses (P1) (membres
    fonctionnels) et (P5) (équation au point) sont DÉCHARGÉES PAR CONSTRUCTION
    (`membres_fonctionnels_realise` / `equation_au_point_realise`).

    PREUVE : `recursion_transfinie_existence` (c60_final) donne l'existence sous
    { bon ordre, realisation_famille(Dfam_real, vh, vh) } ; on DÉCHARGE
    realisation_famille par `realisation_famille_reduite` (= 3 clauses honnêtes).

    ⚠️ vh DOIT produire un terme OPAQUE vh(x) (p.ex. app('rule', x)) — la valeur-règle
    réifiée comme terme dépendant, SANS τ interne (sinon collision de capture avec les
    liants de dom_singleton_couple du noyau déposé ; c'est la représentation des règles
    du test déposé `_vval`).  Le choix vval:=vh est canonique (f(x)=h(x,f|seg)).

    QUATRE hypothèses HONNÊTES (theorie=22) :
      • est_bien_ordonne(R,E)   — (E,R) bien ordonné (donnée de C60) ;
      • clause_P2               — coincidence_membres(Dfam_real(x)) (⇐ solutions_coincident) ;
      • clause_P3               — dom(⋃Dfam_real(x))=seg (⇐ couverture des y<x) ;
      • clause_P4               — recursion_sur_segment(Dfam_real(x)) (⇐ valeur_union_famille).
    Conclusion ∉ hypothèses (non vacuous)."""
    R = _graphe_R(G)
    ve = _t(e)
    Dfam = lambda t: Dfam_real(vh, e, G, t, V)
    vval = _vval_canon(vh)
    couvert = couvert_essai(vh, R, ve)

    exist = recursion_transfinie_existence(Dfam, vval, vh, G, e, x, y)   # {bo, realisation}
    rf_form = realisation_famille(Dfam, vval, vh, G, e, x, y)
    red = realisation_famille_reduite(vh, e, G, x, V, y)                 # {P2,P3,P4} ⊢ realisation
    assert red.conclusion == rf_form, "existence_reduite : réduction ≠ realisation_famille"
    res = N.modus_ponens(red, N.loi_deduction(rf_form, exist))          # {bo,P2,P3,P4} ⊢ existence

    cible = couverture_totale(couvert, ve, x)
    assert res.conclusion == cible, "existence_reduite : ≠ couverture totale (existence)"
    W = E.est_bien_ordonne(R, ve)
    assert W in res.hypotheses, "existence_reduite : bon ordre absent"
    assert clause_P2(vh, e, G, x, V, y) in res.hypotheses, "existence_reduite : P2 absente"
    assert clause_P3(vh, e, G, x, V, y) in res.hypotheses, "existence_reduite : P3 absente"
    assert clause_P4(vh, e, G, x, V, y) in res.hypotheses, "existence_reduite : P4 absente"
    assert len(res.hypotheses) == 4, "existence_reduite : hyps ≠ 4"
    assert res.conclusion not in res.hypotheses, "existence_reduite : VACUOUS"
    return res


__all__ = [
    # la construction S8 de la famille concrète des essais des y<x
    "ambiant", "Dfam_real", "axiome_Dfam_real", "theorie_Dfam_real", "membre_Dfam_real",
    # 🎯 clauses CLOSES par construction
    "membres_fonctionnels_realise",   # (P1) CLOS, 0 hyp
    "equation_au_point_realise",      # (P5) CLOS, 0 hyp
    # énoncés des 3 clauses résiduelles (hypothèses honnêtes)
    "antecedent_couverture", "clause_P2", "clause_P3", "clause_P4",
    # 🎯 assemblage : realisation_famille RÉDUITE de 5 à 3 clauses
    "realisation_famille_reduite",
    # 🎯🎯 capstone : existence C60 sous { bon ordre, P2, P3, P4 }
    "recursion_transfinie_existence_reduite",
]
