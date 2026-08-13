"""§III.1-2 — STRUCTURE D'ORDRE de l'intervalle [0,a] pour l'ordre (induit) des
cardinaux : décomposition de est_bien_ordonne(≤_induit,[0,a]) et preuve des paliers
INCONDITIONNELS de la partie « relation d'ordre dans [0,a] » (Définition 1, E.III.2.1).

────────────────────────────────────────────────────────────────────────────────
RAPPEL :  est_bien_ordonne(R, [0,a])  =  est_relation_ordre_dans(R, [0,a])  et
          clause_plus_petit(R, [0,a]).

Et  est_relation_ordre_dans(R, E) = est_relation_ordre(R) et est_reflexive_dans_ordre(R,E),
avec est_relation_ordre(R) = transitive et antisymétrique et réflexive-implicite.

CE MODULE PROUVE INCONDITIONNELLEMENT, pour R := ordre INDUIT des cardinaux sur [0,a] :
  ✅ reflexive_dans_intervalle      — (∀x)( R_induit{x,x} ⇔ x∈[0,a] ).
  ✅ reflexif_implicite_intervalle  — (∀x,y)( R_induit{x,y} ⇒ (R_induit{x,x} et R_induit{y,y}) ).
  ✅ transitif_intervalle           — (∀x,y,z)( (R_induit{x,y} et R_induit{y,z}) ⇒ R_induit{x,z} ).

Ces trois paliers reposent sur :
  • inf_egal_reflexif   (X ≤ X, ensembles_cardinaux_theoremes) — INCONDITIONNEL ;
  • inf_egal_transitive (transitivité de ≤, ensembles_cardinaux_ordre) — INCONDITIONNEL ;
  • pure logique propositionnelle (les gardes x∈[0,a] de l'ordre induit).

⚠️ REPORTÉ honnêtement (les deux pièces dures) :
  • antisymetrie_intervalle  — (∀x,y)( (R_induit{x,y} et R_induit{y,x}) ⇒ x=y ).
       C'est CANTOR–BERNSTEIN (cantor_bernstein : (x≤y et y≤x)⇒Eq(x,y)) PLUS l'identité
       « x∈[0,a] cardinal ⇒ Card x = x » : Eq(x,y) ⇒ Card x = Card y = x = y.  Le théorème
       cantor_bernstein EST disponible ; le fil (Card x = x sur [0,a], passage Eq→égalité)
       reste à assembler — conditionné/posé en HYPOTHÈSE explicite ci-dessous.
  • clause_plus_petit(R_induit,[0,a])  — le BON ORDRE proprement dit (ordinal↔cardinal),
       l'unique vraie irréductible (cf. ensembles_ordinal_cardinal_correspondance).

INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import (
    ordre_induit_intervalle, intervalle_0a,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _refl_terme(t):
    """⊢ t ≤ t  pour un TERME t   (inf_egal_reflexif généralisé-instancié)."""
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))      # (∀X)(X≤X)
    return instancie(refl_all, _t(t))


def _trans_terme(u, v, w):
    """⊢ (u≤v et v≤w) ⇒ u≤w  pour des TERMES   (inf_egal_transitive généralisé-instancié)."""
    trans_all = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(trans_all, _t(u)), _t(v)), _t(w))


# ════════════════════════════════════════════════════════════════════════════
#  PALIER 1 — réflexivité DANS [0,a] :  (∀x)( R_induit{x,x} ⇔ x∈[0,a] )
#
#  R_induit{x,x} = ( (x≤x et x∈[0,a]) et x∈[0,a] ).
#  ⇒ : projeter x∈[0,a].   ⇐ : x∈[0,a] donne x≤x (réflexivité) ; assembler.
# ════════════════════════════════════════════════════════════════════════════
def reflexive_dans_intervalle(a="a", x="x"):
    """⊢ (∀x)( R_induit{x,x} ⇔ x∈[0,a] )   = est_reflexive_dans_ordre(R_induit,[0,a]).

    INCONDITIONNEL.  Sens ⇒ : projection de la garde x∈[0,a] de R_induit{x,x}.
    Sens ⇐ : x∈[0,a] ⇒ x≤x (inf_egal_reflexif) ⇒ R_induit{x,x}=((x≤x et x∈[0,a]) et x∈[0,a]).

    NB : le binder « x » ne collisionne PAS avec le τ-binder interne « y » des cardinaux ;
    inf_egal_reflexif au TERME x reste donc canonique, et la formule == le prédicat."""
    vx = _t(x)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    x_in = appartient(vx, interv)
    Rxx = Rind(vx, vx)                                            # ((x≤x et x∈I) et x∈I)
    # ⇒ : R_induit{x,x} ⇒ x∈[0,a]
    Hf = N.assume(Rxx)
    fwd_in = conjonction_elim_droite(Hf)                         # x∈[0,a]
    fwd = N.loi_deduction(Rxx, fwd_in)
    # ⇐ : x∈[0,a] ⇒ R_induit{x,x}
    Hb = N.assume(x_in)
    xlex = _refl_terme(vx)                                        # x≤x  (canonique : x ne collisionne pas)
    Rxx_b = conjonction_intro(conjonction_intro(xlex, Hb), Hb)   # ((x≤x et x∈I) et x∈I)
    bwd = N.loi_deduction(x_in, Rxx_b)
    eqv = conjonction_intro(fwd, bwd)                            # = equiv(R_induit{x,x}, x∈[0,a])
    return N.generalisation(x, eqv)


# ════════════════════════════════════════════════════════════════════════════
#  PALIER 2 — réflexivité IMPLICITE :
#     (∀x,y)( R_induit{x,y} ⇒ ( R_induit{x,x} et R_induit{y,y} ) )
#
#  R_induit{x,y} = ((x≤y et x∈I) et y∈I).  On en tire x∈I, y∈I ; puis x≤x, y≤y
#  (réflexivité) ; on assemble R_induit{x,x}=((x≤x et x∈I) et x∈I) et R_induit{y,y}.
# ════════════════════════════════════════════════════════════════════════════
def reflexif_implicite_intervalle(a="a", x="xo", y="yo"):
    """⊢ (∀x)(∀y)( R_induit{x,y} ⇒ ( R_induit{x,x} et R_induit{y,y} ) )
        = ordre_reflexif_implicite(R_induit).   INCONDITIONNEL.

    De R_induit{x,y}=((x≤y et x∈I) et y∈I) on projette x∈I, y∈I ; inf_egal_reflexif
    donne x≤x, y≤y ; on reconstruit R_induit{x,x} et R_induit{y,y}.

    ⚠️ binders par défaut xo,yo : non collisionnants avec le τ-binder interne « y »
    des cardinaux (sinon inf_egal_reflexif au TERME y serait α-renommé en « @0 » et la
    formule ne serait QU'α-équivalente au prédicat).  Avec xo,yo : == le prédicat."""
    vx, vy = _t(x), _t(y)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    Rxy = Rind(vx, vy)
    H = N.assume(Rxy)
    x_in = conjonction_elim_droite(conjonction_elim_gauche(H))   # x∈I
    y_in = conjonction_elim_droite(H)                            # y∈I
    xlex = _refl_terme(vx)                                        # x≤x
    yley = _refl_terme(vy)                                        # y≤y
    Rxx = conjonction_intro(conjonction_intro(xlex, x_in), x_in)  # R_induit{x,x}
    Ryy = conjonction_intro(conjonction_intro(yley, y_in), y_in)  # R_induit{y,y}
    concl = conjonction_intro(Rxx, Ryy)
    body = N.loi_deduction(Rxy, concl)
    return N.generalisation(x, N.generalisation(y, body))


# ════════════════════════════════════════════════════════════════════════════
#  PALIER 3 — TRANSITIVITÉ :
#     (∀x,y,z)( ( R_induit{x,y} et R_induit{y,z} ) ⇒ R_induit{x,z} )
#
#  R_induit{x,y}=((x≤y et x∈I) et y∈I), R_induit{y,z}=((y≤z et y∈I) et z∈I).
#  De x≤y, y≤z : x≤z (inf_egal_transitive) ; x∈I (de la 1ère), z∈I (de la 2ème) ;
#  on reconstruit R_induit{x,z}=((x≤z et x∈I) et z∈I).
#
#  ⚠️ BINDERS : appeler avec des noms NE COLLISIONNANT PAS avec le τ-binder interne
#  « y » de valeur(...)/diagonale (sinon l'instanciation α-renomme en « @0 » et casse
#  le matching).  Les binders par défaut xo,yo,zo conviennent (ce sont précisément
#  ceux de l'hypothèse résiduelle est_bien_ordonne).
# ════════════════════════════════════════════════════════════════════════════
def transitif_intervalle(a="a", x="xo", y="yo", z="zo"):
    """⊢ (∀x,y,z)( ( R_induit{x,y} et R_induit{y,z} ) ⇒ R_induit{x,z} )
        = ordre_transitif(R_induit).   INCONDITIONNEL (via inf_egal_transitive).

    De R_induit{x,y}, R_induit{y,z} on projette x≤y, y≤z, x∈I, z∈I ; inf_egal_transitive
    (généralisée puis instanciée aux TERMES x,y,z) donne x≤z ; on reconstruit
    R_induit{x,z}=((x≤z et x∈I) et z∈I).  ⚠️ binders par défaut xo,yo,zo (cf. note)."""
    vx, vy, vz = _t(x), _t(y), _t(z)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    Rxy, Ryz = Rind(vx, vy), Rind(vy, vz)
    hyp = et(Rxy, Ryz)
    H = N.assume(hyp)
    Hxy = conjonction_elim_gauche(H)
    Hyz = conjonction_elim_droite(H)
    xley = conjonction_elim_gauche(conjonction_elim_gauche(Hxy))  # x≤y
    x_in = conjonction_elim_droite(conjonction_elim_gauche(Hxy))  # x∈I
    ylez = conjonction_elim_gauche(conjonction_elim_gauche(Hyz))  # y≤z
    z_in = conjonction_elim_droite(Hyz)                          # z∈I
    xlez = N.modus_ponens(conjonction_intro(xley, ylez), _trans_terme(vx, vy, vz))  # x≤z
    Rxz = conjonction_intro(conjonction_intro(xlez, x_in), z_in)  # R_induit{x,z}
    body = N.loi_deduction(hyp, Rxz)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, body)))


# ════════════════════════════════════════════════════════════════════════════
#  PALIER 4 — ANTISYMÉTRIE :  (∀x,y)( ( R_induit{x,y} et R_induit{y,x} ) ⇒ x=y )
#
#  De R_induit{x,y}, R_induit{y,x} on projette x≤y, y≤x, x∈[0,a], y∈[0,a].
#  x,y∈[0,a] ⇒ est_cardinal(x), est_cardinal(y) (intervalle_implique_cardinal) ;
#  inf_egal_antisymetrique_card (= CANTOR–BERNSTEIN + « Card·=· » sur les cardinaux,
#  DÉJÀ PROUVÉ, ensembles_cardinaux_props_restantes_ordre) conclut x=y.
# ════════════════════════════════════════════════════════════════════════════
def _est_card_de_intervalle(a, t):
    """⊢ ( t ∈ [0,a] ) ⇒ est_cardinal(t)  pour un TERME t   (intervalle_implique_cardinal
    généralisé-instancié au terme t, avec a:=0, b:=a)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import intervalle_implique_cardinal
    gen = N.generalisation("ia", N.generalisation("ib", N.generalisation("ix",
        intervalle_implique_cardinal("ia", "ib", "ix"))))     # (∀ia,ib,ix)(ix∈[ia,ib]⇒card ix)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
    return instancie(instancie(instancie(gen, ZERO), _t(a)), _t(t))   # t∈[0,a] ⇒ card t


def antisymetrie_intervalle(a="a", x="xo", y="yo"):
    """⊢ (∀x,y)( ( R_induit{x,y} et R_induit{y,x} ) ⇒ x=y ) = ordre_antisymetrique(R_induit).

    🎯 PALIER FERMÉ (INCONDITIONNEL) — l'antisymétrie de l'ordre induit des cardinaux
    sur [0,a].  C'est CANTOR–BERNSTEIN assemblé : de R_induit{x,y}=((x≤y et x∈[0,a]) et
    y∈[0,a]) et R_induit{y,x} on extrait x≤y, y≤x, x∈[0,a], y∈[0,a] ; x,y∈[0,a] sont des
    cardinaux (intervalle_implique_cardinal) ; inf_egal_antisymetrique_card (CANTOR–
    BERNSTEIN + Card·=· DÉJÀ PROUVÉ) donne x=y.  ⚠️ binders xo,yo (non collisionnants)."""
    vx, vy = _t(x), _t(y)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    hyp = et(Rind(vx, vy), Rind(vy, vx))
    H = N.assume(hyp)
    Hxy = conjonction_elim_gauche(H)                            # ((x≤y et x∈I) et y∈I)
    Hyx = conjonction_elim_droite(H)                            # ((y≤x et y∈I) et x∈I)
    le_xy = conjonction_elim_gauche(conjonction_elim_gauche(Hxy))  # x≤y
    x_in = conjonction_elim_droite(conjonction_elim_gauche(Hxy))   # x∈[0,a]
    le_yx = conjonction_elim_gauche(conjonction_elim_gauche(Hyx))  # y≤x
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Hyx))   # y∈[0,a]
    card_x = N.modus_ponens(x_in, _est_card_de_intervalle(a, vx))  # est_cardinal(x)
    card_y = N.modus_ponens(y_in, _est_card_de_intervalle(a, vy))  # est_cardinal(y)
    # inf_egal_antisymetrique_card : (∀a∀b)((a≤b et b≤a et card a et card b)⇒a=b)
    # instanciée aux TERMES (x,y).  Binders internes « ca,cb » ≠ x,y (pas de capture).
    full = inf_egal_antisymetrique_card("ca", "cb")            # (∀ca∀cb)(corps)
    antis = instancie(instancie(full, vx), vy)                 # (x≤y et y≤x et card x et card y)⇒x=y
    premisse = conjonction_intro(conjonction_intro(conjonction_intro(
        le_xy, le_yx), card_x), card_y)
    x_eq_y = N.modus_ponens(premisse, antis)                   # x=y
    body = N.loi_deduction(hyp, x_eq_y)
    return N.generalisation(x, N.generalisation(y, body))


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE — la PARTIE ORDRE de est_bien_ordonne, INCONDITIONNELLE :
#     est_relation_ordre_dans( R_induit , [0,a] )  CLOS (0 hyp, == le prédicat).
#
#  est_relation_ordre_dans = ( ( transitif et antisymétrique ) et réflexif-implicite )
#                            et réflexif-dans-E.   Les QUATRE paliers ci-dessus, fermés.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.2 Demo.1 | E III.24 L.16-30 | PDF p.127
def relation_ordre_dans_intervalle(a="a"):
    """⊢ est_relation_ordre_dans( R_induit , [0,a] )   CLOS (INCONDITIONNEL).

    🎯🎯 LA MOITIÉ « ORDRE » de est_bien_ordonne(R_induit,[0,a]) — PROUVÉE SANS
    HYPOTHÈSE.  Assemble les 4 paliers (transitif, antisymétrique, réflexif-implicite,
    réflexif-dans-[0,a]) dans l'ordre EXACT de est_relation_ordre_dans (binders
    xo,yo,zo — ceux de l'hypothèse résiduelle).  La conclusion == le prédicat
    est_relation_ordre_dans(R_induit, [0,a]) LITTÉRALEMENT.  theorie=22.

    CONSÉQUENCE : est_bien_ordonne(R_induit,[0,a]) = ( CE THÉORÈME ) et clause_plus_petit ;
    le SEUL report de tout l'arc devient la clause de PLUS PETIT ÉLÉMENT (bottleneck
    ordinal↔cardinal), la partie ordre étant désormais ACQUISE."""
    interv = intervalle_0a(a)
    p1 = reflexive_dans_intervalle(a, "xo")               # est_reflexive_dans_ordre(R,[0,a],xo)
    p2 = reflexif_implicite_intervalle(a, "xo", "yo")     # ordre_reflexif_implicite(R,xo,yo)
    p3 = transitif_intervalle(a, "xo", "yo", "zo")        # ordre_transitif(R,xo,yo,zo)
    p4 = antisymetrie_intervalle(a, "xo", "yo")           # ordre_antisymetrique(R,xo,yo)
    ro = conjonction_intro(conjonction_intro(p3, p4), p2)  # est_relation_ordre(R,xo,yo,zo)
    return conjonction_intro(ro, p1)                       # est_relation_ordre_dans(R,[0,a])


__all__ = [
    "reflexive_dans_intervalle",
    "reflexif_implicite_intervalle",
    "transitif_intervalle",
    "antisymetrie_intervalle",
    "relation_ordre_dans_intervalle",
]
