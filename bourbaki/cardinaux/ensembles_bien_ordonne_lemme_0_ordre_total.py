"""LEMME L0 — ⊢ est_relation_ordre_dans( ≤_induit , [0,a] ).

────────────────────────────────────────────────────────────────────────────────
ROUTE R3 (réduction de cardinaux_bien_ordonnes(a) au BON ORDRE de [0,a]) — ce
module prouve le 1er des DEUX conjoints de

        est_bien_ordonne( ≤_induit , [0,a] )
      = et( est_relation_ordre_dans(≤_induit,[0,a]),  CLAUSE_PLUS_PETIT )

(cf. ensembles_abrege.est_bien_ordonne, Déf. 1 E.III.2.1).  La CLAUSE_PLUS_PETIT
(2e conjoint) est le vrai mur (sous-système ordinal §III.2) — traitée AILLEURS.

────────────────────────────────────────────────────────────────────────────────
CIBLE (vérifiée par égalité de formules dans le test miroir) :

    est_relation_ordre_dans(R_ind, I)
  = et( est_relation_ordre(R_ind), est_reflexive_dans_ordre(R_ind, I) )
  = et( et( et( ordre_transitif(R_ind), ordre_antisymetrique(R_ind) ),
            ordre_reflexif_implicite(R_ind) ),
        est_reflexive_dans_ordre(R_ind, I) )

avec  R_ind{u,v} := ( u ≤ v  et  u∈I  et  v∈I )   (= ordre_induit_intervalle(a),
ensembles_ordinal_cardinal_correspondance) et  I := [0,a] = intervalle_entiers(0,a)
= l'ensemble des cardinaux ≤ a (E.III.5.3).

────────────────────────────────────────────────────────────────────────────────
QUATRE CONJOINTS, tous INCONDITIONNELS (pur assemblage, aucun ingrédient neuf) :

  (1) TRANSITIVITÉ   ordre_transitif(R_ind) :
        de (x≤y et x∈I et y∈I) et (y≤z et y∈I et z∈I) on tire
        x≤z  (inf_egal_transitive, CLOS),  x∈I (du 1er),  z∈I (du 2e).

  (2) ANTISYMÉTRIE   ordre_antisymetrique(R_ind) :
        de R_ind{x,y} et R_ind{y,x} on a  x≤y, y≤x  ET  x∈I, y∈I.
        x∈I, y∈I ⇒ x,y CARDINAUX (intervalle_implique_cardinal, CLOS).
        ⇒ x=y  par  inf_egal_antisymetrique_card  (= CANTOR–BERNSTEIN + Prop 1,
        CLOS, garde « cardinaux »).  C'EST ICI QUE LA GARDE EST FOURNIE PAR I.

  (3) RÉFLEXIVITÉ IMPLICITE  ordre_reflexif_implicite(R_ind) :
        R_ind{x,y} ⇒ (R_ind{x,x} et R_ind{y,y}).
        De (x≤y et x∈I et y∈I), on a x∈I, y∈I ; et x≤x, y≤y (inf_egal_reflexif,
        CLOS) ⇒ R_ind{x,x}=(x≤x et x∈I et x∈I), R_ind{y,y}=(y≤y et y∈I et y∈I).

  (4) RÉFLEXIVITÉ DANS I   est_reflexive_dans_ordre(R_ind, I) :
        (∀x)( R_ind{x,x} ⇔ x∈I ).
        ⇒ : R_ind{x,x}=(x≤x et x∈I et x∈I) projette x∈I.
        ⇐ : x∈I donne x∈I (×2) et x≤x (inf_egal_reflexif, CLOS) ⇒ R_ind{x,x}.

ASSEMBLAGE :  lemme_0_ordre_total(a)  =  conjonction des quatre.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Les seules « théories
locales » mobilisées sont celles DÉJÀ utilisées par les briques importées
(theorie_intervalle_entiers via intervalle_implique_cardinal — axiome S8+A1
légitimé E.III.5.3, identique à son usage dans ensembles_clause_plus_petit).
INCONDITIONNEL : lemme_0_ordre_total(a) a 0 hypothèse (est_clos == True).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, pourtout, equiv,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, est_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import intervalle_implique_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    ordre_induit_intervalle, intervalle_0a,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _le(u, v):
    """≤ BARE des cardinaux  u ≤ v."""
    return inf_egal_card(_t(u), _t(v))


# ── briques-TERME (instances des théorèmes CLOS, pour des termes quelconques) ──
def _refl_le_t(t):
    """⊢ t ≤ t   pour un TERME t  (réflexivité de ≤, instance de inf_egal_reflexif)."""
    gen = N.generalisation("X", inf_egal_reflexif("X"))      # (∀X) X≤X
    return instancie(gen, _t(t))


def _trans_le_t(tx, ty, tz):
    """⊢ (x≤y et y≤z) ⇒ x≤z   pour des TERMES x,y,z  (transitivité de ≤)."""
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))       # (∀X∀Y∀Z)((X≤Y et Y≤Z)⇒X≤Z)
    return instancie(instancie(instancie(gen, _t(tx)), _t(ty)), _t(tz))


def _antisym_card_t(tx, ty):
    """⊢ (x≤y et y≤x et x cardinal et y cardinal) ⇒ x=y   pour des TERMES x,y.

    Instance de inf_egal_antisymetrique_card (= Cantor–Bernstein + Prop 1, CLOS).
    Binders internes a,b instanciés aux termes x,y."""
    base = inf_egal_antisymetrique_card("a", "b")             # (∀a∀b)((a≤b et b≤a et card a et card b)⇒a=b)
    return instancie(instancie(base, _t(tx)), _t(ty))


def _in_interv_implique_card_t(a, t):
    """⊢ (t ∈ [0,a]) ⇒ (t cardinal)   pour des TERMES a,t  (intervalle_implique_cardinal)."""
    gen = N.generalisation("a", N.generalisation("b", N.generalisation("x",
        intervalle_implique_cardinal("a", "b", "x"))))         # (∀a∀b∀x)((x∈[a,b])⇒card x)
    return instancie(instancie(instancie(gen, ZERO), _t(a)), _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  (1) TRANSITIVITÉ  :  (∀x∀y∀z)(( R_ind{x,y} et R_ind{y,z} ) ⇒ R_ind{x,z})
# ════════════════════════════════════════════════════════════════════════════
def transitivite_induit(a="a", x="xo", y="yo", z="zo"):
    """⊢ ordre_transitif( R_ind )  (INCONDITIONNEL)."""
    R = ordre_induit_intervalle(a)
    vx, vy, vz = _t(x), _t(y), _t(z)
    hyp = et(R(vx, vy), R(vy, vz))
    H = N.assume(hyp)
    Rxy = conjonction_elim_gauche(H)                          # x≤y et x∈I et y∈I
    Ryz = conjonction_elim_droite(H)                          # y≤z et y∈I et z∈I
    le_xy = conjonction_elim_gauche(conjonction_elim_gauche(Rxy))   # x≤y
    x_in = conjonction_elim_droite(conjonction_elim_gauche(Rxy))    # x∈I
    le_yz = conjonction_elim_gauche(conjonction_elim_gauche(Ryz))   # y≤z
    z_in = conjonction_elim_droite(Ryz)                            # z∈I
    le_xz = N.modus_ponens(conjonction_intro(le_xy, le_yz),
                           _trans_le_t(vx, vy, vz))               # x≤z
    Rxz = conjonction_intro(conjonction_intro(le_xz, x_in), z_in)  # R_ind{x,z}
    corps = N.loi_deduction(hyp, Rxz)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, corps)))


# ════════════════════════════════════════════════════════════════════════════
#  (2) ANTISYMÉTRIE  :  (∀x∀y)(( R_ind{x,y} et R_ind{y,x} ) ⇒ x=y)
# ════════════════════════════════════════════════════════════════════════════
def antisymetrie_induit(a="a", x="xo", y="yo"):
    """⊢ ordre_antisymetrique( R_ind )  (INCONDITIONNEL).

    La garde « x,y cardinaux » de l'antisymétrie de ≤ est FOURNIE par x,y∈[0,a]
    (intervalle_implique_cardinal).  D'où x=y par Cantor–Bernstein + Prop 1."""
    R = ordre_induit_intervalle(a)
    vx, vy = _t(x), _t(y)
    hyp = et(R(vx, vy), R(vy, vx))
    H = N.assume(hyp)
    Rxy = conjonction_elim_gauche(H)                          # x≤y et x∈I et y∈I
    Ryx = conjonction_elim_droite(H)                          # y≤x et y∈I et x∈I
    le_xy = conjonction_elim_gauche(conjonction_elim_gauche(Rxy))   # x≤y
    le_yx = conjonction_elim_gauche(conjonction_elim_gauche(Ryx))   # y≤x
    x_in = conjonction_elim_droite(conjonction_elim_gauche(Rxy))    # x∈I
    y_in = conjonction_elim_droite(conjonction_elim_gauche(Ryx))    # y∈I
    card_x = N.modus_ponens(x_in, _in_interv_implique_card_t(a, vx))   # card x
    card_y = N.modus_ponens(y_in, _in_interv_implique_card_t(a, vy))   # card y
    # (x≤y et y≤x et card x et card y) ⇒ x=y
    premisse = conjonction_intro(conjonction_intro(conjonction_intro(le_xy, le_yx),
                                                   card_x), card_y)
    x_eq_y = N.modus_ponens(premisse, _antisym_card_t(vx, vy))     # x=y
    corps = N.loi_deduction(hyp, x_eq_y)
    return N.generalisation(x, N.generalisation(y, corps))


# ════════════════════════════════════════════════════════════════════════════
#  (3) RÉFLEXIVITÉ IMPLICITE  :  (∀x∀y)( R_ind{x,y} ⇒ (R_ind{x,x} et R_ind{y,y}) )
# ════════════════════════════════════════════════════════════════════════════
def reflexif_implicite_induit(a="a", x="xo", y="yo"):
    """⊢ ordre_reflexif_implicite( R_ind )  (INCONDITIONNEL)."""
    R = ordre_induit_intervalle(a)
    vx, vy = _t(x), _t(y)
    hyp = R(vx, vy)                                           # x≤y et x∈I et y∈I
    H = N.assume(hyp)
    x_in = conjonction_elim_droite(conjonction_elim_gauche(H))     # x∈I
    y_in = conjonction_elim_droite(H)                             # y∈I
    Rxx = conjonction_intro(conjonction_intro(_refl_le_t(vx), x_in), x_in)  # x≤x et x∈I et x∈I
    Ryy = conjonction_intro(conjonction_intro(_refl_le_t(vy), y_in), y_in)  # y≤y et y∈I et y∈I
    concl = conjonction_intro(Rxx, Ryy)                          # R_ind{x,x} et R_ind{y,y}
    corps = N.loi_deduction(hyp, concl)
    return N.generalisation(x, N.generalisation(y, corps))


# ════════════════════════════════════════════════════════════════════════════
#  (4) RÉFLEXIVITÉ DANS I  :  (∀x)( R_ind{x,x} ⇔ x∈I )
# ════════════════════════════════════════════════════════════════════════════
def reflexive_dans_intervalle(a="a", x="xo"):
    """⊢ est_reflexive_dans_ordre( R_ind , [0,a] )  (INCONDITIONNEL)."""
    R = ordre_induit_intervalle(a)
    interv = intervalle_0a(a)
    vx = _t(x)
    x_in_f = appartient(vx, interv)
    Rxx_f = R(vx, vx)                                         # x≤x et x∈I et x∈I
    # ⇒ : R_ind{x,x} ⇒ x∈I  (projection du conjoint médian)
    Hf = N.assume(Rxx_f)
    x_in_from_R = conjonction_elim_droite(conjonction_elim_gauche(Hf))   # x∈I
    fwd = N.loi_deduction(Rxx_f, x_in_from_R)                 # R_ind{x,x} ⇒ x∈I
    # ⇐ : x∈I ⇒ R_ind{x,x}
    Hb = N.assume(x_in_f)                                     # x∈I
    Rxx = conjonction_intro(conjonction_intro(_refl_le_t(vx), Hb), Hb)   # x≤x et x∈I et x∈I
    bwd = N.loi_deduction(x_in_f, Rxx)                        # x∈I ⇒ R_ind{x,x}
    equ = conjonction_intro(fwd, bwd)                        # R_ind{x,x} ⇔ x∈I
    assert equ.conclusion == equiv(Rxx_f, x_in_f)
    return N.generalisation(x, equ)


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE FINAL  :  est_relation_ordre_dans( R_ind , [0,a] )
# ════════════════════════════════════════════════════════════════════════════
def lemme_0_ordre_total(a="a", x="xo", y="yo", z="zo"):
    """⊢ est_relation_ordre_dans( ≤_induit , [0,a] )   (LEMME L0, INCONDITIONNEL).

    = et( et( et( transitif, antisymétrique ), réflexif-implicite ),
          réflexive-dans-[0,a] )
    = 1er conjoint de est_bien_ordonne(≤_induit, [0,a]).

    Conjonction des quatre composantes ci-dessus, toutes 0-hypothèse.  theorie=22,
    rien postulé.  Le 2e conjoint de est_bien_ordonne (la clause de plus petit
    élément) reste le mur ordinal §III.2, traité ailleurs."""
    tr = transitivite_induit(a, x, y, z)
    asy = antisymetrie_induit(a, x, y)
    ri = reflexif_implicite_induit(a, x, y)
    rd = reflexive_dans_intervalle(a, x)
    # est_relation_ordre(R) = et( et(transitif, antisym), reflexif_implicite )
    ero = conjonction_intro(conjonction_intro(tr, asy), ri)
    # est_relation_ordre_dans(R,I) = et( est_relation_ordre(R), reflexive_dans(R,I) )
    return conjonction_intro(ero, rd)


__all__ = [
    "transitivite_induit",
    "antisymetrie_induit",
    "reflexif_implicite_induit",
    "reflexive_dans_intervalle",
    "lemme_0_ordre_total",
]
