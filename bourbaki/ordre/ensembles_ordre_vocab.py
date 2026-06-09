"""Chapitre III §1-2 — VOCABULAIRE d'ordre manquant (DÉFINITIONS fidèles).

Ce module COMPLÈTE `ensembles_abrege.py` (qui porte déjà : intervalles fermé /
ouvert / illimités fermés, segment, S_x = ]←,x[, bien ordonné, inductif, cofinale,
coinitiale, filtrant, comparables, totalement ordonné) et
`ensembles_ordre_relation.py` (formulation par graphe G).  Il INTRODUIT les
notions de mes sections (III.1, III.2) qui MANQUAIENT, formulées dans la
convention « R notée ≤ = fonction Python (Terme,Terme)↦Formule » (pattern §II.6 /
§III.1, identique à `ensembles_abrege.py`).

Notions introduites ici (énoncés VERBATIM E.III.1.13, E.III.1.3-4, E.III.1.8,
E.III.2) :

  INTERVALLES manquants (E.III.1.13) :
    • [a, b[  = { x∈E | a≤x et x<b }    intervalle_semi_ouvert_droite
    • ]a, b]  = { x∈E | a<x et x≤b }    intervalle_semi_ouvert_gauche
    • ]←, a[  = { x∈E | x<a }           intervalle_illimite_gauche_ouvert  (= S_a)
    • ]a, →[  = { x∈E | a<x }           intervalle_illimite_droite_ouvert
    • E = ]←, →[                        intervalle_total
  Chacun est un terme collectivisant (sélection S8 dans E + unicité A1), CARACTÉRISÉ
  par un axiome de membership dans une théorie dédiée (motif
  theorie_segment_extremite) — JAMAIS dans theorie_ensembles (intangible = 22).

  ISOMORPHISME d'ensembles ordonnés (E.III.1.3) :
    • est_isomorphisme_ordre(f, E, E', R, R') : f bijective de E sur E' et, pour
      tout x,y∈E, (x≤y) ⇔ (f(x)≤'f(y)).
    • sont_isomorphes_ordre(E, E', R, R') : (∃f) …

  ORDRE PRODUIT / produit d'ensembles ordonnés (E.III.1.4) :
    • ordre_produit(R, I, x, y) : (∀ι)(ι∈I ⇒ pr_ι(x) ≤_ι pr_ι(y)).

  ADJONCTION d'un plus grand élément (E.III.1.8) :
    • ordre_adjoint(R, E, a) : ordre sur E∪{a} prolongeant R et faisant de a le plus
      grand élément.

  ORDRE LEXICOGRAPHIQUE / produit lexicographique (E.III.2) :
    • ordre_lexicographique(R, I, RI, x, y) : x=y ou, au plus petit indice ι₀ où
      pr_ι x ≠ pr_ι y, on a pr_{ι₀} x <_{ι₀} pr_{ι₀} y.

NE prouve PAS Zermelo / Zorn / récurrence transfinie / Théorème 3 (reportés, cf.
ensembles_zorn / ensembles_bon_ordre).  Lemmes DIRECTS en bonus (certifiés noyau).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, app, egal, et, ou, impl, non, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _strict(R):
    """Relation stricte associée : x<y := (R{x,y} et x≠y)  (E.III.1.3, C58)."""
    return lambda a, b: et(R(a, b), non(egal(a, b)))


# ════════════════════════════════════════════════════════════════════════════
#  INTERVALLES manquants  (E.III.1.13)
#  Termes opaques collectivisants ; caractérisés par axiomes de membership.
# ════════════════════════════════════════════════════════════════════════════
def intervalle_semi_ouvert_droite(R, e, a, b):
    """[a, b[ := { x∈E | a≤x et x<b }  (intervalle semi-ouvert à droite, E.III.1.13)."""
    return app("interv_fo", _terme(e), _terme(a), _terme(b))


def intervalle_semi_ouvert_gauche(R, e, a, b):
    """]a, b] := { x∈E | a<x et x≤b }  (intervalle semi-ouvert à gauche, E.III.1.13)."""
    return app("interv_of", _terme(e), _terme(a), _terme(b))


def intervalle_illimite_gauche_ouvert(R, e, a):
    """]←, a[ := { x∈E | x<a }  (intervalle ouvert illimité à gauche, E.III.1.13).

    C'est exactement le segment d'extrémité a, S_a (E.III.2.1)."""
    return app("interv_igo", _terme(e), _terme(a))


def intervalle_illimite_droite_ouvert(R, e, a):
    """]a, →[ := { x∈E | a<x }  (intervalle ouvert illimité à droite, E.III.1.13)."""
    return app("interv_ido", _terme(e), _terme(a))


def intervalle_total(R, e):
    """]←, →[ := E   (l'intervalle total est E lui-même, E.III.1.13)."""
    return _terme(e)


# ── axiomes de membership (motif theorie_segment_extremite) ──────────────────
def axiome_intervalle_semi_ouvert_droite(R, e="E", a="a", b="b", x="x"):
    """⊢-schéma : (∀E)(∀a)(∀b)(∀x)( x∈[a,b[ ⇔ (x∈E et a≤x et x<b) ).  (E.III.1.13.)

    Légitimé par S8 (sélection dans E) + A1 (unicité)."""
    vE, va, vb, vx = var(e), var(a), var(b), var(x)
    lt = _strict(R)
    return pourtout(e, pourtout(a, pourtout(b, pourtout(x,
        equiv(appartient(vx, intervalle_semi_ouvert_droite(R, vE, va, vb)),
              et(et(appartient(vx, vE), R(va, vx)), lt(vx, vb)))))))


def axiome_intervalle_semi_ouvert_gauche(R, e="E", a="a", b="b", x="x"):
    """⊢-schéma : (∀E)(∀a)(∀b)(∀x)( x∈]a,b] ⇔ (x∈E et a<x et x≤b) ).  (E.III.1.13.)"""
    vE, va, vb, vx = var(e), var(a), var(b), var(x)
    lt = _strict(R)
    return pourtout(e, pourtout(a, pourtout(b, pourtout(x,
        equiv(appartient(vx, intervalle_semi_ouvert_gauche(R, vE, va, vb)),
              et(et(appartient(vx, vE), lt(va, vx)), R(vx, vb)))))))


def axiome_intervalle_illimite_gauche_ouvert(R, e="E", a="a", x="x"):
    """⊢-schéma : (∀E)(∀a)(∀x)( x∈]←,a[ ⇔ (x∈E et x<a) ).  (E.III.1.13.)"""
    vE, va, vx = var(e), var(a), var(x)
    lt = _strict(R)
    return pourtout(e, pourtout(a, pourtout(x,
        equiv(appartient(vx, intervalle_illimite_gauche_ouvert(R, vE, va)),
              et(appartient(vx, vE), lt(vx, va))))))


def axiome_intervalle_illimite_droite_ouvert(R, e="E", a="a", x="x"):
    """⊢-schéma : (∀E)(∀a)(∀x)( x∈]a,→[ ⇔ (x∈E et a<x) ).  (E.III.1.13.)"""
    vE, va, vx = var(e), var(a), var(x)
    lt = _strict(R)
    return pourtout(e, pourtout(a, pourtout(x,
        equiv(appartient(vx, intervalle_illimite_droite_ouvert(R, vE, va)),
              et(appartient(vx, vE), lt(va, vx))))))


def theorie_intervalles(R, e="E", a="a", b="b", x="x"):
    """Théorie dédiée portant les 4 axiomes de membership des intervalles
    semi-ouverts / illimités ouverts (E.III.1.13).  theorie_ensembles INCHANGÉE."""
    return N.Theorie("Intervalles", [
        axiome_intervalle_semi_ouvert_droite(R, e, a, b, x),
        axiome_intervalle_semi_ouvert_gauche(R, e, a, b, x),
        axiome_intervalle_illimite_gauche_ouvert(R, e, a, x),
        axiome_intervalle_illimite_droite_ouvert(R, e, a, x),
    ])


# ════════════════════════════════════════════════════════════════════════════
#  ISOMORPHISME d'ensembles ordonnés  (E.III.1.3, VERBATIM)
#  « application bijective f de E sur E' telle que x≤y et f(x)≤f(y) équivalentes »
# ════════════════════════════════════════════════════════════════════════════
def compatible_ordre(f, e, R, Rp, x="x", y="y"):
    """compatible_ordre(f,E,R,R') := (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ⇔ R'{f(x),f(y)})).

    « f respecte l'ordre dans les deux sens » : x≤y ⇔ f(x)≤'f(y)  (cœur de la
    Déf. III.1.3 d'isomorphisme d'ensembles ordonnés)."""
    vx, vy, vE = var(x), var(y), _terme(e)
    fx, fy = E.valeur(_terme(f), vx), E.valeur(_terme(f), vy)
    return pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             equiv(R(vx, vy), Rp(fx, fy)))))


def est_isomorphisme_ordre(f, e, ep, R, Rp, x="x", y="y"):
    """est_isomorphisme_ordre(f,E,E',R,R') := f bijective de E sur E' ET
        (∀x)(∀y)((x∈E et y∈E) ⇒ (x≤y ⇔ f(x)≤'f(y))).

    DÉFINITION VERBATIM E.III.1.3 : « On appelle isomorphisme de (E,Γ) sur (E',Γ')
    une application bijective f de E sur E' telle que les relations x≤y et f(x)≤f(y)
    soient équivalentes. »  (R = ≤ sur E, R' = ≤ sur E'.)"""
    return et(E.est_bijective(_terme(f), _terme(e), _terme(ep)),
              compatible_ordre(f, e, R, Rp, x, y))


def sont_isomorphes_ordre(e, ep, R, Rp, f="f", x="x", y="y"):
    """sont_isomorphes_ordre(E,E',R,R') := (∃f) est_isomorphisme_ordre(f,E,E',R,R').

    « (E,R) et (E',R') sont isomorphes en tant qu'ensembles ordonnés »  (E.III.1.3)."""
    return existe(f, est_isomorphisme_ordre(var(f), e, ep, R, Rp, x, y))


# ════════════════════════════════════════════════════════════════════════════
#  ORDRE PRODUIT / produit d'ensembles ordonnés  (E.III.1.4)
#  R_ι = fonction Python ι ↦ (relation ≤_ι).  x, y ∈ F = ∏_ι E_ι.
# ════════════════════════════════════════════════════════════════════════════
def ordre_produit(Rfam, I, x_pt, y_pt, i="i"):
    """ordre_produit(R,I)(x,y) := (∀ι)(ι∈I ⇒ pr_ι(x) ≤_ι pr_ι(y)).

    DÉFINITION VERBATIM E.III.1.4 : « la relation (∀ι)((ι∈I) ⇒ (x_ι ≤ y_ι)) est une
    relation d'ordre entre x=(x_ι) et y=(y_ι) ; on l'appelle ordre produit ».
    Rfam(ι) renvoie la relation ≤_ι (fonction (Terme,Terme)↦Formule) ; pr_ι(x) =
    projection_indice(x, ι) = valeur(x, ι)."""
    vi = var(i)
    vx, vy = _terme(x_pt), _terme(y_pt)
    prx = E.projection_indice(vx, vi)
    pry = E.projection_indice(vy, vi)
    return pourtout(i, impl(appartient(vi, _terme(I)), Rfam(vi)(prx, pry)))


def relation_ordre_produit(Rfam, I, i="i"):
    """Renvoie la RELATION ≤_F (fonction (x,y)↦Formule) de l'ordre produit sur
    F=∏_ι E_ι, prête à être passée à est_relation_ordre / est_totalement_ordonne.
    (E.III.1.4 ; produit des relations d'ordre.)"""
    return lambda x_pt, y_pt: ordre_produit(Rfam, I, x_pt, y_pt, i)


# ════════════════════════════════════════════════════════════════════════════
#  ADJONCTION d'un plus grand élément  (E.III.1.8, Proposition 3)
#  E' = E ∪ {a} ;  l'ordre adjoint prolonge ≤ sur E et fait de a le plus grand.
# ════════════════════════════════════════════════════════════════════════════
def ensemble_adjoint(e, a):
    """E' := E ∪ {a}   (ensemble obtenu en adjoignant l'élément a à E, E.III.1.8).

    Bourbaki prend la SOMME de E et de {a} ; lorsque a∉E, E∪{a} la représente."""
    return E.reunion(_terme(e), E.singleton(_terme(a)))


def relation_adjoint(R, e, a):
    """Relation ≤' sur E'=E∪{a} adjoignant à E le plus grand élément a (E.III.1.8) :

        x ≤' y  :⟺  (x≤y)  ou  (y=a et x∈E')

    Elle PROLONGE ≤ sur E (premier disjoint) et place a au sommet : tout x∈E'
    vérifie x≤'a (second disjoint), et a n'est ≤' à rien d'autre que a.
    (Construction de la Proposition 3, E.III.1.8.)"""
    vEp, va = ensemble_adjoint(e, a), _terme(a)
    return lambda x, y: ou(R(x, y), et(egal(y, va), appartient(x, vEp)))


def est_adjonction_plus_grand(R, Rp, e, a, x="x"):
    """est_adjonction_plus_grand(R,R',E,a) := « R' est un ordre sur E'=E∪{a} qui
        induit R sur E et pour lequel a est le plus grand élément de E' » :

        est_relation_ordre_dans(R', E∪{a})  et
        (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ⇔ R'{x,y}))     [induit R sur E]  et
        est_plus_grand_element(R', E∪{a}, a).

    ÉNONCÉ de la Proposition 3 (E.III.1.8) : « il existe sur E' un ordre et un seul
    induisant sur E l'ordre donné et pour lequel a soit le plus grand élément ».
    DÉFINITION de l'énoncé (existence/unicité = théorème, REPORTÉ)."""
    vE, vEp = _terme(e), ensemble_adjoint(e, a)
    vx, vy = var(x), var("y")
    induit = pourtout(x, pourtout("y",
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             equiv(R(vx, vy), Rp(vx, vy)))))
    return et(et(E.est_relation_ordre_dans(Rp, vEp),
                 induit),
              E.est_plus_grand_element(Rp, vEp, _terme(a)))


# ════════════════════════════════════════════════════════════════════════════
#  ORDRE LEXICOGRAPHIQUE / produit lexicographique  (E.III.2)
#  I bien ordonné ;  R_ι = fonction ι ↦ ≤_ι.  x, y ∈ E = ∏_ι E_ι.
# ════════════════════════════════════════════════════════════════════════════
def ordre_lexicographique(Rfam, I, RI, x_pt, y_pt, i="i", i0="i0", j="j"):
    """ordre_lexicographique(R,I,RI)(x,y) :⟺ (x=y) ∨ (∃ι₀)( ι₀∈I et pr_{ι₀}x <_{ι₀} pr_{ι₀}y
        et (∀ι)((ι∈I et ι <_I ι₀) ⇒ pr_ι x = pr_ι y) ).

    DÉFINITION VERBATIM E.III.2 : « pour le plus petit indice ι∈I (au sens du BON
    ORDRE de I) tel que pr_ι x ≠ pr_ι y, on a pr_ι x <_ι pr_ι y ».  Le « plus petit
    indice où elles diffèrent » est encodé par : ι₀ diffère (<_{ι₀} sur le facteur
    E_{ι₀}) et tout indice ι <_I ι₀ coïncide (I bien ordonné ⇒ ce ι₀ existe dès x≠y).
    ⚠ DEUX ordres distincts : RI = l'ordre (bon ordre) de l'ENSEMBLE D'INDICES I
    (sert à comparer ι <_I ι₀) ; Rfam(ι) = ≤_ι l'ordre du FACTEUR E_ι (sert à
    comparer pr_{ι₀}x <_{ι₀} pr_{ι₀}y).  Confondre les deux (utiliser Rfam pour
    l'ordre des indices) serait INFIDÈLE."""
    vi, vi0, vj = var(i), var(i0), var(j)
    vx, vy = _terme(x_pt), _terme(y_pt)
    lt_comp = _strict(Rfam(vi0))        # <_{ι₀} sur le FACTEUR E_{ι₀}
    lt_I = _strict(RI)                  # <_I sur l'ENSEMBLE D'INDICES I (bon ordre)
    prx0 = E.projection_indice(vx, vi0)
    pry0 = E.projection_indice(vy, vi0)
    # tout indice ι strictement avant ι₀ AU SENS DE RI : pr_ι x = pr_ι y
    avant = pourtout(j, impl(et(appartient(vj, _terme(I)), lt_I(vj, vi0)),
                             egal(E.projection_indice(vx, vj),
                                  E.projection_indice(vy, vj))))
    temoin = existe(i0, et(et(appartient(vi0, _terme(I)),
                              lt_comp(prx0, pry0)),
                           avant))
    return ou(egal(vx, vy), temoin)


def relation_ordre_lexicographique(Rfam, I, RI, i="i", i0="i0", j="j"):
    """Renvoie la RELATION ≤_lex (fonction (x,y)↦Formule) de l'ordre lexicographique
    sur E=∏_ι E_ι, prête à être passée à est_relation_ordre, etc.  (E.III.2.)
    RI = bon ordre de l'ensemble d'indices I ; Rfam(ι) = ≤_ι l'ordre du facteur E_ι."""
    return lambda x_pt, y_pt: ordre_lexicographique(Rfam, I, RI, x_pt, y_pt, i, i0, j)


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS (bonus) — certifiés par le noyau abrégé
# ════════════════════════════════════════════════════════════════════════════
def isomorphisme_ordre_est_bijection(f="f", e="E", ep="Ep", R=None, Rp=None,
                                     x="x", y="y"):
    """{ est_isomorphisme_ordre(f,E,E',R,R') } ⊢ f bijective de E sur E'.

    Un isomorphisme d'ensembles ordonnés est en particulier une bijection
    (projection gauche de la définition, E.III.1.3)."""
    if R is None:
        R = lambda a, b: appartient(E.couple(a, b), var("G"))
    if Rp is None:
        Rp = lambda a, b: appartient(E.couple(a, b), var("Gp"))
    H = N.assume(est_isomorphisme_ordre(f, e, ep, R, Rp, x, y))
    return conjonction_elim_gauche(H)


def isomorphisme_ordre_compatible(f="f", e="E", ep="Ep", R=None, Rp=None,
                                  x="x", y="y"):
    """{ est_isomorphisme_ordre(f,E,E',R,R') } ⊢ compatible_ordre(f,E,R,R').

    Un isomorphisme respecte l'ordre dans les deux sens : x≤y ⇔ f(x)≤'f(y)
    (projection droite de la définition, E.III.1.3)."""
    if R is None:
        R = lambda a, b: appartient(E.couple(a, b), var("G"))
    if Rp is None:
        Rp = lambda a, b: appartient(E.couple(a, b), var("Gp"))
    H = N.assume(est_isomorphisme_ordre(f, e, ep, R, Rp, x, y))
    return conjonction_elim_droite(H)


def adjoint_a_est_plus_grand(R=None, e="E", a="a", x="x"):
    """{ est_adjonction_plus_grand(R,R',E,a) } ⊢ est_plus_grand_element(R',E∪{a},a).

    Dans l'adjonction d'un plus grand élément, a est bien le plus grand élément de
    E'=E∪{a} (projection droite de la Proposition 3, E.III.1.8)."""
    if R is None:
        R = lambda u, v: appartient(E.couple(u, v), var("G"))
    Rp = relation_adjoint(R, e, a)
    H = N.assume(est_adjonction_plus_grand(R, Rp, e, a, x))
    return conjonction_elim_droite(H)


def lexicographique_reflexive(Rfam=None, I="I", RI=None, a="a", i="i", i0="i0", j="j"):
    """⊢ ordre_lexicographique(R,I,RI)(a,a).   (≤_lex est réflexive — branche x=y.)

    Tout point a est ≤_lex à lui-même : la disjonction (a=a)∨… est satisfaite par
    sa branche gauche a=a (réflexivité de l'égalité), via S2.  (RI = ordre de I ;
    n'intervient pas dans la branche réflexive, fourni par défaut.)"""
    if Rfam is None:
        Rfam = lambda ind: (lambda u, v: appartient(E.couple(u, v), E.valeur(var("Gfam"), ind)))
    if RI is None:
        RI = lambda u, v: appartient(E.couple(u, v), var("GI"))
    va = _terme(a)
    lex = ordre_lexicographique(Rfam, I, RI, va, va, i, i0, j)   # = ou(a=a, témoin)
    gauche, droite = lex.sous                                # disjoncts (Formule "ou")
    a_eq_a = N.reflexivite(va)                               # ⊢ a=a  (= gauche)
    # S2 : (a=a) ⇒ ((a=a) ou témoin)
    s2 = N.s2(gauche, droite)
    return N.modus_ponens(a_eq_a, s2)


def intervalle_total_est_E(R=None, e="E"):
    """⊢ intervalle_total(R,E) = E.   (]←,→[ = E, E.III.1.13 — égalité définitionnelle.)"""
    if R is None:
        R = lambda u, v: appartient(E.couple(u, v), var("G"))
    vE = _terme(e)
    return N.reflexivite(vE)   # intervalle_total renvoie E lui-même


__all__ = [
    # intervalles manquants
    "intervalle_semi_ouvert_droite", "intervalle_semi_ouvert_gauche",
    "intervalle_illimite_gauche_ouvert", "intervalle_illimite_droite_ouvert",
    "intervalle_total",
    "axiome_intervalle_semi_ouvert_droite", "axiome_intervalle_semi_ouvert_gauche",
    "axiome_intervalle_illimite_gauche_ouvert", "axiome_intervalle_illimite_droite_ouvert",
    "theorie_intervalles",
    # isomorphisme d'ensembles ordonnés
    "compatible_ordre", "est_isomorphisme_ordre", "sont_isomorphes_ordre",
    # ordre produit
    "ordre_produit", "relation_ordre_produit",
    # adjonction d'un plus grand élément
    "ensemble_adjoint", "relation_adjoint", "est_adjonction_plus_grand",
    # ordre lexicographique
    "ordre_lexicographique", "relation_ordre_lexicographique",
    # lemmes directs
    "isomorphisme_ordre_est_bijection", "isomorphisme_ordre_compatible",
    "adjoint_a_est_plus_grand", "lexicographique_reflexive", "intervalle_total_est_E",
]
