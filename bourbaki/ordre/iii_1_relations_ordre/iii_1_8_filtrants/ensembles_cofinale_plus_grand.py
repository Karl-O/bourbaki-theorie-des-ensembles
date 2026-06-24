"""Chapitre III §1.8 — REMARQUE (E.III.1.8) : « plus grand élément ⟺ partie
cofinale réduite à un seul élément ».

Bourbaki, E III.9 (§III.1.8), après la Définition de partie cofinale :

  « On dit qu'une partie A d'un ensemble préordonné E est *cofinale* (resp.
  *coinitiale*) à E si, pour tout x∈E, il existe y∈A tel que x≤y (resp. y≤x).
  Dire qu'un ensemble ordonné a un plus grand (resp. plus petit) élément
  signifie donc qu'il existe une partie cofinale (resp. coinitiale) de E
  réduite à un seul élément. »

Autrement dit, pour a∈E : a est le plus grand élément de E SI ET SEULEMENT SI
la partie {a} est cofinale à E.  On formalise ici les DEUX sens (équivalence).

Convention « graphe G » de `ensembles_ordre_relation.py` : la relation d'ordre
est un GRAPHE G (ensemble de couples) et x≤y s'écrit (x,y)∈G.  La partie cofinale
réutilise la définition `est_cofinale` de §II.1 avec la relation-graphe :

    R_G(u,v) := (u,v)∈G              (= appartient(E.couple(u,v), G))
    est_cofinale(R_G, {a}, E)
        = (∀x)(x∈E ⇒ (∃y)(y∈{a} et (x,y)∈G)).

RÉSULTATS (certifiés noyau LCF, CLOS sous hypothèses honnêtes) :

  • `plus_grand_implique_cofinale_singleton`  (SENS DIRECT, cible principale) :
        { plus_grand_element(G,E,a) } ⊢ est_cofinale(R_G, {a}, E).
    Pour x∈E, le témoin y:=a convient : a∈{a} (appartient_singleton) et a majore
    E donc (x,a)∈G ; d'où (∃y)(y∈{a} et (x,y)∈G).  (S5, témoin a.)

  • `cofinale_singleton_implique_plus_grand`  (RÉCIPROQUE) :
        { a∈E, est_cofinale(R_G, {a}, E) } ⊢ plus_grand_element(G,E,a).
    Pour x∈E, le témoin y∈{a} donné par la cofinalité vérifie y=a
    (singleton_membre), donc (x,a)∈G ; a majore E, et a∈E par hypothèse.

  • `plus_grand_equivaut_cofinale_singleton`  (ÉQUIVALENCE) :
        { a∈E } ⊢ ( plus_grand_element(G,E,a) ⇔ est_cofinale(R_G, {a}, E) ).

theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ (primitives N.* du noyau LCF),
aucun axiome nouveau.  (E.III.1.8, remarque sur les parties cofinales.)
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, et, impl, equiv, appartient,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import appartient_singleton
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    plus_grand_element, _couple_dans,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# Liants internes FIXÉS — alignés sur les défauts de plus_grand_element (x) et de
# est_cofinale (x, y).  On garde les MÊMES noms que les définitions réutilisées
# pour que les conclusions reconstruites coïncident à l'identique.
_X = "x"   # liant du « majore » de plus_grand_element et du (∀x) de est_cofinale
_Y = "y"   # liant existentiel de est_cofinale


def _R_G(G):
    """Relation-graphe R_G(u,v) := (u,v)∈G, sous forme de fonction (u,v)↦Formule."""
    return lambda u, v: _couple_dans(u, v, G)


def cofinale_singleton(G, E_set, a):
    """est_cofinale(R_G, {a}, E) = (∀x)(x∈E ⇒ (∃y)(y∈{a} et (x,y)∈G)).

    Conclusion-cible des théorèmes ci-dessous (sens direct / équivalence)."""
    return E.est_cofinale(_R_G(G), E.singleton(_t(a)), _t(E_set), _X, _Y)


# ════════════════════════════════════════════════════════════════════════════
#  SENS DIRECT (cible principale) — plus grand élément ⇒ {a} cofinale à E
# ════════════════════════════════════════════════════════════════════════════
def plus_grand_implique_cofinale_singleton(G="Gcf", E_set="Ecf", a="acf"):
    """🎯 { plus_grand_element(G,E,a) } ⊢ est_cofinale(R_G, {a}, E).

    REMARQUE E.III.1.8 (sens direct).  Si a est le plus grand élément de E, la
    partie {a} est cofinale à E.  Pour x∈E, le témoin y:=a convient : a∈{a}
    (appartient_singleton) et, a majorant E, on a (x,a)∈G (instanciation du
    « majore »).  La conjonction (a∈{a} et (x,a)∈G) est (a|y)[y∈{a} et (x,y)∈G],
    donc S5 (témoin a) introduit (∃y)(y∈{a} et (x,y)∈G).  Généralisation sur x
    après décharge de x∈E.  (E.III.1.8.)
    """
    vG, vE, va = _t(G), _t(E_set), _t(a)
    vx = var(_X)
    sa = E.singleton(va)                                   # {a}

    Hpge = N.assume(plus_grand_element(G, E_set, va, _X))  # a∈E et (∀x)(x∈E⇒(x,a)∈G)
    a_majore = conjonction_elim_droite(Hpge)              # (∀x)(x∈E ⇒ (x,a)∈G)

    # ── corps en x : x∈E ⇒ (∃y)(y∈{a} et (x,y)∈G) ─────────────────────────────
    Hx = N.assume(appartient(vx, vE))                      # x∈E
    xa_G = N.modus_ponens(Hx, instancie(a_majore, vx))    # (x,a)∈G
    a_in_sa = appartient_singleton(a)                     # a∈{a}
    temoin = conjonction_intro(a_in_sa, xa_G)             # a∈{a} et (x,a)∈G  =  (a|y)corps_y
    corps_y = et(appartient(var(_Y), sa), _couple_dans(vx, var(_Y), G))  # y∈{a} et (x,y)∈G
    ex_y = N.modus_ponens(temoin, N.s5(corps_y, va, _Y))  # (∃y)(y∈{a} et (x,y)∈G)

    body = N.loi_deduction(appartient(vx, vE), ex_y)      # x∈E ⇒ (∃y)(...)
    res = N.generalisation(_X, body)                      # est_cofinale(R_G,{a},E)
    assert res.conclusion == cofinale_singleton(G, E_set, a), \
        "conclusion ≠ cible est_cofinale(R_G,{a},E)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  RÉCIPROQUE — a∈E et {a} cofinale à E ⇒ a plus grand élément de E
# ════════════════════════════════════════════════════════════════════════════
def cofinale_singleton_implique_plus_grand(G="Gcf", E_set="Ecf", a="acf"):
    """{ a∈E, est_cofinale(R_G, {a}, E) } ⊢ plus_grand_element(G,E,a).

    REMARQUE E.III.1.8 (réciproque).  Si {a} est cofinale à E et a∈E, alors a est
    le plus grand élément de E.  Pour x∈E, la cofinalité donne un y∈{a} avec
    (x,y)∈G ; mais y∈{a} ⇒ y=a (singleton_membre), donc on transporte (x,y)∈G en
    (x,a)∈G (Leibniz S6, 2e coordonnée).  Ainsi a majore E ; avec a∈E, a est le
    plus grand élément.  (E.III.1.8.)
    """
    vG, vE, va = _t(G), _t(E_set), _t(a)
    vx, vy = var(_X), var(_Y)
    sa = E.singleton(va)                                   # {a}

    Ha_in = N.assume(appartient(va, vE))                   # a∈E
    Hcof = N.assume(cofinale_singleton(G, E_set, a))       # (∀x)(x∈E⇒(∃y)(y∈{a} et (x,y)∈G))

    # ── corps « a majore E » en x : x∈E ⇒ (x,a)∈G ─────────────────────────────
    Hx = N.assume(appartient(vx, vE))                      # x∈E
    ex_y = N.modus_ponens(Hx, instancie(Hcof, vx))        # (∃y)(y∈{a} et (x,y)∈G)

    # sous le témoin y : y∈{a} ⇒ y=a, d'où (x,y)∈G transporté en (x,a)∈G
    corps_y = et(appartient(vy, sa), _couple_dans(vx, vy, G))   # y∈{a} et (x,y)∈G
    Hy = N.assume(corps_y)
    y_in_sa = conjonction_elim_gauche(Hy)                 # y∈{a}
    xy_G = conjonction_elim_droite(Hy)                    # (x,y)∈G
    y_eq_a = N.modus_ponens(y_in_sa, equivalence_avant(singleton_membre(vy, va)))  # y=a
    # Leibniz S6 : (y=a) ⇒ ((x,y)∈G ⇔ (x,a)∈G), trou « w » sur la 2e coordonnée
    phi = _couple_dans(vx, var("wcf"), G)                 # Φ(w) = (x,w)∈G
    leib = N.s6(vy, va, "wcf", phi)                       # (y=a)⇒((x,y)∈G ⇔ (x,a)∈G)
    xa_G = N.modus_ponens(xy_G, equivalence_avant(N.modus_ponens(y_eq_a, leib)))   # (x,a)∈G
    imp_y = N.loi_deduction(corps_y, xa_G)                # (y∈{a} et (x,y)∈G) ⇒ (x,a)∈G
    xa_from_ex = N.modus_ponens(ex_y, existe_elimination(imp_y, _Y))   # (x,a)∈G  (sous x∈E)

    body = N.loi_deduction(appartient(vx, vE), xa_from_ex)   # x∈E ⇒ (x,a)∈G
    a_majore = N.generalisation(_X, body)                 # (∀x)(x∈E ⇒ (x,a)∈G)
    res = conjonction_intro(Ha_in, a_majore)              # plus_grand_element(G,E,a)
    assert res.conclusion == plus_grand_element(G, E_set, va, _X), \
        "conclusion ≠ cible plus_grand_element(G,E,a)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ÉQUIVALENCE — sous a∈E, plus grand élément ⟺ {a} cofinale à E
# ════════════════════════════════════════════════════════════════════════════
def plus_grand_equivaut_cofinale_singleton(G="Gcf", E_set="Ecf", a="acf"):
    """🎯 { a∈E } ⊢ ( plus_grand_element(G,E,a) ⇔ est_cofinale(R_G, {a}, E) ).

    REMARQUE E.III.1.8 (équivalence).  On combine les deux sens.  Le sens direct
    n'utilise pas a∈E (a∈{a} suffit pour le témoin) ; la réciproque, elle, en a
    besoin.  On décharge donc a∈E dans le sens direct (hypothèse inutile mais
    licite) pour aligner les hypothèses, puis on conjoint les deux implications.
    (E.III.1.8.)
    """
    vE, va = _t(E_set), _t(a)
    pge = plus_grand_element(G, E_set, va, _X)
    cof = cofinale_singleton(G, E_set, a)

    # ⇒ : plus_grand ⇒ cofinale  (décharge complète, 0 hypothèse résiduelle)
    direct = plus_grand_implique_cofinale_singleton(G, E_set, a)
    imp_direct = N.loi_deduction(pge, direct)             # ⊢ pge ⇒ cof

    # ⇐ : cofinale ⇒ plus_grand  (sous a∈E ; on décharge la cofinalité)
    recip = cofinale_singleton_implique_plus_grand(G, E_set, a)
    imp_recip = N.loi_deduction(cof, recip)               # { a∈E } ⊢ cof ⇒ pge

    # ⇔ := (pge⇒cof) et (cof⇒pge)  (def. de equiv)
    res = conjonction_intro(imp_direct, imp_recip)        # { a∈E } ⊢ pge ⇔ cof
    assert res.conclusion == equiv(pge, cof), \
        "conclusion ≠ cible plus_grand_element(G,E,a) ⇔ est_cofinale(R_G,{a},E)"
    return res


__all__ = [
    "cofinale_singleton",
    "plus_grand_implique_cofinale_singleton",
    "cofinale_singleton_implique_plus_grand",
    "plus_grand_equivaut_cofinale_singleton",
]
