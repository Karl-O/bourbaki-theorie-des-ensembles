"""§III.3.5 — EXPONENTIATION CARDINALE : a^(b+c) = a^b · a^c  (Proposition 9 / Cor. 1
de la Proposition 10, E.III.3.5).

ÉNONCÉ visé (forme cardinale binaire, miroir de l'arithmétique cardinale du projet) :

    ⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))

c.-à-d.  exposant_cardinal_binaire(A, B⊔C) = produit_cardinal_binaire(
              exposant_cardinal_binaire(A, B), exposant_cardinal_binaire(A, C)).

CRUX (DUR — bijection d'ESPACES DE FONCTIONS) : la bijection
        Φ : 𝓕(B⊔C; A) → 𝓕(B;A) × 𝓕(C;A),  f ↦ (f∘ι_B, f∘ι_C)
(f restreinte à la copie de B, f restreinte à la copie de C), où ι_B, ι_C sont les
injections canoniques u↦(u,0), v↦(v,1) dans la somme disjointe B⊔C := (B×{0})∪(C×{1}).
Inverse : (g,h) ↦ « recoller » g et h en l'application qui vaut g(u) sur (u,0) et h(v)
sur (v,1).  Ceci est une bijection d'espaces de fonctions : MOYEN-DUR.

═══════════════════════════════════════════════════════════════════════════════
ÉTAT (SALVAGE, paliers sûrs livrés au fur et à mesure) :

PALIER 0 (CLOS) — DÉFINITIONS / FORMES :
  • exposant_somme_cardinal(A,B,C)   : a^(b+c) := Card(𝓕(B⊔C; A))  (terme) ;
  • produit_exposants_cardinal(A,B,C): a^b · a^c := Card(𝓕(B;A) × 𝓕(C;A))  (terme).

PALIER 1 (CLOS) — CARACTÉRISATION MEMBERSHIP (via les axiomes de DÉFINITION) :
  • membre_applications_somme(A,B,C)  : t∈𝓕(B⊔C;A) ⇔ (∃G)(t=((G,B⊔C),A) et G∈A^(B⊔C)) ;
  • membre_exposant_somme(A,B,C)      : G∈A^(B⊔C) ⇔ (G⊂(B⊔C)×A et G fonct et dom G=B⊔C) ;
  • membre_produit_applications(A,B,C): t∈𝓕(B;A)×𝓕(C;A)
        ⇔ (∃p)(∃q)(t=(p,q) et p∈𝓕(B;A) et q∈𝓕(C;A))  [AXIOME_PRODUIT] ;
  • membre_applications_b(A,B)        : t∈𝓕(B;A) ⇔ (∃G)(t=((G,B),A) et G∈A^B).

Ces caractérisations d'appartenance sont des instances DIRECTES des axiomes de
DÉFINITION `axiome_applications` / `axiome_exposant` / `AXIOME_PRODUIT` — rien postulé.

CŒUR (la bijection restriction Φ et l'égalité finale via _prop1_direct_t) : REPORTÉ
(bijection d'espaces de fonctions, voir StructuredOutput pour la raison précise).
═══════════════════════════════════════════════════════════════════════════════
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, ou, impl, appartient,
                     existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 0 — DÉFINITIONS / FORMES  (a^(b+c) et a^b·a^c comme cardinaux)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_somme_cardinal(a, b, c):
    """a^(b+c) := Card(𝓕(B⊔C; A))   (membre de gauche de la Proposition 9).

    = exposant_cardinal_binaire(A, B⊔C) où B⊔C = somme_disjointe(B, C)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return exposant_cardinal_binaire(va, somme_disjointe(vb, vc))


def produit_exposants_cardinal(a, b, c):
    """a^b · a^c := Card(𝓕(B;A) × 𝓕(C;A))   (membre de droite de la Proposition 9).

    = produit_cardinal_binaire(exposant_cardinal_binaire(A,B),
                               exposant_cardinal_binaire(A,C))  modulo les supports."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return cardinal(E.produit(E.applications(vb, va), E.applications(vc, va)))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1 — CARACTÉRISATION MEMBERSHIP  (instances des axiomes de DÉFINITION)
# ═══════════════════════════════════════════════════════════════════════════════
def membre_exposant_somme(a="A", b="B", c="C", g="G"):
    """⊢ (G ∈ A^(B⊔C)) ⇔ (G⊂(B⊔C)×A et G fonctionnel et dom G = B⊔C).

    Instance DIRECTE de l'axiome de DÉFINITION `axiome_exposant` (E={B⊔C}, F=A).
    Caractérise les graphes fonctionnels de la somme disjointe B⊔C dans A."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    vG = _t(g)
    ax = N.axiome(E.theorie_exposant(BC, va), E.axiome_exposant(BC, va))
    return instancie(ax, vG)


def membre_applications_somme(a="A", b="B", c="C", t="t"):
    """⊢ (t ∈ 𝓕(B⊔C; A)) ⇔ (∃G)(t = ((G, B⊔C), A) et G ∈ A^(B⊔C)).

    Instance DIRECTE de l'axiome de DÉFINITION `axiome_applications` (E=B⊔C, F=A).
    Une application de B⊔C dans A est le triple ((G,B⊔C),A) d'un graphe G∈A^(B⊔C)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    vt = _t(t)
    ax = N.axiome(E.theorie_applications(BC, va, "t", "G"),
                  E.axiome_applications(BC, va, "t", "G"))
    return instancie(ax, vt)


def membre_applications_b(a="A", b="B", t="t"):
    """⊢ (t ∈ 𝓕(B; A)) ⇔ (∃G)(t = ((G, B), A) et G ∈ A^B).

    Instance DIRECTE de l'axiome de DÉFINITION `axiome_applications` (E=B, F=A)
    pour le PREMIER facteur 𝓕(B;A) du produit (idem 𝓕(C;A) avec C)."""
    va, vb = _t(a), _t(b)
    vt = _t(t)
    ax = N.axiome(E.theorie_applications(vb, va, "t", "G"),
                  E.axiome_applications(vb, va, "t", "G"))
    return instancie(ax, vt)


def membre_produit_applications(a="A", b="B", c="C", t="t"):
    """⊢ (t ∈ 𝓕(B;A)×𝓕(C;A)) ⇔ (∃p)(∃q)(t=(p,q) et p∈𝓕(B;A) et q∈𝓕(C;A)).

    Instance DIRECTE d'AXIOME_PRODUIT sur le produit 𝓕(B;A)×𝓕(C;A) (membre de
    droite de la Proposition 9 : un couple de deux applications)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    FB = E.applications(vb, va)                 # 𝓕(B;A)
    FC = E.applications(vc, va)                 # 𝓕(C;A)
    vt = _t(t)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    return instancie(instancie(instancie(ax, FB), FC), vt)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 2 — DÉCOMPOSITION STRUCTURELLE  (le sens « facile » de la caractérisation)
#   Tout t ∈ 𝓕(B⊔C;A) est le triple ((G,B⊔C),A) d'un graphe fonctionnel G défini
#   sur tout B⊔C.  C'est la donnée d'entrée de la restriction Φ : f ↦ (f|B, f|C).
# ═══════════════════════════════════════════════════════════════════════════════
def applications_somme_donne_graphe(a="A", b="B", c="C", t="t"):
    """{t ∈ 𝓕(B⊔C; A)} ⊢ (∃G)(t = ((G, B⊔C), A)
                              et (G ⊂ (B⊔C)×A et G fonctionnel et dom G = B⊔C)).

    DÉCOMPOSITION STRUCTURELLE (sens « facile ») : toute application de B⊔C dans A
    expose son graphe fonctionnel G, total sur B⊔C.  C'est l'entrée de la
    restriction Φ : f ↦ (f|B, f|C).  Preuve : membre_applications_somme donne
    (∃G)(t=((G,B⊔C),A) et G∈A^(B⊔C)) ; membre_exposant_somme déplie G∈A^(B⊔C) en
    ses trois conjoints ; congruence sous l'existentielle ; rien postulé."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BC = somme_disjointe(vb, vc)
    vt, vG = _t(t), var("G")
    triple = E.couple(E.couple(vG, BC), va)               # ((G,B⊔C),A)
    in_exp = appartient(vG, E.exposant(BC, va))           # G ∈ A^(B⊔C)
    corps_exp = et(et(inclus(vG, E.produit(BC, va)), E.est_fonctionnel(vG)),
                   egal(E.dom(vG), BC))                   # G⊂(B⊔C)×A et G fonct et domG=B⊔C
    cible = et(egal(vt, triple), corps_exp)               # corps de l'∃ visé
    # t∈𝓕(B⊔C;A) ⇒ (∃G)(t=((G,B⊔C),A) et G∈A^(B⊔C))
    app_car = membre_applications_somme(a, b, c, t)       # ⇔
    ht = N.assume(appartient(vt, E.applications(BC, va)))
    ex_in = N.modus_ponens(ht, equivalence_avant(app_car))   # (∃G)(t=triple et G∈A^(B⊔C))
    # sous le corps (t=triple et G∈A^(B⊔C)) : déplier G∈A^(B⊔C) → corps_exp
    exp_car = membre_exposant_somme(a, b, c, "G")         # G∈A^(B⊔C) ⇔ corps_exp
    body = et(egal(vt, triple), in_exp)
    hb = N.assume(body)
    t_eq = conjonction_elim_gauche(hb)                    # t=triple
    g_in = conjonction_elim_droite(hb)                    # G∈A^(B⊔C)
    g_corps = N.modus_ponens(g_in, equivalence_avant(exp_car))   # corps_exp
    wit = conjonction_intro(t_eq, g_corps)               # cible (témoin G courant)
    ex_cible = N.modus_ponens(wit, N.s5(cible, vG, "G"))  # (∃G)cible  (S5 idempotent)
    inner = existe_elimination(N.loi_deduction(body, ex_cible), "G")   # (∃G)body ⇒ (∃G)cible
    ex_concl = N.modus_ponens(ex_in, inner)              # (∃G)cible   [sous t∈𝓕]
    return N.loi_deduction(appartient(vt, E.applications(BC, va)), ex_concl)


__all__ = [
    "exposant_somme_cardinal", "produit_exposants_cardinal",
    "membre_exposant_somme", "membre_applications_somme",
    "membre_applications_b", "membre_produit_applications",
    "applications_somme_donne_graphe",
]
