"""§III.3.2 — Ensemble des cardinaux ≤ a, et borne supérieure d'une famille de
cardinaux (notions auparavant ABSENTES).

Bourbaki, E.III.3.2 :
  • (Remarque) « Pour tout cardinal a, la relation "x est un cardinal et x ≤ a" est
    collectivisante en x (équivalente à "x est de la forme Card(X) pour X ⊂ a") ;
    l'ensemble des x satisfaisant à cette relation est appelé l'ensemble des
    cardinaux ≤ a. »
  • (après Prop 2) « Par abus de langage, le cardinal b de la proposition 2 est
    appelé la borne supérieure de la famille (a_ι)_{ι∈I} de cardinaux et se note
    sup_{ι∈I} a_ι. »  (Prop 2 : il existe un cardinal b tel que a_ι ≤ b pour tout
    ι∈I, et tel que pour tout cardinal c vérifiant a_ι ≤ c pour tout ι, on ait
    b ≤ c.)

On INTRODUIT (définitions fidèles, niveau objet) :
  • `relation_cardinal_inf_egal(x, a)` := « x est un cardinal et x ≤ a »  (relation
    caractéristique de l'ensemble des cardinaux ≤ a) ;
  • `ensemble_cardinaux_inf_egal(a)` := l'ensemble {x | x cardinal et x ≤ a} (terme
    de l'ensemble des cardinaux ≤ a) ;
  • `membre_cardinaux_inf_egal(x, a)` := la caractérisation d'appartenance
    « x ∈ {cardinaux ≤ a} ⇔ (x cardinal et x ≤ a) »  (relation membre) ;
  • `est_borne_superieure_cardinaux(b, f, i)` := « b = sup_{ι∈I} a_ι » : b est un
    cardinal, b majore tous les a_ι, et b est le PLUS PETIT majorant cardinal
    (clauses VERBATIM de Prop 2).

Le caractère COLLECTIVISANT de la relation (Remarque) et l'EXISTENCE de la borne
supérieure (Prop 2) reposent sur le Théorème 1 (≤ est un bon ordre) : ces THÉORÈMES
sont REPORTÉS honnêtement (cf. docstrings).  On certifie deux LEMMES DIRECTS cheap :
  • `a_dans_cardinaux_inf_egal` : ⊢ est_cardinal(a) ⇒ relation_cardinal_inf_egal(a,a)
    (a satisfait sa propre relation : a est cardinal et a ≤ a, réflexivité) ;
  • `borne_sup_majore` : ⊢ est_borne_superieure_cardinaux(b,f,I) ⇒ (a_ι ≤ b clause)
    (le sup majore la famille — projection NON vacuux de la conjonction).

theorie_ensembles() inchangée (22 axiomes) ; noyau intact.  Aucun axiome ajouté.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, app, egal, et, impl, equiv, pourtout,
                                       appartient)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (est_cardinal, inf_egal_card,
                                                    cardinal)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)


def _t(s):
    return var(s) if isinstance(s, str) else s


# ─────────────────────────────────────────────────────────────────────────────
# §III.3.2 (Remarque) — ENSEMBLE DES CARDINAUX ≤ a
# ─────────────────────────────────────────────────────────────────────────────
def relation_cardinal_inf_egal(x, a):
    """Relation caractéristique « x est un cardinal et x ≤ a »  (E.III.3.2, Remarque).

    C'est la relation collectivisante en x dont l'ensemble des solutions est
    l'ensemble des cardinaux ≤ a.  Renvoie la Formule « est_cardinal(x) et x ≤ a »."""
    return et(est_cardinal(_t(x)), inf_egal_card(_t(x), _t(a)))


def ensemble_cardinaux_inf_egal(a):
    """Ensemble des cardinaux ≤ a := {x | x cardinal et x ≤ a}  (E.III.3.2, Remarque).

    « l'ensemble des x satisfaisant à cette relation est appelé l'ensemble des
    cardinaux ≤ a. »  Représenté par le terme app("cardinaux_inf_egal", a) ; son
    existence (caractère COLLECTIVISANT de la relation) est REPORTÉE (Théorème 1, ≤
    bon ordre).  Sa caractérisation d'appartenance est `membre_cardinaux_inf_egal`."""
    return app("cardinaux_inf_egal", _t(a))


def membre_cardinaux_inf_egal(x, a):
    """Caractérisation d'appartenance à l'ensemble des cardinaux ≤ a (E.III.3.2).

    « x ∈ {cardinaux ≤ a} ⇔ (x est un cardinal et x ≤ a) ».  Renvoie la Formule
    d'équivalence (membre ⇔ relation caractéristique) ; c'est la propriété
    DÉFINISSANT l'ensemble (collectivisé), valable une fois la collectivisation
    acquise (Théorème 1, reportée pour la PREUVE)."""
    return equiv(appartient(_t(x), ensemble_cardinaux_inf_egal(a)),
                 relation_cardinal_inf_egal(x, a))


def a_dans_cardinaux_inf_egal(a="A"):
    """⊢ est_cardinal(a) ⇒ relation_cardinal_inf_egal(a, a)   (E.III.3.2).

    « a satisfait à sa propre relation » : si a est un cardinal, alors (a est un
    cardinal et a ≤ a), la seconde clause par réflexivité de ≤
    (cardinal_inf_egal_reflexif).  LEMME DIRECT cheap (a est le PLUS GRAND élément de
    l'ensemble des cardinaux ≤ a).  NON vacuux : la conclusion (conjonction) n'est
    pas l'hypothèse (est_cardinal seul)."""
    va = _t(a)
    h = N.assume(est_cardinal(va))                      # a cardinal
    refl = inf_egal_reflexif(a)                         # ⊢ a ≤ a  (réflexivité de ≤)
    conc = conjonction_intro(h, refl)                  # a cardinal et a ≤ a
    return N.loi_deduction(est_cardinal(va), conc)     # ⇒


# ─────────────────────────────────────────────────────────────────────────────
# §III.3.2 (après Prop 2) — BORNE SUPÉRIEURE d'une famille de cardinaux
# ─────────────────────────────────────────────────────────────────────────────
def majore_famille_cardinaux(b, f, i, iota="iota"):
    """« b majore la famille (a_ι)_{ι∈I} » := (∀ι)(ι∈I ⇒ a_ι ≤ b)  (E.III.3.2, Prop 2).

    `f` = la famille (fonction ι↦a_ι), `i` = l'ensemble d'indices I.  a_ι est la
    valeur en ι de la famille (valeur_famille).  Renvoie la Formule majorant."""
    vb, vi, viota = _t(b), _t(i), var(iota)
    a_iota = E.valeur_famille(_t(f), viota)
    return pourtout(iota, impl(appartient(viota, vi), inf_egal_card(a_iota, vb)))


def plus_petit_majorant_cardinaux(b, f, i, c="c", iota="iota"):
    """« b est le PLUS PETIT majorant cardinal de (a_ι) » (E.III.3.2, Prop 2).

    « pour tout cardinal c vérifiant a_ι ≤ c pour tout ι∈I, on a b ≤ c. »  Renvoie
    la Formule
      (∀c)[ (c cardinal et (∀ι)(ι∈I ⇒ a_ι ≤ c)) ⇒ b ≤ c ]."""
    vb, vc = _t(b), _t(c)
    hyp = et(est_cardinal(vc), majore_famille_cardinaux(b, f, i, iota))
    return pourtout(c, impl(hyp, inf_egal_card(vb, vc)))


def est_borne_superieure_cardinaux(b, f, i, c="c", iota="iota"):
    """« b = sup_{ι∈I} a_ι » : b est la borne supérieure de la famille de cardinaux
    (a_ι)_{ι∈I}  (E.III.3.2, après Prop 2).

    Conjonction des trois clauses de Prop 2 :
      1° b est un cardinal ;
      2° b majore tous les a_ι (b est un majorant) ;
      3° b est le plus petit cardinal majorant (b ≤ c pour tout majorant cardinal c).
    Renvoie la Formule « est_cardinal(b) et majore(...) et plus_petit_majorant(...) ».
    L'EXISTENCE d'un tel b (Prop 2) est REPORTÉE (Théorème 1, ≤ bon ordre)."""
    vb = _t(b)
    return et(et(est_cardinal(vb), majore_famille_cardinaux(b, f, i, iota)),
              plus_petit_majorant_cardinaux(b, f, i, c, iota))


def borne_sup_majore(b="B", f="f", i="I", c="c", iota="iota"):
    """⊢ est_borne_superieure_cardinaux(b,f,I) ⇒ majore_famille_cardinaux(b,f,I).

    LEMME DIRECT : la borne supérieure d'une famille de cardinaux MAJORE cette
    famille (clause 2° extraite de la définition par projection de la conjonction).
    NON vacuux : la conclusion (le majorant (∀ι)(ι∈I⇒a_ι≤b)) est une SOUS-partie
    propre de la définition de la borne supérieure, pas la définition entière."""
    bsup = est_borne_superieure_cardinaux(b, f, i, c, iota)
    h = N.assume(bsup)
    # bsup = ((cardinal et majore) et plus_petit) ; majore = conj. gauche de la gauche
    majore = conjonction_elim_droite(conjonction_elim_gauche(h))
    return N.loi_deduction(bsup, majore)


__all__ = [
    "relation_cardinal_inf_egal", "ensemble_cardinaux_inf_egal",
    "membre_cardinaux_inf_egal", "a_dans_cardinaux_inf_egal",
    "majore_famille_cardinaux", "plus_petit_majorant_cardinaux",
    "est_borne_superieure_cardinaux", "borne_sup_majore",
]
