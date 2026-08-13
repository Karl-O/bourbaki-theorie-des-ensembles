"""§III.1.7 (Remarque) — le PLUS PETIT élément est l'UNIQUE élément MINIMAL.

Énoncé (E.III.1.7, Remarque suivant la Définition 4, convention graphe G) :

    { plus_petit_element(G,E,a), element_minimal(G,E,m) }  ⊢  m = a.

« Si E possède un plus petit élément a, tout élément minimal m de E coïncide
avec a. »  Autrement dit le plus petit élément, lorsqu'il existe, est l'UNIQUE
élément minimal de E.

Stratégie (order-théorique pure, < 0.1 s) — l'ANTISYMÉTRIE n'est PAS utilisée :

  1. a plus petit élément : a∈E  et  (∀x)(x∈E ⇒ (a,x)∈G).
  2. m élément minimal :    m∈E  et  (∀x)((x∈E et (x,m)∈G) ⇒ x=m).
  3. a minore E, instancié en m∈E :        (a,m)∈G.
  4. m minimal, instancié en a, appliqué à (a∈E et (a,m)∈G) :   a = m.
  5. symétrie de l'égalité :                m = a.

L'égalité x=m sortie de la minimalité naît du fait que (a,m)∈G place a « sous »
m ; comme rien n'est strictement sous un élément minimal, a vaut m.  L'antisymétrie
serait redondante : la minimalité fournit directement la coïncidence.

Théorème certifié par le noyau abrégé (primitives N.* uniquement) ; hypothèses
exactement { plus_petit_element(G,E,a), element_minimal(G,E,m) } (énoncé minimal).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, appartient
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    plus_petit_element, element_minimal,
)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §1.7 Rem.- | E III.8 L.34-35 | PDF p.111
def plus_petit_est_unique_minimal(G, E_set="E", a="a", m="m", x="x"):
    """{ plus_petit_element(G,E,a), element_minimal(G,E,m) } ⊢ m=a.

    Le plus petit élément a de E est l'unique élément minimal : tout élément
    minimal m coïncide avec a.  (E.III.1.7, Remarque — preuve sans antisymétrie.)
    """
    va, vm = _terme(a), _terme(m)
    # (1) a est le plus petit élément de E
    Hpp = N.assume(plus_petit_element(G, E_set, va, x))    # a∈E et (∀x)(x∈E⇒(a,x)∈G)
    a_in = conjonction_elim_gauche(Hpp)                    # a∈E
    a_min_body = conjonction_elim_droite(Hpp)              # (∀x)(x∈E⇒(a,x)∈G)
    # (2) m est un élément minimal de E
    Hmin = N.assume(element_minimal(G, E_set, vm, x))      # m∈E et (∀x)((x∈E et (x,m)∈G)⇒x=m)
    m_in = conjonction_elim_gauche(Hmin)                   # m∈E
    min_body = conjonction_elim_droite(Hmin)               # (∀x)((x∈E et (x,m)∈G)⇒x=m)
    # (3) a minore E, instancié en m : (a,m)∈G
    am = N.modus_ponens(m_in, instancie(a_min_body, vm))   # (a,m)∈G
    # (4) m minimal, instancié en a : (a∈E et (a,m)∈G) ⇒ a=m, appliqué
    min_a = instancie(min_body, va)                        # (a∈E et (a,m)∈G)⇒a=m
    a_eq_m = N.modus_ponens(conjonction_intro(a_in, am), min_a)   # a=m
    # (5) symétrie : m=a
    return N.modus_ponens(a_eq_m, symetrie(va, vm))        # m=a


# Cible : énoncé (clos après décharge des hypothèses) visé par le théorème.
def cible(G, E_set="E", a="a", m="m"):
    """Formule but : m = a  (la conclusion certifiée du théorème)."""
    return egal(_terme(m), _terme(a))


__all__ = ["plus_petit_est_unique_minimal", "cible"]
