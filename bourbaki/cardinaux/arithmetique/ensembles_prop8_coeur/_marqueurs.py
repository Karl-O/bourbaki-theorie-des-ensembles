"""CŒUR Prop. 8 — faits sur le marqueur * = (∅,1) sous l'hypothèse h(*) = *.

Briques partagées par les deux directions du conjoint IMAGE (cas où le marqueur
est FIXÉ par la bijection h : A⊔{∅} → B⊔{∅}) :

  • m_dans_AS(a)     — * ∈ A⊔{∅}            (marqueur_dans_somme) ;
  • m_hors_A0(a)     — ¬(* ∈ A×{0})          (marqueur_hors_copie_gauche) ;
  • mm_dans_h(...)   — {h(*)=*, dom h=A⊔{∅}} ⊢ (*,*) ∈ h
        (le marqueur, fixé, donne le couple diagonal (*,*) dans le graphe) ;
  • m_diff_si_A0(...) — {u∈A×{0}} ⊢ ¬(u = *)  (le marqueur n'est pas dans A×{0}).
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, non, appartient, existe)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, congruence_terme
from bourbaki.ensembles.familles.ensembles_somme_disjointe import UN
from bourbaki.cardinaux.arithmetique.ensembles_prop8_plus_point import (
    marqueur, marqueur_dans_somme, marqueur_hors_copie_gauche)


_STAR = E.couple(E.VIDE, UN)            # * = (∅, 1)


def m_dans_AS(a="A"):
    """⊢ * ∈ A⊔{∅}.   (le marqueur est dans l'ensemble augmenté ; clos.)"""
    return marqueur_dans_somme(a)


def m_hors_A0(a="A"):
    """⊢ ¬(* ∈ A×{0}).   (le marqueur n'est pas dans la copie de gauche ; clos.)"""
    return marqueur_hors_copie_gauche(a)


def mm_dans_h(a_somme, h="h"):
    """{h(*)=*, dom h = A⊔{∅}, * ∈ A⊔{∅}} ⊢ (*,*) ∈ h.

    Le marqueur *, fixé par h (h(*)=*) et dans le domaine, produit le couple
    diagonal (*,*) : (*,h(*))∈h (valeur_dans_graphe sous *∈dom h) puis h(*)=* le
    réécrit en (*,*).  `a_somme` = le terme A⊔{∅} (= dom h)."""
    from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_dans_graphe
    vh = var(h)
    AS = a_somme
    m = _STAR
    hm = E.valeur(vh, m)                                   # h(*)
    # *∈dom h  (de dom h=A⊔{∅} et *∈A⊔{∅})
    hdom = N.assume(egal(E.dom(vh), AS))
    m_inAS = N.assume(appartient(m, AS))
    # *∈dom h via Leibniz dom h=AS  (réécrire AS→dom h dans *∈AS)
    eq_dom = N.modus_ponens(hdom, symetrie(E.dom(vh), AS))   # AS = dom h
    m_in_dom = N.modus_ponens(m_inAS, equivalence_avant(N.modus_ponens(
        eq_dom, N.s6(AS, E.dom(vh), "w", appartient(m, var("w"))))))   # *∈dom h
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vh), m)              # *∈dom h ⇔ (∃y)((*,y)∈h)
    exy = N.modus_ponens(m_in_dom, equivalence_avant(car))  # (∃y)((*,y)∈h)
    m_hm_in = N.modus_ponens(exy, N.existe_temoin(
        appartient(E.couple(m, var("y")), vh), "y"))        # (*,h(*))∈h
    # (*,*)∈h : réécrire h(*)→* via h(*)=*
    hmm = N.assume(egal(hm, m))                            # h(*)=*
    return N.modus_ponens(m_hm_in, equivalence_avant(N.modus_ponens(
        hmm, N.s6(hm, m, "w", appartient(E.couple(m, var("w")), vh)))))   # (*,*)∈h


def m_diff_si_A0(a, point):
    """{point ∈ A×{0}} ⊢ ¬(point = *).   (un point de A×{0} n'est pas le marqueur.)

    Si point=*, alors *∈A×{0} (Leibniz, point→*), contredisant m_hors_A0
    (¬(*∈A×{0})).  Donc point≠*."""
    from bourbaki.logique.formule import Terme
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_coeur._g import A0_terme
    pt = point if isinstance(point, Terme) else var(point)
    A0 = A0_terme(a)
    m = _STAR
    p_inA0 = N.assume(appartient(pt, A0))                  # point∈A×{0}
    heq = N.assume(egal(pt, m))                            # point=*
    # *∈A×{0} : Leibniz point→* dans point∈A×{0}
    m_inA0 = N.modus_ponens(p_inA0, equivalence_avant(N.modus_ponens(
        heq, N.s6(pt, m, "w", appartient(var("w"), A0)))))  # *∈A×{0}
    contra = m_hors_A0(a)                                  # ¬(*∈A×{0})
    falso = N.modus_ponens(m_inA0,
        N.modus_ponens(contra, N.s2(non(appartient(m, A0)), non(egal(pt, m)))))
    n_eq = N.modus_ponens(N.loi_deduction(egal(pt, m), falso), N.s1(non(egal(pt, m))))
    return n_eq                                            # {point∈A×{0}} ⊢ ¬(point=*)


__all__ = ["m_dans_AS", "m_hors_A0", "mm_dans_h", "m_diff_si_A0"]
