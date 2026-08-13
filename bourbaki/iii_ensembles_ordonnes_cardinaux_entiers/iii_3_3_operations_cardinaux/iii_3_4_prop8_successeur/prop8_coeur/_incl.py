"""CŒUR Prop. 8 — inclusions élémentaires de la copie de gauche A×{0}.

  • A0_inclus_AS(a)       — ⊢ A×{0} ⊂ A⊔{∅}   (A⊔{∅} = (A×{0})∪({∅}×{1}), inclusion
        de la réunion gauche) ;
  • A0_inclus_dom(a)      — {dom h = A⊔{∅}} ⊢ A×{0} ⊂ dom h  (transport par l'égalité
        dom h = A⊔{∅} de l'inclusion A×{0} ⊂ A⊔{∅}).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient, inclus, impl
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (equivalence_avant,
                               equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import congruence_terme
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN, somme_disjointe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.prop8_coeur._g import A0_terme


# (inclusions élémentaires de la copie de gauche — CAS 1 de la démo de la Prop.8.)
# @livre Ch.III §3.4 Demo.8 | E III.28 L.9-9 | PDF p.131
def A0_inclus_AS(a="A"):
    """⊢ A×{0} ⊂ A⊔{∅}.   (la copie de gauche est incluse dans l'ensemble augmenté ; clos.)

    A⊔{∅} := (A×{0}) ∪ ({∅}×{1}) ; z∈A×{0} ⇒ (z∈A×{0} ∨ z∈{∅}×{1}) ⇒ z∈A⊔{∅}
    (AXIOME_REUNION ⇐), généralisé.  Construit avec des TERMES (≠ helper à noms)."""
    A0 = A0_terme(a)
    R1 = E.produit(E.singleton(E.VIDE), E.singleton(UN))   # {∅}×{1}
    AS = E.reunion(A0, R1)                                  # = A⊔{∅}
    vz = var("z")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    car = instancie(instancie(instancie(ax, A0), R1), vz)  # z∈A0∪R1 ⇔ (z∈A0 ∨ z∈R1)
    s2 = N.s2(appartient(vz, A0), appartient(vz, R1))      # z∈A0 ⇒ (z∈A0 ∨ z∈R1)
    imp = syllogisme(s2, equivalence_arriere(car))         # z∈A0 ⇒ z∈A0∪R1
    return N.generalisation("z", imp)                      # A×{0} ⊂ A⊔{∅}


def A0_inclus_dom(a="A", h="h"):
    """{dom h = A⊔{∅}} ⊢ A×{0} ⊂ dom h.

    De A×{0} ⊂ A⊔{∅} et dom h = A⊔{∅} (donc A⊔{∅} = dom h), Leibniz dans le 2ᵉ
    membre de l'inclusion."""
    vh = var(h)
    A0 = A0_terme(a)
    AS = somme_disjointe(var(a) if isinstance(a, str) else a, E.singleton(E.VIDE))
    incl = A0_inclus_AS(a)                                  # A×{0} ⊂ A⊔{∅}
    hdom = N.assume(egal(E.dom(vh), AS))                    # dom h = A⊔{∅}
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
    eq2 = N.modus_ponens(hdom, symetrie(E.dom(vh), AS))     # A⊔{∅} = dom h
    # réécrire A⊔{∅} → dom h dans (A×{0} ⊂ ·)
    return N.modus_ponens(incl, equivalence_avant(N.modus_ponens(
        eq2, N.s6(AS, E.dom(vh), "w", inclus(A0, var("w"))))))


__all__ = ["A0_inclus_AS", "A0_inclus_dom"]
