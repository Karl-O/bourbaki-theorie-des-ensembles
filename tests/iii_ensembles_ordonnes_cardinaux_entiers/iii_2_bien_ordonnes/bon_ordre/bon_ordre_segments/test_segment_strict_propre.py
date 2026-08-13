"""Tests — §III.2.1 Proposition 2 (préliminaire « x↦S_x strictement croissante »).

On vérifie les DEUX lemmes-témoins de la strictité de l'inclusion des segments :

  (L-a) element_hors_de_son_segment :  ⊢ ¬( x ∈ seg(R,E,x) )   [INCONDITIONNEL].
  (L-b) seg_strict_propre :  { x∈E, R{x,y}, x≠y } ⊢ ( x∈seg(R,E,y) et ¬(x∈seg(R,E,x)) ).

Pour CHAQUE lemme : conclusion == cible, hypothèses EXACTES, non-vacuité, et
l'invariant theorie_ensembles = 22 axiomes.  (L-a) doit en outre être CLOS.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments import (
    ensembles_segment_strict_propre as SP,
)


def _Rgraphe(a, b):
    """Relation-test R{a,b} := (a,b)∈R (même lecture que seg/membre_segment)."""
    return appartient(E.couple(a, b), var("R"))


# ════════════════════════════════════════════════════════════════════════════
#  (L-a)  element_hors_de_son_segment :  ⊢ ¬( x ∈ seg(R,E,x) )   [INCONDITIONNEL].
# ════════════════════════════════════════════════════════════════════════════
def test_hors_segment_cible():
    th = SP.element_hors_de_son_segment()
    cible = SP.element_hors_de_son_segment_cible()      # ¬(x∈seg(R,E,x))
    assert th.conclusion == cible


def test_hors_segment_inconditionnel():
    th = SP.element_hors_de_son_segment()
    # INCONDITIONNEL : exactement 0 hypothèse, et est_clos.
    assert th.hypotheses == frozenset()
    assert th.est_clos is True


def test_hors_segment_non_vacuous():
    th = SP.element_hors_de_son_segment()
    assert th.conclusion not in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  (L-b)  seg_strict_propre :  { x∈E, R{x,y}, x≠y } ⊢ ( x∈S_y et ¬(x∈S_x) ).
# ════════════════════════════════════════════════════════════════════════════
def test_strict_propre_cible():
    th = SP.seg_strict_propre()
    cible = SP.seg_strict_propre_cible()                # (x∈S_y et ¬(x∈S_x))
    assert th.conclusion == cible


def test_strict_propre_hypotheses():
    th = SP.seg_strict_propre()
    vx, vy = var("x"), var("y")
    h_x_in_E = appartient(vx, var("E"))                 # x∈E
    h_Rxy = _Rgraphe(vx, vy)                            # R{x,y}
    h_x_ne_y = non(egal(vx, vy))                        # x≠y
    # EXACTEMENT les trois antécédents load-bearing, rien de plus.
    assert th.hypotheses == frozenset({h_x_in_E, h_Rxy, h_x_ne_y})


def test_strict_propre_non_vacuous():
    th = SP.seg_strict_propre()
    assert th.conclusion not in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  Invariant du noyau.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_invariante():
    assert len(E.theorie_ensembles().axiomes) == 22
