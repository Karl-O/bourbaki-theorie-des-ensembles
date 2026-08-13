"""Tests — §III.2.1 Proposition 2 (E III.15) : STRICTITÉ de x ↦ S_x.

On vérifie le théorème de strictité, CONJONCTION de deux théorèmes déjà clos :

  segment_extremite_strictement_croissant :
      { est_bien_ordonne(R,E),  x∈E,  R{x,y},  x≠y }
          ⊢ ( seg(E,R,x) ⊂ seg(E,R,y)
              et ( x∈seg(E,R,y) et ¬(x∈seg(E,R,x)) ) ).

Vérifications (leçon prop10 : un import NE PROUVE RIEN — on APPELLE la fonction) :
  • conclusion == cible reconstruite avec les MÊMES constructeurs (seg/inclus/et/non/appartient) ;
  • hypothèses EXACTEMENT les 4 antécédents Bourbaki, aucune parasite, conclusion absente ;
  • theorie_ensembles() = 22 axiomes.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, appartient, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments import (
    ensembles_segment_extremite_injectif as INJ,
)


def _Rgraphe(a, b):
    """Relation-test R{a,b} := (a,b)∈R (même lecture que seg/membre_segment)."""
    return appartient(E.couple(a, b), var("R"))


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  Conclusion exacte : inclusion large + témoin d'écart.
# ════════════════════════════════════════════════════════════════════════════
def test_strictement_croissant_cible():
    th = INJ.segment_extremite_strictement_croissant()
    vx, vy = var("x"), var("y")
    Sx, Sy = seg("R", "E", vx), seg("R", "E", vy)
    cible = et(inclus(Sx, Sy),
               et(appartient(vx, Sy), non(appartient(vx, Sx))))
    assert th.conclusion == cible
    # cohérence avec le miroir exposé par le module
    assert th.conclusion == INJ.segment_extremite_strictement_croissant_cible()


# ════════════════════════════════════════════════════════════════════════════
#  Les 4 hypothèses load-bearing — EXACTES, aucune parasite.
# ════════════════════════════════════════════════════════════════════════════
def test_strictement_croissant_hypotheses():
    th = INJ.segment_extremite_strictement_croissant()
    vx, vy = var("x"), var("y")
    h_bo = E.est_bien_ordonne(_R_de("R"), var("E"))     # est_bien_ordonne(R,E)
    h_xE = appartient(vx, var("E"))                     # x∈E
    h_Rxy = _Rgraphe(vx, vy)                            # R{x,y}
    h_xney = non(egal(vx, vy))                          # x≠y
    # EXACTEMENT les quatre antécédents Bourbaki, rien de plus.
    assert th.hypotheses == frozenset({h_bo, h_xE, h_Rxy, h_xney})


def test_strictement_croissant_non_vacuous():
    th = INJ.segment_extremite_strictement_croissant()
    # la conclusion (inclusion + témoin) n'est aucune des hypothèses.
    assert th.conclusion not in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  Invariant du noyau.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_invariante():
    assert len(E.theorie_ensembles().axiomes) == 22
