"""Tests — §III.2.1 Proposition 2 (E III.15), SENS LARGE : x≤y ⟹ S_x ⊂ S_y.

On vérifie le théorème NOMMÉ III.2, ré-exposition CLOSE d'un théorème déjà clos en
aval (seg_strict_monotone_de_bon_ordre), forme CLOSE par double décharge :

  segment_extremite_monotone :
      ⊢ est_bien_ordonne(R,E) ⇒ ( R{x,y} ⇒ inclus(seg(E,R,x), seg(E,R,y)) ).

Vérifications (leçon prop10 : un import NE PROUVE RIEN — on APPELLE la fonction) :
  • conclusion == cible reconstruite avec les MÊMES constructeurs (impl/seg/inclus/appartient) ;
  • CLOS : 0 hypothèse pendante (les deux antécédents Bourbaki sont des implications) ;
  • theorie_ensembles() = 22 axiomes.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, impl, appartient, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments import (
    ensembles_segment_extremite_monotone as MONO,
)


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  Conclusion exacte : impl( bon ordre, impl( R{x,y}, inclus(seg(x), seg(y)) ) ).
# ════════════════════════════════════════════════════════════════════════════
def test_monotone_cible():
    th = MONO.segment_extremite_monotone()
    vx, vy = var("x"), var("y")
    Rf = _R_de("R")
    bo = E.est_bien_ordonne(Rf, var("E"))               # est_bien_ordonne(R,E)
    rxy = Rf(vx, vy)                                     # R{x,y}
    Sx, Sy = seg("R", "E", vx), seg("R", "E", vy)
    cible = impl(bo, impl(rxy, inclus(Sx, Sy)))
    assert th.conclusion == cible
    # cohérence avec le miroir exposé par le module
    assert th.conclusion == MONO.segment_extremite_monotone_cible()


# ════════════════════════════════════════════════════════════════════════════
#  CLOS : aucune hypothèse pendante (double décharge réussie).
# ════════════════════════════════════════════════════════════════════════════
def test_monotone_clos():
    th = MONO.segment_extremite_monotone()
    assert th.est_clos
    assert th.hypotheses == frozenset()


# ════════════════════════════════════════════════════════════════════════════
#  Invariant du noyau.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_invariante():
    assert len(E.theorie_ensembles().axiomes) == 22
