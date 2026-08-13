# -*- coding: utf-8 -*-
"""Test §III.5.6 — division euclidienne, CAS PETIT (a<b → (q,r)=(0, Card a)).

On APPELLE le théorème : CLOS (0 hypothèse — l'hypothèse d'ordre est déchargée par la loi de
déduction), conclusion == cible (implication vers le double existentiel, opérations cardinales
RÉELLES), theorie == 22. Import cardinaux lourd → marqué slow.
"""
import pytest

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_cas_petit as M

pytestmark = pytest.mark.slow


def test_division_cas_petit():
    """⊢ (Card a < b) ⇒ (∃q)(∃r)(b·q + r = Card a et r < b) — clos, fidèle, 22 axiomes."""
    t = M.division_cas_petit()
    assert t.conclusion == M.division_cas_petit_cible()
    assert t.est_clos                                   # hypothèse d'ordre déchargée
    assert len(theorie_ensembles().axiomes) == 22       # frontière intacte
