# -*- coding: utf-8 -*-
"""Test §III.5.6 Th.1 — EXISTENCE de la division euclidienne (assemblage final).

division_existence ⊢ {b≠0, Fini b, + résidus C61} ⊢ (∀n)(Fini n ⇒ (∃q)(∃r)(b·q+r=n et r<b)).
« CLOS modulo C61 » : résidus honnêtes b≠0 / predecesseur_fini_universel / principe_recurrence /
cardinal_pas_entre (les mêmes que l'existence de ℕ). theorie == 22, aucun postulat."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence_final import (
    _strong_step, division_existence, enonce_division_existence)

pytestmark = pytest.mark.slow


def test_strong_step():
    """⊢ {Fini b, b≠0, +C61} (∀n)(S{n} ⇒ (Fini n ⇒ R{n}))  — cœur par trichotomie."""
    r = _strong_step()
    assert len(r.hypotheses) == 4          # {Fini b, b≠0, principe_recurrence, cardinal_pas_entre}


def test_division_existence():
    """⊢ {b≠0, Fini b, pred_univ, +C61} (∀n)(Fini n ⇒ (∃q,r)(b·q+r=n et r<b))."""
    r = division_existence()
    assert r.conclusion == enonce_division_existence()
    assert len(r.hypotheses) == 5          # + predecesseur_fini_universel


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
