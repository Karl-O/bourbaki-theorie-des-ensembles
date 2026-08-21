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


def test_division_euclidienne_complete():
    """🎯🎯 LE THEOREME DU LIVRE (couple unique) :
    ⊢ {Fini a, Fini b, 0<b, + residus C61}
      (Eq)(Er)(b.q+r=a et r<b)  ET  cloture-(pour tout) de l'unicite.
    L'hypothese est le << b > 0 >> du livre — b != 0 en est DERIVE."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence_final import (
        division_euclidienne, enonce_division_euclidienne)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_strict_card
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, ZERO

    r = division_euclidienne()
    assert r.conclusion == enonce_division_euclidienne()
    #   les hypotheses du LIVRE presentes, le b!=0 des briques ABSENT (derive)
    assert est_fini(var("adf")) in r.hypotheses
    assert est_fini(var("bdf")) in r.hypotheses
    assert inf_strict_card(ZERO, var("bdf")) in r.hypotheses
    assert non(egal(var("bdf"), ZERO)) not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
