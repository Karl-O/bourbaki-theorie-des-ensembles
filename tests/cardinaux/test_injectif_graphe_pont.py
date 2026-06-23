"""Tests — PONT couple→valeur : injectif_graphe(F) ⇒ injective_dans(F, dom F)."""
from bourbaki.logique.formule import var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.ensembles_recollement_famille_injectif import injectif_graphe
from bourbaki.cardinaux.ensembles_injectif_graphe_pont import (
    injectif_graphe_implique_injective_dans,
)


def test_theorie_ensembles_reste_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_pont_conclusion_injective_dans():
    th = injectif_graphe_implique_injective_dans()
    vF = var("Fpont")
    assert th.conclusion == E.injective_dans(vF, E.dom(vF))
    assert th.conclusion not in th.hypotheses


def test_pont_deux_hyps_honnetes():
    th = injectif_graphe_implique_injective_dans()
    vF = var("Fpont")
    assert E.est_fonctionnel(vF) in th.hypotheses
    assert injectif_graphe(vF) in th.hypotheses
    assert len(th.hypotheses) == 2
