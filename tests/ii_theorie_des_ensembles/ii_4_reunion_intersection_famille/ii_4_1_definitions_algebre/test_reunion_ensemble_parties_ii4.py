# -*- coding: utf-8 -*-
"""Test brique ⋃𝔊 (ensemble de parties) — appartenance sous famille identité."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_reunion_ensemble_parties_ii4 import (
    membre_reunion_ensemble, enonce_membre_reunion_ensemble,
    membre_inter_ensemble, enonce_membre_inter_ensemble, est_famille_identite,
    partie_incluse_reunion, enonce_partie_incluse_reunion,
    inter_incluse_partie, enonce_inter_incluse_partie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides)


def test_membre_reunion_ensemble():
    """⊢ {famille_identite(f,U)} (z∈⋃U) ⇔ (∃i)(i∈U et z∈i)."""
    r = membre_reunion_ensemble()
    assert r.conclusion == enonce_membre_reunion_ensemble()
    assert r.est_clos is False
    assert r.hypotheses == frozenset([est_famille_identite(E.var("f"), E.var("U"))])


def test_membre_inter_ensemble():
    """⊢ {famille_identite(f,U), (∃i)(i∈U)} (z∈⋂U) ⇔ (∀i)(i∈U ⇒ z∈i).

    ÉNONCÉ RENFORCÉ par la migration Déf. 2 (⋂ = sélection dans ⋃, E II.22).
    Le test exigeait auparavant la SEULE hypothèse `est_famille_identite` ; cette
    forme-là est FAUSSE pour U=∅ (⋂∅=∅ mais (∀i)(i∈∅⇒z∈i) vaut pour tout z) et
    n'était dérivable que de l'ancien AXIOME_INTER_FAM, qui rendait la théorie
    contradictoire.  On assère donc désormais la présence de l'hypothèse que
    Bourbaki écrit dans la Déf. 2 : « I n'est pas vide », ici (∃i)(i∈U).
    La conclusion, elle, est inchangée."""
    r = membre_inter_ensemble()
    assert r.conclusion == enonce_membre_inter_ensemble()
    assert r.est_clos is False
    assert r.hypotheses == frozenset([est_famille_identite(E.var("f"), E.var("U")),
                                      indices_non_vides(E.var("U"))])


def test_partie_incluse_reunion():
    """⊢ {famille_identite(f,U)} (c∈U) ⇒ (c⊂⋃U)."""
    r = partie_incluse_reunion()
    assert r.conclusion == enonce_partie_incluse_reunion()
    assert r.hypotheses == frozenset([est_famille_identite(E.var("f"), E.var("U"))])


def test_inter_incluse_partie():
    """⊢ {famille_identite(f,U)} (c∈U) ⇒ (⋂U⊂c)."""
    r = inter_incluse_partie()
    assert r.conclusion == enonce_inter_incluse_partie()
    assert r.hypotheses == frozenset([est_famille_identite(E.var("f"), E.var("U"))])


def test_theorie_inchangee():
    membre_reunion_ensemble()
    partie_incluse_reunion()
    inter_incluse_partie()
    assert len(E.theorie_ensembles().axiomes) == 22
