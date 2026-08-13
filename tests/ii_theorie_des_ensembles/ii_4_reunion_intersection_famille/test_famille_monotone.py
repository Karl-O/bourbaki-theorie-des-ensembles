"""Tests Résumé §6.12 — Familles croissantes/décroissantes de parties."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
import bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ensembles_famille_monotone as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_definitions_bien_formees():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Formule
    cr, dc = M.famille_croissante_parties(), M.famille_decroissante_parties()
    assert isinstance(cr, Formule) and isinstance(dc, Formule)
    assert cr != dc                                        # croissante ≠ décroissante


def test_famille_croissante_monotone_close():
    th = M.famille_croissante_monotone()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_famille_croissante_monotone()


def test_famille_decroissante_monotone_close():
    th = M.famille_decroissante_monotone()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_famille_decroissante_monotone()


def test_parametrable():
    th = M.famille_croissante_monotone("H", "Y", "p", "q")
    assert th.est_clos
    assert th.conclusion == M.cible_famille_croissante_monotone("H", "Y", "p", "q")
    assert len(E.theorie_ensembles().axiomes) == 22
