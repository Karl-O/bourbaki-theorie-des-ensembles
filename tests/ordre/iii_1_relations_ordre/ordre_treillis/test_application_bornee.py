"""Tests §III.1 — Application majorée/minorée/bornée + bornes d'une application (Résumé §6.7)."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_application_bornee as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_definitions_bien_formees():
    """Les définitions se construisent (Formule) — bornée == majorée ET minorée."""
    from bourbaki.logique.i_1_termes_relations.formule import et
    assert M.est_application_bornee() == et(M.est_application_majoree(),
                                            M.est_application_minoree())


def test_borne_sup_implique_majoree():
    th = M.borne_sup_application_majoree()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_borne_sup_application_majoree()


def test_borne_inf_implique_minoree():
    th = M.borne_inf_application_minoree()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_borne_inf_application_minoree()


def test_bornee_implique_majoree_et_minoree():
    for f, c in [(M.application_bornee_majoree, M.cible_application_bornee_majoree),
                 (M.application_bornee_minoree, M.cible_application_bornee_minoree)]:
        th = f()
        assert th.est_clos and len(th.hypotheses) == 0
        assert th.conclusion == c()
    assert len(E.theorie_ensembles().axiomes) == 22
