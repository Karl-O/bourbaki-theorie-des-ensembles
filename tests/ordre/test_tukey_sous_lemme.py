"""Tests — sous-lemme de Tukey prouvé par récurrence finie (§III.4-5)."""
from bourbaki.ordre.ensembles_tukey_sous_lemme import sous_lemme_preuve
from bourbaki.ordre.ensembles_tukey_iii4 import (
    sous_lemme_partie_finie_dans_membre, Incl,
)
from bourbaki.ordre.ensembles_ordre_relation import totalement_ordonne
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.formule import var, existe, appartient


def test_sous_lemme_conclusion_et_hyps():
    r = sous_lemme_preuve()
    # conclusion = EXACTEMENT le résidu déposé dans Tukey
    assert r.conclusion == sous_lemme_partie_finie_dans_membre("S", "T", "Y", "Mtk")
    # 2 hypothèses HONNÊTES (non vacueuses) : 𝔗 chaîne + 𝔗 non vide
    assert len(r.hypotheses) == 2
    assert totalement_ordonne(Incl(var("S")), var("T")) in r.hypotheses
    assert existe("M0tk", appartient(var("M0tk"), var("T"))) in r.hypotheses
    # anti-vacuité : la conclusion n'est PAS dans les hypothèses
    assert r.conclusion not in r.hypotheses


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
