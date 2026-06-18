"""Tests — §III.1 Propositions 5/6/7/9 sur le calcul des bornes supérieures.

Vérifie que chaque théorème est CERTIFIÉ par le noyau (construction sans erreur),
que les théorèmes CLOS le sont vraiment, que les conditionnels portent exactement
leurs hypothèses HONNÊTES (jamais la conclusion parmi les hypothèses → jamais
vacuité), et que theorie_ensembles reste = 22 axiomes (rien postulé)."""
from __future__ import annotations

import bourbaki.ordre.ensembles_sup_generiques_iii1 as M
from bourbaki.ensembles import ensembles_abrege as E


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_majorant_de_sur_partie():
    t = M.majorant_de_sur_partie()
    assert len(t.hypotheses) == 2          # A⊂B, majorant(B)
    assert t.conclusion not in t.hypotheses


def test_prop5_sup_monotone_inclusion():
    t = M.sup_monotone_inclusion()
    assert len(t.hypotheses) == 3          # A⊂B, m=supA, n=supB
    assert t.conclusion not in t.hypotheses


def test_cor5_sup_sous_famille():
    t = M.sup_sous_famille_le()
    assert len(t.hypotheses) == 3
    assert t.conclusion not in t.hypotheses
    # identique à Prop 5 (même conclusion)
    assert t.conclusion == M.sup_monotone_inclusion().conclusion


def test_majorant_de_sur_domine():
    t = M.majorant_de_sur_domine()
    assert len(t.hypotheses) == 3          # transitivité, domine, majorant(B)
    assert t.conclusion not in t.hypotheses


def test_prop6_sup_monotone_termes():
    t = M.sup_monotone_termes()
    assert len(t.hypotheses) == 4          # transitivité, domine, m=supA, n=supB
    assert t.conclusion not in t.hypotheses


def test_prop9_sup_induit_sur_partie():
    t = M.sup_induit_sur_partie()
    assert len(t.hypotheses) == 3          # m=sup_E A, m∈F, plus-petit-dans-F
    assert t.conclusion not in t.hypotheses


def test_prop7_majorant_reunion_iff_CLOS():
    t = M.majorant_reunion_iff()
    assert t.est_clos                       # totalement clos, 0 hypothèse
    assert len(t.hypotheses) == 0
