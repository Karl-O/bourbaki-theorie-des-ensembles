"""Tests du critère typique C41 (Bourbaki E I.37).

Chaque test APPELLE le théorème et compare la conclusion à la CIBLE reconstruite
depuis les primitives BRUTES (==), vérifie la clôture (théorème pur, 0 hypothèse)
et theorie == 22.  A, S sont des relations contenant la lettre liée x ; R en est
LIBRE (fraîcheur exigée par C41).
"""
import pytest
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, et, ou, equiv, existe, appartient)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_4_criteres_typiques_c41 import (
    c41_existe_typique, c41_existe_typique_cible,
    c41_pourtout_typique, c41_pourtout_typique_cible)

A = appartient(var("x"), var("E"))     # x∈E  (relation « typique » en x)
R = appartient(var("z"), var("R0"))    # z∈R0 (NE contient PAS x)
S = appartient(var("x"), var("S0"))    # x∈S0


def test_c41_existe_et():
    """⊢ (∃_A x)(R et S) ⇔ (R et (∃_A x)S)  =  (∃x)(A et(R et S)) ⇔ (R et (∃x)(A et S))."""
    t = c41_existe_typique(A, R, S, "x")
    raw = equiv(existe("x", et(A, et(R, S))), et(R, existe("x", et(A, S))))
    assert t.conclusion == raw == c41_existe_typique_cible(A, R, S, "x")
    assert t.est_clos and not t.hypotheses
    assert len(theorie_ensembles().axiomes) == 22


def test_c41_pourtout_ou():
    """⊢ (∀_A x)(R ou S) ⇔ (R ou (∀_A x)S)  =  ¬(∃x)(A et¬(R∨S)) ⇔ (R ∨ ¬(∃x)(A et¬S))."""
    t = c41_pourtout_typique(A, R, S, "x")
    raw = equiv(non(existe("x", et(A, non(ou(R, S))))),
                ou(R, non(existe("x", et(A, non(S))))))
    assert t.conclusion == raw == c41_pourtout_typique_cible(A, R, S, "x")
    assert t.est_clos and not t.hypotheses
    assert len(theorie_ensembles().axiomes) == 22


def test_c41_fraicheur_exigee():
    """C41 refuse une lettre figurant dans R (la fraîcheur est load-bearing)."""
    with pytest.raises(ValueError):
        c41_existe_typique(A, A, S, "x")        # A contient x → refus
    with pytest.raises(ValueError):
        c41_pourtout_typique(A, A, S, "x")
