"""Tests §II.1 — RECOUVREMENT caractérisé par le COMPLÉMENT (E.R.4 nº14 f).

    ( X ∪ Y = E )  ⇔  ( ∁_E X ⊂ Y )      sous les hypothèses honnêtes X⊂E et Y⊂E.

Dual de nº14 e).  Honnêteté LCF : le théorème est APPELÉ (un import ne prouve
rien) ; conclusion == cible (== structurelle, l'équivalence Bourbaki) ;
hypotheses == {inclus(X,E), inclus(Y,E)} EXACTEMENT (les deux « parties de E » du
nº14, requises par le demi-sens X∪Y⊂E du ⇐) ; est_clos == False ; PAS de
tautologie déguisée (conclusion ≠ chacun de ses membres, ≠ une hypothèse) ;
theorie_ensembles() = 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ii_1_algebre_booleenne.ensembles_recouvrement_complement as R

X, Y, EE = var("X"), var("Y"), var("E")


def _cible():
    return R.cible_recouvrement_complement()


def test_conclusion_est_la_cible():
    t = R.recouvrement_complement()
    assert t.conclusion == _cible()


def test_hypotheses_honnetes_exactes_X_et_Y_inclus_E():
    t = R.recouvrement_complement()
    # exactement deux hypothèses non déchargées : X⊂E et Y⊂E (le contexte « X, Y
    # parties de E » du nº14), requises par le demi-sens X∪Y⊂E du ⇐.
    assert t.hypotheses == frozenset({inclus(X, EE), inclus(Y, EE)})
    assert not t.est_clos


def test_pas_de_tautologie_deguisee():
    t = R.recouvrement_complement()
    membre_g = egal(E.reunion(X, Y), EE)                    # X∪Y = E
    membre_d = inclus(E.difference(EE, X), Y)               # ∁_E X ⊂ Y
    # caractérisation réelle : les deux membres diffèrent de la conclusion et l'un
    # de l'autre ; la conclusion n'est aucune des hypothèses.
    assert t.conclusion != membre_g
    assert t.conclusion != membre_d
    assert membre_g != membre_d
    assert _cible() != inclus(X, EE)
    assert _cible() != inclus(Y, EE)
    assert _cible() not in t.hypotheses


def test_theorie_inchangee_22():
    R.recouvrement_complement()
    assert len(E.theorie_ensembles().axiomes) == 22
