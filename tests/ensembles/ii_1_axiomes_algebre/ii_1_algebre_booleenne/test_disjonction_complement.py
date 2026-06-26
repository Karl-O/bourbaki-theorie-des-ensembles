"""Tests §II.1 — DISJONCTION caractérisée par le COMPLÉMENT (E.R.4 nº14 e).

    ( X ∩ Y = ∅ )  ⇔  ( X ⊂ ∁_E Y )      sous l'hypothèse honnête X ⊂ E.

Honnêteté LCF : le théorème est APPELÉ (un import ne prouve rien) ; conclusion ==
cible (== structurelle, l'équivalence Bourbaki) ; hypotheses == {inclus(X,E)}
EXACTEMENT (X⊂E honnêtement non déchargée — le contexte « X partie de E » du
nº14, requis par le sens ⇒) ; est_clos == False ; PAS de tautologie déguisée
(conclusion ≠ chacun de ses membres, ≠ l'hypothèse) ; theorie_ensembles() = 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ii_1_algebre_booleenne.ensembles_disjonction_complement as D

X, Y, EE = var("X"), var("Y"), var("E")


def _cible():
    return D.cible_disjonction_complement()


def test_conclusion_est_la_cible():
    t = D.disjonction_complement()
    assert t.conclusion == _cible()


def test_hypothese_honnete_exacte_X_inclus_E():
    t = D.disjonction_complement()
    # une seule hypothèse non déchargée, exactement X⊂E (le contexte « X partie de E »),
    # requise par le sens ⇒ (z∈X ⟹ z∈E pour donner sens à z∈E∖Y).
    assert t.hypotheses == frozenset({inclus(X, EE)})
    assert not t.est_clos


def test_pas_de_tautologie_deguisee():
    t = D.disjonction_complement()
    membre_g = egal(E.intersection(X, Y), E.VIDE)            # X∩Y = ∅
    membre_d = inclus(X, E.difference(EE, Y))               # X ⊂ E∖Y
    # le contenu est une caractérisation réelle : les deux membres diffèrent de
    # la conclusion et l'un de l'autre ; la conclusion n'est pas l'hypothèse.
    assert t.conclusion != membre_g
    assert t.conclusion != membre_d
    assert membre_g != membre_d
    assert _cible() != inclus(X, EE)
    assert _cible() not in t.hypotheses


def test_theorie_inchangee_22():
    D.disjonction_complement()
    assert len(E.theorie_ensembles().axiomes) == 22
