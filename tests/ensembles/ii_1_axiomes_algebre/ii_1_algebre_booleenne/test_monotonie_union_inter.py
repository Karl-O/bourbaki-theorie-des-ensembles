"""Tests §II.1 — MONOTONIE de ∪ / ∩ binaires (E.R.5 nº14 h).

    X ⊂ Y  entraîne  X∪Z ⊂ Y∪Z  et  X∩Z ⊂ Y∩Z.

Honnêteté LCF : le théorème APPELÉ (un import ne prouve rien) ; conclusion ==
conjonction des deux inclusions-cibles (== structurelle) ; hypotheses ==
{inclus(X,Y)} EXACTEMENT (X⊂Y honnêtement non déchargée) ; est_clos == False ;
la conclusion n'est PAS une hypothèse (pas de tautologie déguisée) ; theorie = 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, et, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ii_1_algebre_booleenne.ensembles_monotonie_union_inter as M

X, Y, Z = var("X"), var("Y"), var("Z")


def _cible():
    return et(inclus(E.reunion(X, Z), E.reunion(Y, Z)),
              inclus(E.intersection(X, Z), E.intersection(Y, Z)))


def test_monotonie_conclusion_est_la_cible():
    t = M.monotonie_union_inter()
    assert t.conclusion == _cible()


def test_monotonie_hypothese_honnete_exacte():
    t = M.monotonie_union_inter()
    # une seule hypothèse non déchargée, exactement X⊂Y
    assert t.hypotheses == frozenset({inclus(X, Y)})
    assert not t.est_clos


def test_monotonie_pas_de_tautologie_deguisee():
    t = M.monotonie_union_inter()
    # la conclusion n'est pas (re)posée comme hypothèse
    assert _cible() not in t.hypotheses
    # la conclusion diffère réellement de l'unique hypothèse X⊂Y
    assert _cible() != inclus(X, Y)


def test_theorie_inchangee_22():
    M.monotonie_union_inter()
    assert len(E.theorie_ensembles().axiomes) == 22
