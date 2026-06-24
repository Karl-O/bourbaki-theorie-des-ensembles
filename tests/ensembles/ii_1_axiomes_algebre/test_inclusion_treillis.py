"""Tests §II.1 — caractérisations de ⊂ par ∩/∪ (A⊂B ⇔ A∩B=A ; A⊂B ⇔ A∪B=B).

Honnêteté LCF : CLOS (0 hyp), conclusion == l'ÉQUIVALENCE fidèle (inclus ⇔ égalité),
les deux membres DIFFÈRENT, theorie = 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, equiv, inclus, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_inclusion_treillis as M

A, B, Ev = var("A"), var("B"), var("E")


def test_inclusion_ssi_intersection_egale():
    t = M.inclusion_ssi_intersection_egale()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == equiv(inclus(A, B), egal(E.intersection(A, B), A))
    assert inclus(A, B) != egal(E.intersection(A, B), A)


def test_inclusion_ssi_reunion_egale():
    t = M.inclusion_ssi_reunion_egale()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == equiv(inclus(A, B), egal(E.reunion(A, B), B))
    assert inclus(A, B) != egal(E.reunion(A, B), B)


def test_antitonie_complement():
    """E.II.6 nº7 : A⊂B ⇔ ∁B⊂∁A, sous hyp HONNÊTES {A⊂E, B⊂E}, conclusion fidèle."""
    t = M.antitonie_complement()
    cible = equiv(inclus(A, B),
                  inclus(E.difference(Ev, B), E.difference(Ev, A)))
    assert t.conclusion == cible
    # hypothèses == exactement {A⊂E, B⊂E} (honnêtes, aucune parasite)
    assert t.hypotheses == frozenset({inclus(A, Ev), inclus(B, Ev)})
    # clos-sous-hyps-honnêtes : la conclusion n'est pas une hypothèse
    assert cible not in t.hypotheses
    assert not t.est_clos


def test_theorie_inchangee_22():
    M.inclusion_ssi_intersection_egale()
    M.inclusion_ssi_reunion_egale()
    M.antitonie_complement()
    assert len(E.theorie_ensembles().axiomes) == 22
