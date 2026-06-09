"""Tests — gr(f)=pr₁(pr₁ f), extraction du graphe d'une application-triple (§II.3.1)."""
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de, graphe_de_triple
from bourbaki.logique.formule import var, egal
import bourbaki.ensembles.ensembles_abrege as E


def test_graphe_de_terme():
    f = var("f")
    t = graphe_de(f)
    assert t == E.pr1(E.pr1(f, "a", "b"), "a", "b")   # gr(f)=pr₁(pr₁ f) (liants a,b)


def test_graphe_de_triple_clos():
    th = graphe_de_triple("G", "E", "F")
    assert th.est_clos               # extraction INCONDITIONNELLE
    vG, vE, vF = var("G"), var("E"), var("F")
    triple = E.couple(E.couple(vG, vE), vF)
    # conclusion = gr(((G,E),F)) = G
    assert th.conclusion == egal(graphe_de(triple), vG)


def test_graphe_de_triple_termes():
    A, B, C = var("A"), var("B"), var("C")
    th = graphe_de_triple(A, B, C)
    triple = E.couple(E.couple(A, B), C)
    assert th.est_clos and th.conclusion == egal(graphe_de(triple), A)
