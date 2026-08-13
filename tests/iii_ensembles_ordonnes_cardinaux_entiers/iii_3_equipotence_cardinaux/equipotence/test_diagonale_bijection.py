# -*- coding: utf-8 -*-
"""Tests E.R.13 item 4 — application diagonale x↦(x,x) (4 lemmes, surjectivité à suivre)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_diagonale_bijection import (
    diagonale_graphe, diag_graphe_fonctionnel, diag_graphe_domaine,
    diag_graphe_valeur, diag_graphe_injective)


def test_fonctionnel_et_domaine_clos():
    assert not diag_graphe_fonctionnel().hypotheses
    d = diag_graphe_domaine()
    assert d.conclusion == egal(E.dom(diagonale_graphe("X")), var("X"))
    assert not d.hypotheses


def test_valeur_hypothese_honnete():
    v = diag_graphe_valeur()
    assert v.conclusion == egal(E.valeur(diagonale_graphe("X"), var("u")),
                                E.couple(var("u"), var("u")))
    assert v.hypotheses == frozenset({appartient(var("u"), var("X"))})


def test_injective_close():
    i = diag_graphe_injective()
    assert i.conclusion == E.injective_dans(diagonale_graphe("X"), var("X"))
    assert not i.hypotheses


def test_surjective_et_bijection_closes():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_diagonale_bijection import (
        diag_graphe_surjective, diag_graphe_bijection)
    s = diag_graphe_surjective()
    assert s.conclusion == E.est_surjective(diagonale_graphe("X"), var("X"),
                                            E.diagonale(var("X")))
    assert not s.hypotheses
    b = diag_graphe_bijection()
    assert b.conclusion == E.est_bijective(diagonale_graphe("X"), var("X"),
                                           E.diagonale(var("X")))
    assert not b.hypotheses
