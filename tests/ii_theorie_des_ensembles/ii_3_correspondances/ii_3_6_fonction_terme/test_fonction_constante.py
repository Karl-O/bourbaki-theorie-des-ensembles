"""Tests Résumé §2 n°3 — FONCTION CONSTANTE  (E.R.6).

Vérifie :
  • la FORME de `fonction_constante` (= fonction_terme(E, a, C) de terme constant) ;
  • le THÉORÈME « graphe fonctionnel » : conclusion == est_fonctionnel(F), CLOS ;
  • le THÉORÈME « valeur = a » : conclusion == (F(u) = a), hypothèse {u∈E} ;
  • theorie_ensembles() reste à 22 axiomes.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, libres_t
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme import ensembles_fonction_constante as FC


def test_fonction_constante_forme():
    """fonction_constante(E,a,C) == fonction_terme(E,a,C)  (x↦a, terme constant)."""
    vE, va, vC = var("E"), var("a"), var("C")
    f = FC.fonction_constante(vE, va, vC)
    assert f == E.fonction_terme(vE, va, vC, "x")
    # le graphe est bien {(x,a)|x∈E}
    assert f == E.couple(E.couple(E.graphe_terme(vE, va, "x"), vE), vC)


def test_fonction_constante_rejette_terme_non_constant():
    """Fidélité : a doit être constant (x non libre dans a)."""
    vE, vC = var("E"), var("C")
    a_var = var("x")              # T = x : DÉPEND de x → pas constant
    assert "x" in libres_t(a_var)
    with pytest.raises(AssertionError):
        FC.fonction_constante(vE, a_var, vC)


def test_graphe_constante_fonctionnel_conclusion_exacte():
    """⊢ F fonctionnel, F = graphe_terme(E,a) ; CLOS, conclusion == est_fonctionnel(F)."""
    vE, va = var("E"), var("a")
    thm = FC.graphe_constante_fonctionnel(vE, va, "x", "y")
    F = E.graphe_terme(vE, va, "x")
    assert thm.est_clos
    assert list(thm.hypotheses) == []
    assert thm.conclusion == E.est_fonctionnel(F)


def test_valeur_constante_conclusion_exacte():
    """{u∈E} ⊢ F(u) = a, F = graphe_terme(E,a) ; conclusion == egal(valeur(F,u), a)."""
    vE, va, vu = var("E"), var("a"), var("u")
    thm = FC.valeur_constante(vE, va, "u", "x", "y")
    F = E.graphe_terme(vE, va, "x")
    cible = egal(E.valeur(F, vu), va)
    assert thm.conclusion == cible
    # hypothèse unique : u∈E (fidèle à « pour tout x de E »)
    assert not thm.est_clos
    hyps = list(thm.hypotheses)
    assert len(hyps) == 1
    assert hyps[0] == E.appartient(vu, vE)


def test_theorie_inchangee_22_axiomes():
    """L'invariant noyau : aucun axiome ajouté à theorie_ensembles()."""
    FC.graphe_constante_fonctionnel(var("E"), var("a"))
    FC.valeur_constante(var("E"), var("a"))
    assert len(E.theorie_ensembles().axiomes) == 22
