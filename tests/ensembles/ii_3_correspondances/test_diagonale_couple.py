"""Tests §II.3 — caractérisation au COUPLE de la diagonale Δ_X (Bourbaki E II.13, Déf.8).

On APPELLE le théorème, on vérifie : CLÔTURE (0 hypothèse — équivalence pure),
conclusion == cible reconstruite depuis primitives BRUTES (⇔, couple, diagonale,
appartient, =), theorie == 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
import bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple as M


def test_couple_diagonale_cible_litterale():
    t = M.couple_diagonale()
    a, b, X = var("a"), var("b"), var("X")
    # cible : (a,b)∈Δ_X ⇔ (a∈X et a=b)
    cible = equiv(appartient(E.couple(a, b), E.diagonale(X)), et(appartient(a, X), egal(a, b)))
    assert t.conclusion == cible == M.couple_diagonale_cible()
    assert t.est_clos and not t.hypotheses           # équivalence pure (0 hypothèse)
    assert len(theorie_ensembles().axiomes) == 22


def test_couple_diagonale_non_tautologie():
    """Les deux membres de l'équivalence sont distincts (pas une tautologie)."""
    a, b, X = var("a"), var("b"), var("X")
    gauche = appartient(E.couple(a, b), E.diagonale(X))
    droite = et(appartient(a, X), egal(a, b))
    assert gauche != droite
