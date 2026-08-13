"""Tests de ensembles_intervalles_prop13.py — PROPOSITION 13 (E.III.1.13).

Vérifie : conclusion EXACTE == cible (construite indépendamment), clôture
(est_clos, 0 hypothèse), et invariant theorie_ensembles == 22 (l'axiome de
membership de [·,·] vit dans une théorie DÉDIÉE, jamais dans theorie_ensembles).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, equiv, appartient, pourtout, alpha_egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import (
    ensembles_ordre_treillis_props as P,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import (
    ensembles_intervalles_prop13 as I13,
)


G = var("G")
Es = var("E")
a, b, c, d, x = var("a"), var("b"), var("c"), var("d"), var("x")


def _couple_dans(t, u, Gr):
    return appartient(E.couple(t, u), Gr)


def _cible():
    """Cible CONSTRUITE INDÉPENDAMMENT (anti-tautologie), assoc. à gauche."""
    Iab = E.intervalle_ferme(P._rg(G), Es, a, b)
    Icd = E.intervalle_ferme(P._rg(G), Es, c, d)
    inter = E.intersection(Iab, Icd)
    rhs = et(et(et(et(appartient(x, Es), _couple_dans(a, x, G)),
                    _couple_dans(c, x, G)),
                 _couple_dans(x, b, G)),
             _couple_dans(x, d, G))
    return pourtout("x", equiv(appartient(x, inter), rhs))


def test_conclusion_egale_cible():
    t = I13.intersection_intervalles_fermes(G)
    cible = _cible()
    # conclusion EXACTE == cible (et == fonction-cible exportée)
    assert t.conclusion == cible
    assert t.conclusion == I13.cible_intersection_intervalles(G)
    assert alpha_egal(t.conclusion, cible)


def test_theoreme_clos():
    t = I13.intersection_intervalles_fermes(G)
    # THÉORÈME CLOS : aucune hypothèse libre (axiome déchargé via N.axiome).
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_theorie_ensembles_intangible_22():
    # l'axiome de membership de [·,·] vit dans une théorie DÉDIÉE.
    assert len(E.theorie_ensembles().axiomes) == 22
    # construire le théorème ne modifie pas theorie_ensembles.
    I13.intersection_intervalles_fermes(G)
    assert len(E.theorie_ensembles().axiomes) == 22
