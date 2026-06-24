"""Test V9 — §II.3.2 INVOLUTION de la réciproque : (G⁻¹)⁻¹ = G  (E II.11, Déf. 5).

  { est_graphe(G) } ⊢ reciproque(reciproque(G)) = G.

Vérifie (en APPELANT le théorème) : la conclusion reconstruite indépendamment,
la clôture conditionnelle HONNÊTE (une seule hypothèse = est_graphe(G), conclusion
∉ hypothèses), et l'invariant theorie_ensembles() == 22.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_3_correspondances.ensembles_graphe_inclus_produit import est_graphe
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque_involution import (
    reciproque_involution, reciproque_involution_cible)


def test_reciproque_involution_conclusion():
    vG = var("G")
    t = reciproque_involution("G")
    # conclusion reconstruite : (G⁻¹)⁻¹ = G = egal(reciproque(reciproque(G)), G)
    cible = egal(E.reciproque(E.reciproque(vG)), vG)
    assert t.conclusion == cible
    assert t.conclusion == reciproque_involution_cible("G")


def test_reciproque_involution_hypothese_honnete():
    vG = var("G")
    t = reciproque_involution("G")
    # clôture CONDITIONNELLE honnête : exactement une hypothèse = est_graphe(G).
    assert t.hypotheses == frozenset({est_graphe(vG)})
    assert not t.est_clos
    # honnêteté : la conclusion n'est PAS une hypothèse.
    assert t.conclusion not in t.hypotheses


def test_theorie_invariant_22():
    assert len(E.theorie_ensembles().axiomes) == 22
