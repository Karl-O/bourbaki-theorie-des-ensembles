"""Test V9 — §II.3.1 : tout ensemble de couples est partie d'un produit (E II.10).

  { est_graphe(G) } ⊢ G ⊂ (pr₁G) × (pr₂G).

Vérifie (en APPELANT le théorème) : la conclusion reconstruite indépendamment,
la clôture conditionnelle HONNÊTE (une seule hypothèse = est_graphe(G), conclusion
∉ hypothèses), et l'invariant theorie_ensembles() == 22.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_3_correspondances.ensembles_graphe_inclus_produit import (
    est_graphe, graphe_inclus_produit, graphe_inclus_produit_cible)


def test_graphe_inclus_produit_conclusion():
    vG = var("G")
    t = graphe_inclus_produit("G")
    # conclusion reconstruite : G ⊂ (pr₁G) × (pr₂G) = inclus(G, produit(dom G, img G))
    cible = inclus(vG, E.produit(E.dom(vG), E.img(vG)))
    assert t.conclusion == cible
    assert t.conclusion == graphe_inclus_produit_cible("G")


def test_graphe_inclus_produit_hypothese_honnete():
    vG = var("G")
    t = graphe_inclus_produit("G")
    # clôture CONDITIONNELLE honnête : exactement une hypothèse = est_graphe(G).
    assert t.hypotheses == frozenset({est_graphe(vG)})
    assert not t.est_clos
    # honnêteté : la conclusion n'est PAS une hypothèse.
    assert t.conclusion not in t.hypotheses


def test_theorie_invariant_22():
    assert len(E.theorie_ensembles().axiomes) == 22
