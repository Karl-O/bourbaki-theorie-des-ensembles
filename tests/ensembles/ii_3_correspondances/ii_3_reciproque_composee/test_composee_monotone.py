"""Test V9 — §II.3.3 monotonie de la composée (E II.13, Rem.) :
   { G₁⊂G₂, G₁'⊂G₂' } ⊢ G₁'∘G₁ ⊂ G₂'∘G₂.

Le test APPELLE le théorème et vérifie conclusion == cible, les deux hypothèses
exactement, et est_clos == False. Un import ne prouve rien : c'est l'objet Theoreme
certifié par le noyau qui est inspecté."""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import composee
from bourbaki.ensembles.ii_3_correspondances.ii_3_reciproque_composee.ensembles_composee_monotone import (
    composee_monotone)


def test_composee_monotone():
    vG1, vG2, vG1p, vG2p = var("G1"), var("G2"), var("G1p"), var("G2p")
    t = composee_monotone("G1", "G2", "G1p", "G2p")

    # (a) conclusion == cible (== structurelle).
    cible = inclus(composee(vG1p, vG1), composee(vG2p, vG2))
    assert t.conclusion == cible

    # (b) hypothèses EXACTEMENT les deux inclusions ; rien de parasite.
    h1 = inclus(vG1, vG2)
    h2 = inclus(vG1p, vG2p)
    assert t.hypotheses == frozenset({h1, h2})
    assert len(t.hypotheses) == 2

    # (c) théorème ouvert ; conclusion hors des hypothèses (pas de tautologie déguisée).
    assert not t.est_clos
    assert t.conclusion not in t.hypotheses
