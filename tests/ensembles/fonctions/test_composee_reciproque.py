"""Test V9 — §II.3.3 Proposition 3 (E.II.42) : (Gp∘G)⁻¹ = G⁻¹ ∘ Gp⁻¹."""
from __future__ import annotations

from bourbaki.logique.formule import var, egal
from bourbaki.ensembles.ensembles_abrege import composee, reciproque
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee_reciproque import reciproque_composee


def test_reciproque_composee():
    vGp, vG = var("Gp"), var("G")
    t = reciproque_composee("Gp", "G")
    cible = egal(reciproque(composee(vGp, vG)),
                 composee(reciproque(vG), reciproque(vGp)))
    assert t.conclusion == cible and t.est_clos
