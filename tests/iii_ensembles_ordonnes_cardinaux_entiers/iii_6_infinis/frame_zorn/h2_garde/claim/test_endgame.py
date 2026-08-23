# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_endgame.py — LE CLAIM de Bourbaki.

Ce que le test verrouille : la dérivation de « Card S₀ = Card E » ne laisse
AUCUNE hypothèse mentionnant un témoin (U, ψ), et ses hypothèses restantes se
répartissent en données du maximal (fournies par `unpack_sous_maximal`) et
résidus honnêtes NOMMÉS (absorption, transport, donnees_extension)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, inclus, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_endgame import (
    donnees_extension, non_strict_clos, claim_clos,
)


def test_non_strict_clos():
    """⊢ ¬(Card S₀ < Card E), tous témoins éliminés, absurde déchargé."""
    vE, vS = var("E"), var("S0")
    absurde = inf_strict_card(cardinal(vS), cardinal(vE))
    t = non_strict_clos()
    assert t.conclusion == non(absurde)
    assert absurde not in t.hypotheses, "raisonnement par l'absurde non clos"
    for h in t.hypotheses:
        assert "Ucadre" not in libres_f(h) and "psi" not in libres_f(h)
    assert donnees_extension() in t.hypotheses, "le garde ∀U doit être porté"


def test_claim_clos():
    """🎯🎯 ⊢ Card S₀ = Card E — LE CLAIM."""
    vE, vS = var("E"), var("S0")
    t = claim_clos()
    assert t.conclusion == egal(cardinal(vS), cardinal(vE))
    assert len(t.hypotheses) == 8, "hyps : %d" % len(t.hypotheses)
    assert inclus(vS, vE) in t.hypotheses, "S₀⊂E doit venir du maximal"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
