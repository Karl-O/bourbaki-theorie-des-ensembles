# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_hessenberg_final.py — 🏆 Hessenberg a·a = a.

Ce que le test verrouille : l'énoncé de Bourbaki (Th. 2, E III.47) est obtenu
sous DEUX hypothèses seulement, toutes deux explicites — l'existence du
maximal (que `hess_maximal` prouve, certifié) et les trois résidus honnêtes
quantifiés sur le maximal."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_unpack_garde import (
    existence_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_hessenberg_final import (
    residus_maximal, hessenberg_par_extension, _residus,
)


def test_deux_residus_honnetes():
    """Le CLAIM ne laisse plus que DEUX résidus : transport et garde ∀U.

    L'absorption 𝔟+𝔟=𝔟 en est sortie le 2026-08-23 : `absorption_au_maximal`
    la DÉRIVE de la bijection φ₀ du maximal (LEÇON 16)."""
    assert len(_residus("E")) == 2


def test_hessenberg_par_extension():
    """🏆🏆 { existence_maximal, residus_maximal } ⊢ E infini ⇒ Card E·Card E = Card E."""
    t = hessenberg_par_extension("E")
    assert t.conclusion == enonce_hessenberg("E")
    assert set(t.hypotheses) == {existence_maximal("E"), residus_maximal("E")}, \
        "hypothèses inattendues : l'assemblage a fui"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
