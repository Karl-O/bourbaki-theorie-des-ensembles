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


def test_un_seul_residu_honnete():
    """🎯 Le CLAIM ne laisse plus qu'UN résidu : le garde ∀U (le paquet ψ).

    Les deux autres sont tombés le 2026-08-23 — l'absorption 𝔟+𝔟=𝔟 est DÉRIVÉE
    de la bijection φ₀ (LEÇON 16), le transport était déjà CLOS en amont
    (GAP B).  Et ce résidu unique EST exactement `donnees_extension`."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_endgame import (
        donnees_extension,
    )
    residus = _residus("E")
    assert len(residus) == 1
    assert residus[0] == donnees_extension("E", "Smx", "phimx")


def test_hessenberg_par_extension():
    """🏆🏆 { existence_maximal, residus_maximal } ⊢ E infini ⇒ Card E·Card E = Card E."""
    t = hessenberg_par_extension("E")
    assert t.conclusion == enonce_hessenberg("E")
    assert set(t.hypotheses) == {existence_maximal("E"), residus_maximal("E")}, \
        "hypothèses inattendues : l'assemblage a fui"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
