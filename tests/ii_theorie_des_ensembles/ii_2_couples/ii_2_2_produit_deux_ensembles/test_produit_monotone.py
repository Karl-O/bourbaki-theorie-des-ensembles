# -*- coding: utf-8 -*-
"""Miroir de ii_2_2/ensembles_produit_monotone.py — le produit croît avec ⊂."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_monotone import (
    produit_monotone_carre,
)


def test_produit_monotone_carre():
    """🎯 { A ⊂ B } ⊢ A×A ⊂ B×B.

    Écrit pour la donnée (9) du recollement de Hessenberg, mais l'énoncé est
    général : sa place est au chapitre du produit, pas dans le §III.6."""
    vA, vB = var("Apm"), var("Bpm")
    t = produit_monotone_carre()
    assert t.conclusion == inclus(E.produit(vA, vA), E.produit(vB, vB), "zpm")
    assert list(t.hypotheses) == [inclus(vA, vB)]
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
