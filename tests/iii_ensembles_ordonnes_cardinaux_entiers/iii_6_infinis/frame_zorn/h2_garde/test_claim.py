# -*- coding: utf-8 -*-
"""Test — du CLAIM de Bourbaki à l'énoncé de Hessenberg (endgame)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_claim import (
    claim_vers_endgame,
)


def test_claim_vers_endgame():
    """🎯 {Card S₀=Card E, bij φ₀} ⊢ E infini ⇒ Card E·Card E = Card E."""
    vS0, vphi0, vE = var("Smx"), var("phimx"), var("E")
    bij0 = N.assume(est_bijection_de(vphi0, E.produit(vS0, vS0), vS0))
    claim = N.assume(egal(cardinal(vS0), cardinal(vE)))
    t = claim_vers_endgame("E", "Smx", "phimx", bij0, claim)
    assert t.conclusion == enonce_hessenberg("E")
    assert len(t.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22
