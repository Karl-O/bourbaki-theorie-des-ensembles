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
    claim_vers_endgame, claim_depuis_non_strict,
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


def test_claim_depuis_non_strict():
    """🎯 {S₀⊂E, ¬(Card S₀<Card E)} ⊢ Card S₀ = Card E  (étapes 7+8)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        non, inclus,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_strict_card,
    )
    vS0, vE = var("Smx"), var("E")
    S_inc = N.assume(inclus(vS0, vE))
    non_strict = N.assume(non(inf_strict_card(cardinal(vS0), cardinal(vE))))
    t = claim_depuis_non_strict("E", "Smx", S_inc, non_strict)
    assert t.conclusion == egal(cardinal(vS0), cardinal(vE))
    assert set(t.hypotheses) == {S_inc.conclusion, non_strict.conclusion}
    assert len(E.theorie_ensembles().axiomes) == 22


def test_claim_chaine_complete():
    """🎯🎯 Bout à bout : {S₀⊂E, ¬(<), bij φ₀} ⊢ enonce_hessenberg(E)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        non, inclus,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_strict_card,
    )
    vS0, vphi0, vE = var("Smx"), var("phimx"), var("E")
    S_inc = N.assume(inclus(vS0, vE))
    non_strict = N.assume(non(inf_strict_card(cardinal(vS0), cardinal(vE))))
    bij0 = N.assume(est_bijection_de(vphi0, E.produit(vS0, vS0), vS0))
    claim = claim_depuis_non_strict("E", "Smx", S_inc, non_strict)
    t = claim_vers_endgame("E", "Smx", "phimx", bij0, claim)
    assert t.conclusion == enonce_hessenberg("E")
    assert len(t.hypotheses) == 3
