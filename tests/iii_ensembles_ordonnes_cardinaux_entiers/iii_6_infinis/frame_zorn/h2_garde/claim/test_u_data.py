# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_u_data.py — les données élémentaires de U.

Le test décisif n'est pas la forme des conclusions mais leur IDENTITÉ avec
deux des douze hypothèses de STEP 5 : ce sont bien elles qui sont retirées."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, appartient, inclus, pourtout, impl,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_u_data import (
    u_disjoint_S, reunion_inclus_E,
)


def test_u_disjoint_S():
    """{U ⊂ E∖S₀} ⊢ (∀u)(u∈U ⇒ ¬(u∈S₀))."""
    vE, vS, vU = var("E"), var("S0"), var("Ucadre")
    t = u_disjoint_S()
    assert t.conclusion == pourtout("uwit", impl(
        appartient(var("uwit"), vU), non(appartient(var("uwit"), vS))))
    assert list(t.hypotheses) == [inclus(vU, E.difference(vE, vS))]
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reunion_inclus_E():
    """{S₀⊂E, U ⊂ E∖S₀} ⊢ S₀∪U ⊂ E."""
    vE, vS, vU = var("E"), var("S0"), var("Ucadre")
    t = reunion_inclus_E()
    assert t.conclusion == inclus(E.reunion(vS, vU), vE)
    assert len(t.hypotheses) == 2


def test_sont_bien_des_hypotheses_de_step5():
    """🎯 Les deux conclusions SONT des hypothèses de extension_absurde_chainee."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_chaine_vraie import (
        extension_absurde_chainee,
    )
    step5 = extension_absurde_chainee("E", "phi0", "psi", "S0", "Ucadre", "uwit")
    hyps = set(step5.hypotheses)
    assert u_disjoint_S().conclusion in hyps, "U∩S₀=∅ n'est pas l'hyp de STEP 5"
    assert reunion_inclus_E().conclusion in hyps, "S₀∪U⊂E n'est pas l'hyp de STEP 5"
