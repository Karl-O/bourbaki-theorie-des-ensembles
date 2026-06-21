"""Tests — pièces cardinal-arith de l'extension du maximal (Hessenberg, §III.6.3)."""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_hessenberg_extension import (
    complement_grand, complement_grand_cible,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_complement_grand_clos_et_cible():
    thm = complement_grand()
    assert thm.conclusion == complement_grand_cible()
    # hypothèses honnêtes attendues, non vacuous
    assert thm.conclusion not in thm.hypotheses
    # 3 hyps honnêtes
    from bourbaki.logique.formule import egal, inclus, var
    from bourbaki.cardinaux.ensembles_cardinaux import (
        cardinal, inf_strict_card,
    )
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_cardinale_binaire
    vE, vS = var("E"), var("S0")
    cS, cE = cardinal(vS), cardinal(vE)
    assert inclus(vS, vE) in thm.hypotheses
    assert egal(somme_cardinale_binaire(cS, cS), cS) in thm.hypotheses
    assert inf_strict_card(cS, cE) in thm.hypotheses
