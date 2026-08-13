"""Tests — pièces cardinal-arith de l'extension du maximal (Hessenberg, §III.6.3)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_extension import (
    complement_grand, complement_grand_cible,
    existe_sous_ensemble_cardinal_dans_card,
    existe_sous_ensemble_cardinal_dans_card_cible,
    existe_sous_ensemble_cardinal, existe_sous_ensemble_cardinal_cible,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_complement_grand_clos_et_cible():
    thm = complement_grand()
    assert thm.conclusion == complement_grand_cible()
    # hypothèses honnêtes attendues, non vacuous
    assert thm.conclusion not in thm.hypotheses
    # 3 hyps honnêtes
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal, inclus, var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal, inf_strict_card,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire
    vE, vS = var("E"), var("S0")
    cS, cE = cardinal(vS), cardinal(vE)
    assert inclus(vS, vE) in thm.hypotheses
    assert egal(somme_cardinale_binaire(cS, cS), cS) in thm.hypotheses
    assert inf_strict_card(cS, cE) in thm.hypotheses


def test_existe_sous_ensemble_dans_card_clos():
    thm = existe_sous_ensemble_cardinal_dans_card()
    assert thm.conclusion == existe_sous_ensemble_cardinal_dans_card_cible()
    assert thm.est_clos
    assert thm.conclusion not in thm.hypotheses


def test_existe_sous_ensemble_cardinal_conditionnel():
    thm = existe_sous_ensemble_cardinal()
    assert thm.conclusion == existe_sous_ensemble_cardinal_cible()
    assert thm.conclusion not in thm.hypotheses
    # exactement 1 hyp honnête : le transport
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_extension import _transport_sous_ensemble_hyp
    assert _transport_sous_ensemble_hyp("cE", "AE", "UE", "VE") in thm.hypotheses
