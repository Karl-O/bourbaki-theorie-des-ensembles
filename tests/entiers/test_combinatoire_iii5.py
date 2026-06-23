"""Tests §III.5 combinatoire (1ère vague) : Prop. 1 binaire (somme/produit entiers)."""
from bourbaki.logique.i_1_termes_relations.formule import egal, impl, et, var
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, est_fini
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22


def test_somme_succ_distribue_close():
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_succ_distribue
    a, b = var("Asd"), var("Bsd")
    cible = impl(et(est_cardinal(a), est_cardinal(b)),
                 egal(somme_cardinale_binaire(a, successeur(b)),
                      successeur(somme_cardinale_binaire(a, b))))
    th = somme_succ_distribue()
    assert th.est_clos
    assert th.conclusion == cible


def test_somme_zero_neutre_droite_close():
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_zero_neutre_droite
    from bourbaki.cardinaux.ensembles_cardinaux import cardinal
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import VIDE
    a = var("Asz")
    cible = impl(est_cardinal(a),
                 egal(somme_cardinale_binaire(a, cardinal(VIDE)), a))
    th = somme_zero_neutre_droite()
    assert th.est_clos
    assert th.conclusion == cible


def test_somme_binaire_entier_close():
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_binaire_entier
    a, b = var("asbe"), var("bsbe")
    cible = impl(et(est_fini(a), est_fini(b)),
                 est_fini(somme_cardinale_binaire(a, b)))
    th = somme_binaire_entier()
    assert th.est_clos
    assert th.conclusion == cible
