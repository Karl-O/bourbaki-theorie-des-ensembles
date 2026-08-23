# -*- coding: utf-8 -*-
"""Miroir du volet FORT de props_restantes/ensembles_prop13_complement.py.

La Proposition 13 renforcée : le témoin du complément est en outre déclaré
CARDINAL. C'est l'étape 1 de la réparation R-12 (division euclidienne).

POURQUOI CE RENFORCEMENT EST NÉCESSAIRE, et pas cosmétique. La version nue
conclut « (∃c) Card a = b + c » ; or `somme_cardinale_binaire(b,c) = Card(b⊔c)`
ne contraint EN RIEN c à être un cardinal — tout ensemble équipotent à un témoin
valable en est un. Donc `est_cardinal(τc.(a = b+c))` n'est PAS dérivable, et la
différence `diff_somme` reste hors de portée de `Fini`. La version forte lève
exactement cet obstacle, pour le prix d'un conjoint : le témoin construit par la
preuve EST littéralement `Card(a ∖ Im)`.

Le premier test est une NON-RÉGRESSION : la version nue doit rester identique.
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    existe_complement_depuis_inf_egal, existe_complement_depuis_inf_egal_cible,
    existe_complement_cardinal_fort,
)


def test_non_regression_version_nue():
    """La version nue survit à l'ajout du paramètre `fort`.   [~6 s]"""
    t = existe_complement_depuis_inf_egal()
    assert t.conclusion == existe_complement_depuis_inf_egal_cible(), \
        "la conclusion de la version nue a changé"
    assert not t.hypotheses, "la version nue doit rester CLOSE"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_version_forte_est_close():
    """🎯 ⊢ (est_cardinal(b) et b ≤ a) ⇒ (∃c)(est_cardinal(c) et Card a = b+c).

    CLOSE, et pour presque rien : le témoin de la preuve est déjà un `Card(·)`,
    il suffisait de le déclarer avant le S5 final.   [~6 s]"""
    t = existe_complement_depuis_inf_egal(fort=True)
    assert not t.hypotheses, "la version forte doit être CLOSE"
    #  le conséquent est EXACTEMENT la formule renforcée
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
        antecedent_consequent,
    )
    _, cons = antecedent_consequent(t.conclusion)
    assert cons == existe_complement_cardinal_fort("Bp13", "Ap13", "Cp13"), \
        "le conséquent n'est pas la formule renforcée"
    assert len(E.theorie_ensembles().axiomes) == 22
