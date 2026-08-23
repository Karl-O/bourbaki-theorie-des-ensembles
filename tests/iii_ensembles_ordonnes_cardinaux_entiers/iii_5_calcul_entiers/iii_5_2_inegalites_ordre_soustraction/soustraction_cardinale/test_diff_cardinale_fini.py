# -*- coding: utf-8 -*-
"""Miroir de soustraction_cardinale/ensembles_diff_cardinale_fini.py.

Étape 3 de R-12 : `Fini(a − b)` SANS l'universel nu de `fini_downward`.

CE QUE LE SECOND TEST GARANTIT. `_diff_est_fini` (§III.5.6) obtient la même
conclusion en instanciant une hypothèse NON SATISFAITE — ses dépendants sont
donc vrais et VIDES. Ici la version GARDÉE suffit, et le test vérifie
explicitement que l'universel nu est ABSENT des hypothèses : sans cette
vérification, rien ne distinguerait les deux preuves à l'œil.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, pourtout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    cardinal_pas_entre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.soustraction_cardinale.ensembles_diff_cardinale import (
    diff_cardinale,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.soustraction_cardinale.ensembles_diff_cardinale_fini import (
    diff_cardinale_inf_egal, diff_cardinale_fini,
)

_GARDES = {est_cardinal(var("adf")), est_cardinal(var("bdf")),
           inf_egal_card(var("bdf"), var("adf"))}


def test_diff_cardinale_inf_egal():
    """{ card a, card b, b ≤ a } ⊢ ( a − b ) ≤ a.

    Directement depuis l'équation caractéristique, sans l'invariance de ≤ par
    équipotence dont la version `diff_somme` avait besoin."""
    t = diff_cardinale_inf_egal("adf", "bdf")
    assert t.conclusion == inf_egal_card(diff_cardinale(var("adf"), var("bdf")),
                                         var("adf"))
    assert set(t.hypotheses) == _GARDES
    assert len(E.theorie_ensembles().axiomes) == 22


def test_diff_cardinale_fini_sans_hypothese_fausse():
    """🎯🎯 { card a, card b, b ≤ a, Fini a } ⊢ Fini( a − b ).

    Le remplaçant sûr de `_diff_est_fini`. Quatre gardes, toutes VRAIES et
    toutes présentes chez Bourbaki — aucune trace de la ∀∀-clôture NUE de
    `cardinal_pas_entre`, dont ANOMALIES 2026-08-23 établit qu'elle n'est pas
    satisfaite. C'est cette absence qui distingue ce théorème du précédent :
    l'énoncé est le même, la valeur ne l'est pas."""
    t = diff_cardinale_fini("adf", "bdf")
    assert t.conclusion == est_fini(diff_cardinale(var("adf"), var("bdf")))
    assert set(t.hypotheses) == _GARDES | {est_fini(var("adf"))}, \
        "gardes résiduelles inattendues : %d" % len(t.hypotheses)

    nue = pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c"))))
    assert nue not in t.hypotheses, \
        "l'hypothèse NON SATISFAITE est revenue — le théorème serait vide"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
