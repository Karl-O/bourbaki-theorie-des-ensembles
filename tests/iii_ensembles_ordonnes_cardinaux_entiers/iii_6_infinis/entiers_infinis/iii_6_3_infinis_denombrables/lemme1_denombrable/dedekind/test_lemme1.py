# -*- coding: utf-8 -*-
"""Test D1d — 🏆 LE LEMME 1 : tout ensemble infini contient un dénombrable."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, existe, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_lemme1 import (
    lemme_1,
)

_E = var("Eld")


def test_lemme_1():
    """🏆 {est_infini(Card E)} ⊢ (∃D)( D⊂E ∧ Eq(D,ℕ) ) — le Lemme 1 du livre."""
    t = lemme_1("Eld")
    vD = var("Dld")
    attendu = existe("Dld", et(inclus(vD, _E), equipotent(vD, ensemble_NN())))
    assert t.conclusion == attendu
    assert list(t.hypotheses) == [est_infini(cardinal(_E))]
    assert len(E.theorie_ensembles().axiomes) == 22
