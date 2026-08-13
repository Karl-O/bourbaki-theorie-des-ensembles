"""La 2ᵉ fournée de lemmes machine — PROFONDEUR 2, redérivés, protégés.

Leur particularité (CY3 en streaming, 8 août 2026) : le COMPOUNDING — ils sont
nés en chaînant les lemmes machine de la 1ʳᵉ fournée (fini_somme_cardinal_successeur
a un lemme machine comme PREMIER maillon). Conclusions vérifiées contre des
formules bâties ICI, indépendamment des compagnes du module.
Marqués `slow` : machinerie C61 (~200 s en process frais).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, et, impl, var,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur,
)
from outils_ia.arithmetique.lemmes_conjectures_2 import (
    fini_somme_cardinal_successeur, prop2_sous_somme_finie, succ_fini_cardinal,
)


@pytest.mark.slow
def test_les_trois_lemmes_de_profondeur_2_sont_clos():
    """⊢ les trois, clos, conclusions vérifiées contre des formules bâties ICI."""
    va, vb, vp, vc = var("a"), var("b"), var("p"), var("c")
    ab = SC(va, vb)

    th1 = succ_fini_cardinal()
    assert th1.est_clos and th1.conclusion == impl(
        est_fini(va), est_cardinal(successeur(va)))

    th2 = fini_somme_cardinal_successeur()
    assert th2.est_clos and th2.conclusion == impl(
        et(est_fini(va), est_fini(vb)), est_cardinal(successeur(ab)))

    th3 = prop2_sous_somme_finie()
    assert th3.est_clos and th3.conclusion == impl(
        et(est_fini(va), est_fini(vb)),
        impl(egal(vp, SC(ab, vc)), inf_egal_card(ab, vp)))

    assert len(E.theorie_ensembles().axiomes) == 22
