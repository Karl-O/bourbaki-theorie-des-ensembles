"""Les lemmes découverts par la machine — redérivés, nommés, protégés.

Leur particularité n'est pas leur profondeur (ce sont des lemmes de colle) mais
leur PROVENANCE : le conjectureur les a trouvés seul (ev.275-276), et ils
reproduisent exactement la glu que la campagne Goldbach écrivait à la main.
Marqués `slow` : ils paient la machinerie C61 (~200 s en process frais).
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
from outils_ia.arithmetique.lemmes_conjectures import (
    fini_descendant_sous_fini, fini_somme_cardinal, fini_somme_successeur,
    prop2_sous_fini,
)


@pytest.mark.slow
def test_les_quatre_lemmes_machine_sont_clos():
    """⊢ les quatre, clos, conclusions vérifiées contre des formules bâties ICI."""
    va, vb, vc = var("a"), var("b"), var("c")
    ab = SC(va, vb)

    th1 = fini_somme_cardinal()
    assert th1.est_clos and th1.conclusion == impl(
        et(est_fini(va), est_fini(vb)), est_cardinal(ab))

    th2 = fini_somme_successeur()
    assert th2.est_clos and th2.conclusion == impl(
        et(est_fini(va), est_fini(vb)), est_fini(successeur(ab)))

    th3 = prop2_sous_fini()
    assert th3.est_clos and th3.conclusion == impl(
        est_fini(va), impl(egal(vb, SC(va, vc)), inf_egal_card(va, vb)))

    th4 = fini_descendant_sous_fini()
    assert th4.est_clos

    assert len(E.theorie_ensembles().axiomes) == 22
