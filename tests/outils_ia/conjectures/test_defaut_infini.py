"""Le second défaut de `goldbach()` — démontré, et non plus argumenté.

⚠️ MARQUÉ `slow` : ℵ₀ demande ~235 s à construire (le ℕ concret).  C'est le prix
d'une démonstration plutôt que d'un raisonnement de marge ; il est payé une fois.

    pytest tests/outils_ia/conjectures/test_defaut_infini.py -m slow
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, subst_f,
)
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures.defaut_infini import (
    ancien_antecedent, antecedent_satisfait_par_un_infini, temoin_pair_infini,
)


def test_l_ancien_antecedent_n_est_plus_celui_de_l_enonce():
    """Garde bon marché : la formule fautive ne doit pas être revenue.

    Elle est conservée dans `defaut_infini.ancien_antecedent` — et NULLE PART
    ailleurs.  Si `goldbach()` la reprenait un jour, ce test tomberait sans
    qu'on ait à payer les 235 s de ℵ₀."""
    vn = var("ngb")
    assert GB.goldbach().sous[0] != ancien_antecedent(vn), (
        "l'antécédent fautif (sans est_fini) est revenu dans goldbach()")


@pytest.mark.slow
def test_un_cardinal_infini_satisfait_l_ancien_antecedent():
    """🔴 LA DÉMONSTRATION — ce qui n'était qu'un argument le devient.

    Pour n := ℕ+ℕ, l'antécédent d'avant la réparation est SATISFAIT, clos et sans
    hypothèse.  Comme n est infini, il n'est somme d'aucun couple de premiers :
    l'énoncé affirmait donc que ℕ+ℕ est somme de deux nombres premiers.

    L'assertion qui porte tout est la dernière : la conclusion doit être ÉGALE à
    `ancien_antecedent` instancié en n.  Sans elle on démontrerait une formule
    voisine — et l'on n'aurait rien montré."""
    th = antecedent_satisfait_par_un_infini()
    assert th.est_clos and not th.hypotheses
    n = temoin_pair_infini()
    assert th.conclusion == subst_f(n, "ngb", ancien_antecedent(var("ngb")))
    assert len(E.theorie_ensembles().axiomes) == 22
