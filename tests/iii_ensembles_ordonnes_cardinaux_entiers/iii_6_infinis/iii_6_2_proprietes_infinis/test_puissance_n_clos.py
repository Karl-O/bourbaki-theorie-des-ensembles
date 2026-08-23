# -*- coding: utf-8 -*-
"""Miroir de iii_6_2_proprietes_infinis/ensembles_puissance_n_clos.py.

Le Corollaire 1 du Théorème 2 (aⁿ = a) ramené à la SEULE hypothèse du livre :
le Théorème 2 lui-même. Les trois hypothèses que portait
`a_puissance_n_egale_a` sont déchargées.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, impl, appartient, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_a_puissance_n_er import (
    enonce_a_puissance_n_egale_a,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_puissance_n_clos import (
    puissance_n_sous_hessenberg, puissance_n_clos,
)


@pytest.mark.slow
def test_puissance_n_sous_hessenberg():
    """Étage intermédiaire : deux hypothèses, et a₀ n'apparaît plus qu'une fois.

    C'est la condition de licéité de l'∃-élimination qui suit : si a₀ était
    libre dans une AUTRE hypothèse, l'élimination serait illicite et le
    théorème final invalide."""
    vA = var("A")
    t = puissance_n_sous_hessenberg()
    reste = set(t.hypotheses) - {appartient(var("a0"), vA)}
    assert not any("a0" in libres_f(h) for h in reste), \
        "a₀ ne doit être libre que dans sa propre hypothèse"
    assert enonce_hessenberg("A") in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_puissance_n_clos():
    """🎯🎯 { enonce_hessenberg(A) } ⊢ est_infini(Card A) ⇒ (∀n≥1) aⁿ = a.

    Le Corollaire 1 sous la SEULE hypothèse du livre. Les trois hypothèses de
    `a_puissance_n_egale_a` — predecesseur_fini_universel, hyp_carre, a₀∈A —
    sont toutes déchargées, la dernière par ∃-élimination.

    Le Théorème 2 reste porté en hypothèse honnête plutôt que dérivé : sa preuve
    coûte 5172,8 s et n'a pas à être repayée ici (RÈGLE PERF)."""
    vA = var("A")
    t = puissance_n_clos()
    assert t.conclusion == impl(est_infini(cardinal(vA)),
                                enonce_a_puissance_n_egale_a("A"))
    assert set(t.hypotheses) == {enonce_hessenberg("A")}, \
        "il ne doit rester QUE le Théorème 2 : %d hypothèses" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
