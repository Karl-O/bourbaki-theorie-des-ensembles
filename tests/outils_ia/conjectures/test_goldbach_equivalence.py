"""L'ÉQUIVALENCE — goldbach() ⇔ forme moitiés, sur TOUT n, sans borne.

Le résultat central de la campagne : la conjecture de Goldbach EST la forme
« moitiés », interdérivables dans le noyau.  Les gardes bon marché (sans `slow`)
protègent les PRÉLÈVEMENTS — c'est par eux que la fidélité tient ; le théorème
lui-même coûte ~6 min et porte le marqueur `slow`.

    pytest tests/outils_ia/conjectures/test_goldbach_equivalence.py -m slow
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, et, impl, pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from outils_ia.arithmetique.machine_num import NUM, fic_t
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures import goldbach_borne as GBB
from outils_ia.conjectures.goldbach_equivalence import (
    card_egal_soi, equivalence_moities, reciproque_moities,
)
from outils_ia.conjectures.goldbach_reduction import (
    hypothese_moities, preleve_goldbach, reduction_moities,
)

mp = N.modus_ponens


def test_les_prelevements_recomposent_les_enonces():
    """🔴 LES GARDES QUI PORTENT TOUT — découpe puis recomposition, à l'identique.

    goldbach() est découpé en (ANTE, DEC) ; H est l'antécédent de goldbach_borne
    PRIVÉ de son conjoint de borne.  Si l'une des recompositions tombe, tout ce
    que les théorèmes « disent » devient suspect — c'est le test à regarder en
    premier."""
    ANTE, DEC = preleve_goldbach()
    assert pourtout("ngb", impl(ANTE, DEC)) == GB.goldbach()

    vk = var("kgb")
    H = hypothese_moities()
    sans_borne = GBB.antecedent(vk, 2).sous[0].sous[0].sous[0]
    assert et(sans_borne, inf_egal_card(vk, NUM(2))) == GBB.antecedent(vk, 2)
    assert H == pourtout("kgb", impl(sans_borne,
                                     GBB.decomposition(somme_cardinale_binaire(vk, vk))))


def test_la_charniere_card_k_egal_k():
    """⊢ Card k = k sous est_cardinal k — ce qui transforme Card k ≤ k+k en k ≤ k+k.

    Sans elle, la réciproque ne peut pas majorer k ; on la teste isolément parce
    qu'elle servira ailleurs (toute preuve qui passe d'un ensemble à son cardinal)."""
    vk = var("kZZ")
    h_fini = N.assume(est_fini(vk))
    th = card_egal_soi(vk, mp(h_fini, fic_t(vk)))
    assert th.conclusion == egal(cardinal(vk), vk)
    assert th.hypotheses == frozenset({est_fini(vk)})


@pytest.mark.slow
def test_l_equivalence_est_close():
    """👑 ⊢ ( H ⇒ goldbach() ) et ( goldbach() ⇒ H )  —  CLOS, 0 hypothèse.

    Mesuré : ~320 s (réciproque 217 s + aller 45 s + machinerie).  La conclusion
    est comparée à la formule assemblée depuis les prélèvements — pas recopiée."""
    eq = equivalence_moities()
    H = hypothese_moities()
    assert eq.est_clos and not eq.hypotheses
    assert eq.conclusion == et(impl(H, GB.goldbach()), impl(GB.goldbach(), H))
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_chaque_direction_seule_est_close():
    """Les deux directions valent aussi séparément (consommables telles quelles)."""
    H = hypothese_moities()
    fwd = reduction_moities()
    assert fwd.est_clos and fwd.conclusion == impl(H, GB.goldbach())
    rec = reciproque_moities()
    assert rec.est_clos and rec.conclusion == impl(GB.goldbach(), H)
