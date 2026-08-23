# -*- coding: utf-8 -*-
"""Miroir de frame_zorn/ensembles_fini_downward_garde.py.

🎯 CE QUE CE TEST GARDE : la downward-closure de Fini doit être obtenue SANS
l'hypothèse non satisfaite (la ∀∀-clôture NUE de `cardinal_pas_entre`), dont
ANOMALIES 2026-08-23 établit qu'elle rend vides les théorèmes qui la portent.
Si une régression la réintroduisait, l'assertion explicite ci-dessous tombe."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, impl, pourtout, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    cardinal_pas_entre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_fini_downward_garde import (
    fini_downward_cardinal,
)


def test_fini_downward_cardinal():
    """⊢ (Card S₀ ≤ Card Z et Fini(Card Z)) ⇒ Fini(Card S₀).   CLOS."""
    vS = var("S0")
    cZ = cardinal(E.reunion(vS, var("Ucadre")))
    t = fini_downward_cardinal("S0", cZ)
    cS = cardinal(vS)
    assert t.conclusion == impl(et(inf_egal_card(cS, cZ), est_fini(cZ)), est_fini(cS))
    #  2026-08-23 : CLOS. `predecesseur_fini_universel` n'était pas un résidu —
    #  le dépôt le PROUVE (Prop. 2 §III.5), il n'était simplement pas branché.
    assert not t.hypotheses, "doit être CLOS : %d hyps" % len(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hypothese_nue_absente():
    """🎯 L'hypothèse NON SATISFAITE ne doit PAS reparaître (ANOMALIES 2026-08-23).

    La ∀∀-clôture nue de `cardinal_pas_entre` perd la garde `est_cardinal(b)`
    que le dépôt exige pour la prouver ; elle est fausse dès que b n'est pas un
    cardinal, et rend vide tout théorème qui la porte."""
    vS = var("S0")
    cZ = cardinal(E.reunion(vS, var("Ucadre")))
    t = fini_downward_cardinal("S0", cZ)
    nue = pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c"))))
    assert nue not in t.hypotheses, "l'hypothèse nue non satisfaite est revenue"
