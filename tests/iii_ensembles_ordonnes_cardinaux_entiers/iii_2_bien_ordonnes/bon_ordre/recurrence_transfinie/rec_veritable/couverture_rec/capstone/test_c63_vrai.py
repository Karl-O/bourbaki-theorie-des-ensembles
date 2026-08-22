# -*- coding: utf-8 -*-
"""Tests R8'-final — 🎯🎯🎯 LE C63 VÉRITABLE (l'itération du livre)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_N import (
    regle_iteration_vraie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_c63_vrai import (
    corps_c63, iteration_complete,
)


def _S(t):
    """Le pas jouet (opaque) : S = s(·)."""
    return E.valeur(var("sitv"), t)


def test_iteration_complete():
    """🎯🎯🎯 {règle bornée} ⊢ (∃g)( g(0)=a ∧ (∀n∈ℕ)(g(succ n)=S(g(n))) )."""
    t = iteration_complete(_S, ZERO)
    T = regle_iteration_vraie(_S, ZERO)
    assert t.conclusion == existe("gcap", corps_c63(_S, ZERO))
    assert list(t.hypotheses) == [regle_dans_V(T, "Vitv")]
    assert t.conclusion not in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
