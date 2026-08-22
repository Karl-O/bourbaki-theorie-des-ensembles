# -*- coding: utf-8 -*-
"""Tests R7' étape 5 — 🎯🎯🎯 LE CRITÈRE C60 VÉRITABLE (existence)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_critere_c60_vrai import (
    existence_solution,
)

_G, _E = var("Gsr"), var("Esr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_existence_solution():
    """🎯🎯🎯 C60-VRAI : {bo, règle bornée} ⊢ (∃g)( sol(g) )."""
    t = existence_solution(_vh)
    attendu = existe("gcap", est_solution_rec(var("gcap"), _vh, _G, _E))
    assert t.conclusion == attendu
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert regle_dans_V(_vh) in hyps
    assert t.conclusion not in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
