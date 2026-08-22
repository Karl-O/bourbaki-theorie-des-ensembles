# -*- coding: utf-8 -*-
"""Tests R7' étape 1 — la famille globale et sa compatibilité."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, equiv, appartient, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    famille_compatible,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_capstone_rec import (
    Dglob_rec, membre_Dglob_rec, compatibilite_Dglob,
)

_G, _E, _P = var("Gsr"), var("Esr"), var("pDg")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_membre_Dglob_rec():
    """p∈Dglob ⇔ (p∈𝔓(E×V) ∧ (∃y∈E) essai_rec(p,y))."""
    t = membre_Dglob_rec(_vh)
    vy = var("yDg")
    attendu = equiv(
        appartient(_P, Dglob_rec(_G, _E)),
        et(appartient(_P, ambiant("Esr")),
           existe("yDg", et(appartient(vy, _E),
                            est_essai_rec(_P, _vh, _G, _E, vy)))))
    assert t.conclusion == attendu
    assert len(E.theorie_ensembles().axiomes) == 22


def test_compatibilite_Dglob():
    """🎯 {bo} ⊢ famille_compatible(Dglob_rec) — 1 hypothèse."""
    t = compatibilite_Dglob(_vh)
    assert t.conclusion == famille_compatible(Dglob_rec(_G, _E))
    assert list(t.hypotheses) == [E.est_bien_ordonne(_graphe_R(_G), _E)]
    assert len(E.theorie_ensembles().axiomes) == 22
