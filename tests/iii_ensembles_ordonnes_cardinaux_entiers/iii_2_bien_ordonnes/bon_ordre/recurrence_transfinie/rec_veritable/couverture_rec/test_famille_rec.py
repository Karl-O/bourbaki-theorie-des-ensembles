# -*- coding: utf-8 -*-
"""Tests R5'b — la famille S8 des essais récursifs (théorie dédiée)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, equiv, appartient, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec, membre_Dfam_rec,
)

_G, _E, _X, _P = var("Gsr"), var("Esr"), var("xsr"), var("pDr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_membre_Dfam_rec():
    """L'axiome instancié : p∈Dfam_rec(x) ⇔ (p∈𝔓(E×V) ∧ (∃y∈seg) essai_rec(p,y))."""
    t = membre_Dfam_rec(_vh)
    seg = E.segment_extremite(_G, _E, _X)
    vy = var("yDr")
    attendu = equiv(
        appartient(_P, Dfam_rec(_G, _E, _X)),
        et(appartient(_P, ambiant("Esr")),
           existe("yDr", et(appartient(vy, seg),
                            est_essai_rec(_P, _vh, _G, _E, vy)))))
    assert t.conclusion == attendu
    assert len(E.theorie_ensembles().axiomes) == 22


def test_terme_porte_le_graphe():
    """Deux graphes distincts donnent des termes Dfam_rec DISTINCTS (leçon seg_ext)."""
    assert Dfam_rec(var("G1"), _E, _X) != Dfam_rec(var("G2"), _E, _X)
    assert len(E.theorie_ensembles().axiomes) == 22
