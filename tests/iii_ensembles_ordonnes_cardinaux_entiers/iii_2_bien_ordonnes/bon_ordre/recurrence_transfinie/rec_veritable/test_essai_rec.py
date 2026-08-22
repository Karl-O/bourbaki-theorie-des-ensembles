# -*- coding: utf-8 -*-
"""Tests R1' — le prédicat d'essai récursif (formes, aucun théorème)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    restriction_seg, est_essai_rec, couvert_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    dom_essai,
)


def _vh(u):
    """Règle-itération jouet : S = g(·)."""
    return E.valeur(var("gitr"), u)


def test_est_essai_rec_forme():
    """Le prédicat == sa reconstruction par builders (l'équation lit la restriction)."""
    vp, vz = var("pesr"), var("zesr")
    f = est_essai_rec("pesr", _vh, "Gesr", "Eesr", "xesr")
    eq = pourtout("zesr", impl(
        appartient(vz, E.dom(vp)),
        egal(E.valeur(vp, vz), _vh(restriction_seg(vp, "Gesr", "Eesr", vz)))))
    attendu = et(et(E.est_fonctionnel(vp),
                    egal(E.dom(vp), dom_essai("Gesr", "Eesr", "xesr"))), eq)
    assert f == attendu
    assert len(E.theorie_ensembles().axiomes) == 22


def test_couvert_essai_rec_forme():
    """couvert_rec(x) == (∃pesr) est_essai_rec(pesr, x)."""
    c = couvert_essai_rec(_vh, "Gesr", "Eesr")(var("xesr"))
    attendu = existe("pesr", est_essai_rec(var("pesr"), _vh, "Gesr", "Eesr",
                                           var("xesr"), "zesr"))
    assert c == attendu
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
