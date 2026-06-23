"""Tests — §III.2 : DÉFINITION PAR RÉCURRENCE TRANSFINIE (C60), EXISTENCE (suite).

Vérifie les briques CONSTRUCTIVES du « prolongement d'un pas » (cœur reporté de
l'EXISTENCE) et la couverture-via-C59 sur le prédicat CONCRET d'existence d'un essai :

  (E1) singleton_couple_fonctionnel     — {(x,v)} fonctionnel             [CLOS, 0 hyp]
  (E2) dom_singleton_couple             — dom({(x,v)}) = {x}             [CLOS, 0 hyp]
  (E3) point_hors_segment               — ¬(x∈seg(R,E,x))               [CLOS, 0 hyp]
  (E4) domaines_essai_disjoints         — dom(p) ⊥ dom({(x,v)})         [1 hyp honnête]
  (E5) extension_un_pas_fonctionnelle   — est_fonctionnel(p∪{(x,v)})    [2 hyps honnêtes]
  (E6) couverture_essais_via_c59        — (∀x∈E)(∃p)essai(p,x)          [2 hyps honnêtes]

theorie_ensembles() = 22 intangible ; conclusions NON vacuous (concl ∉ hyps) ;
GÉNÉRIQUE sur la valeur-règle vh.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, app, egal, et, non, appartient, pourtout
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie import ensembles_c60_existence_close as C
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
    couverture_totale, heredite_couverture,
)


def _vh(z):
    return app("h_regle", z)


def _vh2(z):
    return E.valeur(var("Hbis"), z)


# ── théorie intangible ────────────────────────────────────────────────────────
def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


# ══════════════════════════════════════════════════════════════════════════════
#  (E1) — FONCTIONNALITÉ DU GRAPHE-ESSAI TRIVIAL {(x,v)}.
# ══════════════════════════════════════════════════════════════════════════════
def test_e1_singleton_couple_fonctionnel_clos():
    th = C.singleton_couple_fonctionnel()
    assert th.est_clos
    assert len(th.hypotheses) == 0
    S = E.singleton(E.couple(var("x0"), var("v0")))
    assert th.conclusion == E.est_fonctionnel(S)


def test_e1_generique_autres_points():
    th = C.singleton_couple_fonctionnel("a", "b")
    assert th.est_clos
    S = E.singleton(E.couple(var("a"), var("b")))
    assert th.conclusion == E.est_fonctionnel(S)


# ══════════════════════════════════════════════════════════════════════════════
#  (E2) — DOMAINE DU GRAPHE-ESSAI TRIVIAL  dom({(x,v)}) = {x}.
# ══════════════════════════════════════════════════════════════════════════════
def test_e2_dom_singleton_couple_clos():
    th = C.dom_singleton_couple()
    assert th.est_clos
    assert len(th.hypotheses) == 0
    S = E.singleton(E.couple(var("x0"), var("v0")))
    assert th.conclusion == egal(E.dom(S), E.singleton(var("x0")))


# ══════════════════════════════════════════════════════════════════════════════
#  (E3) — UN POINT HORS DE SON PROPRE SEGMENT  ¬(x∈seg(R,E,x)).
# ══════════════════════════════════════════════════════════════════════════════
def test_e3_point_hors_segment_clos():
    th = C.point_hors_segment()
    assert th.est_clos
    assert len(th.hypotheses) == 0
    R = _graphe_R("G")
    seg = E.segment_extremite(R, var("E"), var("x0"))
    assert th.conclusion == non(appartient(var("x0"), seg))


# ══════════════════════════════════════════════════════════════════════════════
#  (E4) — DISJONCTION DES DOMAINES.
# ══════════════════════════════════════════════════════════════════════════════
def test_e4_domaines_essai_disjoints_une_hyp():
    th = C.domaines_essai_disjoints()
    assert len(th.hypotheses) == 1
    R = _graphe_R("G")
    seg = E.segment_extremite(R, var("E"), var("x0"))
    assert egal(E.dom(var("p")), seg) in th.hypotheses           # hyp honnête : dom p = seg


def test_e4_domaines_essai_disjoints_conclusion():
    th = C.domaines_essai_disjoints()
    S = E.singleton(E.couple(var("x0"), var("v0")))
    cible = pourtout("u", non(et(appartient(var("u"), E.dom(var("p"))),
                                 appartient(var("u"), E.dom(S)))))
    assert th.conclusion == cible
    assert th.conclusion not in th.hypotheses                    # NON vacuous


# ══════════════════════════════════════════════════════════════════════════════
#  (E5) — 🎯 PROLONGEMENT D'UN PAS, moitié FONCTIONNALITÉ.
# ══════════════════════════════════════════════════════════════════════════════
def test_e5_extension_un_pas_deux_hyps_honnetes():
    th = C.extension_un_pas_fonctionnelle()
    assert len(th.hypotheses) == 2
    R = _graphe_R("G")
    seg = E.segment_extremite(R, var("E"), var("x0"))
    assert E.est_fonctionnel(var("p")) in th.hypotheses          # p fonctionnel
    assert egal(E.dom(var("p")), seg) in th.hypotheses           # dom p = seg


def test_e5_extension_un_pas_conclusion():
    th = C.extension_un_pas_fonctionnelle()
    S = E.singleton(E.couple(var("x0"), var("v0")))
    assert th.conclusion == E.est_fonctionnel(E.reunion(var("p"), S))
    assert th.conclusion not in th.hypotheses                    # NON vacuous


# ══════════════════════════════════════════════════════════════════════════════
#  (E6) — 🎯 COUVERTURE-VIA-C59 sur le prédicat CONCRET d'essai.
# ══════════════════════════════════════════════════════════════════════════════
def test_e6_couverture_essais_deux_hyps_honnetes():
    th = C.couverture_essais_via_c59(_vh)
    assert len(th.hypotheses) == 2
    R = _graphe_R("G")
    e = var("E")
    couvert = C.couvert_essai(_vh, R, e)
    assert E.est_bien_ordonne(R, e) in th.hypotheses
    assert heredite_couverture(couvert, R, e, "x0tf", "ytf") in th.hypotheses


def test_e6_couverture_essais_conclusion():
    th = C.couverture_essais_via_c59(_vh)
    R = _graphe_R("G")
    e = var("E")
    couvert = C.couvert_essai(_vh, R, e)
    assert th.conclusion == couverture_totale(couvert, e, "x0tf")
    assert th.conclusion not in th.hypotheses                    # NON vacuous


def test_e6_generique_autre_regle():
    th = C.couverture_essais_via_c59(_vh2)
    assert len(th.hypotheses) == 2
    assert th.conclusion not in th.hypotheses


def test_e6_predicat_essai_bien_forme():
    R = _graphe_R("G")
    e = var("E")
    ess = C.est_essai(var("p"), _vh, R, e, var("x0"))
    # est_essai est une conjonction ((func p et dom p=seg∪{x}) et eq) — bien formée
    assert ess is not None
    assert C.dom_essai(R, e, var("x0")) == E.reunion(
        E.segment_extremite(R, e, var("x0")), E.singleton(var("x0")))
