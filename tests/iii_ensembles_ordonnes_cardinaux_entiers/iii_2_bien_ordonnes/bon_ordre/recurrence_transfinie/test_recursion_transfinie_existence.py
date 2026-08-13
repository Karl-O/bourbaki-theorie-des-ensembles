"""Tests — §III.2 : DÉFINITION PAR RÉCURRENCE TRANSFINIE (Critère C60), moitié EXISTENCE.

Vérifie les sous-lemmes CLOS (sous hypothèses HONNÊTES) :
  (a) solutions_coincident       — deux solutions de la même règle locale coïncident ;
  (b) reunion_essais_fonctionnelle — la réunion de deux essais à domaines disjoints
      est fonctionnelle.
theorie_ensembles() = 22 intangible ; conclusions NON vacuous (concl ∉ hyps) ;
GÉNÉRIQUE sur les fonctions-valeur vf, vg, vhf, vhg.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, app, egal, et, non, impl, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie import ensembles_recursion_transfinie_existence as EX
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R, coincidence_solutions,
)


def _R(a, b):
    """Relation-test R{x,y} := (x,y)∈G."""
    return appartient(E.couple(a, b), var("G"))


def _vf(x):
    return E.valeur(var("Ff"), x)


def _vg(x):
    return E.valeur(var("Fg"), x)


def _vhf(x):
    return E.valeur(var("Hf"), x)


def _vhg(x):
    return E.valeur(var("Hg"), x)


# ── théorie intangible ────────────────────────────────────────────────────────
def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── énoncés bien formés ───────────────────────────────────────────────────────
def test_enonces_bien_formes():
    e = var("E")
    assert EX.equation_recursion(_vf, _vhf, e) is not None
    assert EX.regle_locale(_vf, _vg, _vhf, _vhg, var("G"), e) is not None


# ══════════════════════════════════════════════════════════════════════════════
#  LEMME (a) — COHÉRENCE DES SOLUTIONS (CLOS sous 4 hyps honnêtes).
# ══════════════════════════════════════════════════════════════════════════════
def test_a_solutions_coincident_quatre_hyps_honnetes():
    th = EX.solutions_coincident(_vf, _vg, _vhf, _vhg)
    # NON inconditionnel : EXACTEMENT 4 hypothèses honnêtes
    assert len(th.hypotheses) == 4
    e = var("E")
    R = _graphe_R("G")
    assert E.est_bien_ordonne(R, e) in th.hypotheses                     # bon ordre
    assert EX.equation_recursion(_vf, _vhf, e, "x0tf") in th.hypotheses  # vf solution
    assert EX.equation_recursion(_vg, _vhg, e, "x0tf") in th.hypotheses  # vg solution
    assert EX.regle_locale(_vf, _vg, _vhf, _vhg, var("G"), e, "x0tf", "ytf") in th.hypotheses  # localité


def test_a_solutions_coincident_conclusion_exacte():
    th = EX.solutions_coincident(_vf, _vg, _vhf, _vhg)
    e = var("E")
    assert th.conclusion == coincidence_solutions(_vf, _vg, e, "x0tf")


def test_a_solutions_coincident_non_vacuous():
    th = EX.solutions_coincident(_vf, _vg, _vhf, _vhg)
    # la conclusion (coïncidence) n'est PAS l'une des hypothèses (P⇒P interdit)
    assert th.conclusion not in th.hypotheses


def test_a_generique_autres_valeurs():
    """Marche pour d'autres fonctions-valeur (généricité du méta-théorème)."""
    def wf(x):
        return E.valeur(var("AA"), x)

    def wg(x):
        return E.valeur(var("BB"), x)

    def whf(x):
        return app("rule_f", x)

    def whg(x):
        return app("rule_g", x)

    th = EX.solutions_coincident(wf, wg, whf, whg)
    assert len(th.hypotheses) == 4
    assert th.conclusion not in th.hypotheses


# ══════════════════════════════════════════════════════════════════════════════
#  LEMME (b) — FONCTIONNALITÉ DE LA RÉUNION DE DEUX ESSAIS.
# ══════════════════════════════════════════════════════════════════════════════
def test_b_reunion_essais_fonctionnelle():
    th = EX.reunion_essais_fonctionnelle()
    # 3 hypothèses honnêtes : func G, func H, domaines disjoints
    assert len(th.hypotheses) == 3
    assert th.conclusion == E.est_fonctionnel(E.reunion(var("G"), var("H")))


def test_b_reunion_essais_non_vacuous():
    th = EX.reunion_essais_fonctionnelle()
    assert th.conclusion not in th.hypotheses


# ══════════════════════════════════════════════════════════════════════════════
#  LEMME (c) — COUVERTURE TRANSFINIE (squelette C59 de l'existence).
# ══════════════════════════════════════════════════════════════════════════════
def _couvert(x):
    """Prédicat-test « x est couvert » := x ∈ Couv  (symbolique)."""
    return appartient(x, var("Couv"))


def test_c_couverture_transfinie_deux_hyps_honnetes():
    th = EX.couverture_transfinie(_couvert)
    assert len(th.hypotheses) == 2
    e = var("E")
    R = _graphe_R("G")
    assert E.est_bien_ordonne(R, e) in th.hypotheses
    assert EX.heredite_couverture(_couvert, var("G"), e, "x0tf", "ytf") in th.hypotheses


def test_c_couverture_transfinie_conclusion_exacte():
    th = EX.couverture_transfinie(_couvert)
    e = var("E")
    assert th.conclusion == EX.couverture_totale(_couvert, e, "x0tf")


def test_c_couverture_transfinie_non_vacuous():
    th = EX.couverture_transfinie(_couvert)
    assert th.conclusion not in th.hypotheses


def test_c_generique_autre_couvert():
    def couv2(x):
        return non(egal(x, app("bot")))
    th = EX.couverture_transfinie(couv2)
    assert len(th.hypotheses) == 2
    assert th.conclusion not in th.hypotheses


# ══════════════════════════════════════════════════════════════════════════════
#  LEMME (d) — TRANSFERT DE VALEUR de la réunion (binaire).
# ══════════════════════════════════════════════════════════════════════════════
def test_d_valeur_essai_reunion():
    th = EX.valeur_essai_reunion()
    # 4 hyps honnêtes : func G, func H, dom disjoints, u∈dom G
    assert len(th.hypotheses) == 4
    assert th.conclusion == egal(E.valeur(E.reunion(var("G"), var("H")), var("u")),
                                 E.valeur(var("G"), var("u")))


def test_d_valeur_essai_reunion_non_vacuous():
    th = EX.valeur_essai_reunion()
    assert th.conclusion not in th.hypotheses
