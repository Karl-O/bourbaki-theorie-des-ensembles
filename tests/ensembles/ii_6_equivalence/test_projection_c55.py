"""Tests — §II.6.2 critère C55 : caractérisation de la projection canonique.

Vérifie (noyau LCF strict) :
  • le théorème BUILD (pas d'exception du noyau) et est CLOS modulo hypothèses ;
  • non VACUEUX : conclusion ∉ hypothèses ;
  • CONCLUSION littéralement la cible Bourbaki ( p(a)=p(b) ) ⇔ ( R{a,b} ) ;
  • HYPOTHÈSES = exactement l'union des deux maillons (réfl/sym/trans, b∈E, et les
    deux relations de valeur p(a)=Cl(a), p(b)=Cl(b)) — 6 au total ;
  • theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf : pur recollage logique).
"""
from __future__ import annotations

import bourbaki.ensembles.ii_6_equivalence.ensembles_projection_c55 as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, egal, equiv, appartient


def _G():
    return E.rel_graphe("G")


def _non_vacuous(thm):
    assert thm.conclusion not in thm.hypotheses, "VACUEUX : conclusion ∈ hypothèses"


# ── theorie inchangée ─────────────────────────────────────────────────────────
def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── cible : ( p(a)=p(b) ) ⇔ ( R{a,b} ) ─────────────────────────────────────────
def test_cible_projection_c55():
    R, va, vb = _G(), var("a"), var("b")
    vg, ve = var("G"), var("E")
    p = E.application_canonique(vg, ve)
    pa, pb = E.valeur(p, va), E.valeur(p, vb)
    assert M.cible_projection_c55("G", "E", "a", "b") == equiv(egal(pa, pb), R(va, vb))


# ── projection_c55 : conclusion == cible, séquent == union des deux maillons ────
def test_projection_c55():
    t = M.projection_c55("G", "E", "a", "b", "x", "z")
    _non_vacuous(t)
    R, va, vb, ve = _G(), var("a"), var("b"), var("E")
    vg = var("G")
    p = E.application_canonique(vg, ve)
    pa, pb = E.valeur(p, va), E.valeur(p, vb)
    cla, clb = E.classe(vg, va), E.classe(vg, vb)
    # conclusion littéralement la cible
    assert t.conclusion == equiv(egal(pa, pb), R(va, vb))
    assert t.conclusion == M.cible_projection_c55("G", "E", "a", "b")
    # séquent : union EXACTE des hypothèses des deux maillons (6)
    # — de relation_ssi_classe_egale : réfl, sym, trans, b∈E
    assert E.est_reflexive_dans(R, ve, "x") in t.hypotheses
    assert E.est_symetrique(R, "p", "q") in t.hypotheses
    assert E.est_transitive(R, "p", "q", "r") in t.hypotheses
    assert appartient(vb, ve) in t.hypotheses
    # — de projection_valeur_classe : les deux relations de valeur
    assert egal(pa, cla) in t.hypotheses
    assert egal(pb, clb) in t.hypotheses
    # a∈E n'intervient PAS (la classe de b suffit côté ⇐)
    assert appartient(va, ve) not in t.hypotheses
    assert len(t.hypotheses) == 6


# ── théorie toujours intacte après usage ───────────────────────────────────────
def test_theorie_22_apres_usage():
    M.projection_c55()
    assert len(E.theorie_ensembles().axiomes) == 22
