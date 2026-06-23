"""Tests — §II.6 propriétés ensemblistes des classes/relations d'équivalence.

Vérifie (noyau LCF strict) :
  • chaque théorème BUILD (pas d'exception du noyau) ;
  • non VACUEUX : conclusion ∉ hypothèses ;
  • CONCLUSION littéralement la cible Bourbaki attendue ;
  • HYPOTHÈSES = exactement le séquent conditionnel annoncé (sym/trans/réfl/∈, valeurs) ;
  • theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf).
"""
from __future__ import annotations

import bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, equiv, appartient, existe


def _G():
    return E.rel_graphe("G")


def _R():
    return E.rel_graphe("GR")


def _Rp():
    return E.rel_graphe("GRp")


def _non_vacuous(thm):
    assert thm.conclusion not in thm.hypotheses, "VACUEUX : conclusion ∈ hypothèses"


# ── theorie inchangée ─────────────────────────────────────────────────────────
def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── appartient_classe : x ∈ Cl_R(x) ───────────────────────────────────────────
def test_appartient_classe():
    t = M.appartient_classe("G", "a", "E", "x")
    _non_vacuous(t)
    R, va, ve = _G(), var("a"), var("E")
    assert t.conclusion == appartient(va, E.classe(var("G"), va))
    assert E.est_reflexive_dans(R, ve, "x") in t.hypotheses
    assert appartient(va, ve) in t.hypotheses
    assert len(t.hypotheses) == 2


# ── relation_implique_classe_egale : R{a,b} ⇒ Cl(a)=Cl(b) ──────────────────────
def test_relation_implique_classe_egale():
    t = M.relation_implique_classe_egale("G", "a", "b", "z")
    _non_vacuous(t)
    R, va, vb = _G(), var("a"), var("b")
    cl = egal(E.classe(var("G"), va), E.classe(var("G"), vb))
    assert t.conclusion == impl(R(va, vb), cl)
    assert E.est_symetrique(R, "p", "q") in t.hypotheses
    assert E.est_transitive(R, "p", "q", "r") in t.hypotheses
    assert len(t.hypotheses) == 2


# ── classe_egale_implique_relation : Cl(a)=Cl(b) ⇒ R{a,b} ──────────────────────
def test_classe_egale_implique_relation():
    t = M.classe_egale_implique_relation("G", "a", "b", "E", "x")
    _non_vacuous(t)
    R, va, vb, ve = _G(), var("a"), var("b"), var("E")
    cl = egal(E.classe(var("G"), va), E.classe(var("G"), vb))
    assert t.conclusion == impl(cl, R(va, vb))
    # seul b∈E est requis (a∈E n'intervient pas)
    assert E.est_reflexive_dans(R, ve, "x") in t.hypotheses
    assert appartient(vb, ve) in t.hypotheses
    assert appartient(va, ve) not in t.hypotheses
    assert len(t.hypotheses) == 2


# ── relation_ssi_classe_egale : R{a,b} ⇔ Cl(a)=Cl(b) ───────────────────────────
def test_relation_ssi_classe_egale():
    t = M.relation_ssi_classe_egale("G", "a", "b", "E", "x", "z")
    _non_vacuous(t)
    R, va, vb, ve = _G(), var("a"), var("b"), var("E")
    cl = egal(E.classe(var("G"), va), E.classe(var("G"), vb))
    assert t.conclusion == equiv(R(va, vb), cl)
    # séquent : réflexivité, symétrie, transitivité, b∈E (a∈E non requis)
    assert E.est_reflexive_dans(R, ve, "x") in t.hypotheses
    assert E.est_symetrique(R, "p", "q") in t.hypotheses
    assert E.est_transitive(R, "p", "q", "r") in t.hypotheses
    assert appartient(vb, ve) in t.hypotheses
    assert len(t.hypotheses) == 4


# ── classes_se_rencontrent_egales : (∃z)(z∈Cl(a) et z∈Cl(b)) ⇒ Cl(a)=Cl(b) ─────
def test_classes_se_rencontrent_egales():
    t = M.classes_se_rencontrent_egales("G", "a", "b", "z", "wc")
    _non_vacuous(t)
    R, va, vb, vz = _G(), var("a"), var("b"), var("z")
    ante = existe("z", et(appartient(vz, E.classe(var("G"), va)),
                          appartient(vz, E.classe(var("G"), vb))))
    cl = egal(E.classe(var("G"), va), E.classe(var("G"), vb))
    assert t.conclusion == impl(ante, cl)
    assert E.est_symetrique(R, "p", "q") in t.hypotheses
    assert E.est_transitive(R, "p", "q", "r") in t.hypotheses
    assert len(t.hypotheses) == 2


# ── projection_valeur_classe : p(a)=p(b) ⇔ Cl(a)=Cl(b) ─────────────────────────
def test_projection_valeur_classe():
    t = M.projection_valeur_classe("G", "E", "a", "b")
    _non_vacuous(t)
    vg, ve, va, vb = var("G"), var("E"), var("a"), var("b")
    p = E.application_canonique(vg, ve)
    pa, pb = E.valeur(p, va), E.valeur(p, vb)
    cla, clb = E.classe(vg, va), E.classe(vg, vb)
    assert t.conclusion == equiv(egal(pa, pb), egal(cla, clb))
    # hypothèses : les deux relations de valeur p(a)=Cl(a), p(b)=Cl(b)
    assert egal(pa, cla) in t.hypotheses
    assert egal(pb, clb) in t.hypotheses
    assert len(t.hypotheses) == 2


# ── intersection de relations d'équivalence ────────────────────────────────────
def test_intersection_symetrique():
    t = M.intersection_symetrique()
    _non_vacuous(t)
    R, Rp = _R(), _Rp()
    S = M.relation_intersection(R, Rp)
    assert t.conclusion == E.est_symetrique(S, "x", "y")
    assert E.est_symetrique(R, "a", "b") in t.hypotheses
    assert E.est_symetrique(Rp, "a", "b") in t.hypotheses
    assert len(t.hypotheses) == 2


def test_intersection_transitive():
    t = M.intersection_transitive()
    _non_vacuous(t)
    R, Rp = _R(), _Rp()
    S = M.relation_intersection(R, Rp)
    assert t.conclusion == E.est_transitive(S, "x", "y", "z")
    assert E.est_transitive(R, "a", "b", "c") in t.hypotheses
    assert E.est_transitive(Rp, "a", "b", "c") in t.hypotheses
    assert len(t.hypotheses) == 2


def test_intersection_relation_equivalence():
    t = M.intersection_relation_equivalence()
    _non_vacuous(t)
    R, Rp = _R(), _Rp()
    S = M.relation_intersection(R, Rp)
    assert t.conclusion == E.est_relation_equivalence(S, "x", "y", "z")
    # séquent : sym R, trans R, sym R', trans R'
    assert E.est_symetrique(R, "a", "b") in t.hypotheses
    assert E.est_transitive(R, "a", "b", "c") in t.hypotheses
    assert E.est_symetrique(Rp, "a", "b") in t.hypotheses
    assert E.est_transitive(Rp, "a", "b", "c") in t.hypotheses
    assert len(t.hypotheses) == 4


# ── théorie toujours intacte après usage ───────────────────────────────────────
def test_theorie_22_apres_usage():
    M.appartient_classe()
    M.relation_ssi_classe_egale()
    M.intersection_relation_equivalence()
    M.classes_se_rencontrent_egales()
    M.projection_valeur_classe()
    assert len(E.theorie_ensembles().axiomes) == 22
