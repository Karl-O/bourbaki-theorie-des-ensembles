"""Tests V9 — §II.6.5 / E.R.23 item 3 : surjectivité de b sur f⟨E⟩ (valeurs)
et assemblage bijection (injectivité + surjectivité).  Hyps exactes {pont, Hf1} ;
conclusions littérales ; theorie=22."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition import (
    ensembles_decomposition_effective as D,
    ensembles_decomposition_bijection as M)


def test_b_surjective_valeurs():
    """{pont, Hf1} ⊢ (∀z)(z∈f⟨E⟩ ⇒ (∃x)(x∈E et b(θx)=z)) — cible + hyps exactes."""
    vf, vb, vE = var("f"), var("b"), var("E")
    t = M.b_surjective_valeurs("f", "b", vE)
    assert t.conclusion == M.b_surjective_valeurs_cible(vf, vb, vE)
    pont = D.pont_valeurs_b(vf, vb, e=vE)
    assert t.hypotheses == frozenset({pont, E.est_fonctionnel(vf)})
    assert not t.est_clos
    assert len(theorie_ensembles().axiomes) == 22


def test_b_surjective_valeurs_dom_par_defaut():
    """E = dom f par défaut."""
    vf, vb = var("f"), var("b")
    t = M.b_surjective_valeurs("f", "b")
    assert t.conclusion == M.b_surjective_valeurs_cible(vf, vb, E.dom(vf))


def test_b_bijective_valeurs():
    """{pont, Hf1} ⊢ injective ET surjective — conjonction littérale, hyps exactes."""
    vf, vb, vE = var("f"), var("b"), var("E")
    t = M.b_bijective_valeurs("f", "b", vE)
    inj = D.b_injective_via_pont("f", "b", vE)
    surj = M.b_surjective_valeurs("f", "b", vE)
    assert t.conclusion == et(inj.conclusion, surj.conclusion)
    pont = D.pont_valeurs_b(vf, vb, e=vE)
    assert t.hypotheses == frozenset({pont, E.est_fonctionnel(vf)})
    assert len(theorie_ensembles().axiomes) == 22
