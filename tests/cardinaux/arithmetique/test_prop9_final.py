"""Tests ISOLÉS — Proposition 9 (forme exponentielle), assemblage final de Φ.

Vérifient (noyau strict, PROUVE == certifie) :
  • W fonctionnel / dom W = 𝓕(B⊔C;A) / W(f)=Φ(f)            (conjoints structurels) ;
  • injectivité demi : W(f₁)=W(f₂) ⇒ restrictions coïncident ;
  • dernier mile conditionnel : W bijection ⟹ Card(𝓕(B⊔C;A))=Card(𝓕(B;A)×𝓕(C;A)).
"""
from bourbaki.logique.formule import var, egal, et
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.ensembles_prop9_exp_somme import (
    cible_prop9_exp_somme, restriction_gauche, restriction_droite)
from bourbaki.cardinaux.arithmetique.ensembles_prop9_final import (
    phi_valeur, domaine_phi, codomaine_phi, W,
    W_fonctionnel, W_domaine, W_valeur,
    W_injective_restrictions_coincident,
    equipotent_si_bijection, card_eq_si_bijection,
    bijection_phi_conjoints_durs_REPORTE)

A, B, C = var("A"), var("B"), var("C")


# ── PALIER W — graphe de Φ et conjoints structurels ──────────────────────────
def test_W_fonctionnel_clos():
    th = W_fonctionnel()
    assert th.conclusion == E.est_fonctionnel(W())
    assert not th.hypotheses          # CLOS (automatique, C54)


def test_W_domaine_clos():
    th = W_domaine()
    assert th.conclusion == egal(E.dom(W()), domaine_phi())
    assert not th.hypotheses          # CLOS (automatique, C54)


def test_W_valeur_sous_membership():
    th = W_valeur("g")
    # conclusion : W(g) = Φ(g)
    assert th.conclusion == egal(E.valeur(W(), var("g")), phi_valeur(var("g")))
    # unique hypothèse : g ∈ 𝓕(B⊔C;A)
    assert any(h == E.appartient(var("g"), domaine_phi()) for h in th.hypotheses)


# ── PALIER INJ½ — mêmes restrictions ─────────────────────────────────────────
def test_W_injective_restrictions_coincident():
    th = W_injective_restrictions_coincident()
    f1, f2 = var("f1"), var("f2")
    cible = et(egal(restriction_gauche(f1, B), restriction_gauche(f2, B)),
               egal(restriction_droite(f1, C), restriction_droite(f2, C)))
    assert th.conclusion == cible
    # hypothèses : f₁∈dom, f₂∈dom, W(f₁)=W(f₂)
    dom = domaine_phi()
    hyps = set(th.hypotheses)
    assert E.appartient(f1, dom) in hyps
    assert E.appartient(f2, dom) in hyps
    assert egal(E.valeur(W(), f1), E.valeur(W(), f2)) in hyps


# ── PALIER FIN — dernier mile conditionnel ───────────────────────────────────
def test_equipotent_si_bijection():
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    th = equipotent_si_bijection()
    assert th.conclusion == equipotent(domaine_phi(), codomaine_phi())
    # unique hypothèse : est_bijection_de(W, dom, cod)
    bij = est_bijection_de(W(), domaine_phi(), codomaine_phi())
    assert set(th.hypotheses) == {bij}


def test_card_eq_si_bijection_donne_la_cible():
    th = card_eq_si_bijection()
    # la conclusion est LITTÉRALEMENT l'énoncé-cible de la Proposition 9
    assert th.conclusion == cible_prop9_exp_somme("A", "B", "C")
    # sous l'unique hypothèse « W est une bijection »
    bij = est_bijection_de(W(), domaine_phi(), codomaine_phi())
    assert set(th.hypotheses) == {bij}


# ── le cœur dur est honnêtement reporté ──────────────────────────────────────
def test_conjoints_durs_reportes():
    import pytest
    with pytest.raises(NotImplementedError):
        bijection_phi_conjoints_durs_REPORTE()
