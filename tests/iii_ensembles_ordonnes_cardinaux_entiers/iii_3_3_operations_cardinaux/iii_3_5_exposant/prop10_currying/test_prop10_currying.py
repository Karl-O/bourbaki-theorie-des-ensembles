"""Tests ISOLÉS — Proposition 10 / Corollaire 3 (forme CURRYING) : a^(b·c)=(a^b)^c.

Vérifient (noyau strict, PROUVE == certifie) :
  • caractérisations membership des 3 espaces 𝓕(B×C;A), 𝓕(B;A), 𝓕(C;𝓕(B;A)), A^B ;
  • W fonctionnel / dom W = 𝓕(B×C;A) / W(f)=Λval(f)         (conjoints structurels) ;
  • injectivité demi : W(f₁)=W(f₂) ⇒ graphes curry coïncident ;
  • dernier mile conditionnel : W bijection ⟹ Card(𝓕(B×C;A))=Card(𝓕(C;𝓕(B;A))).
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient, equiv, existe, inclus
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop10_currying.ensembles_prop10_currying import (
    espace_BA, domaine_lambda, codomaine_lambda, cible_prop10,
    membership_BCA, membership_BA, membership_C_BA, exposant_BA,
    tranche, slice_appli, curry, lambda_val, W,
    W_fonctionnel, W_domaine, W_valeur,
    W_injective_curry_coincident,
    equipotent_si_bijection_currying, card_eq_si_bijection_currying,
    bijection_currying_conjoints_durs_REPORTE,
)

A, B, C = var("A"), var("B"), var("C")


# ── PALIER M — caractérisations membership des trois espaces ──────────────────
def test_membership_BCA_clos():
    th = membership_BCA("t")
    BC = E.produit(B, C)
    triple = E.couple(E.couple(var("G"), BC), A)
    corps = existe("G", et(egal(var("t"), triple), appartient(var("G"), E.exposant(BC, A))))
    assert th.conclusion == equiv(appartient(var("t"), domaine_lambda()), corps)
    assert not th.hypotheses          # instance d'axiome, CLOS


def test_membership_BA_clos():
    th = membership_BA("t")
    triple = E.couple(E.couple(var("G"), B), A)
    corps = existe("G", et(egal(var("t"), triple), appartient(var("G"), E.exposant(B, A))))
    assert th.conclusion == equiv(appartient(var("t"), espace_BA()), corps)
    assert not th.hypotheses


def test_membership_C_BA_clos():
    th = membership_C_BA("t")
    FBA = espace_BA()
    triple = E.couple(E.couple(var("G"), C), FBA)
    corps = existe("G", et(egal(var("t"), triple), appartient(var("G"), E.exposant(C, FBA))))
    assert th.conclusion == equiv(appartient(var("t"), codomaine_lambda()), corps)
    assert not th.hypotheses


def test_exposant_BA_clos():
    th = exposant_BA("G")
    corps = et(et(inclus(var("G"), E.produit(B, A)), E.est_fonctionnel(var("G"))),
               egal(E.dom(var("G")), B))
    assert th.conclusion == equiv(appartient(var("G"), E.exposant(B, A)), corps)
    assert not th.hypotheses


# ── PALIER W — graphe de Λ (deux niveaux) et conjoints structurels ────────────
def test_W_fonctionnel_clos():
    th = W_fonctionnel()
    assert th.conclusion == E.est_fonctionnel(W())
    assert not th.hypotheses          # CLOS (automatique, C54)


def test_W_domaine_clos():
    th = W_domaine()
    assert th.conclusion == egal(E.dom(W()), domaine_lambda())
    assert not th.hypotheses          # CLOS (automatique, C54)


def test_W_valeur_sous_membership():
    th = W_valeur("g")
    assert th.conclusion == egal(E.valeur(W(), var("g")), lambda_val(var("g")))
    # unique hypothèse : g ∈ 𝓕(B×C;A)
    assert any(h == appartient(var("g"), domaine_lambda()) for h in th.hypotheses)


def test_lambda_val_structure():
    # Λval(f) = ((curry(f), C), 𝓕(B;A)) — emballage triple à deux niveaux
    f = var("g")
    assert lambda_val(f) == E.couple(E.couple(curry(f), C), espace_BA())
    # curry(f) est un graphe-terme sur C de valeur slice_appli(f, p)
    assert curry(f) == E.graphe_terme(C, slice_appli(f, var("p")), "p")
    # slice_appli(f, p) = ((tranche(f,p), B), A)
    assert slice_appli(f, var("p")) == E.couple(E.couple(tranche(f, var("p")), B), A)


# ── PALIER INJ½ — même graphe curry ───────────────────────────────────────────
def test_W_injective_curry_coincident():
    th = W_injective_curry_coincident()
    f1, f2 = var("f1"), var("f2")
    assert th.conclusion == egal(curry(f1), curry(f2))
    dom = domaine_lambda()
    hyps = set(th.hypotheses)
    assert appartient(f1, dom) in hyps
    assert appartient(f2, dom) in hyps
    assert egal(E.valeur(W(), f1), E.valeur(W(), f2)) in hyps


# ── PALIER FIN — dernier mile conditionnel ────────────────────────────────────
def test_equipotent_si_bijection_currying():
    th = equipotent_si_bijection_currying()
    assert th.conclusion == equipotent(domaine_lambda(), codomaine_lambda())
    bij = est_bijection_de(W(), domaine_lambda(), codomaine_lambda())
    assert set(th.hypotheses) == {bij}


def test_card_eq_si_bijection_currying_donne_la_cible():
    th = card_eq_si_bijection_currying()
    # la conclusion est LITTÉRALEMENT l'énoncé-cible de la Proposition 10
    assert th.conclusion == cible_prop10("A", "B", "C")
    bij = est_bijection_de(W(), domaine_lambda(), codomaine_lambda())
    assert set(th.hypotheses) == {bij}


def test_cible_prop10_forme():
    # Card(𝓕(B×C;A)) = Card(𝓕(C;𝓕(B;A)))  =  a^(b·c) = (a^b)^c
    assert cible_prop10() == egal(cardinal(domaine_lambda()), cardinal(codomaine_lambda()))


# ── le cœur dur est honnêtement reporté ───────────────────────────────────────
def test_conjoints_durs_reportes():
    with pytest.raises(NotImplementedError):
        bijection_currying_conjoints_durs_REPORTE()
