# -*- coding: utf-8 -*-
"""Test n°111 (a^n=a) — ponts d'assemblage (multi-tick)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_a_puissance_n_er import (
    copie_gauche_inclus_somme, enonce_copie_gauche_inclus_somme, support_copie_gauche,
    eq_exposant_copie_gauche, inf_Fn_Fsucc, sup_Fsucc_produit,
    eq_produit_Fn_F1, hyp_recurrence, sup_Fsucc_le_A, hyp_carre, inf_A_Fsucc,
    eq_Fsucc_A, enonce_eq_Fsucc_A, eq_R_np1, enonce_eq_R_np1,
    heredite_111, enonce_heredite_111, base_111, enonce_base_111,
    a_puissance_n_egale_a, enonce_a_puissance_n_egale_a, hyp_carre)


def test_copie_gauche_inclus_somme():
    """⊢ (n × {∅}) ⊆ (n ⊔ {∅}) — CLOS, 0 hyp."""
    r = copie_gauche_inclus_somme()
    assert r.conclusion == enonce_copie_gauche_inclus_somme()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_support_copie_gauche():
    """⊢ {a₀∈A} 𝓕(n×{∅};A) ≤ 𝓕(n⊔{∅};A)."""
    r = support_copie_gauche()
    assert r.hypotheses == frozenset([appartient(E.var("a0"), E.var("A"))])


def test_eq_exposant_copie_gauche():
    """⊢ Eq(𝓕(n;A), 𝓕(n×{∅};A)) — CLOS."""
    r = eq_exposant_copie_gauche()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_inf_Fn_Fsucc():
    """⊢ {a₀∈A} 𝓕(n;A) ≤ 𝓕(n⊔{∅};A)  (borne INF niveau 𝓕)."""
    r = inf_Fn_Fsucc()
    assert r.hypotheses == frozenset([appartient(E.var("a0"), E.var("A"))])


def test_sup_Fsucc_produit():
    """⊢ 𝓕(n⊔{∅};A) ≤ 𝓕(n;A)×𝓕({∅};A) — CLOS  (borne SUP niveau 𝓕, Dir.A Prop.9)."""
    r = sup_Fsucc_produit()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_eq_produit_Fn_F1():
    """⊢ {Eq(𝓕(n;A),A)} Eq(𝓕(n;A)×𝓕({∅};A), A×A)  (SUP, invariance produit)."""
    r = eq_produit_Fn_F1()
    assert r.hypotheses == frozenset([hyp_recurrence()])


def test_sup_Fsucc_le_A():
    """⊢ {Eq(𝓕(n;A),A), Eq(A×A,A)} 𝓕(n⊔{∅};A) ≤ A  (BORNE SUP complète conditionnelle)."""
    r = sup_Fsucc_le_A()
    assert r.hypotheses == frozenset([hyp_recurrence(), hyp_carre()])


def test_inf_A_Fsucc():
    """⊢ {Eq(𝓕(n;A),A), a₀∈A} A ≤ 𝓕(n⊔{∅};A)  (BORNE INF complète)."""
    r = inf_A_Fsucc()
    assert r.hypotheses == frozenset([hyp_recurrence(), appartient(E.var("a0"), E.var("A"))])


def test_eq_Fsucc_A():
    """⊢ {Eq(𝓕(n;A),A), Eq(A×A,A), a₀∈A} Eq(𝓕(n⊔{∅};A), A)  (Cantor-Bernstein, cœur récurrence)."""
    r = eq_Fsucc_A()
    assert r.conclusion == enonce_eq_Fsucc_A()
    assert r.hypotheses == frozenset([
        hyp_recurrence(), hyp_carre(), appartient(E.var("a0"), E.var("A"))])


def test_eq_R_np1():
    """⊢ {Eq(𝓕(n;A),A), Eq(A×A,A), a₀∈A} Eq(𝓕(succ n;A),A)  (pas de récurrence R{n}⇒R{n+1})."""
    r = eq_R_np1()
    assert r.conclusion == enonce_eq_R_np1()
    assert r.hypotheses == frozenset([
        hyp_recurrence(), hyp_carre(), appartient(E.var("a0"), E.var("A"))])


def test_heredite_111():
    """⊢ {Eq(A×A,A), a₀∈A} (∀n)((n entier et n≥1 et R{n}) ⇒ R{n+1})  (hérédité récurrence)."""
    r = heredite_111()
    assert r.conclusion == enonce_heredite_111()
    assert r.hypotheses == frozenset([hyp_carre(), appartient(E.var("a0"), E.var("A"))])


def test_base_111():
    """⊢ Eq(𝓕(1;A), A) — CLOS  (base R{1}=a^1=a, exposant entier 1)."""
    r = base_111()
    assert r.conclusion == enonce_base_111()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_a_puissance_n_egale_a():
    """🎯 CONDITIONNEL {a²=a, a₀∈A, pred_univ} ⊢ (∀n≥1) Eq(𝓕(n;A),A)  (Cor.1 Th.2, n°111)."""
    r = a_puissance_n_egale_a()
    assert r.conclusion == enonce_a_puissance_n_egale_a()
    # trois hypothèses honnêtes : a²=a (Hessenberg), a₀∈A (A non vide), pred_univ (C61)
    assert len(r.hypotheses) == 3
    assert hyp_carre() in r.hypotheses
    assert appartient(E.var("a0"), E.var("A")) in r.hypotheses


def test_theorie_inchangee():
    base_111()
    heredite_111()
    a_puissance_n_egale_a()
    assert len(E.theorie_ensembles().axiomes) == 22
