"""Tests §III.5.4 / §III.6 (Déf. 2) — NOTIONS de numérotation & suites multiples.

Vérifie : (1) toutes les DÉFINITIONS NEUVES se construisent ; (2) les notions DÉRIVÉES
sont fidèles (premier/dernier = k-ième en 1 / n ; suite multiple = I ⊂ N^p) ;
(3) les théorèmes DIRECTS sont == cible exacte ET clos.

L'existence/unicité de l'isomorphisme f : [1,n] → I (Prop. 6) repose sur la récurrence
/ le bon ordre de ℕ (NON disponibles) → REPORTÉ (numérotation réifiée par un terme).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl, inclus, libres_f
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (UN, longueur_suite, intervalle_entiers)
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import NN
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_notions_complementaires import ensembles_entiers_notions_suites as S


# ── (1) DÉFINITIONS NEUVES se construisent ────────────────────────────────────
def test_definitions_suites_se_construisent():
    t, i, k, p, f = var("t"), var("I"), var("k"), var("p"), var("f")
    # §5.4 numérotation
    S.numerotation_canonique(t, i)
    S.intervalle_un_n(i)
    S.kieme_terme(t, i, k)
    S.premier_terme(t, i)
    S.dernier_terme(t, i)
    # §6 Déf. 2 suite multiple
    S.produit_puissance_N(p)
    S.est_suite_multiple(f, i, p)
    S.est_suite_double(f, i)


# ── (2) notions dérivées fidèles ──────────────────────────────────────────────
def test_premier_est_kieme_en_un():
    """premier_terme(t,I) est, par construction, kieme_terme(t,I,1)."""
    t, i = var("t"), var("I")
    assert S.premier_terme(t, i) == S.kieme_terme(t, i, UN)


def test_dernier_est_kieme_en_longueur():
    """dernier_terme(t,I) est kieme_terme(t,I, longueur(I))."""
    t, i = var("t"), var("I")
    assert S.dernier_terme(t, i) == S.kieme_terme(t, i, longueur_suite(i))


def test_intervalle_un_n_est_intervalle_1_longueur():
    """[1,n] = intervalle_entiers(1, longueur(I))."""
    i = var("I")
    assert S.intervalle_un_n(i) == intervalle_entiers(UN, longueur_suite(i))


def test_suite_multiple_est_inclusion_dans_Np():
    """est_suite_multiple(f,I,p) := I ⊂ N^p (Déf. 2)."""
    f, i, p = var("f"), var("I"), var("p")
    assert S.est_suite_multiple(f, i, p) == inclus(i, S.produit_puissance_N(p))


def test_suite_double_est_inclusion_dans_NxN():
    """est_suite_double(f,I) := I ⊂ N × N (Déf. 2, cas p=2)."""
    f, i = var("f"), var("I")
    assert S.est_suite_double(f, i) == inclus(i, E.produit(NN, NN))


# ── (3) THÉORÈMES DIRECTS — cible exacte + clos ───────────────────────────────
def test_premier_egale_kieme_en_un_clos():
    t, i = var("t"), var("I")
    thm = S.premier_egale_kieme_en_un("t", "I")
    cible = egal(S.premier_terme(t, i), S.kieme_terme(t, i, UN))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_suite_multiple_identite_close():
    f, i, p = var("f"), var("I"), var("p")
    thm = S.suite_multiple_implique_suite_multiple("f", "I", "p")
    cible = impl(S.est_suite_multiple(f, i, p), S.est_suite_multiple(f, i, p))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_suite_double_identite_close():
    f, i = var("f"), var("I")
    thm = S.suite_double_implique_suite_double("f", "I")
    cible = impl(S.est_suite_double(f, i), S.est_suite_double(f, i))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── théorie_ensembles intangible (22 axiomes) ─────────────────────────────────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
