"""Tests §III.5.6 / §III.5.7 — NOTIONS arithmétiques complémentaires sur les entiers.

Vérifie : (1) toutes les DÉFINITIONS NEUVES se construisent (Terme/Formule bien formés) ;
(2) les SYNONYMIES de la Déf. 1 sont fidèles (multiple/divisible/diviseur = divise) ;
(3) les théorèmes DIRECTS de synonymie sont == cible exacte ET clos.

Tout le reste (existence/unicité de la division euclidienne, propriétés du
développement de base b, Cor. 3 « a^b entier ») repose sur l'arithmétique cardinale
binaire et/ou la récurrence (NON disponibles) → REPORTÉ (cf. docstrings du module).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl, libres_f
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_notions_complementaires import ensembles_entiers_notions_arith as A


# ── (1) DÉFINITIONS NEUVES se construisent ────────────────────────────────────
def test_definitions_arith_se_construisent():
    a, b, q, r, h = var("a"), var("b"), var("q"), var("r"), var("h")
    # §5.6 Déf. 1 — multiple / divisible / diviseur / quotient
    A.est_multiple(a, b)
    A.est_divisible_par(a, b)
    A.est_diviseur(b, a)
    A.quotient_a_sur_b(a, b)
    A.notation_quotient_implique_divise(a, b)
    A.partie_entiere_quotient(a, b)
    # §5.6 — division euclidienne (couple) + condition
    A.division_euclidienne(a, b)
    A.condition_division_euclidienne(a, b, q, r)
    # §5.1 Cor. 3 — puissance entiers
    A.puissance_entiers(a, b)
    # §5.7 — développement de base b
    A.est_chiffre(r, b)
    A.developpement_base_b(a, b)
    A.symbole_numerique(a, b)
    A.chiffre_de_rang(a, b, h)


# ── (2) SYNONYMIES de la Déf. 1 fidèles (= divise, notion existante réutilisée) ─
def test_multiple_est_divise():
    """est_multiple(a,b) est, verbatim, divise(b,a) (a multiple de b ⇔ b divise a)."""
    a, b = var("a"), var("b")
    assert A.est_multiple(a, b) == Ent.divise(b, a)
    assert A.est_divisible_par(a, b) == Ent.divise(b, a)
    assert A.est_diviseur(b, a) == Ent.divise(b, a)


def test_quotient_notation_est_quotient_division():
    """a/b et la partie entière réutilisent le quotient déjà posé (pas de doublon)."""
    a, b = var("a"), var("b")
    assert A.quotient_a_sur_b(a, b) == Ent.quotient_division(a, b)
    assert A.partie_entiere_quotient(a, b) == Ent.quotient_division(a, b)


def test_division_euclidienne_est_couple_q_r():
    """divmod(a,b) = (quotient_division, reste_division) — couple des notions posées."""
    a, b = var("a"), var("b")
    assert A.division_euclidienne(a, b) == E.couple(
        Ent.quotient_division(a, b), Ent.reste_division(a, b))


def test_puissance_entiers_est_exposant_cardinal():
    """a^b sur les entiers = exponentiation cardinale (Cor. 3 ; pas de doublon)."""
    a, b = var("a"), var("b")
    assert A.puissance_entiers(a, b) == exposant_cardinal_binaire(a, b)


# ── (3) THÉORÈMES DIRECTS (synonymies) — cible exacte + clos ───────────────────
def test_multiple_ssi_divise_clos():
    a, b = var("a"), var("b")
    thm = A.multiple_ssi_divise("a", "b")
    cible = impl(A.est_multiple(a, b), Ent.divise(b, a))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_divise_ssi_multiple_clos():
    a, b = var("a"), var("b")
    thm = A.divise_ssi_multiple("a", "b")
    cible = impl(Ent.divise(b, a), A.est_multiple(a, b))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_diviseur_et_divisible_clos():
    a, b = var("a"), var("b")
    t1 = A.diviseur_ssi_divise("a", "b")
    t2 = A.divisible_ssi_multiple("a", "b")
    assert t1.conclusion == impl(A.est_diviseur(b, a), Ent.divise(b, a))
    assert t2.conclusion == impl(A.est_divisible_par(a, b), A.est_multiple(a, b))
    assert t1.est_clos and t2.est_clos


# ── théorie_ensembles intangible (22 axiomes) — non touchée par ce module ──────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── chiffre / condition bien formés et clos ───────────────────────────────────
def test_est_chiffre_et_condition_bien_formes():
    r, b, q, a = var("r"), var("b"), var("q"), var("a")
    # est_chiffre(r,b) ne lie aucune variable parasite : r,b libres
    assert libres_f(A.est_chiffre(r, b)) == {"r", "b"}
    # condition de division : a,b,q,r libres
    assert libres_f(A.condition_division_euclidienne(a, b, q, r)) == {"a", "b", "q", "r"}
