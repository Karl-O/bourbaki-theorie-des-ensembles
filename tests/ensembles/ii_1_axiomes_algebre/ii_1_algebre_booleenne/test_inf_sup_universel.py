"""Tests §II.1 — PROPRIÉTÉS UNIVERSELLES de ∩ (inf) / ∪ (sup) BINAIRES (E.R.5 nº14 i).

    (Z⊂X et Z⊂Y) ⇔ Z⊂X∩Y   ;   (X⊂Z et Y⊂Z) ⇔ X∪Y⊂Z.

Honnêteté LCF : les théorèmes sont APPELÉS (un import ne prouve rien) ; conclusion
== cible (== structurelle, l'équivalence Bourbaki) ; est_clos == True pour les DEUX
(0 hypothèse, implications internes déchargées) ; pas de tautologie déguisée
(conclusion ≠ chacun de ses deux membres) ; theorie_ensembles() = 22 axiomes.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, et, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ii_1_algebre_booleenne.ensembles_inf_sup_universel as U

X, Y, Z = var("X"), var("Y"), var("Z")


def _cible_inf():
    return U.cible_inf_universel_binaire()


def _cible_sup():
    return U.cible_sup_universel_binaire()


# ── inf (∩) ───────────────────────────────────────────────────────────────────
def test_inf_conclusion_est_la_cible():
    t = U.inf_universel_binaire()
    assert t.conclusion == _cible_inf()


def test_inf_est_clos_zero_hypothese():
    t = U.inf_universel_binaire()
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_inf_pas_de_tautologie_deguisee():
    t = U.inf_universel_binaire()
    # le contenu est une caractérisation via ∩, pas une trivialité : les deux
    # membres de l'équivalence diffèrent réellement de la conclusion.
    membre_g = et(inclus(Z, X), inclus(Z, Y))
    membre_d = inclus(Z, E.intersection(X, Y))
    assert t.conclusion != membre_g
    assert t.conclusion != membre_d
    assert membre_g != membre_d


# ── sup (∪) ───────────────────────────────────────────────────────────────────
def test_sup_conclusion_est_la_cible():
    t = U.sup_universel_binaire()
    assert t.conclusion == _cible_sup()


def test_sup_est_clos_zero_hypothese():
    t = U.sup_universel_binaire()
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_sup_pas_de_tautologie_deguisee():
    t = U.sup_universel_binaire()
    membre_g = et(inclus(X, Z), inclus(Y, Z))
    membre_d = inclus(E.reunion(X, Y), Z)
    assert t.conclusion != membre_g
    assert t.conclusion != membre_d
    assert membre_g != membre_d


# ── invariant théorie ─────────────────────────────────────────────────────────
def test_theorie_inchangee_22():
    U.inf_universel_binaire()
    U.sup_universel_binaire()
    assert len(E.theorie_ensembles().axiomes) == 22
