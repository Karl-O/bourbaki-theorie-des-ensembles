"""Tests — §III.4.2 PROPOSITIONS sur les ENSEMBLES FINIS (atteignables sans récurrence).

Module testé : bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props.

On vérifie pour chaque théorème INCONDITIONNEL qu'il est CLOS (aucune hypothèse
résiduelle) et que sa CONCLUSION est EXACTEMENT l'énoncé attendu (le noyau certifie ;
on contrôle la FORME — anti-affaibli/anti-tautologie).  Pour les énoncés REPORTÉS on
contrôle la formule-cible ; pour les formes CONDITIONNELLES, l'implication report ⇒
conclusion.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, ou, non, impl, inclus
from bourbaki.cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal, cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import (
    fini_implique_inf_egal_reflexif,
    antisymetrie_card_egal,
    antisymetrie_cardinaux,
    comparabilite_finis,
    transitivite_inf_egal_finis,
    inf_strict_exclut_reciproque,
    inf_strict_irreflexif,
    inf_strict_transitif,
    trichotomie_finis,
    partie_inf_egal_card,
    cor1_partie_finie_est_finie_conditionnel,
    prop2_cardinal_inf_n_est_entier,
    cor2_partie_stricte_card_strict,
)

_a, _b, _c = var("a"), var("b"), var("c")
_X, _E, _n = var("X"), var("E"), var("n")


def _clos(thm):
    """Le théorème ne porte aucune hypothèse résiduelle."""
    return not thm.hypotheses


# ══════════════════════════════════════════════════════════════════════════════
#  INCONDITIONNELS — propriétés directes de ≤ / < pour les cardinaux (finis incl.)
# ══════════════════════════════════════════════════════════════════════════════
def test_fini_implique_inf_egal_reflexif_clos():
    thm = fini_implique_inf_egal_reflexif("a")
    assert _clos(thm)
    # Fini(a) ⇒ (a ≤ a)
    assert thm.conclusion == impl(est_fini(_a), inf_egal_card(_a, _a))


def test_antisymetrie_card_egal_clos():
    thm = antisymetrie_card_egal("a", "b")
    assert _clos(thm)
    # (a≤b et b≤a) ⇒ Card a = Card b   (Cantor–Bernstein + Prop. 1)
    assert thm.conclusion == impl(et(inf_egal_card(_a, _b), inf_egal_card(_b, _a)),
                                  egal(cardinal(_a), cardinal(_b)))


def test_antisymetrie_cardinaux_clos():
    thm = antisymetrie_cardinaux("a", "b")
    assert _clos(thm)
    # (est_card a et est_card b et a≤b et b≤a) ⇒ a = b
    ante = et(et(et(est_cardinal(_a), est_cardinal(_b)),
                 inf_egal_card(_a, _b)), inf_egal_card(_b, _a))
    assert thm.conclusion == impl(ante, egal(_a, _b))


def test_comparabilite_finis_clos():
    thm = comparabilite_finis("a", "b")
    assert _clos(thm)
    # a ≤ b OU b ≤ a   (ordre total)
    assert thm.conclusion == ou(inf_egal_card(_a, _b), inf_egal_card(_b, _a))


def test_transitivite_inf_egal_finis_clos():
    thm = transitivite_inf_egal_finis("a", "b", "c")
    assert _clos(thm)
    # (a≤b et b≤c) ⇒ a≤c
    assert thm.conclusion == impl(et(inf_egal_card(_a, _b), inf_egal_card(_b, _c)),
                                  inf_egal_card(_a, _c))


def test_inf_strict_exclut_reciproque_clos():
    thm = inf_strict_exclut_reciproque("a", "b")
    assert _clos(thm)
    # est_card(a) ⇒ (est_card(b) ⇒ ((a<b) ⇒ ¬(b≤a)))   (ASYMÉTRIE du <)
    assert thm.conclusion == impl(
        est_cardinal(_a),
        impl(est_cardinal(_b),
             impl(inf_strict_card(_a, _b), non(inf_egal_card(_b, _a)))))


def test_inf_strict_irreflexif_clos():
    thm = inf_strict_irreflexif("a")
    assert _clos(thm)
    # ¬(a < a)
    assert thm.conclusion == non(inf_strict_card(_a, _a))


def test_inf_strict_transitif_clos():
    thm = inf_strict_transitif("a", "b", "c")
    assert _clos(thm)
    # est_card(b) ⇒ (est_card(c) ⇒ ((a<b et b<c) ⇒ a<c))
    assert thm.conclusion == impl(
        est_cardinal(_b),
        impl(est_cardinal(_c),
             impl(et(inf_strict_card(_a, _b), inf_strict_card(_b, _c)),
                  inf_strict_card(_a, _c))))


def test_trichotomie_finis_clos():
    thm = trichotomie_finis("a", "b")
    assert _clos(thm)
    # (a<b) OU ((a=b) OU (b<a))   (TRICHOTOMIE)
    assert thm.conclusion == ou(inf_strict_card(_a, _b),
                                ou(egal(_a, _b), inf_strict_card(_b, _a)))


def test_partie_inf_egal_card_clos():
    thm = partie_inf_egal_card("X", "E")
    assert _clos(thm)
    # (X ⊂ E) ⇒ (X ≤ E)   (une partie a un cardinal ≤)
    assert thm.conclusion == impl(inclus(_X, _E), inf_egal_card(_X, _E))


# ══════════════════════════════════════════════════════════════════════════════
#  CONDITIONNEL au contenu non trivial — COROLLAIRE 1 (report fini_downward déchargé)
# ══════════════════════════════════════════════════════════════════════════════
def test_cor1_partie_finie_est_finie_conditionnel_clos():
    thm = cor1_partie_finie_est_finie_conditionnel("X", "E")
    assert _clos(thm)
    cX, cE = cardinal(_X), cardinal(_E)
    # H = (Card X ≤ Card E et Fini(Card E)) ⇒ Fini(Card X)   (report Prop. 2 instancié)
    H = impl(et(inf_egal_card(cX, cE), est_fini(cE)), est_fini(cX))
    # conclusion = H ⇒ ((X⊂E et Fini(Card E)) ⇒ Fini(Card X))
    consequent = impl(et(inclus(_X, _E), est_fini(cE)), est_fini(cX))
    assert thm.conclusion == impl(H, consequent)


def test_cor1_conditionnel_n_est_pas_tautologie_PimpP():
    """L'implication n'est PAS H ⇒ H : l'antécédent (report Prop. 2 instancié) DIFFÈRE
    du conséquent (l'énoncé du Corollaire 1) — contenu réel via partie_inf_egal_card +
    pont Eq.  Garde-fou anti-tautologie."""
    thm = cor1_partie_finie_est_finie_conditionnel("X", "E")
    ante = thm.conclusion.sous[0].sous[0]   # H  (impl encodé ou(non H, conseq))
    conseq = thm.conclusion.sous[1]
    assert ante != conseq, "le conditionnel s'est effondré en tautologie H⇒H"


# ══════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS REPORTÉS (formules-cibles — PAS des théorèmes ; on vérifie la forme)
# ══════════════════════════════════════════════════════════════════════════════
def test_prop2_cardinal_inf_n_est_entier_enonce():
    f = prop2_cardinal_inf_n_est_entier("a", "n")
    # (a ≤ n et Fini n) ⇒ Fini a   (énoncé de la Proposition 2, reporté)
    assert f == impl(et(inf_egal_card(_a, _n), est_fini(_n)), est_fini(_a))


def test_cor2_partie_stricte_card_strict_enonce():
    f = cor2_partie_stricte_card_strict("X", "E")
    cX, cE = cardinal(_X), cardinal(_E)
    # (X⊂E et X≠E et Fini(Card E)) ⇒ Card X < Card E   (Corollaire 2, reporté)
    assert f == impl(et(et(inclus(_X, _E), non(egal(_X, _E))), est_fini(cE)),
                     inf_strict_card(cX, cE))


# ══════════════════════════════════════════════════════════════════════════════
#  GARDE-FOU GLOBAL — theorie_ensembles() reste à 22 axiomes (intangible)
# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_reste_22():
    from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
    assert len(E.theorie_ensembles().axiomes) == 22
