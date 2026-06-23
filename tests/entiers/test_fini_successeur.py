"""Tests — §III.4.1 PROPOSITION 1 : ⊢ est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞+1)).

On vérifie que chaque lemme du module ensembles_fini_successeur est CLOS (aucune
hypothèse résiduelle, sauf indication contraire) et que sa CONCLUSION est exactement
l'énoncé attendu (le noyau certifie ; on contrôle la forme).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, non, et, impl, equiv
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, est_fini
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    cardinal_de_cardinal, successeur_est_un_cardinal,
    distinct_implique_succ_egal, succ_egal_implique_distinct,
    fini_implique_fini_successeur, fini_successeur_implique_fini,
    fini_ssi_fini_successeur)


_A = var("a")
_SUCC = successeur(_A)              # 𝔞 + 1
_SUCC2 = successeur(_SUCC)          # 𝔞 + 2


def _clos(thm):
    """Le théorème ne porte aucune hypothèse résiduelle."""
    return not thm.hypotheses


# ── Lemmes de support ─────────────────────────────────────────────────────────
def test_cardinal_de_cardinal_clos():
    thm = cardinal_de_cardinal("a")
    assert _clos(thm)
    assert thm.conclusion == impl(est_cardinal(_A), egal(cardinal(_A), _A))


def test_successeur_est_un_cardinal_clos():
    thm = successeur_est_un_cardinal("a")
    assert _clos(thm)
    assert thm.conclusion == est_cardinal(_SUCC)


def test_distinct_implique_succ_egal_clos():
    thm = distinct_implique_succ_egal("a")
    assert _clos(thm)
    # (𝔞 = 𝔞+1) ⇒ (𝔞+1 = 𝔞+2)
    assert thm.conclusion == impl(egal(_A, _SUCC), egal(_SUCC, _SUCC2))


def test_succ_egal_implique_distinct_clos():
    thm = succ_egal_implique_distinct("a")
    assert _clos(thm)
    # est_cardinal(𝔞) ⇒ ((𝔞+1 = 𝔞+2) ⇒ (𝔞 = 𝔞+1))
    assert thm.conclusion == impl(est_cardinal(_A),
                                  impl(egal(_SUCC, _SUCC2), egal(_A, _SUCC)))


# ── Les deux sens de la Proposition 1 ─────────────────────────────────────────
def test_fini_implique_fini_successeur_clos():
    thm = fini_implique_fini_successeur("a")
    assert _clos(thm)
    # Fini(𝔞) ⇒ Fini(𝔞+1)   (sens DIRECT, inconditionnel)
    assert thm.conclusion == impl(est_fini(_A), est_fini(_SUCC))


def test_fini_successeur_implique_fini_clos():
    thm = fini_successeur_implique_fini("a")
    assert _clos(thm)
    # est_cardinal(𝔞) ⇒ (Fini(𝔞+1) ⇒ Fini(𝔞))   (sens RÉCIPROQUE)
    assert thm.conclusion == impl(est_cardinal(_A),
                                  impl(est_fini(_SUCC), est_fini(_A)))


# ── PROPOSITION 1 (complète) ──────────────────────────────────────────────────
def test_fini_ssi_fini_successeur_clos():
    thm = fini_ssi_fini_successeur("a")
    assert _clos(thm)
    # est_cardinal(𝔞) ⇒ (Fini(𝔞) ⇔ Fini(𝔞+1))
    assert thm.conclusion == impl(est_cardinal(_A),
                                  equiv(est_fini(_A), est_fini(_SUCC)))


def test_proposition_1_est_bien_une_equivalence():
    """La conclusion sous est_cardinal(𝔞) est littéralement la conjonction des deux
    implications (Fini(𝔞)⇒Fini(𝔞+1)) et (Fini(𝔞+1)⇒Fini(𝔞)) — la forme ⇔."""
    thm = fini_ssi_fini_successeur("a")
    # le conséquent de l'implication est l'équivalence et(impl(f,s), impl(s,f))
    consequent = thm.conclusion.sous[1]      # ou(¬est_cardinal, équiv) : sous[1] = équiv
    assert consequent == et(impl(est_fini(_A), est_fini(_SUCC)),
                            impl(est_fini(_SUCC), est_fini(_A)))
