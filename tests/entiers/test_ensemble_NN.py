"""Tests — §III.6.1 : ℕ COMME OBJET CONCRET (le set NN = τy(∀x)(x∈y⇔Fini x)).

NN est NOMMÉ par τ à partir de la collectivisation DÉJÀ PROUVÉE (N_existe, 0 hyp).  Ses
propriétés sont DÉRIVÉES (jamais postulées) via l'axiome-τ (existe_temoin) :
  • appartenance_NN   ⊢ (∀x)( x∈NN ⇔ Fini x )            [CLOS] — la caractérisation ;
  • zero_dans_NN      ⊢ 0 ∈ NN                            [CLOS] ;
  • NN_clos_successeur⊢ (∀n)( n∈NN ⇒ successeur(n)∈NN )  [CLOS] — stabilité (Peano).
theorie_ensembles() = 22 (rien postulé).

⚠️ PERF : la première construction de N_existe (~5 min, τ-cardinaux imbriqués) est
MÉMOÏSÉE (lru_cache) ; un fixture session-scope la déclenche une seule fois et tous les
tests réutilisent les théorèmes."""
import pytest

from bourbaki.logique.formule import (
    var, tau, equiv, impl, appartient, pourtout, libres_t,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO

import bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN as M


# ────────────────────────────────────────────────────────────────────────────
#  Fixtures session-scope : on construit chaque théorème UNE fois (N_existe lent).
# ────────────────────────────────────────────────────────────────────────────
@pytest.fixture(scope="module")
def NN():
    return M.ensemble_NN()


@pytest.fixture(scope="module")
def ap():
    return M.appartenance_NN()


@pytest.fixture(scope="module")
def z0():
    return M.zero_dans_NN()


@pytest.fixture(scope="module")
def succ_clos():
    return M.NN_clos_successeur()


# ────────────────────────────────────────────────────────────────────────────
#  INVARIANT : theorie inchangée = 22
# ────────────────────────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  1. DÉFINITION — NN est un terme CLOS (constant), = τy(∀x)(x∈y⇔Fini x)
# ────────────────────────────────────────────────────────────────────────────
def test_ensemble_NN_est_tau_clos(NN):
    assert NN.tag == "tau"
    # AUCUNE variable libre : NN est un véritable CONSTANT (l'ensemble ℕ).
    assert libres_t(NN) == set()
    # le corps du τ EST exactement (∀x)( x∈y ⇔ Fini x ) (le binder τ étant « y »).
    corps_attendu = pourtout("x", equiv(appartient(var("x"), var("y")), est_fini(var("x"))))
    assert NN.lieur == "y"
    assert NN.args[0] == corps_attendu


# ────────────────────────────────────────────────────────────────────────────
#  2. CARACTÉRISATION — (∀x)( x∈NN ⇔ Fini x ), CLOSE, DÉRIVÉE de N_existe
# ────────────────────────────────────────────────────────────────────────────
def test_appartenance_NN_close(ap):
    assert ap.est_clos and len(ap.hypotheses) == 0


def test_appartenance_NN_conclusion_exacte(ap, NN):
    """conclusion = (∀x)( x∈NN ⇔ Fini x ) — la VRAIE caractérisation, PAS une tautologie."""
    attendu = pourtout("x", equiv(appartient(var("x"), NN), est_fini(var("x"))))
    assert ap.conclusion == attendu
    # NON-vacuité : la conclusion n'est aucune hypothèse (il n'y en a aucune) et n'est
    # pas un trivial P⇔P (le membre gauche x∈NN diffère du membre droit Fini x).
    assert ap.conclusion not in ap.hypotheses
    # NON-trivialité : les deux membres de l'équivalence sont DIFFÉRENTS (x∈NN vs Fini x),
    # donc ce n'est pas un vacuous P⇔P.
    gauche = appartient(var("x"), NN)
    droite = est_fini(var("x"))
    assert gauche != droite
    # et la conclusion EST l'équivalence de CES deux membres (déjà vérifié == attendu).
    assert attendu == pourtout("x", equiv(gauche, droite))


def test_appartenance_NN_derivee_de_N_existe(ap):
    """La caractérisation est DÉRIVÉE de N_existe (coll), PAS supposée : elle utilise
    l'axiome-τ existe_temoin dont l'antécédent est EXACTEMENT coll(x, Fini x)."""
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import _coll_fini
    from bourbaki.logique import noyau_abrege as N
    R = _coll_fini("x").sous[0]
    ax_tau = N.existe_temoin(R, "y")                       # (∃y)R ⇒ (τy R | y)R
    # l'antécédent de l'axiome-τ EST coll(x, Fini x), la chose prouvée par N_existe
    assert ax_tau.conclusion.sous[0].sous[0] == _coll_fini("x")
    # et le conséquent EST la conclusion de appartenance_NN (caractérisation)
    assert ax_tau.conclusion.sous[1] == ap.conclusion


def test_appartenance_NN_instanciee(ap):
    equ0 = M.appartenance_NN_instanciee(ZERO)
    assert equ0.est_clos and len(equ0.hypotheses) == 0
    assert equ0.conclusion == equiv(appartient(ZERO, M.ensemble_NN()), est_fini(ZERO))


# ────────────────────────────────────────────────────────────────────────────
#  3. 0 ∈ NN  (CLOS)
# ────────────────────────────────────────────────────────────────────────────
def test_zero_dans_NN_close(z0):
    assert z0.est_clos and len(z0.hypotheses) == 0


def test_zero_dans_NN_conclusion(z0, NN):
    assert z0.conclusion == appartient(ZERO, NN)
    assert z0.conclusion not in z0.hypotheses


# ────────────────────────────────────────────────────────────────────────────
#  4. NN stable par successeur :  (∀n)( n∈NN ⇒ successeur(n)∈NN )  (CLOS)
# ────────────────────────────────────────────────────────────────────────────
def test_NN_clos_successeur_close(succ_clos):
    assert succ_clos.est_clos and len(succ_clos.hypotheses) == 0


def test_NN_clos_successeur_conclusion(succ_clos, NN):
    vn = var("n")
    attendu = pourtout("n", impl(appartient(vn, NN), appartient(successeur(vn), NN)))
    assert succ_clos.conclusion == attendu
    assert succ_clos.conclusion not in succ_clos.hypotheses
    # NON-vacuité : antécédent (n∈NN) ≠ conséquent (succ(n)∈NN).
    assert appartient(vn, NN) != appartient(successeur(vn), NN)


# ────────────────────────────────────────────────────────────────────────────
#  Invariant final : rien postulé
# ────────────────────────────────────────────────────────────────────────────
def test_theorie_22_apres(ap, z0, succ_clos):
    assert len(E.theorie_ensembles().axiomes) == 22
