"""Tests §III.6 — Ensembles infinis : A4, définitions, théorèmes DIRECTS.

Chaque test vérifie que la CONCLUSION du Theoreme renvoyé == la cible EXACTE
attendue (formule construite indépendamment) ET que le théorème est CLOS (⊢ sans
hypothèse), conformément à la discipline LCF stricte du projet.
"""
from formule import var, egal, et, non, impl, equiv, existe, inclus
import noyau_abrege as N
import ensembles_infinis as I
import ensembles_infinis_theoremes as T
from ensembles_entiers import est_fini_ensemble


# ── A4 : axiome de l'infini ───────────────────────────────────────────────────
def test_A4_est_axiome_valide():
    """A4 est bien un axiome de theorie_infini() ; N.axiome le certifie."""
    ax = N.axiome(I.theorie_infini(), I.A4)
    assert ax.est_clos
    assert ax.conclusion == I.A4


def test_A4_enonce_il_existe_un_ensemble_infini():
    """A4 = (∃X) ¬Fini(Card(X)) = (∃X)(X est infini)  (énoncé verbatim §III.6.1)."""
    cible = existe("X", non(est_fini_ensemble(var("X"))))
    assert I.A4 == cible


def test_existe_ensemble_infini():
    """⊢ (∃X) ¬Fini(Card(X))  — A4 exhibé comme théorème."""
    thm = T.existe_ensemble_infini()
    assert thm.est_clos
    assert thm.conclusion == I.A4


# ── Déf. 1 : infini = non fini ────────────────────────────────────────────────
def test_infini_non_fini():
    """⊢ (E infini) ⇒ ¬Fini(Card(E))."""
    thm = T.infini_non_fini("E")
    assert thm.est_clos
    cible = impl(I.est_infini_ensemble(var("E")), I.est_infini_ensemble(var("E")))
    assert thm.conclusion == cible


def test_infini_ssi_non_fini():
    """⊢ (E infini) ⇔ ¬Fini(Card(E))  (équivalence définitionnelle A⇔A)."""
    thm = T.infini_ssi_non_fini("E")
    assert thm.est_clos
    P = I.est_infini_ensemble(var("E"))
    assert thm.conclusion == equiv(P, P)


def test_est_infini_ensemble_est_negation_de_fini():
    """est_infini_ensemble(E) est LITTÉRALEMENT ¬est_fini_ensemble(E) (Déf. 1)."""
    assert I.est_infini_ensemble(var("E")) == non(est_fini_ensemble(var("E")))


# ── Déf. 1 (niveau cardinal) : 𝔞 infini ⇔ ¬Fini(𝔞) ───────────────────────────
def test_cardinal_infini_ssi_non_fini():
    """⊢ (𝔞 infini) ⇔ ¬Fini(𝔞)  (Déf. 1 §III.6.1, niveau cardinal, A⇔A) — clos."""
    from ensembles_entiers import est_fini
    a = var("a")
    thm = T.cardinal_infini_ssi_non_fini("a")
    assert thm.est_clos
    P = I.est_infini(a)                    # = ¬Fini(𝔞)
    assert thm.conclusion == equiv(P, P)
    assert I.est_infini(a) == non(est_fini(a))   # fidélité Déf. 1 (cardinal)


def test_fini_implique_cardinal_non_infini():
    """⊢ Fini(𝔞) ⇒ ¬(𝔞 infini)  (un cardinal fini n'est pas infini) — clos."""
    from ensembles_entiers import est_fini
    a = var("a")
    thm = T.fini_implique_cardinal_non_infini("a")
    assert thm.est_clos
    assert thm.conclusion == impl(est_fini(a), non(I.est_infini(a)))


# ── Déf. 2 : suites ───────────────────────────────────────────────────────────
def test_suite_infinie_est_suite():
    """⊢ (suite infinie d'indices I) ⇒ (suite d'indices I)."""
    thm = T.suite_infinie_est_suite("f", "I")
    assert thm.est_clos
    cible = impl(I.est_suite_infinie("f", "I"), I.est_suite("f", "I"))
    assert thm.conclusion == cible


def test_suite_infinie_indices_infinis():
    """⊢ (suite infinie d'indices I) ⇒ (I est infini)."""
    thm = T.suite_infinie_indices_infinis("f", "I")
    assert thm.est_clos
    cible = impl(I.est_suite_infinie("f", "I"), I.est_infini_ensemble(var("I")))
    assert thm.conclusion == cible


# ── Définitions : bonne construction (clôture, structure attendue) ────────────
def test_denombrable_verbatim():
    """est_denombrable(E) = (∃Y)(Y⊂N et Eq(E,Y))  (Déf. 3 verbatim)."""
    from ensembles_cardinaux import equipotent
    vY = var("Y")
    cible = existe("Y", et(inclus(vY, I.NN), equipotent(var("E"), vY)))
    assert I.est_denombrable("E") == cible


def test_puissance_continu_verbatim():
    """a_puissance_continu(E) = Eq(E, P(N))  (Déf. 4 verbatim)."""
    from ensembles_cardinaux import equipotent
    import ensembles_abrege as E
    assert I.a_puissance_continu("E") == equipotent(var("E"), E.parties(I.NN))


def test_stationnaire_est_clos_et_existentiel():
    """est_stationnaire((x_n)) commence par (∃m) (Déf. 5)."""
    f = I.est_stationnaire("f")
    # (∃m)(...) — la formule abrégée est un ∃ sur m
    assert f.tag == "exists" and f.lieur == "m"


def test_aleph0_est_card_de_N():
    """ℵ₀ = Card(N)."""
    from ensembles_cardinaux import cardinal
    assert I.aleph0() == cardinal(I.NN)
