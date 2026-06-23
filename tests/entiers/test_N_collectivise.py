"""Tests §III.6.1 — THÉORÈME 1 : « Fini(x) est collectivisante » (l'ensemble N existe).

Discipline LCF stricte : chaque test vérifie la CONCLUSION EXACTE (formule construite
indépendamment) et l'ensemble des HYPOTHÈSES (clos ou conditionné à l'unique report B).

INVARIANT vérifié : theorie_ensembles() reste = 22 (l'axiome de séparation Ncol est en
théorie DÉDIÉE).  La collectivisation de Fini est DÉMONTRÉE (= théorème), JAMAIS postulée.
"""
from bourbaki.logique.formule import (
    var, coll, pourtout, equiv, appartient, non, existe, et,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, ZERO
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence import ensembles_N_collectivise as M


# ── INVARIANT : theorie_ensembles() intangible = 22 ──────────────────────────
def test_theorie_ensembles_reste_22():
    """L'axiome de Ncol est en théorie DÉDIÉE ; theorie_ensembles() = 22 inchangé."""
    assert len(E.theorie_ensembles().axiomes) == 22
    assert len(M.theorie_Ncol().axiomes) == 1


# ── ÉTAPE A — un cardinal infini existe (INCONDITIONNEL, A4) ──────────────────
def test_cardinal_infini_existe_clos():
    """⊢ (∃a)¬Fini(a)  — il existe un cardinal infini ; CLOS (déchargé par A4)."""
    thm = M.cardinal_infini_existe("a")
    assert thm.est_clos
    assert thm.conclusion == existe("a", non(est_fini(var("a"))))


# ── ÉTAPE C — tout entier n ≤ a  (sous A + B + Fini(n)) ───────────────────────
def test_entier_inf_egal_a_conclusion():
    """⊢ { ¬Fini(a), fini_downward(a,n), Fini(n) } ⊢ n ≤ a."""
    va, vn = var("a"), var("n")
    thm = M.entier_inf_egal_a(va, "n")
    assert thm.conclusion == inf_egal_card(vn, va)
    attendues = {
        non(est_fini(va)),
        M.fini_downward(va, vn),
        est_fini(vn),
    }
    assert set(thm.hypotheses) == attendues


# ── borne 0 : 0 ≤ x pour x cardinal ──────────────────────────────────────────
def test_zero_inf_egal_cardinal():
    """⊢ { est_cardinal(x) } ⊢ 0 ≤ x."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal
    vx = var("x")
    thm = M.zero_inf_egal_cardinal("x")
    assert thm.conclusion == inf_egal_card(ZERO, vx)
    assert set(thm.hypotheses) == {est_cardinal(vx)}


# ── ÉTAPE D — séparation Ncol(a) (axiome de membership, S8 dans [0,a]) ─────────
def test_Ncol_membre_clos():
    """⊢ ( x ∈ Ncol(a) ) ⇔ ( x ∈ [0,a] et Fini(x) )  — axiome instancié, CLOS."""
    thm = M.Ncol_membre("a", "x")
    assert thm.est_clos
    va, vx = var("a"), var("x")
    cible = equiv(appartient(vx, M.Ncol(va)),
                  et(appartient(vx, E.intervalle_entiers(ZERO, va)), est_fini(vx)))
    assert thm.conclusion == cible


def test_fini_implique_dans_intervalle():
    """⊢ { ¬Fini(a), fini_downward(a,x), Fini(x) } ⊢ x ∈ [0,a]."""
    va, vx = var("a"), var("x")
    thm = M.fini_implique_dans_intervalle(va, "x")
    assert thm.conclusion == appartient(vx, E.intervalle_entiers(ZERO, va))
    assert len(thm.hypotheses) == 3


# ── ÉTAPE E — Ncol(a) collectivise Fini ──────────────────────────────────────
def test_Ncol_equivaut_fini():
    """⊢ { ¬Fini(a), (∀x)fini_downward(a,x) } ⊢ (∀x)( x∈Ncol(a) ⇔ Fini(x) )."""
    va, vx = var("a"), var("x")
    thm = M.Ncol_equivaut_fini(va, "x")
    cible = pourtout("x", equiv(appartient(vx, M.Ncol(va)), est_fini(vx)))
    assert thm.conclusion == cible
    attendues = {non(est_fini(va)), pourtout("x", M.fini_downward(va, vx))}
    assert set(thm.hypotheses) == attendues


# ── sous-théorème : coll sous (¬Fini(a), (∀x)dwn(a,x)) ────────────────────────
def test_N_collectivise_sous_cardinal():
    """⊢ { ¬Fini(a), (∀x)fini_downward(a,x) } ⊢ coll(x, Fini(x))."""
    va, vx = var("a"), var("x")
    thm = M.N_collectivise_sous_cardinal("a", "x", "y")
    assert thm.conclusion == coll("x", est_fini(vx))
    attendues = {non(est_fini(va)), pourtout("x", M.fini_downward(va, vx))}
    assert set(thm.hypotheses) == attendues


# ── 🎯 THÉORÈME 1 — Fini est collectivisante (sous l'unique report B) ─────────
def test_N_collectivise_theoreme():
    """⊢ { (∀a)(∀x)fini_downward(a,x) } ⊢ coll(x, Fini(x))   (l'ensemble N existe).

    Conclusion EXACTE = coll(x, Fini(x)) = (∃Y)(∀x)(x∈Y ⇔ Fini(x)).  UNIQUE hypothèse
    = la downward-closure de Fini (ÉTAPE B, REPORTÉE).  Tout le reste (A, C, D, E) est
    déchargé."""
    thm = M.N_collectivise()
    assert thm.conclusion == coll("x", est_fini(var("x")))
    unique = pourtout("a", pourtout("x", M.fini_downward(var("a"), var("x"))))
    assert set(thm.hypotheses) == {unique}


def test_N_collectivise_ne_postule_pas_la_collectivisation():
    """La collectivisation de Fini n'est PAS un axiome : aucune théorie ne la contient.

    theorie_Ncol contient SEULEMENT la séparation Ncol(a)={x∈[0,a]|Fini x} (S8), PAS
    coll(x,Fini x).  La collectivisation est le THÉORÈME N_collectivise (conditionné B)."""
    coll_fini = coll("x", est_fini(var("x")))
    for ax in M.theorie_Ncol().axiomes:
        assert ax != coll_fini
    assert len(E.theorie_ensembles().axiomes) == 22
