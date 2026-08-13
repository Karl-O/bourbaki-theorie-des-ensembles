"""Tests V9 — §I.5.3 critère C46 (« R fonctionnelle ⇔ x = τ_x(R) »), E.I.41 L.24-36.

C46 est un MÉTATHÉORÈME (critère chap. I) réalisé en fonctions-schémas vérifiables
(c46_avant / c46_arriere) : pour R concret elles ÉMETTENT une dérivation du noyau.
Les tests appellent réellement les livrables et comparent par égalité STRUCTURELLE.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, tau, equiv, et, existe, subst_f, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_3_relations_fonctionnelles_c45 import (
    relation_fonctionnelle_en_x, c45_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_3_relations_fonctionnelles_c46_c47 import (
    c46_avant, c46_arriere, c47_equivalence,
)

# Relation de travail : R = (x = a) — fonctionnelle en x (témoin a, univoque).
X = "x"
R = egal(var("x"), var("a"))
T = var("a")                                            # terme ne contenant pas x


def _thm_fonctionnelle(y="y", z="z"):
    """⊢ relation_fonctionnelle_en_x(R, x) CLOS : (∃x)R [témoin a] et univoque [C45 rec.]."""
    exR = N.modus_ponens(N.reflexivite(var("a")), N.s5(R, var("a"), X))   # ⊢ (∃x)R
    uni = c45_arriere(R, X, T, a_implique_a(R), y, z)                     # ⊢ univoque(R)
    return conjonction_intro(exR, uni)


# ── C46 sens DIRECT ───────────────────────────────────────────────────────────

def test_c46_avant_produit_equivalence():
    """De ⊢ « R fonctionnelle » produit ⊢ R ⇔ (x=τ_x(R)), CLOS."""
    thm_fonc = _thm_fonctionnelle("y", "z")
    assert thm_fonc.conclusion == relation_fonctionnelle_en_x(R, X, "y", "z")
    res = c46_avant(R, X, thm_fonc, "y", "z")
    assert res.conclusion == equiv(R, egal(var(X), tau(X, R)))
    assert res.est_clos and not res.hypotheses
    assert isinstance(res, N.Theoreme)


def test_c46_avant_refuse_hypothese_non_fonctionnelle():
    """thm_fonc doit être CLOS et conclure « R fonctionnelle » (mêmes lettres fraîches)."""
    import pytest
    with pytest.raises(ValueError):
        c46_avant(R, X, a_implique_a(R), "y", "z")      # pas la forme fonctionnelle


# ── C46 sens RÉCIPROQUE ───────────────────────────────────────────────────────

def test_c46_arriere_produit_fonctionnelle():
    """De ⊢ (R ⇔ (x=T)) [T sans x] produit ⊢ « R fonctionnelle en x », CLOS."""
    thm_equiv = conjonction_intro(a_implique_a(R), a_implique_a(R))       # R ⇔ (x=a)
    assert thm_equiv.conclusion == equiv(R, egal(var(X), T))
    res = c46_arriere(R, X, T, thm_equiv)
    # conclusion == (∃x)R et relation_univoque_x(R) (lettres fraîches internes)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, existe
    assert res.conclusion.tag == et(existe(X, R), R).tag                  # une conjonction
    assert res.conclusion.sous is not None
    assert res.est_clos and not res.hypotheses
    assert isinstance(res, N.Theoreme)


def test_c46_arriere_refuse_T_contient_x():
    """Garde de fidélité : T ne doit pas contenir x ; thm doit conclure R ⇔ (x=T)."""
    import pytest
    thm_equiv = conjonction_intro(a_implique_a(R), a_implique_a(R))
    with pytest.raises(ValueError):
        c46_arriere(R, X, var("x"), thm_equiv)          # T = x interdit
    with pytest.raises(ValueError):
        c46_arriere(R, X, T, a_implique_a(R))           # thm n'est pas une équivalence R⇔(x=T)


# ── C47 : S{τ_x(R)} ⇔ (∃x)(R et S) ────────────────────────────────────────────

def test_c47_equivalence_forme_exacte():
    """De ⊢ « R fonctionnelle » produit ⊢ S{τ_x(R)} ⇔ (∃x)(R et S), CLOS.
    Ici R := (x=a) (fonctionnelle), S := (x ∈ b)."""
    S = appartient(var("x"), var("b"))
    thm_fonc = _thm_fonctionnelle("y", "z")
    res = c47_equivalence(R, X, S, thm_fonc, "y", "z")
    t = tau(X, R)
    cible = equiv(subst_f(t, X, S), existe(X, et(R, S)))
    assert res.conclusion == cible
    assert res.est_clos and not res.hypotheses
    assert isinstance(res, N.Theoreme)
