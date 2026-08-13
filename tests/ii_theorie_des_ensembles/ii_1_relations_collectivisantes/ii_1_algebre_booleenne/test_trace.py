"""Tests Résumé E.R.5 n°16 — TRACE X_A = A∩X et ses identités (LCF).

Honnêteté LCF : la définition est la NOTATION A∩X (forme du terme vérifiée) ;
chaque identité est un théorème dont la conclusion est l'ÉGALITÉ FIDÈLE exprimée
via `trace(...)` (== cible STRUCTURELLE), avec son statut de clôture exact :
  (1) trace_reunion, (2) trace_intersection : CLOSES (0 hyp) ;
  (3) trace_complement : NON close, hypothèse EXACTE inclus(A, E).
theorie = 22, aucune théorie dédiée / S8.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_trace as M

A, X, Y, Ev = var("A"), var("X"), var("Y"), var("E")
U, I, D = E.reunion, E.intersection, E.difference


# ── DÉFINITION (forme du terme) ───────────────────────────────────────────────
def test_trace_forme():
    """trace(X, A) EST le terme A∩X (pure notation)."""
    assert M.trace(X, A) == I(A, X)
    assert M.trace(X, A) == E.intersection(A, X)


# ── IDENTITÉ (1) : trace(X∪Y, A) = trace(X,A) ∪ trace(Y,A) ────────────────────
def test_trace_reunion():
    t = M.trace_reunion()
    # cible STRUCTURELLE, exprimée via trace(...)
    cible = egal(M.trace(U(X, Y), A), U(M.trace(X, A), M.trace(Y, A)))
    assert t.conclusion == cible
    assert t.est_clos and not t.hypotheses           # CLOSE
    lhs, rhs = t.conclusion.termes
    assert lhs != rhs                                # égalité NON triviale


def test_trace_reunion_reutilise_distributivite():
    """(1) est STRUCTURELLEMENT la loi distributivite_intersection_reunion(A,X,Y)."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne import (
        distributivite_intersection_reunion as distrib)
    assert M.trace_reunion().conclusion == distrib(A, X, Y).conclusion
    # et la cible coïncide bien avec A∩(X∪Y) = (A∩X)∪(A∩Y)
    assert M.trace(U(X, Y), A) == I(A, U(X, Y))
    assert U(M.trace(X, A), M.trace(Y, A)) == U(I(A, X), I(A, Y))


# ── IDENTITÉ (2) : trace(X∩Y, A) = trace(X,A) ∩ trace(Y,A) ────────────────────
def test_trace_intersection():
    t = M.trace_intersection()
    cible = egal(M.trace(I(X, Y), A), I(M.trace(X, A), M.trace(Y, A)))
    assert t.conclusion == cible
    assert t.est_clos and not t.hypotheses           # CLOSE
    lhs, rhs = t.conclusion.termes
    assert lhs != rhs                                # A∩(X∩Y) ≠ (A∩X)∩(A∩Y) (structurel)


# ── IDENTITÉ (3) : ∁_A X_A = (∁_E X)_A  — NON close, hyp. inclus(A,E) ──────────
def test_trace_complement():
    t = M.trace_complement()
    cible = egal(D(A, M.trace(X, A)), M.trace(D(Ev, X), A))   # A∖(A∩X) = A∩(E∖X)
    assert t.conclusion == cible
    assert not t.est_clos                            # NON close
    assert t.hypotheses == frozenset({inclus(A, Ev)})  # hypothèse EXACTE A⊂E
    lhs, rhs = t.conclusion.termes
    assert lhs != rhs


# ── invariant : theorie == 22 (aucune théorie dédiée / S8) ────────────────────
def test_theorie_inchangee_22():
    for f in M.__all__:
        if f == "trace":
            continue                                  # def = terme, pas un théorème
        getattr(M, f)()
    assert len(E.theorie_ensembles().axiomes) == 22
