"""Résumé E.R.5 n°16 — TRACE d'une partie X sur une partie A : X_A := A ∩ X.

Bourbaki (Résumé E.R.5, n°16, PDF p.308) : « Dans certaines questions, on
considère une partie déterminée A d'un ensemble E ; si X est une autre partie
arbitraire de E, on appelle alors *trace* de X sur A l'ensemble A ∩ X, qu'on note
souvent aussi X_A, et qu'on considère toujours, dans ce cas, comme une partie de
A. » Les identités vérifiées par Bourbaki sont :

    (X∪Y)_A = X_A ∪ Y_A ;        (X∩Y)_A = X_A ∩ Y_A ;        ∁_A X_A = (∁_E X)_A.

DÉFINITION (terme / abréviation, pas une nouvelle constante introductrice) :

    trace(X, A) := A ∩ X = E.intersection(A, X).

C'est purement une NOTATION : trace(X,A) est exactement le terme A∩X. Les trois
identités deviennent alors des ÉGALITÉS ENSEMBLISTES entre traces, toutes
exprimées via `trace(...)` (conclusion == cible STRUCTURELLE).

  • IDENTITÉ (1)  trace(X∪Y, A) = trace(X,A) ∪ trace(Y,A)   [A∩(X∪Y)=(A∩X)∪(A∩Y)].
    STRUCTURELLEMENT identique à la loi de distributivité ∩/∪ déjà certifiée :
    trace(reunion(X,Y),A) == A∩(X∪Y) et reunion(trace(X,A),trace(Y,A)) ==
    (A∩X)∪(A∩Y), donc la conclusion EST celle de
    `distributivite_intersection_reunion(A, X, Y)`. On la RÉUTILISE telle quelle
    (théorème déjà clos), AUCUNE re-preuve.

  • IDENTITÉ (2)  trace(X∩Y, A) = trace(X,A) ∩ trace(Y,A)   [A∩(X∩Y)=(A∩X)∩(A∩Y)].
    Vraie preuve (≠ structurel : A∩(X∩Y) n'est PAS (A∩X)∩(A∩Y) comme assemblage —
    le A est dupliqué). Égalité par extension : au niveau de z l'équivalence
    repose sur la duplication idempotente de z∈A
    (`_et_et_distrib`, lemme du module voisin : P et (Q et R) ⇔ (P et Q) et (P et R)).

  • IDENTITÉ (3)  complement(A, trace(X,A)) = trace(complement(E,X), A)
    [∁_A(A∩X) = A∩(E∖X)], c.-à-d. A∖(A∩X) = A∩(E∖X). HONNÊTE : cette égalité
    n'est PAS close — elle requiert l'hypothèse A⊂E (sans elle, z∈A n'entraîne pas
    z∈E et les deux membres diffèrent). Hypothèse exacte : `inclus(A, E)`. Preuve
    par extension sous cette unique hypothèse (instanciée au point z).

Toutes les égalités sont obtenues par les SEULES primitives N.* et tactiques
certifiées (extensionnalité + congruences/transitivité de ⇔, S6 pour =) ; AUCUNE
théorie dédiée, AUCUN S8 ; theorie_ensembles() INCHANGÉE = 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient, et, non, impl, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    et_congruence_gauche, et_congruence_droite, contraposition, equiv_neg,
    equivalence_transitivite, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne import (
    distributivite_intersection_reunion, _instance_inter, _instance_diff, _et_et_distrib)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


# ════════════════════════════════════════════════════════════════════════════
#  DÉFINITION (notation : terme A∩X)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §1.16 Def.16 | E.R.5 L.28-31 | PDF p.308
# @livre Ch.R §2 Def.- | E.R.8 item 6 (trace X_A = image réciproque par l'application canonique de A dans E) | PDF p.311
def trace(x, a):
    """X_A := A ∩ X  (trace de la partie X sur la partie A, Résumé E.R.5 n°16).

    Pure ABRÉVIATION : renvoie le terme E.intersection(A, X). Aucune constante
    introductrice, aucun axiome — `trace(X, A)` EST le terme A∩X."""
    return E.intersection(_t(a), _t(x))


# ════════════════════════════════════════════════════════════════════════════
#  IDENTITÉS (égalités ensemblistes entre traces)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §1.16 Prop.16 | E.R.5 L.32-32 | PDF p.308
def trace_reunion(x="X", y="Y", a="A"):
    """⊢ (X∪Y)_A = X_A ∪ Y_A   c.-à-d.  A∩(X∪Y) = (A∩X)∪(A∩Y).

    Théorème CLOS (0 hypothèse). RÉUTILISE `distributivite_intersection_reunion`
    (la conclusion est STRUCTURELLEMENT identique : voir module). Aucune re-preuve."""
    vx, vy, va = _t(x), _t(y), _t(a)
    # distributivite_intersection_reunion(A, X, Y) : A∩(X∪Y) = (A∩X)∪(A∩Y),
    # soit trace(X∪Y, A) = trace(X,A) ∪ trace(Y,A)  (égalité IDENTIQUE).
    return distributivite_intersection_reunion(va, vx, vy)


# @livre Ch.R §1.16 Prop.16 | E.R.5 L.32-32 | PDF p.308
def trace_intersection(x="X", y="Y", a="A"):
    """⊢ (X∩Y)_A = X_A ∩ Y_A   c.-à-d.  A∩(X∩Y) = (A∩X)∩(A∩Y).

    Théorème CLOS (0 hypothèse). Vraie preuve par extension : au niveau de z,
        z∈A∩(X∩Y) ⇔ (z∈A et (z∈X et z∈Y))
                  ⇔ ((z∈A et z∈X) et (z∈A et z∈Y))   [_et_et_distrib, idempot. de et]
                  ⇔ z∈(A∩X)∩(A∩Y)."""
    vx, vy, va, vz = _t(x), _t(y), _t(a), var("z")
    XY = E.intersection(vx, vy)
    zA, zX, zY = appartient(vz, va), appartient(vz, vx), appartient(vz, vy)
    # char LHS : z ∈ A∩(X∩Y) ⇔ ((z∈A et z∈X) et (z∈A et z∈Y))
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(va, XY, vz),                        # z∈A∩(X∩Y) ⇔ (z∈A et z∈X∩Y)
        et_congruence_droite(zA, _instance_inter(vx, vy, vz))),  # ⇔ (z∈A et (z∈X et z∈Y))
        _et_et_distrib(zA, zX, zY)))                        # ⇔ ((z∈A et z∈X) et (z∈A et z∈Y))
    AX, AY = E.intersection(va, vx), E.intersection(va, vy)
    # char RHS : z ∈ (A∩X)∩(A∩Y) ⇔ ((z∈A et z∈X) et (z∈A et z∈Y))
    char_v = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(AX, AY, vz),                        # z∈(A∩X)∩(A∩Y) ⇔ (z∈A∩X et z∈A∩Y)
        et_congruence_gauche(_instance_inter(va, vx, vz), appartient(vz, AY))),
        et_congruence_droite(et(zA, zX), _instance_inter(va, vy, vz))))
    return egalite_par_extension(char_u, char_v, E.intersection(va, XY),
                                 E.intersection(AX, AY))


def _trace_complement_equiv(g, zA, zX, zE):
    """Sous l'hyp. G : (z∈A ⇒ z∈E), prouve l'équivalence ponctuelle
        (z∈A et ¬(z∈A et z∈X)) ⇔ (z∈A et (z∈E et ¬(z∈X))).

    g : théorème Γ ⊢ (z∈A ⇒ z∈E)  (instance de inclus(A,E) au point z).
    C'est le cœur de l'identité (3) ; l'hypothèse A⊂E est INDISPENSABLE (z∈E à
    droite ne se déduit de z∈A qu'avec elle)."""
    Lhs = et(zA, non(et(zA, zX)))
    Rhs = et(zA, et(zE, non(zX)))
    AX = et(zA, zX)
    # ── fwd : Lhs ⇒ Rhs ──
    hL = N.assume(Lhs)
    a_h = conjonction_elim_gauche(hL)                      # ⊢ z∈A
    nAX = conjonction_elim_droite(hL)                      # ⊢ ¬(z∈A et z∈X)
    e_h = N.modus_ponens(a_h, g)                           # ⊢ z∈E      (via G : z∈A ⇒ z∈E)
    # ¬(z∈A et z∈X) ⇒ ¬(z∈X) : contraposée de (z∈X ⇒ (z∈A et z∈X)) [sous z∈A].
    x_to_ax = N.loi_deduction(zX, conjonction_intro(a_h, N.assume(zX)))  # z∈X ⇒ (z∈A et z∈X)
    nX = N.modus_ponens(nAX, contraposition(x_to_ax))     # ⊢ ¬(z∈X)
    fwd = N.loi_deduction(Lhs, conjonction_intro(a_h, conjonction_intro(e_h, nX)))
    # ── bwd : Rhs ⇒ Lhs ──
    hR = N.assume(Rhs)
    a_h2 = conjonction_elim_gauche(hR)                     # ⊢ z∈A
    nX2 = conjonction_elim_droite(conjonction_elim_droite(hR))  # ⊢ ¬(z∈X)
    # ¬(z∈X) ⇒ ¬(z∈A et z∈X) : contraposée de ((z∈A et z∈X) ⇒ z∈X).
    ax_to_x = N.loi_deduction(AX, conjonction_elim_droite(N.assume(AX)))  # (z∈A et z∈X) ⇒ z∈X
    nAX2 = N.modus_ponens(nX2, contraposition(ax_to_x))   # ⊢ ¬(z∈A et z∈X)
    bwd = N.loi_deduction(Rhs, conjonction_intro(a_h2, nAX2))
    return conjonction_intro(fwd, bwd)


# @livre Ch.R §1.16 Prop.16 | E.R.5 L.34-34 | PDF p.308
def trace_complement(x="X", a="A", e="E"):
    """⊢ ∁_A X_A = (∁_E X)_A   c.-à-d.  A∖(A∩X) = A∩(E∖X)   SOUS l'hyp. A⊂E.

    NON close : hypothèse exacte `inclus(A, E)` (rapportée dans .hypotheses).
    complement(A, trace(X,A)) = A∖(A∩X) ; trace(complement(E,X), A) = A∩(E∖X).
    Preuve par extension, l'hypothèse A⊂E étant instanciée au point z."""
    vx, va, vE, vz = _t(x), _t(a), _t(e), var("z")
    AX = E.intersection(va, vx)                             # X_A = A∩X
    EX = E.difference(vE, vx)                               # ∁_E X = E∖X
    zA, zX, zE = appartient(vz, va), appartient(vz, vx), appartient(vz, vE)
    # hypothèse A⊂E (= (∀z)(z∈A ⇒ z∈E)), instanciée au point z
    hyp = N.assume(pourtout("z", impl(zA, zE)))
    g = instancie(hyp, vz)                                  # Γ ⊢ (z∈A ⇒ z∈E)
    # char LHS : z ∈ A∖(A∩X) ⇔ (z∈A et (z∈E et ¬(z∈X)))
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_diff(va, AX, vz),                         # z∈A∖(A∩X) ⇔ (z∈A et ¬(z∈A∩X))
        et_congruence_droite(zA, _neg_inter(va, vx, vz))),  # ⇔ (z∈A et ¬(z∈A et z∈X))
        _trace_complement_equiv(g, zA, zX, zE)))            # ⇔ (z∈A et (z∈E et ¬(z∈X)))
    # char RHS : z ∈ A∩(E∖X) ⇔ (z∈A et (z∈E et ¬(z∈X)))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_inter(va, EX, vz),                        # z∈A∩(E∖X) ⇔ (z∈A et z∈E∖X)
        et_congruence_droite(zA, _instance_diff(vE, vx, vz))))  # ⇔ (z∈A et (z∈E et ¬(z∈X)))
    return egalite_par_extension(char_u, char_v, E.difference(va, AX),
                                 E.intersection(va, EX))


def _neg_inter(a, b, z):
    """⊢ ¬(z ∈ a∩b) ⇔ ¬(z∈a et z∈b)   (négation congruente de l'instance ∩)."""
    return equiv_neg(_instance_inter(a, b, z))


__all__ = ["trace", "trace_reunion", "trace_intersection", "trace_complement"]
