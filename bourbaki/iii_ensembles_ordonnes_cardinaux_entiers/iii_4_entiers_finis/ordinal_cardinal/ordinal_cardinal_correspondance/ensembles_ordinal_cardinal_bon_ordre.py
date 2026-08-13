"""§III.2 + §III.4 — ENGINE : extraction du PLUS PETIT ÉLÉMENT d'un bon ordre.

────────────────────────────────────────────────────────────────────────────────
RÔLE dans le chantier ORDINAL↔CARDINAL → cardinaux_bien_ordonnes(a) → C61 → ℕ.

`cardinaux_bien_ordonnes(a)` (cible, ensembles_recurrence_C61.py) affirme :

    (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) )

c.-à-d. « toute partie non vide de [0,a] a un plus petit cardinal ».  C'est
EXACTEMENT la clause de bon ordre de la Définition 1 (E.III.2.1) :

    est_bien_ordonne(R, E) =
        est_relation_ordre_dans(R, E) et
        (∀X)( ( X ⊂ E et ¬(X=∅) ) ⇒ (∃a)( a∈X et (∀w)(w∈X ⇒ R{a,w}) ) ).

Ce module fournit l'ENGINE INCONDITIONNEL, réutilisable, qui EXTRAIT le plus petit
élément :

    plus_petit_de_bon_ordre :
        { est_bien_ordonne(R,E),  X ⊂ E,  X ≠ ∅ }
            ⊢ (∃a)( a∈X et (∀w)(w∈X ⇒ R{a,w}) ).

C'est le DERNIER MAILLON de l'argument : une fois transportée la non-vacuité et
l'inclusion de S (∈ [0,a]) sur un X bien ordonné par l'ordre des cardinaux, et une
fois SU que [0,a] est bien ordonné par ≤ (le report ORDINAL↔CARDINAL, isolé dans
ensembles_ordinal_cardinal_correspondance.py), cet engine livre le plus petit élément.

INVARIANT : theorie_ensembles() = 22 (aucun axiome ajouté ; on ne fait QUE projeter
et instancier la Définition 1).  Rien postulé : on EXTRAIT une conjonction existante.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  La clause de BON ORDRE isolée  (2ᵉ conjoint de est_bien_ordonne)
# ════════════════════════════════════════════════════════════════════════════
def clause_plus_petit(R, e, X="X", a="a", w="w"):
    """La 2ᵉ composante de est_bien_ordonne(R,E) — « toute partie non vide a un plus
    petit élément » :

        (∀X)( ( X ⊂ E et ¬(X=∅) ) ⇒ (∃a)( a∈X et (∀w)(w∈X ⇒ R{a,w}) ) ).

    (formule IDENTIQUE au 2ᵉ conjoint de E.est_bien_ordonne, par construction.)"""
    ve = _t(e)
    vX, va, vw = var(X), var(a), var(w)
    petit = existe(a, et(appartient(va, vX),
                         pourtout(w, impl(appartient(vw, vX), R(va, vw)))))
    return pourtout(X, impl(et(inclus(vX, ve), non(egal(vX, E.VIDE))), petit))


def bon_ordre_donne_clause_plus_petit(R, e="E", x="x", y="y", z="z",
                                      X="X", a="a", w="w"):
    """⊢ est_bien_ordonne(R, E)  ⇒  clause_plus_petit(R, E).

    PROJECTION DROITE de la conjonction de la Définition 1 (E.III.2.1).  Le 2ᵉ
    conjoint de est_bien_ordonne EST clause_plus_petit (mêmes binders X,a,w).
    INCONDITIONNEL, theorie=22 : on ne fait que décomposer une conjonction."""
    ve = _t(e)
    hyp = E.est_bien_ordonne(R, ve, x, y, z, X, a, w)
    H = N.assume(hyp)
    clause = conjonction_elim_droite(H)                       # 2ᵉ conjoint = clause_plus_petit
    return N.loi_deduction(hyp, clause)


# @livre Ch.III §3.2 Demo.1 | E III.24 L.16-30 | PDF p.127
def plus_petit_de_bon_ordre(R, e="E", X="X", x="x", y="y", z="z", a="a", w="w"):
    """⊢ { est_bien_ordonne(R,E),  X ⊂ E,  X ≠ ∅ }
            ⊢ (∃a)( a∈X et (∀w)(w∈X ⇒ R{a,w}) ).

    🎯 ENGINE INCONDITIONNEL — l'extraction du PLUS PETIT ÉLÉMENT d'une partie non
    vide d'un ensemble bien ordonné (E.III.2.1, Définition 1).  On projette la clause
    de bon ordre, on l'instancie à la partie X, puis on lui fournit (X⊂E et X≠∅).

    C'est le dernier maillon de cardinaux_bien_ordonnes : avec R := ordre des
    cardinaux et E := [0,a] bien ordonné par ≤ (report ordinal↔cardinal isolé), il
    livre le plus petit cardinal de toute partie non vide.  theorie=22, rien postulé."""
    ve, vX = _t(e), _t(X)
    # est_bien_ordonne(R,E) ⊢ clause_plus_petit(R,E)
    clause = N.modus_ponens(N.assume(E.est_bien_ordonne(R, ve, x, y, z, X, a, w)),
                            bon_ordre_donne_clause_plus_petit(R, e, x, y, z, X, a, w))
    # instancie la clause à la PARTIE X
    inst = instancie(clause, vX)            # (X⊂E et X≠∅) ⇒ (∃a)(a∈X et ...)
    # fournir (X⊂E et X≠∅)
    premisse = conjonction_intro(N.assume(inclus(vX, ve)),
                                 N.assume(non(egal(vX, E.VIDE))))
    return N.modus_ponens(premisse, inst)   # (∃a)(a∈X et (∀w)(w∈X ⇒ R{a,w}))


__all__ = [
    "clause_plus_petit",
    "bon_ordre_donne_clause_plus_petit",
    "plus_petit_de_bon_ordre",
]
