"""Chapitre II §1.4 — « La relation x ∈ y est collectivisante en x » (E II.3, Ex. 1).

Théorème (Bourbaki, E.II.3, §1.4 Exemples, n°1) :

    ⊢ Coll_x(x ∈ y)   c.-à-d.   ⊢ (∃Y)(∀x)((x ∈ Y) ⇔ (x ∈ y))

« La relation x ∈ y est évidemment collectivisante en x » : il existe un ensemble
Y dont les éléments sont exactement les objets x vérifiant x ∈ y. Énoncé CLOS
(zéro hypothèse), démontré sur les 22 axiomes SEULS — aucune théorie dédiée,
aucun schéma S8. Le témoin est l'ensemble y LUI-MÊME (Y := y) : x ∈ y ⇔ x ∈ y.

────────────────────────────────────────────────────────────────────────────────
CONTRASTE (honnêteté) avec le théorème voisin `pas_ensemble_universel` (E.II.6) :
celui-ci s'appuyait sur une SÉLECTION S8 portée par une théorie dédiée (Russell).
ICI, RIEN de tel : x ∈ y borne déjà les x cherchés, donc Y := y convient
DIRECTEMENT. Le contenu non trivial reste l'EXISTENCE d'un tel ensemble Y (étape
S5, ∃-introduction avec témoin y), PAS une tautologie « P ⇒ P ».

────────────────────────────────────────────────────────────────────────────────
STRATÉGIE (preuve directe, niveau ABRÉGÉ, sur Formule)

  Soit f := (x ∈ y) et la cible C := Coll_x(f) = (∃Y)(∀x)((x ∈ Y) ⇔ (x ∈ y)),
  où Y est le liant ∃ choisi par `coll` (frais : y est libre dans f, cf. formule.py).

  (1) RÉFLEXIVITÉ DE L'ÉQUIVALENCE.  `conjonction_intro(a_implique_a(f),
      a_implique_a(f))` donne  ⊢ (x ∈ y) ⇔ (x ∈ y).  (Schéma de
      `tactiques_prop.equivalence_reflexive`, porté sur le noyau abrégé : ⇔ y est
      aussi (A⇒A) et (A⇒A) ; aucune dérivation tierce.)

  (2) GÉNÉRALISATION.  `N.generalisation('x', .)` →
      ⊢ (∀x)((x ∈ y) ⇔ (x ∈ y)).  (Théorème clos, donc 'x' non libre dans Γ=∅.)

  (3) ∃-INTRODUCTION, TÉMOIN Y := y (S5).  Le corps du ∃ de C est
      corps = (∀x)((x ∈ Y) ⇔ (x ∈ y)).  `N.s5(corps, var('y'), Y)` donne
      ⊢ (y|Y)corps ⇒ (∃Y)corps = C.  Or (y|Y)corps coïncide STRUCTURELLEMENT avec
      l'étape (2) (substituer Y := y dans (x ∈ Y) redonne (x ∈ y)) ; un
      `N.modus_ponens` conclut  ⊢ C.

INVARIANTS
  • conclusion == coll('x', appartient(var('x'), var('y')))  (== STRUCTURELLE).
  • est_clos == True : zéro hypothèse (aucune n'est introduite ; preuve directe).
  • theorie_ensembles() reste à 22 axiomes : AUCUN `N.axiome(...)`, AUCUNE théorie
    dédiée, AUCUN schéma S8 n'est invoqué (le témoin Y := y suffit).
  • Le contenu EST l'existence du témoin (S5) : sans l'étape ∃-introduction, on
    n'aurait que (∀x)(f ⇔ f) — ce n'est donc pas une tautologie déguisée.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, coll
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro


# @livre Ch.II §1.4 Ex.1 | E II.3 L.45-45 | PDF p.54
def appartenance_collectivisante(x: str = "x", y: str = "y"):
    """⊢ Coll_x(x ∈ y).  (E.II.3, §1.4 Ex.1 : x ∈ y est collectivisante en x ; CLOS.)

    Preuve directe sur les 22 axiomes, témoin Y := y. Voir le docstring du module
    pour la stratégie (réflexivité de ⇔, généralisation, S5 témoin y, modus ponens)."""
    f = appartient(var(x), var(y))          # f := (x ∈ y)
    cible = coll(x, f)                       # C := (∃Y)(∀x)((x∈Y) ⇔ (x∈y))
    corps = cible.sous[0]                    # (∀x)((x∈Y) ⇔ (x∈y))   (Y = cible.lieur)

    # (1) réflexivité de l'équivalence : ⊢ (x∈y) ⇔ (x∈y)
    refl = conjonction_intro(a_implique_a(f), a_implique_a(f))
    # (2) généralisation : ⊢ (∀x)((x∈y) ⇔ (x∈y))     [== (y|Y)corps]
    gen = N.generalisation(x, refl)
    # (3) ∃-introduction, témoin Y := y : ⊢ (y|Y)corps ⇒ Coll_x(x∈y)
    s5 = N.s5(corps, var(y), cible.lieur)
    return N.modus_ponens(gen, s5)           # ⊢ Coll_x(x ∈ y)


__all__ = ["appartenance_collectivisante"]
