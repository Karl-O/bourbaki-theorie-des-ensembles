"""§III.6 — Ensembles infinis : théorèmes DIRECTS certifiés par le noyau.

Les DÉFINITIONS et l'AXIOME A4 sont dans ensembles_infinis.py (lus verbatim V7 §III.6).

Théorèmes DIRECTS atteignables au niveau abrégé (instances de A4 + dépliage
définitionnel) — chaque conclusion est certifiée par le noyau (type Theoreme) :

  • existe_ensemble_infini   ⊢ (∃X) ¬Fini(Card(X))            [A4, axiome de l'infini]
  • infini_non_fini          ⊢ (E infini) ⇒ ¬Fini(Card(E))    [Déf. 1, identité A⇒A]
  • non_fini_infini          ⊢ ¬Fini(Card(E)) ⇒ (E infini)    [Déf. 1, identité A⇒A]
  • infini_ssi_non_fini      ⊢ (E infini) ⇔ ¬Fini(Card(E))    [Déf. 1, A⇔A]
  • suite_infinie_est_suite  ⊢ (suite (x_n)_{n∈I} infinie) ⇒ (suite (x_n)_{n∈I})
                                                              [Déf. 2, projection ∧]
  • suite_infinie_indices_infinis ⊢ (suite infinie) ⇒ (I infini)   [Déf. 2, proj. ∧]

REPORTÉ honnêtement (cf. en-tête d'ensembles_infinis.py) : Théorème 1 (collectivisa-
tion de « x entier »), Théorème 2 (𝔞²=𝔞), Lemmes 1-2, Cor. 1-4, Prop. 1-7, C62/C63
— tous reposent sur l'arithmétique cardinale infinie (§III.6.3) et/ou la récurrence
(C61) et le bon ordre de N, NON disponibles dans le projet.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, non, equiv, impl
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables import ensembles_infinis as I
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, est_fini_ensemble
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite)


# ── A4 exhibé comme théorème : il existe un ensemble infini ───────────────────
# @livre Ch.III §6.1 Ax.A4 | E III.45 L.14-15 | PDF p.148  (A4 exhibé comme théorème de la théorie dédiée)
def existe_ensemble_infini():
    """⊢ (∃X) ¬Fini(Card(X))   (= il existe un ensemble infini, A4, §III.6.1).

    THÉORÈME DIRECT : instance de l'axiome A4 de la théorie de l'infini.  C'est le
    point de départ de toute la théorie des ensembles infinis (Bourbaki §III.6.1)."""
    return N.axiome(I.theorie_infini(), I.A4)


# ── Déf. 1 : « infini » = « non fini » (identités définitionnelles) ───────────
# @livre Ch.III §6.1 Def.1 | E III.45 L.3-4 | PDF p.148  (identités définitionnelles « infini = non fini »)
def infini_non_fini(e="E"):
    """⊢ (E est infini) ⇒ ¬Fini(Card(E))   (Déf. 1, §III.6.1).

    THÉORÈME DIRECT (identité A⇒A) : par définition, est_infini_ensemble(E) EST
    littéralement ¬Fini(Card(E)) (= ¬est_fini_ensemble(E))."""
    return a_implique_a(I.est_infini_ensemble(var(e)))


def non_fini_infini(e="E"):
    """⊢ ¬Fini(Card(E)) ⇒ (E est infini)   (Déf. 1, §III.6.1, réciproque-identité)."""
    return a_implique_a(I.est_infini_ensemble(var(e)))


def infini_ssi_non_fini(e="E"):
    """⊢ (E est infini) ⇔ ¬Fini(Card(E))   (Déf. 1, §III.6.1).

    THÉORÈME DIRECT (A⇔A) : l'équivalence définitionnelle « infini ⟺ non fini »,
    conjonction des deux identités."""
    return conjonction_intro(infini_non_fini(e), non_fini_infini(e))


# ── Déf. 1 (niveau CARDINAL) : un cardinal infini est un cardinal non fini ────
# @livre Ch.III §6.1 Def.1 | E III.45 L.3-4 | PDF p.148  (« En particulier, un cardinal est infini s'il n'est pas un entier », niveau cardinal)
def cardinal_infini_ssi_non_fini(a="a"):
    """⊢ (𝔞 est infini) ⇔ ¬Fini(𝔞)   (Déf. 1, §III.6.1, niveau cardinal).

    THÉORÈME DIRECT (A⇔A) : « un cardinal est infini s'il n'est pas un entier »
    (Déf. 1).  est_infini(𝔞) EST littéralement ¬Fini(𝔞) (= ¬est_fini(𝔞)) ; l'énoncé
    est l'équivalence définitionnelle au niveau des CARDINAUX (l'énoncé pour les
    ENSEMBLES est infini_ssi_non_fini).  a : nom de variable (str) OU Terme."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme
    va = a if isinstance(a, Terme) else var(a)
    sens = a_implique_a(I.est_infini(va))               # (𝔞 infini) ⇒ (𝔞 infini) = ¬Fini(𝔞)
    return conjonction_intro(sens, sens)


def fini_implique_cardinal_non_infini(a="a"):
    """⊢ Fini(𝔞) ⇒ ¬(𝔞 est infini)   (Déf. 1, §III.6.1 ; reflet du report « infini = non fini »).

    THÉORÈME DIRECT : un cardinal fini n'est pas infini.  est_infini(𝔞)=¬Fini(𝔞),
    donc ¬(𝔞 infini)=¬¬Fini(𝔞) ; double négation à partir de Fini(𝔞).  (Délégué au
    théorème homonyme d'ensembles_entiers_theoremes pour éviter la duplication.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_non_infini
    return fini_implique_non_infini(a)


# ── Déf. 2 : une suite infinie est une suite, d'indices infinis ───────────────
# @livre Ch.III §6.1 Def.2 | E III.45 L.25-27 | PDF p.148  (projections définitionnelles de « suite infinie »)
def suite_infinie_est_suite(f="f", i="I"):
    """⊢ (la suite (x_n)_{n∈I} est infinie) ⇒ (c'est une suite)   (Déf. 2, §III.6.1).

    THÉORÈME DIRECT : est_suite_infinie(f,I) = (I⊂N et I infini) ; projection gauche
    donne est_suite(f,I) = (I⊂N).  Sous l'hypothèse « suite infinie » déchargée."""
    hyp = I.est_suite_infinie(f, i)
    proj = conjonction_elim_gauche(N.assume(hyp))         # I ⊂ N  (= est_suite)
    return N.loi_deduction(hyp, proj)


def suite_infinie_indices_infinis(f="f", i="I"):
    """⊢ (la suite (x_n)_{n∈I} est infinie) ⇒ (I est infini)   (Déf. 2, §III.6.1).

    THÉORÈME DIRECT : projection droite de (I⊂N et I infini)."""
    hyp = I.est_suite_infinie(f, i)
    proj = conjonction_elim_droite(N.assume(hyp))         # I infini
    return N.loi_deduction(hyp, proj)


__all__ = ["existe_ensemble_infini", "infini_non_fini", "non_fini_infini",
           "infini_ssi_non_fini", "cardinal_infini_ssi_non_fini",
           "fini_implique_cardinal_non_infini",
           "suite_infinie_est_suite", "suite_infinie_indices_infinis"]
