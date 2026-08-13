# -*- coding: utf-8 -*-
"""§II.4 — PONT ⋂-de-famille pour les preuves d'IMAGE (Prop. 3/4 + Cor., E.II.25).

RAISON D'ÊTRE.  La Déf. 2 (E II.22) est désormais réalisée par SÉLECTION dans la
réunion (`ii_4_intersection_fondation.ensembles_inter_selection_ii4`) :

    z ∈ ⋂_{ι∈I} X_ι  ⇔  ( z ∈ ⋃_{ι∈I} X_ι  ∧  (∀i)((i∈I) ⇒ z∈X_i) )

Le membre droit est une CONJONCTION : on ne peut plus attaquer directement
`equivalence_avant` / `equivalence_arriere` de l'axiome comme si c'était l'ancien
`z∈⋂ ⇔ (∀i)(…)`.  Ce module fournit les trois gestes dont les preuves d'image ont
besoin, et RIEN d'autre :

  1. `inter_elim`          — ÉLIMINATION, INCHANGÉE par la réparation (projection
                             droite) : ⊢ (z∈⋂) ⇒ (∀i)((i∈I) ⇒ z∈X_i).
  2. `temoin_indice_via_inter` — le geste NEUF, et le cœur de la réparation : quand
                             on DISPOSE DÉJÀ d'un élément x∈⋂_{ι∈I} X_ι, l'ensemble
                             d'indices est NÉCESSAIREMENT non vide, car x∈⋂ ⊂ ⋃ et
                             z∈⋃ ⇔ (∃i)(i∈I ∧ z∈X_i).  On en tire un TÉMOIN
                             D'INDICE canonique T₀ := τi(i∈I ∧ x∈X_i) avec ⊢ T₀∈I.
                             C'est ce qui permet aux inclusions Γ⟨⋂X⟩ ⊂ ⋂Γ⟨X_ι⟩ et
                             f⁻¹⟨⋂Y⟩ ⊂ ⋂f⁻¹⟨Y_ι⟩ de rester INCONDITIONNELLES
                             (issue A) : elles n'ont pas besoin de « I ≠ ∅ » en
                             hypothèse, elles se le FABRIQUENT à partir de leur
                             propre antécédent.
  3. `inter_intro`         — INTRODUCTION : de ⊢ T∈I et ⊢ (∀i)((i∈I) ⇒ z∈X_i)
                             conclure ⊢ z ∈ ⋂_{ι∈I} X_ι.

INVARIANTS
  • `theorie_ensembles()` reste à 22 axiomes ; AXIOME_INTER_FAM_SEL == E.AXIOME_INTER_FAM
    (la migration a remplacé l'axiome DANS le corpus), donc les lemmes-ponts de
    `ensembles_inter_selection_ii4` s'appliquent tels quels au corpus.
  • Liant d'indice « i » IMPOSÉ (celui d'AXIOME_REUNION_FAM / AXIOME_INTER_FAM).
  • Rien de postulé : tout passe par les lemmes CLOS de la fondation.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, tau)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche as _cg, equivalence_avant, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    inter_donne_membres, inter_inclus_reunion, inter_par_membres_si_temoin_terme)

_IDX = var("i")


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_reunion(f, i_set, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i).   (AXIOME_REUNION_FAM, 22 ax.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, _t(f)), _t(i_set)), _t(z))


# ── 1. ÉLIMINATION — le geste INCHANGÉ ────────────────────────────────────────
# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (Déf. 2, direction ⊂ de « {x | (∀ι)((ι∈I) ⇒ (x∈X_ι))} » : appartenir à ⋂ DONNE la relation définissante — instance de `inter_donne_membres`)
def inter_elim(fam, i_set, z):
    """⊢ ( z ∈ ⋂_{ι∈I} X_ι ) ⇒ (∀i)((i∈I) ⇒ z∈X_i).

    Remplace exactement l'ancien `equivalence_avant(_inst_inter(fam, I, z))` :
    même énoncé, mais obtenu par PROJECTION DROITE de la conjonction de sélection
    (`inter_donne_membres`, CLOS).  `z` peut être un Terme quelconque sans « i »
    libre (dans les preuves d'image : var("x") ou var("z"))."""
    return instancie(inter_donne_membres(_t(fam), _t(i_set), "z"), _t(z))


# ── 2. Le TÉMOIN d'indice fabriqué à partir d'un élément de ⋂ ─────────────────
# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (corollaire immédiat de la Déf. 2 réalisée par sélection : ⋂ ⊂ ⋃ donne « I n'est pas vide » — l'hypothèse que Bourbaki POSE devient ici DÉRIVABLE dès qu'on tient un x∈⋂)
def temoin_indice_via_inter(fam, i_set, x, x_dans_inter):
    """De ⊢ x ∈ ⋂_{ι∈I} X_ι tirer (T₀, ⊢ T₀ ∈ I) — I est non vide, gratuitement.

    Route : x∈⋂ ⇒ x∈⋃ (projection GAUCHE, `inter_inclus_reunion`) ; puis
    x∈⋃ ⇔ (∃i)(i∈I et x∈X_i) (AXIOME_REUNION_FAM) ; puis `N.existe_temoin` livre
    le témoin canonique T₀ := τi(i∈I et x∈X_i), dont la projection gauche est T₀∈I.

    C'est LE point qui garde inconditionnelles les inclusions « ⋂ à gauche » :
    l'hypothèse I≠∅ de Bourbaki y est DÉRIVABLE, pas à supposer."""
    vfam, vI, vx = _t(fam), _t(i_set), _t(x)
    corps = et(appartient(_IDX, vI), appartient(vx, E.valeur_famille(vfam, _IDX)))
    T0 = tau("i", corps)
    x_reunion = N.modus_ponens(x_dans_inter,
                               instancie(inter_inclus_reunion(vfam, vI, "z"), vx))
    ex_i = N.modus_ponens(x_reunion, equivalence_avant(_inst_reunion(vfam, vI, vx)))
    return T0, _cg(N.modus_ponens(ex_i, N.existe_temoin(corps, "i")))


# ── 3. INTRODUCTION — exige désormais un témoin d'indice ──────────────────────
# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (Déf. 2, direction ⊃ : la relation définissante DONNE l'appartenance à ⋂ — sous le témoin d'indice « Si α est un élément de I » du texte, E II.22 L.45-48)
def inter_intro(fam, i_set, temoin, temoin_dans_I, corps_thm, z):
    """De ⊢ T∈I et ⊢ (∀i)((i∈I) ⇒ z∈X_i), conclure ⊢ z ∈ ⋂_{ι∈I} X_ι.

    Remplace l'ancien `equivalence_arriere(_inst_inter(fam, I, z))`, qui n'exigeait
    aucun témoin — et c'est précisément par là que l'ancien axiome peuplait
    ⋂_{ι∈∅} X_ι de TOUT objet."""
    return N.modus_ponens(
        corps_thm,
        N.modus_ponens(temoin_dans_I,
                       inter_par_membres_si_temoin_terme(_t(fam), _t(i_set),
                                                         _t(temoin), _t(z))))


__all__ = ["inter_elim", "temoin_indice_via_inter", "inter_intro"]
