"""§II.4.2 — MONOTONIE DÉCROISSANTE de l'intersection EN L'ENSEMBLE D'INDICES.

    (J ⊂ I) ⇒ ( (∃i)(i∈J) ⇒ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι )
                                                  (`inter_incluse_sous_indices`)

À FAMILLE f FIXÉE, l'intersection DÉCROÎT quand l'ensemble d'indices CROÎT :
l'intersection sur le PLUS GROS ensemble d'indices (I) est la PLUS PETITE.  C'est
le DUAL universel (∀) de la croissance de la réunion EN L'INDICE
(`reunion_incluse_sous_indices`, §II.4.2, déjà certifiée) : là où la réunion
quantifie existentiellement (témoin i∈J⊂I), l'intersection quantifie
universellement, donc PLUS d'indices = PLUS de contraintes = ensemble PLUS PETIT.

────────────────────────────────────────────────────────────────────────────────
⚠ RENFORCEMENT D'ÉNONCÉ (migration Déf. 2 par SÉLECTION, cf.
`ii_4_intersection_fondation/ensembles_inter_selection_ii4`).

L'ANCIENNE forme de ce résultat — « (J ⊂ I) ⇒ ⋂_I X_ι ⊂ ⋂_J X_ι », SANS aucune
hypothèse sur J — était **FAUSSE pour J = ∅**, et elle n'était démontrable que
parce que l'ancien AXIOME_INTER_FAM était lui-même contradictoire (il peuplait
⋂_{ι∈∅} X_ι de TOUT objet ; cf. `outils_ia/audit/preuve_incoherence_inter_vide.py`).

Contre-exemple avec la Déf. 2 réparée : J = ∅ ⊂ I = {0}, X_0 = {a}.  Alors
⋂_{ι∈∅} X_ι = ∅ (`inter_famille_vide_egale_vide`) tandis que a ∈ ⋂_{ι∈I} X_ι ;
l'inclusion ⋂_I ⊂ ⋂_J est donc en défaut.

L'hypothèse ajoutée est celle que Bourbaki écrit noir sur blanc pour la Déf. 2
(E II.22 : « … dont l'ensemble d'indices n'est pas vide »), portée ici par
l'ensemble d'indices **J** — le PETIT, celui qui indexe l'intersection d'ARRIVÉE.
Ce n'est PAS (∃i)(i∈I) qui suffit : avec J = ∅ et I ≠ ∅ l'énoncé reste faux.
Noter que (∃i)(i∈J) et J ⊂ I entraînent (∃i)(i∈I), de sorte que les deux membres
de l'inclusion sont simultanément régis par la Déf. 2 sous sa propre hypothèse.
────────────────────────────────────────────────────────────────────────────────

STRATÉGIE (dualise ∃→∀ pour le corps, mais réclame un témoin pour la BORNE) :
  1. ÉLIMINATION (inchangée par la migration) : z∈⋂_I ⇒ (∀i)(i∈I ⇒ z∈X_i), par
     `inter_donne_membres` (projection DROITE de la conjonction de sélection).
  2. Pour i quelconque, i∈J donne i∈I (par J⊂I), d'où z∈X_i ; on regénéralise en
     (∀i)(i∈J ⇒ z∈X_i) — le CORPS de la Déf. 2 relatif à J.
  3. INTRODUCTION (ce qui change) : conclure z∈⋂_J exige aussi z∈⋃_J, donc un
     TÉMOIN d'indice.  `N.existe_temoin` livre T₀ := τi(i∈J) avec T₀∈J sous
     l'hypothèse (∃i)(i∈J), et `inter_par_membres_si_temoin_terme` referme.
  4. Loi de déduction sur « z∈⋂_I ⇒ z∈⋂_J », généralisation en z, refermeture en
     inclusion, puis décharge de (∃i)(i∈J) puis de J⊂I.

GARDE-FOUS : primitives N.* uniquement (aucun Theoreme fabriqué) ; theorie_
ensembles() reste à 22 axiomes ; binders frais (i, z).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, appartient, impl, inclus, tau)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    inter_donne_membres, inter_par_membres_si_temoin_terme)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
# MONOTONIE EN L'ENSEMBLE D'INDICES (décroissance J ↦ ⋂_{ι∈J} X_ι).   (E.II.4.2.)
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §4.2 Prop.- | E II.24 L.5-7 | PDF p.75
# @livre Ch.R §4 Prop.- | E.R.19 item 8 (le RÉSUMÉ écrit « quel que soit J ⊂ I, ⋂_I X_ι ⊂ ⋂_J X_ι » SANS hypothèse : ce n'est PAS l'énoncé formalisé ici. Le Résumé travaille sur des familles de PARTIES d'un E fixé, où sa formule (40) pose ⋂_{ι∈∅} X_ι = E, ce qui rend l'item vrai sans condition. Le chapitre — Déf. 2, E II.22 — n'a pas d'ambiant E et exige J ≠ ∅ ; c'est LUI qui fait foi, cf. le marqueur E II.24 ci-dessus) | PDF p.322
def inter_incluse_sous_indices(f="X", j="J", i="I"):
    """⊢ (J ⊂ I) ⇒ ( (∃i)(i∈J) ⇒ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι ).   CLOS — 0 hypothèse.

    (E.II.4.2 — décroissance en l'indice.)  À FAMILLE f FIXÉE, l'intersection
    DÉCROÎT avec l'ensemble d'indices (dual ∀ de `reunion_incluse_sous_indices`).

    ⚠ ÉNONCÉ RENFORCÉ : l'hypothèse « J n'est pas vide » (celle de la Déf. 2,
    E II.22) est INDISPENSABLE depuis la réparation de ⋂ par sélection — sans
    elle l'énoncé est FAUX pour J = ∅ (⋂_{ι∈∅} X_ι = ∅ alors que ⋂_I peut être
    non vide).  L'ancienne forme sans hypothèse n'était démontrable que par
    l'axiome contradictoire.  Voir l'en-tête du module.

    z∈⋂_I ⇒ (∀i)(i∈I ⇒ z∈X_i) (élimination inconditionnelle) ; pour i quelconque
    i∈J ⊂ I donne i∈I, d'où z∈X_i, regénéralisé en (∀i)(i∈J ⇒ z∈X_i) ; le témoin
    T₀ := τi(i∈J) fourni par (∃i)(i∈J) referme sur z∈⋂_J."""
    vf, vJ, vI = _t(f), _t(j), _t(i)
    vz, vi = var("z"), var("i")
    interJ = E.inter_famille(vf, vJ)
    interI = E.inter_famille(vf, vI)
    non_vide = indices_non_vides(vJ)                    # (∃i)(i∈J)
    hyp = inclus(vJ, vI)                                # J⊂I = (∀z')(z'∈J ⇒ z'∈I)
    hH = N.assume(hyp)

    # ── témoin d'indice dans J (la BORNE ⋃_J de la sélection l'exige) ──────────
    T0 = tau("i", appartient(vi, vJ))                   # τi(i∈J)
    hNE = N.assume(non_vide)
    t_in_J = N.modus_ponens(hNE, N.existe_temoin(appartient(vi, vJ), "i"))   # T₀∈J

    # ── élimination : z∈⋂_I donne le corps (∀i)(i∈I ⇒ z∈X_i) ──────────────────
    hL = N.assume(appartient(vz, interI))
    forall = N.modus_ponens(hL, instancie(inter_donne_membres(vf, vI, "z"), vz))

    # ── transport du corps de I vers J (par J⊂I) ──────────────────────────────
    hii = N.assume(appartient(vi, vJ))                  # i∈J
    i_in_I = N.modus_ponens(hii, instancie(hH, vi))     # i∈I
    z_Xi = N.modus_ponens(i_in_I, instancie(forall, vi))  # z∈X_i
    forallJ = N.generalisation("i", N.loi_deduction(appartient(vi, vJ), z_Xi))

    # ── introduction : corps + témoin T₀∈J ⇒ z∈⋂_J ────────────────────────────
    bwd = N.modus_ponens(t_in_J, inter_par_membres_si_temoin_terme(vf, vJ, T0, vz))
    z_interJ = N.modus_ponens(forallJ, bwd)             # z∈⋂_J

    incl = N.generalisation("z", N.loi_deduction(appartient(vz, interI), z_interJ))
    res = N.loi_deduction(hyp, N.loi_deduction(non_vide, incl))
    assert res.conclusion == cible(f, j, i), \
        "inter_incluse_sous_indices : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), "inter_incluse_sous_indices : doit être CLOS"
    return res


def cible(f="X", j="J", i="I"):
    """Énoncé visé (CLOS) : (J⊂I) ⇒ ( (∃i)(i∈J) ⇒ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι ).

    L'hypothèse fidèle J⊂I est déchargée en implication (loi de déduction), comme
    pour le patron dual `reunion_incluse_sous_indices` : 0 hypothèse résiduelle.
    L'hypothèse (∃i)(i∈J) — « J n'est pas vide », Déf. 2 E II.22 — est déchargée
    de même ; elle est NÉCESSAIRE (l'énoncé est faux pour J=∅), cf. module."""
    vf, vJ, vI = _t(f), _t(j), _t(i)
    return impl(inclus(vJ, vI),
                impl(indices_non_vides(vJ),
                     inclus(E.inter_famille(vf, vI), E.inter_famille(vf, vJ))))


__all__ = ["inter_incluse_sous_indices", "cible"]
