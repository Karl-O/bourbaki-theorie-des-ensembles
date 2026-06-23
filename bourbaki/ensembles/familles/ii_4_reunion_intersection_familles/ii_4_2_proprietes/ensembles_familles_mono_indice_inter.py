"""§II.4.2 — MONOTONIE DÉCROISSANTE de l'intersection EN L'ENSEMBLE D'INDICES.

    J ⊂ I ⊢ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι                 (`inter_incluse_sous_indices`)

À FAMILLE f FIXÉE, l'intersection DÉCROÎT quand l'ensemble d'indices CROÎT :
l'intersection sur le PLUS GROS ensemble d'indices (I) est la PLUS PETITE.  C'est
le DUAL universel (∀) de la croissance de la réunion EN L'INDICE
(`reunion_incluse_sous_indices`, §II.4.2, déjà certifiée) : là où la réunion
quantifie existentiellement (témoin i∈J⊂I), l'intersection quantifie
universellement, donc PLUS d'indices = PLUS de contraintes = ensemble PLUS PETIT.

INCONDITIONNELLE modulo l'hypothèse FIDÈLE J⊂I (jamais postulée ; déchargée en
implication par la loi de déduction).

STRATÉGIE (dualise ∃→∀ ; pas de témoin, pas d'élimination de ∃) :
  z∈⋂_{I} ⇒ (∀i)(i∈I ⇒ z∈X_i) ; pour i quelconque, i∈J donne i∈I (par J⊂I), d'où
  z∈X_i ; on regénéralise en (∀i)(i∈J ⇒ z∈X_i) = z∈⋂_{J}.  Loi de déduction sur
  « z∈⋂_I ⇒ z∈⋂_J », généralisation en z, refermeture en inclusion, puis
  décharge de J⊂I.

GARDE-FOUS : primitives N.* uniquement (aucun Theoreme fabriqué) ; theorie_
ensembles() reste à 22 axiomes ; binders frais (i, z).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, appartient, impl, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    equivalence_avant, equivalence_arriere, instancie)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


# ══════════════════════════════════════════════════════════════════════════════
# MONOTONIE EN L'ENSEMBLE D'INDICES (décroissance J ↦ ⋂_{ι∈J} X_ι).   (E.II.4.2.)
# ══════════════════════════════════════════════════════════════════════════════
def inter_incluse_sous_indices(f="X", j="J", i="I"):
    """{J ⊂ I} ⊢ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι.   (E.II.4.2 — décroissance en l'indice.)

    À FAMILLE f FIXÉE, l'intersection DÉCROÎT avec l'ensemble d'indices (dual ∀ de
    `reunion_incluse_sous_indices`).  INCONDITIONNELLE modulo l'hypothèse FIDÈLE J⊂I.
    z∈⋂_{I} ⇒ (∀i)(i∈I ⇒ z∈X_i) ; pour i quelconque, i∈J ⊂ I donne i∈I, d'où
    z∈X_i ; regénéralisé en (∀i)(i∈J ⇒ z∈X_i), soit z∈⋂_{J}."""
    vf, vJ, vI = _t(f), _t(j), _t(i)
    vz, vi = var("z"), var("i")
    interJ = E.inter_famille(vf, vJ)
    interI = E.inter_famille(vf, vI)
    Xi = E.valeur_famille(vf, vi)
    hyp = inclus(vJ, vI)                                # J⊂I = (∀z')(z'∈J ⇒ z'∈I)
    hH = N.assume(hyp)
    i_in_I_imp = instancie(hH, vi)                      # i∈J ⇒ i∈I

    hL = N.assume(appartient(vz, interI))
    forall = N.modus_ponens(hL, equivalence_avant(_inst_inter(vf, vI, vz)))  # (∀i)(i∈I ⇒ z∈X_i)

    # but : z∈⋂_{J} = (∀i)(i∈J ⇒ z∈X_i)
    hii = N.assume(appartient(vi, vJ))                  # i∈J
    i_in_I = N.modus_ponens(hii, i_in_I_imp)            # i∈I
    z_Xi = N.modus_ponens(i_in_I, instancie(forall, vi))  # z∈X_i
    forallJ = N.generalisation("i", N.loi_deduction(appartient(vi, vJ), z_Xi))  # (∀i)(i∈J ⇒ z∈X_i)
    z_interJ = N.modus_ponens(forallJ, equivalence_arriere(_inst_inter(vf, vJ, vz)))  # z∈⋂_{J}

    incl = N.generalisation("z", N.loi_deduction(appartient(vz, interI), z_interJ))
    return N.loi_deduction(hyp, incl)


def cible(f="X", j="J", i="I"):
    """Énoncé visé (CLOS) : (J⊂I) ⇒ (⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι).

    L'hypothèse fidèle J⊂I est déchargée en implication (loi de déduction), comme
    pour le patron dual `reunion_incluse_sous_indices` : 0 hypothèse résiduelle."""
    vf, vJ, vI = _t(f), _t(j), _t(i)
    return impl(inclus(vJ, vI),
                inclus(E.inter_famille(vf, vI), E.inter_famille(vf, vJ)))


__all__ = ["inter_incluse_sous_indices", "cible"]
