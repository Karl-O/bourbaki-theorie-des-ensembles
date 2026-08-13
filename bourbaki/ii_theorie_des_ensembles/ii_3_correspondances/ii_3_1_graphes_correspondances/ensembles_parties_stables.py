"""Résumé §2 (E.R.7 item 4) — PARTIES STABLES par une application. Définitions.

Bourbaki : « on dit qu'une partie X de E est STABLE pour f si f⟨X⟩ ⊂ X ;
plus généralement, X est stable pour un ensemble 𝔉 d'applications de E dans E
si elle est stable pour chaque f ∈ 𝔉. »

Formalisation VERBATIM au niveau formule (E.image et ⊂ déposés) — ces
définitions manquaient (entrée n°74 de CAMPAGNE_DEMOS) ; rien à démontrer ici,
ce sont des constructeurs de relations.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, impl, pourtout, appartient, inclus)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.R §2 Def.- | E.R.7 item 4 | PDF p.310  (partie stable par f : f⟨X⟩ ⊂ X)
def est_stable_par(X, f) -> Terme:
    """« X est stable pour f »  :=  f⟨X⟩ ⊂ X   (E.R.7 item 4)."""
    tX = _t(X)
    return inclus(E.image(_t(f), tX), tX)


# @livre Ch.R §2 Def.- | E.R.7 item 4 | PDF p.310  (partie stable par un ENSEMBLE d'applications)
def est_stable_par_ensemble(X, F, f: str = "fstb") -> Terme:
    """« X est stable pour l'ensemble 𝔉 »  :=  (∀f)( f ∈ 𝔉 ⇒ f⟨X⟩ ⊂ X )."""
    vf = var(f)
    return pourtout(f, impl(appartient(vf, _t(F)), est_stable_par(X, vf)))


__all__ = ["est_stable_par", "est_stable_par_ensemble"]
