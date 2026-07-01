"""Résumé §6 item 12 — Familles croissantes / décroissantes de parties.

Une famille de parties (X_ι)_{ι∈I} (application ι↦X_ι, E.II.4.1 ; X_ι = valeur_famille)
indexée par un ensemble ORDONNÉ (I, G_I) est CROISSANTE si ι≤κ ⇒ X_ι ⊂ X_κ, et
DÉCROISSANTE si ι≤κ ⇒ X_κ ⊂ X_ι  (E.R.29, item 12).  On pose les deux prédicats et on
certifie leur DÉPLIAGE (instanciation à un couple ordonné (a,b)∈G_I).  Rien postulé ;
theorie_ensembles INCHANGÉE (22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, appartient, impl, pourtout, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.R §6 Def.- | E.R.29 item 12 (famille croissante de parties) | PDF p.332
def famille_croissante_parties(gi="GI", x="X"):
    """« (X_ι) croissante » := (∀i)(∀j)((i,j) ∈ G_I ⇒ X_i ⊂ X_j)."""
    vgi, vx, vi, vj = _t(gi), _t(x), var("i"), var("j")
    return pourtout("i", pourtout("j", impl(
        appartient(E.couple(vi, vj), vgi),
        inclus(E.valeur_famille(vx, vi), E.valeur_famille(vx, vj)))))


# @livre Ch.R §6 Def.- | E.R.29 item 12 (famille décroissante de parties) | PDF p.332
def famille_decroissante_parties(gi="GI", x="X"):
    """« (X_ι) décroissante » := (∀i)(∀j)((i,j) ∈ G_I ⇒ X_j ⊂ X_i)."""
    vgi, vx, vi, vj = _t(gi), _t(x), var("i"), var("j")
    return pourtout("i", pourtout("j", impl(
        appartient(E.couple(vi, vj), vgi),
        inclus(E.valeur_famille(vx, vj), E.valeur_famille(vx, vi)))))


# @livre Ch.R §6 Prop.- | E.R.29 item 12 (dépliage croissante) | PDF p.332
def famille_croissante_monotone(gi="GI", x="X", i="a", j="b"):
    """⊢ famille_croissante_parties(G_I,X) ⇒ ((a,b) ∈ G_I ⇒ X_a ⊂ X_b)."""
    vgi, vx, va, vb = _t(gi), _t(x), _t(i), _t(j)
    h = N.assume(famille_croissante_parties(vgi, vx))
    inst = instancie(instancie(h, va), vb)                # (a,b)∈G_I ⇒ X_a⊂X_b
    return N.loi_deduction(famille_croissante_parties(vgi, vx), inst)


# @livre Ch.R §6 Prop.- | E.R.29 item 12 (dépliage décroissante) | PDF p.332
def famille_decroissante_monotone(gi="GI", x="X", i="a", j="b"):
    """⊢ famille_decroissante_parties(G_I,X) ⇒ ((a,b) ∈ G_I ⇒ X_b ⊂ X_a)."""
    vgi, vx, va, vb = _t(gi), _t(x), _t(i), _t(j)
    h = N.assume(famille_decroissante_parties(vgi, vx))
    inst = instancie(instancie(h, va), vb)
    return N.loi_deduction(famille_decroissante_parties(vgi, vx), inst)


def cible_famille_croissante_monotone(gi="GI", x="X", i="a", j="b"):
    vgi, vx, va, vb = _t(gi), _t(x), _t(i), _t(j)
    return impl(famille_croissante_parties(vgi, vx),
                impl(appartient(E.couple(va, vb), vgi),
                     inclus(E.valeur_famille(vx, va), E.valeur_famille(vx, vb))))


def cible_famille_decroissante_monotone(gi="GI", x="X", i="a", j="b"):
    vgi, vx, va, vb = _t(gi), _t(x), _t(i), _t(j)
    return impl(famille_decroissante_parties(vgi, vx),
                impl(appartient(E.couple(va, vb), vgi),
                     inclus(E.valeur_famille(vx, vb), E.valeur_famille(vx, va))))


__all__ = [
    "famille_croissante_parties", "famille_decroissante_parties",
    "famille_croissante_monotone", "famille_decroissante_monotone",
    "cible_famille_croissante_monotone", "cible_famille_decroissante_monotone",
]
