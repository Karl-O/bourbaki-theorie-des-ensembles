"""§II.1 — IDENTITÉS de la différence (relations ∖ / ∩ / ∪).

Bourbaki E.II.1 (formulaire) :

    A∩(B∖C) = (A∩B)∖C          (A∖B)∖C = A∖(B∪C)

CLOSES (0 hyp) par extensionnalité (`egalite_par_extension`) sur AXIOME_INTER/DIFF/REUNION
(dans les 22) + lois propositionnelles fermées (assoc de et, De Morgan ¬(∨)=et¬).
theorie_ensembles() INCHANGÉE = 22 ; aucun axiome ajouté.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, appartient, et, non
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_theoremes import _instance_reunion, egalite_par_extension
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, et_congruence_droite, et_congruence_gauche,
    equivalence_transitivite, equivalence_symetrie, assoc_et, demorgan_ou,
    equiv_neg, instancie,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _refl_equiv(f):
    return conjonction_intro(a_implique_a(f), a_implique_a(f))


def _instance_inter(a, b, z):
    return instancie(instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_INTER), a), b), z)


def _instance_diff(e, x, z):
    return instancie(instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF), e), x), z)


def intersection_difference_associe(a="A", b="B", c="C"):
    """⊢ A∩(B∖C) = (A∩B)∖C."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    zA, zB, nC = appartient(vz, va), appartient(vz, vb), non(appartient(vz, vc))
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(va, E.difference(vb, vc), vz),
        et_congruence_droite(zA, _instance_diff(vb, vc, vz))),
        assoc_et(zA, zB, nC)))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_diff(E.intersection(va, vb), vc, vz),
        et_congruence_gauche(_instance_inter(va, vb, vz), nC)))
    return egalite_par_extension(char_u, char_v, E.intersection(va, E.difference(vb, vc)),
                                 E.difference(E.intersection(va, vb), vc))


def difference_reunion(a="A", b="B", c="C"):
    """⊢ (A∖B)∖C = A∖(B∪C)."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    zA, zB, zC = appartient(vz, va), appartient(vz, vb), appartient(vz, vc)
    nB, nC = non(zB), non(zC)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        _instance_diff(E.difference(va, vb), vc, vz),
        et_congruence_gauche(_instance_diff(va, vb, vz), nC)),
        equivalence_symetrie(assoc_et(zA, nB, nC))),
        et_congruence_droite(zA, equivalence_symetrie(demorgan_ou(zB, zC)))))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_diff(va, E.reunion(vb, vc), vz),
        et_congruence_droite(zA, equiv_neg(_instance_reunion(vb, vc, vz)))))
    return egalite_par_extension(char_u, char_v, E.difference(E.difference(va, vb), vc),
                                 E.difference(va, E.reunion(vb, vc)))


__all__ = ["intersection_difference_associe", "difference_reunion"]
