"""§II.1 — IDENTITÉS de l'ensemble vide (∅ neutre/absorbant, différences triviales).

Bourbaki E.II.1 (formulaire) : ∅ est neutre pour ∪, absorbant pour ∩, et

    A∪∅ = A        A∩∅ = ∅        A∖∅ = A        A∖A = ∅

Toutes CLOSES (0 hyp), par extensionnalité (`egalite_par_extension`) à partir des
axiomes de membership ∪/∩/∖ (dans les 22) et de AXIOME_VIDE (∀z ¬(z∈∅)).  La règle
ex falso quodlibet (¬P ⊢ P⇒Q) est DÉRIVÉE ici au noyau (`_efq`, via contraposition +
double négation) ; rien postulé.  theorie_ensembles() INCHANGÉE = 22.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, appartient, et, ou, non
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion, egalite_par_extension
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_transitivite, dni, dne, contraposition, instancie, cas,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _refl_equiv(f):
    return conjonction_intro(a_implique_a(f), a_implique_a(f))


def _instance_inter(a, b, z):
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _instance_diff(e, x, z):
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def _vide_inst(vz):
    """⊢ ¬(z ∈ ∅)   (instance de AXIOME_VIDE)."""
    return instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)


def _efq(notP_thm, q):
    """De ⊢¬P, déduire ⊢ (P ⇒ Q)   (ex falso quodlibet ; P⇒¬¬P⇒¬¬Q⇒Q)."""
    P = notP_thm.conclusion.sous[0]
    h = N.loi_deduction(non(q), notP_thm)             # ¬Q ⇒ ¬P
    return syllogisme(syllogisme(dni(P), contraposition(h)), dne(q))   # P ⇒ Q


def reunion_vide_neutre(a="A"):
    """⊢ A∪∅ = A   (∅ neutre pour la réunion)."""
    va, vz = _t(a), var("z")
    zA, zV = appartient(vz, va), appartient(vz, E.VIDE)
    ou_simpl = conjonction_intro(
        N.loi_deduction(ou(zA, zV), cas(N.assume(ou(zA, zV)), a_implique_a(zA),
                                        _efq(_vide_inst(vz), zA))),     # (z∈A ∨ z∈∅) ⇒ z∈A
        N.s2(zA, zV))                                                   # z∈A ⇒ (z∈A ∨ z∈∅)
    char_u = N.generalisation("z", equivalence_transitivite(_instance_reunion(va, E.VIDE, vz), ou_simpl))
    char_v = N.generalisation("z", _refl_equiv(zA))
    return egalite_par_extension(char_u, char_v, E.reunion(va, E.VIDE), va)


def intersection_vide(a="A"):
    """⊢ A∩∅ = ∅   (∅ absorbant pour l'intersection)."""
    va, vz = _t(a), var("z")
    zA, zV = appartient(vz, va), appartient(vz, E.VIDE)
    et_simpl = conjonction_intro(
        N.loi_deduction(et(zA, zV), conjonction_elim_droite(N.assume(et(zA, zV)))),   # (z∈A et z∈∅) ⇒ z∈∅
        N.loi_deduction(zV, conjonction_intro(                                        # z∈∅ ⇒ (z∈A et z∈∅)
            N.modus_ponens(N.assume(zV), _efq(_vide_inst(vz), zA)), N.assume(zV))))
    char_u = N.generalisation("z", equivalence_transitivite(_instance_inter(va, E.VIDE, vz), et_simpl))
    char_v = N.generalisation("z", _refl_equiv(zV))
    return egalite_par_extension(char_u, char_v, E.intersection(va, E.VIDE), E.VIDE)


def difference_vide_neutre(a="A"):
    """⊢ A∖∅ = A   (retrancher ∅ ne change rien)."""
    va, vz = _t(a), var("z")
    zA = appartient(vz, va)
    notzV = _vide_inst(vz)                                             # ⊢ ¬(z∈∅)
    et_vrai = conjonction_intro(
        N.loi_deduction(et(zA, non(appartient(vz, E.VIDE))),
                        conjonction_elim_gauche(N.assume(et(zA, non(appartient(vz, E.VIDE)))))),  # ⇒ z∈A
        N.loi_deduction(zA, conjonction_intro(N.assume(zA), notzV)))  # z∈A ⇒ (z∈A et ¬z∈∅)
    char_u = N.generalisation("z", equivalence_transitivite(_instance_diff(va, E.VIDE, vz), et_vrai))
    char_v = N.generalisation("z", _refl_equiv(zA))
    return egalite_par_extension(char_u, char_v, E.difference(va, E.VIDE), va)


def difference_self(a="A"):
    """⊢ A∖A = ∅."""
    va, vz = _t(a), var("z")
    zA, zV = appartient(vz, va), appartient(vz, E.VIDE)
    hc = N.assume(et(zA, non(zA)))
    fwd = N.loi_deduction(et(zA, non(zA)),                             # (z∈A et ¬z∈A) ⇒ z∈∅
                          N.modus_ponens(conjonction_elim_gauche(hc),
                                         _efq(conjonction_elim_droite(hc), zV)))
    hv = N.assume(zV)
    bwd = N.loi_deduction(zV, conjonction_intro(                      # z∈∅ ⇒ (z∈A et ¬z∈A)
        N.modus_ponens(hv, _efq(_vide_inst(vz), zA)),
        N.modus_ponens(hv, _efq(_vide_inst(vz), non(zA)))))
    contra_equiv = conjonction_intro(fwd, bwd)                        # (z∈A et ¬z∈A) ⇔ z∈∅
    char_u = N.generalisation("z", equivalence_transitivite(_instance_diff(va, va, vz), contra_equiv))
    char_v = N.generalisation("z", _refl_equiv(zV))
    return egalite_par_extension(char_u, char_v, E.difference(va, va), E.VIDE)


__all__ = ["reunion_vide_neutre", "intersection_vide", "difference_vide_neutre", "difference_self"]
