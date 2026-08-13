"""§II.4.5 — COMMUTATIVITÉ DE LA RÉUNION / INTERSECTION BINAIRES.

Dérive des axiomes de la section (AXIOME_REUNION, AXIOME_INTER) les deux
identités élémentaires de commutativité du calcul ensembliste binaire :

  • commutativite_reunion_binaire   ⊢ A ∪ B = B ∪ A
  • commutativite_inter_binaire     ⊢ A ∩ B = B ∩ A

INCONDITIONNELLES (0 hypothèse, CLOS), theorie_ensembles() inchangée (22 axiomes).

Preuve : pointwise par extensionnalité.  Pour ∪ :
  z∈A∪B ⇔ (z∈A ∨ z∈B)            (instance de AXIOME_REUNION)
        ⇔ (z∈B ∨ z∈A)            (commutativité du ∨ : comm_ou)
        ⇔ z∈B∪A                  (instance de AXIOME_REUNION, sens arrière)
La chaîne d'équivalences (equivalence_transitivite) donne, après généralisation
sur z, deux caractérisations de A∪B et B∪A par la MÊME relation R := (z∈A ∨ z∈B),
d'où l'égalité par egalite_par_extension.  Identique pour ∩ avec comm_et.

C'est exactement le schéma de `commutativite_paire` ({a,b}={b,a}) de
ii_1_relations_collectivisantes.ensembles_theoremes, transposé de la paire à ∪ / ∩.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient, ou, et, Terme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    comm_ou, comm_et, equivalence_transitivite)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import egalite_par_extension
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
    _instance_reunion, _instance_inter)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  1. COMMUTATIVITÉ DE LA RÉUNION BINAIRE — ⊢ A ∪ B = B ∪ A.
# ════════════════════════════════════════════════════════════════════════════
def cible_commutativite_reunion_binaire(a="A", b="B"):
    vA, vB = _t(a), _t(b)
    return egal(E.reunion(vA, vB), E.reunion(vB, vA))


# @livre Ch.II §4.5 Prop.- | E II.26 L.36-37 | PDF p.77
def commutativite_reunion_binaire(a="A", b="B"):
    """⊢ A ∪ B = B ∪ A.   (§II.4.5 — CLOS, 0 hyp, INCONDITIONNEL.)"""
    vA, vB, vz = _t(a), _t(b), var("z")
    inA = appartient(vz, vA)
    inB = appartient(vz, vB)

    # char_AB : (∀z)(z∈A∪B ⇔ (z∈A ∨ z∈B)).
    char_AB = N.generalisation("z", _instance_reunion(vA, vB, vz))

    # char_BA : (∀z)(z∈B∪A ⇔ (z∈A ∨ z∈B)) — MÊME relation R que char_AB.
    #   z∈B∪A ⇔ (z∈B ∨ z∈A)   puis   (z∈B ∨ z∈A) ⇔ (z∈A ∨ z∈B)   (comm_ou)
    eba = equivalence_transitivite(_instance_reunion(vB, vA, vz),
                                   comm_ou(inB, inA))               # z∈B∪A ⇔ (z∈A∨z∈B)
    char_BA = N.generalisation("z", eba)

    return egalite_par_extension(char_AB, char_BA,
                                 E.reunion(vA, vB), E.reunion(vB, vA))


# ════════════════════════════════════════════════════════════════════════════
#  2. COMMUTATIVITÉ DE L'INTERSECTION BINAIRE — ⊢ A ∩ B = B ∩ A.
# ════════════════════════════════════════════════════════════════════════════
def cible_commutativite_inter_binaire(a="A", b="B"):
    vA, vB = _t(a), _t(b)
    return egal(E.intersection(vA, vB), E.intersection(vB, vA))


# @livre Ch.II §4.5 Prop.- | E II.26 L.36-37 | PDF p.77
def commutativite_inter_binaire(a="A", b="B"):
    """⊢ A ∩ B = B ∩ A.   (§II.4.5 — CLOS, 0 hyp, INCONDITIONNEL.)"""
    vA, vB, vz = _t(a), _t(b), var("z")
    inA = appartient(vz, vA)
    inB = appartient(vz, vB)

    # char_AB : (∀z)(z∈A∩B ⇔ (z∈A et z∈B)).
    char_AB = N.generalisation("z", _instance_inter(vA, vB, vz))

    # char_BA : (∀z)(z∈B∩A ⇔ (z∈A et z∈B)) — MÊME relation R que char_AB.
    #   z∈B∩A ⇔ (z∈B et z∈A)   puis   (z∈B et z∈A) ⇔ (z∈A et z∈B)   (comm_et)
    eba = equivalence_transitivite(_instance_inter(vB, vA, vz),
                                   comm_et(inB, inA))               # z∈B∩A ⇔ (z∈A et z∈B)
    char_BA = N.generalisation("z", eba)

    return egalite_par_extension(char_AB, char_BA,
                                 E.intersection(vA, vB), E.intersection(vB, vA))


__all__ = [
    "commutativite_reunion_binaire", "cible_commutativite_reunion_binaire",
    "commutativite_inter_binaire", "cible_commutativite_inter_binaire",
]
