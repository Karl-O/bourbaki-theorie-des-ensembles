"""§II.4/§II.1 — Différence E∖X et lois de De Morgan (forme binaire).

⊢ E∖(A∪B) = (E∖A)∩(E∖B)   et   ⊢ E∖(A∩B) = (E∖A)∪(E∖B).
Débloque les Propositions De Morgan des familles (§4 P5/P6, §5.6) en fournissant
le terme complémentaire/différence absent jusqu'ici.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, ou, non, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_transitivite,
                               equivalence_symetrie, equiv_neg, demorgan_ou, demorgan_et,
                               et_ou_distrib, ou_congruence,
                               et_congruence_droite, et_congruence_gauche, instancie)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (_instance_reunion, _instance_intersection,
                                 egalite_par_extension)


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def _dup_et(p, q, r):
    """⊢ (P et (Q et R)) ⇔ ((P et Q) et (P et R))   (duplication de P)."""
    h1 = N.assume(et(p, et(q, r)))
    qr = conjonction_elim_droite(h1)
    fwd = N.loi_deduction(et(p, et(q, r)), conjonction_intro(
        conjonction_intro(conjonction_elim_gauche(h1), conjonction_elim_gauche(qr)),
        conjonction_intro(conjonction_elim_gauche(h1), conjonction_elim_droite(qr))))
    h2 = N.assume(et(et(p, q), et(p, r)))
    pq = conjonction_elim_gauche(h2)
    bwd = N.loi_deduction(et(et(p, q), et(p, r)), conjonction_intro(
        conjonction_elim_gauche(pq),
        conjonction_intro(conjonction_elim_droite(pq),
                          conjonction_elim_droite(conjonction_elim_droite(h2)))))
    return conjonction_intro(fwd, bwd)


# @livre Ch.R §1.14 Prop.(8) | E.R.4 L.27 | PDF p.307
def de_morgan_reunion(e="E", a="A", b="B"):
    """⊢ E∖(A∪B) = (E∖A)∩(E∖B)."""
    vE, vA, vB, vz = var(e), var(a), var(b), var("z")
    zE, za, zb = appartient(vz, vE), appartient(vz, vA), appartient(vz, vB)
    # gauche : z∈E∖(A∪B) ⇔ (z∈E et (¬a et ¬b))
    neg_chain = equivalence_transitivite(equiv_neg(_instance_reunion(vA, vB, vz)),
                                         demorgan_ou(za, zb))      # ¬(z∈A∪B) ⇔ (¬a et ¬b)
    left = equivalence_transitivite(_inst_diff(vE, E.reunion(vA, vB), vz),
                                    et_congruence_droite(zE, neg_chain))
    R = et(et(zE, non(za)), et(zE, non(zb)))                       # ((z∈E et ¬a) et (z∈E et ¬b))
    cu = N.generalisation("z", equivalence_transitivite(left, _dup_et(zE, non(za), non(zb))))
    # droite : z∈(E∖A)∩(E∖B) ⇔ R
    inter = _instance_intersection(E.difference(vE, vA), E.difference(vE, vB), vz)
    right_inner = equivalence_transitivite(
        et_congruence_gauche(_inst_diff(vE, vA, vz), appartient(vz, E.difference(vE, vB))),
        et_congruence_droite(et(zE, non(za)), _inst_diff(vE, vB, vz)))
    cv = N.generalisation("z", equivalence_transitivite(inter, right_inner))
    return egalite_par_extension(cu, cv, E.difference(vE, E.reunion(vA, vB)),
                                 E.intersection(E.difference(vE, vA), E.difference(vE, vB)))


# @livre Ch.R §1.14 Prop.(8) | E.R.4 L.27 | PDF p.307
def de_morgan_inter(e="E", a="A", b="B"):
    """⊢ E∖(A∩B) = (E∖A)∪(E∖B)."""
    vE, vA, vB, vz = var(e), var(a), var(b), var("z")
    zE, za, zb = appartient(vz, vE), appartient(vz, vA), appartient(vz, vB)
    # gauche : z∈E∖(A∩B) ⇔ (z∈E et (¬a ∨ ¬b)) ⇔ ((z∈E et ¬a) ∨ (z∈E et ¬b)) = R
    neg_chain = equivalence_transitivite(equiv_neg(_instance_intersection(vA, vB, vz)),
                                         demorgan_et(za, zb))      # ¬(z∈A∩B) ⇔ (¬a ∨ ¬b)
    left = equivalence_transitivite(
        equivalence_transitivite(_inst_diff(vE, E.intersection(vA, vB), vz),
                                 et_congruence_droite(zE, neg_chain)),
        et_ou_distrib(zE, non(za), non(zb)))                       # ⇔ ((z∈E et ¬a) ∨ (z∈E et ¬b))
    cu = N.generalisation("z", left)
    # droite : z∈(E∖A)∪(E∖B) ⇔ R
    reun = _instance_reunion(E.difference(vE, vA), E.difference(vE, vB), vz)
    right_inner = ou_congruence(_inst_diff(vE, vA, vz), _inst_diff(vE, vB, vz))
    cv = N.generalisation("z", equivalence_transitivite(reun, right_inner))
    return egalite_par_extension(cu, cv, E.difference(vE, E.intersection(vA, vB)),
                                 E.reunion(E.difference(vE, vA), E.difference(vE, vB)))


__all__ = ["de_morgan_reunion", "de_morgan_inter"]
