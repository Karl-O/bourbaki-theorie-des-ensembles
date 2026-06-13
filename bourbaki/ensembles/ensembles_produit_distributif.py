"""§II.2 — DISTRIBUTIVITÉ du produit cartésien sur la réunion / l'intersection,
au niveau de l'APPARTENANCE D'UN COUPLE (clé de l'égalité ensembliste E.II.2).

Bourbaki (E.II.2, formulaire du produit) énonce les égalités ENSEMBLISTES

    A × (B ∪ C) = (A × B) ∪ (A × C)        A × (B ∩ C) = (A × B) ∩ (A × C)

Leur CŒUR (et la voie de preuve par extensionnalité) est l'équivalence d'appartenance
d'un couple, qu'on certifie ici INCONDITIONNELLEMENT (CLOS) par pur recollement de
briques déjà fermées :

  • couple_dans_produit_ssi  ((u,v)∈X×Y ⇔ u∈X et v∈Y)            [ensembles_produit, CLOS]
  • _instance_reunion / _instance_inter  (z∈X∪Y ⇔ z∈X∨z∈Y ; ∩)  [AXIOME_REUNION/INTER]
  • et_ou_distrib   ((P et (Q∨R)) ⇔ ((P et Q)∨(P et R)))          [tactiques, CLOS]
  • congruences ∧/∨ + transitivité de ⇔.

L'égalité ENSEMBLISTE pleine (∀z, z couple ou non) est REPORTÉE (elle exige la poussée
des ∃p,q de AXIOME_PRODUIT à travers ∨/∧ + extensionnalité) ; on ne la prétend PAS ici.
theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, appartient, et
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ensembles.ensembles_theoremes import _instance_reunion
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    et_congruence_droite, et_congruence_gauche, et_ou_distrib, ou_congruence,
    equivalence_symetrie, equivalence_transitivite, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _instance_inter(a, b, z):
    """⊢ (z ∈ a∩b) ⇔ (z∈a et z∈b)   (instance de AXIOME_INTER aux termes a,b,z)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _et_et_distrib(p, q, r):
    """⊢ (P et (Q et R)) ⇔ ((P et Q) et (P et R))   (distribution de et sur et, P dupliqué)."""
    from bourbaki.logique.formule import et as _et
    hf = N.assume(_et(p, _et(q, r)))
    pp = conjonction_elim_gauche(hf)
    qr = conjonction_elim_droite(hf)
    fwd = N.loi_deduction(_et(p, _et(q, r)), conjonction_intro(
        conjonction_intro(pp, conjonction_elim_gauche(qr)),
        conjonction_intro(pp, conjonction_elim_droite(qr))))
    hb = N.assume(_et(_et(p, q), _et(p, r)))
    pq = conjonction_elim_gauche(hb)
    pr = conjonction_elim_droite(hb)
    bwd = N.loi_deduction(_et(_et(p, q), _et(p, r)), conjonction_intro(
        conjonction_elim_gauche(pq),
        conjonction_intro(conjonction_elim_droite(pq), conjonction_elim_droite(pr))))
    return conjonction_intro(fwd, bwd)


def couple_dans_produit_distributif_reunion(u="u", v="v", a="A", b="B", c="C"):
    """⊢ ((u,v) ∈ A×(B∪C)) ⇔ ((u,v) ∈ (A×B)∪(A×C)).   (cœur de A×(B∪C)=(A×B)∪(A×C), E.II.2.)"""
    vu, vv, vA, vB, vC = _t(u), _t(v), _t(a), _t(b), _t(c)
    BC = E.reunion(vB, vC)
    uA = appartient(vu, vA)
    # (u,v)∈A×(B∪C) ⇔ (u∈A et v∈B∪C)
    e1 = couple_dans_produit_ssi(vu, vv, vA, BC)
    # (u∈A et v∈B∪C) ⇔ (u∈A et (v∈B ou v∈C))
    e2 = et_congruence_droite(uA, _instance_reunion(vB, vC, vv))
    # (u∈A et (v∈B ou v∈C)) ⇔ ((u∈A et v∈B) ou (u∈A et v∈C))
    e3 = et_ou_distrib(uA, appartient(vv, vB), appartient(vv, vC))
    # ((u∈A et v∈B) ou (u∈A et v∈C)) ⇔ ((u,v)∈A×B ou (u,v)∈A×C)
    e4 = ou_congruence(equivalence_symetrie(couple_dans_produit_ssi(vu, vv, vA, vB)),
                       equivalence_symetrie(couple_dans_produit_ssi(vu, vv, vA, vC)))
    # ((u,v)∈A×B ou (u,v)∈A×C) ⇔ (u,v)∈(A×B)∪(A×C)
    e5 = equivalence_symetrie(_instance_reunion(E.produit(vA, vB), E.produit(vA, vC),
                                                E.couple(vu, vv)))
    return equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        equivalence_transitivite(e1, e2), e3), e4), e5)


def couple_dans_produit_distributif_intersection(u="u", v="v", a="A", b="B", c="C"):
    """⊢ ((u,v) ∈ A×(B∩C)) ⇔ ((u,v) ∈ (A×B)∩(A×C)).   (cœur de A×(B∩C)=(A×B)∩(A×C), E.II.2.)"""
    vu, vv, vA, vB, vC = _t(u), _t(v), _t(a), _t(b), _t(c)
    BC = E.intersection(vB, vC)
    uA = appartient(vu, vA)
    pAB = et(uA, appartient(vv, vB))
    AC = E.produit(vA, vC)
    # (u,v)∈A×(B∩C) ⇔ (u∈A et v∈B∩C)
    e1 = couple_dans_produit_ssi(vu, vv, vA, BC)
    # (u∈A et v∈B∩C) ⇔ (u∈A et (v∈B et v∈C))
    e2 = et_congruence_droite(uA, _instance_inter(vB, vC, vv))
    # (u∈A et (v∈B et v∈C)) ⇔ ((u∈A et v∈B) et (u∈A et v∈C))
    e3 = _et_et_distrib(uA, appartient(vv, vB), appartient(vv, vC))
    # ((u∈A et v∈B) et (u∈A et v∈C)) ⇔ ((u,v)∈A×B et (u,v)∈A×C)   (congruence des 2 conjoints)
    e4a = et_congruence_droite(pAB, equivalence_symetrie(couple_dans_produit_ssi(vu, vv, vA, vC)))
    e4b = et_congruence_gauche(equivalence_symetrie(couple_dans_produit_ssi(vu, vv, vA, vB)),
                              appartient(E.couple(vu, vv), AC))
    e4 = equivalence_transitivite(e4a, e4b)
    # ((u,v)∈A×B et (u,v)∈A×C) ⇔ (u,v)∈(A×B)∩(A×C)
    e5 = equivalence_symetrie(_instance_inter(E.produit(vA, vB), AC, E.couple(vu, vv)))
    return equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        equivalence_transitivite(e1, e2), e3), e4), e5)


def _reshuffle4(p, q, r, s):
    """⊢ ((P et Q) et (R et S)) ⇔ ((P et R) et (Q et S))   (échange des conjoints médians)."""
    from bourbaki.logique.formule import et as _et
    h = N.assume(_et(_et(p, q), _et(r, s)))
    pq, rs = conjonction_elim_gauche(h), conjonction_elim_droite(h)
    fwd = N.loi_deduction(_et(_et(p, q), _et(r, s)), conjonction_intro(
        conjonction_intro(conjonction_elim_gauche(pq), conjonction_elim_gauche(rs)),
        conjonction_intro(conjonction_elim_droite(pq), conjonction_elim_droite(rs))))
    h2 = N.assume(_et(_et(p, r), _et(q, s)))
    pr, qs = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)
    bwd = N.loi_deduction(_et(_et(p, r), _et(q, s)), conjonction_intro(
        conjonction_intro(conjonction_elim_gauche(pr), conjonction_elim_gauche(qs)),
        conjonction_intro(conjonction_elim_droite(pr), conjonction_elim_droite(qs))))
    return conjonction_intro(fwd, bwd)


def couple_dans_intersection_produits(u="u", v="v", a="A", b="B", c="C", d="D"):
    """⊢ ((u,v) ∈ (A×B)∩(C×D)) ⇔ ((u,v) ∈ (A∩C)×(B∩D)).   (E.II.2 : (A×B)∩(C×D)=(A∩C)×(B∩D).)"""
    vu, vv, vA, vB, vC, vD = _t(u), _t(v), _t(a), _t(b), _t(c), _t(d)
    AB, CD = E.produit(vA, vB), E.produit(vC, vD)
    cpl = E.couple(vu, vv)
    uA, vB_, uC, vD_ = appartient(vu, vA), appartient(vv, vB), appartient(vu, vC), appartient(vv, vD)
    # (u,v)∈(A×B)∩(C×D) ⇔ ((u,v)∈A×B et (u,v)∈C×D)
    e1 = _instance_inter(AB, CD, cpl)
    # ⇔ ((u∈A et v∈B) et (u∈C et v∈D))   (congruence des 2 conjoints)
    e2 = equivalence_transitivite(
        et_congruence_gauche(couple_dans_produit_ssi(vu, vv, vA, vB), appartient(cpl, CD)),
        et_congruence_droite(et(uA, vB_), couple_dans_produit_ssi(vu, vv, vC, vD)))
    # ⇔ ((u∈A et u∈C) et (v∈B et v∈D))   (échange médian)
    e3 = _reshuffle4(uA, vB_, uC, vD_)
    # ⇔ (u∈(A∩C) et v∈(B∩D))
    e4 = equivalence_transitivite(
        et_congruence_gauche(equivalence_symetrie(_instance_inter(vA, vC, vu)), et(vB_, vD_)),
        et_congruence_droite(appartient(vu, E.intersection(vA, vC)),
                             equivalence_symetrie(_instance_inter(vB, vD, vv))))
    # ⇔ (u,v)∈(A∩C)×(B∩D)
    e5 = equivalence_symetrie(couple_dans_produit_ssi(
        vu, vv, E.intersection(vA, vC), E.intersection(vB, vD)))
    return equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        equivalence_transitivite(e1, e2), e3), e4), e5)


__all__ = [
    "couple_dans_produit_distributif_reunion",
    "couple_dans_produit_distributif_intersection",
    "couple_dans_intersection_produits",
]
