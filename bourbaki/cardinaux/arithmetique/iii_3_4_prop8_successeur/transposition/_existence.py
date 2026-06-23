"""§III.3 — EXISTENCE de la transposition comme BIJECTION envoyant q sur p.

  transposition_existe(S,p,q) :
    ⊢ (p∈S et q∈S et ¬(p=q)) ⇒ (∃τ)(est_bijection_de(τ, S, S) et τ(q)=p).

ASSEMBLAGE des 4 conjoints (fonctionnel/domaine/injective/image, tous CLOS sous
leurs conditions) en est_bijection_de(τ,S,S), avec transpo_valeur_q (τ(q)=p), puis
S5 prend le TERME τ comme témoin.  C'est la transposition CONSTRUITE et PROUVÉE
(aucun postulat) : un échange ponctuel p↔q dans S, identité ailleurs.
"""
from __future__ import annotations

import functools

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, appartient, existe)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition._membre import transpo
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition._bijection import (
    transpo_fonctionnel, transpo_domaine)
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition._injective import (
    transpo_injective)
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.transposition._valeur_image import (
    transpo_valeur_q, transpo_image)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


@functools.lru_cache(maxsize=None)
def transposition_existe(s="S", p="p", q="q"):
    """⊢ (p∈S et q∈S et ¬(p=q)) ⇒ (∃τ)(est_bijection_de(τ, S, S) et τ(q)=p).

    Sous (p∈S et q∈S et ¬(p=q)), les 4 conjoints de est_bijection_de(τ,S,S) sont
    réunis : est_fonctionnel(τ) [¬(p=q)], dom(τ)=S [p,q∈S], injective_dans(τ,S) et
    image(τ,S)=S [p,q∈S,¬(p=q)] ; transpo_valeur_q donne τ(q)=p.  S5 prend τ comme
    témoin du ∃.  La transposition est CONSTRUITE (terme transpo) — rien postulé."""
    vS, vp, vq = _t(s), _t(p), _t(q)
    T = transpo(vS, vp, vq)
    pin, qin, npq = appartient(vp, vS), appartient(vq, vS), non(egal(vp, vq))
    hyp = et(et(pin, qin), npq)

    hfull = N.assume(hyp)
    pq = conjonction_elim_gauche(hfull)                        # (p∈S et q∈S)
    pin_t = conjonction_elim_gauche(pq)                        # p∈S
    qin_t = conjonction_elim_droite(pq)                        # q∈S
    npq_t = conjonction_elim_droite(hfull)                     # ¬(p=q)

    # les 4 conjoints, hypothèses coupées par les composantes de hyp
    fonc = N.modus_ponens(npq_t, transpo_fonctionnel(s, p, q))         # est_fonctionnel(τ)
    domS = N.modus_ponens(pq, transpo_domaine(s, p, q))               # dom(τ)=S
    inj = N.modus_ponens(hfull, transpo_injective(s, p, q))           # injective_dans(τ,S)
    img = N.modus_ponens(hfull, transpo_image(s, p, q))               # image(τ,S)=S
    valq = N.modus_ponens(hfull, transpo_valeur_q(s, p, q))           # τ(q)=p

    # est_bijection_de(τ,S,S) = ((fonctionnel et dom=S) et (injective et image=S))
    bij = conjonction_intro(conjonction_intro(fonc, domS),
                            conjonction_intro(inj, img))               # est_bijection_de(τ,S,S)
    body = conjonction_intro(bij, valq)                                # bij(τ,S,S) et τ(q)=p
    # S5 : (τ|F)(bij(F,S,S) et F(q)=p) ⇒ (∃F)(...)
    matrice = et(est_bijection_de(var("F"), vS, vS),
                 egal(E.valeur(var("F"), vq), vp))
    ex = N.modus_ponens(body, N.s5(matrice, T, "F"))                   # (∃F)(bij(F,S,S) et F(q)=p)  [hyp hyp]
    return N.loi_deduction(hyp, ex)


__all__ = ["transposition_existe"]
