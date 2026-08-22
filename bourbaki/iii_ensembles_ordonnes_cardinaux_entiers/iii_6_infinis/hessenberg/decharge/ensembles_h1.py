# -*- coding: utf-8 -*-
"""§III.6.3 — H1 : L'AMORÇAGE DU FRAME DE ZORN — 𝔉(E) ≠ ∅ (par le Lemme 1).

🎯 CIBLE (le résidu H1 de la campagne Hessenberg, frame_maximal_clos) :

    h1_decharge :  { est_infini(Card E) }  ⊢  (∃x)( x ∈ 𝔉(E) )

Le témoin est le couple (D, ψ) : D vient du LEMME 1 (D⊂E, Eq(D,ℕ)) ; ψ est
le τ-témoin de Eq(D×D, D), qui suit de Eq(D,ℕ) par l'invariance du produit
et le LEMME 2 (Eq(ℕ×ℕ,ℕ), clos) ; « D infini » se lit sur Card D = Card ℕ.

theorie_ensembles() INCHANGÉE (22).  theorie_frame = S8 dédiée (jamais
auto-référente).  Noyau INTACT.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, appartient, existe, inclus, tau,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, equipotent, est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    _sym_all, _trans_all,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
    eq_produit_invariant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    _prop1_direct_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini, est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_iii6 import (
    NN_est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_graphe_pairing import (
    lemme_deux_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, _corps_frame,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import (
    _frame_membre_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_lemme1 import (
    lemme_1,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def eq_DD_D(d="Dld"):
    """{ Eq(D,ℕ) } ⊢ Eq(D×D, D)   (invariance du produit + Lemme 2 + sym/trans)."""
    vD = _t(d)
    NN = ensemble_NN()
    h_eq = N.assume(equipotent(vD, NN))                     # Eq(D,ℕ)  [HONNÊTE]
    inv = instancie(instancie(instancie(instancie(
        N.generalisation("X", N.generalisation("Y", N.generalisation(
            "X1", N.generalisation("Y1",
            eq_produit_invariant("F", "G", "X", "Y", "X1", "Y1"))))),
        vD), vD), NN), NN)
    e1 = N.modus_ponens(conjonction_intro(h_eq, h_eq), inv)  # Eq(D×D, ℕ×ℕ)
    sym, trans = _sym_all(), _trans_all()
    e3 = N.modus_ponens(h_eq, instancie(instancie(sym, vD), NN))  # Eq(ℕ, D)
    DD, NNNN = E.produit(vD, vD), E.produit(NN, NN)
    t1 = N.modus_ponens(conjonction_intro(e1, lemme_deux_NN()),
        instancie(instancie(instancie(trans, DD), NNNN), NN))  # Eq(D×D, ℕ)
    res = N.modus_ponens(conjonction_intro(t1, e3),
        instancie(instancie(instancie(trans, DD), NN), vD))    # Eq(D×D, D)
    assert res.conclusion == equipotent(DD, vD), "eq_DD_D : forme"
    assert list(res.hypotheses) == [equipotent(vD, NN)], "eq_DD_D : hyps"
    return res


def psi_de(d="Dld"):
    """ψ := τ_F( est_bijection_de(F, D×D, D) ) — le témoin canonique du τ."""
    vD = _t(d)
    return tau("F", est_bijection_de(var("F"), E.produit(vD, vD), vD))


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def psi_bijection(d="Dld"):
    """{ Eq(D,ℕ) } ⊢ est_bijection_de(ψ, D×D, D)   (existe_temoin sur Eq(D×D,D))."""
    vD = _t(d)
    R = est_bijection_de(var("F"), E.produit(vD, vD), vD)
    res = N.modus_ponens(eq_DD_D(d), N.existe_temoin(R, "F"))
    assert res.conclusion == est_bijection_de(psi_de(d), E.produit(vD, vD), vD), \
        "psi_bijection : forme"
    return res


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def d_infini(d="Dld"):
    """{ Eq(D,ℕ) } ⊢ est_infini_ensemble(D)   (Card D = Card ℕ, ℕ infini)."""
    vD = _t(d)
    NN = ensemble_NN()
    h_eq = N.assume(equipotent(vD, NN))
    c_eq = N.modus_ponens(h_eq, _prop1_direct_t(vD, NN))    # Card D = Card ℕ
    leib = N.s6(cardinal(vD), cardinal(NN), "wh1",
                non(est_fini(var("wh1"))))
    res = N.modus_ponens(NN_est_infini_ensemble(),
        equivalence_arriere(N.modus_ponens(c_eq, leib)))    # est_infini(Card D)
    assert res.conclusion == est_infini_ensemble(vD), "d_infini : forme"
    assert list(res.hypotheses) == [equipotent(vD, NN)], "d_infini : hyps"
    return res


@lru_cache(maxsize=None)  # pur : Theoreme immuable, args hashables
def temoin_frame(d="Dld", e="Eld"):
    """{ D⊂E, Eq(D,ℕ) } ⊢ (∃x)( x ∈ 𝔉(E) )   [2 hyps — le témoin (D, ψ)]."""
    vD, ve = _t(d), _t(e)
    psi = psi_de(d)
    p = E.couple(vD, psi)
    h_incl = N.assume(inclus(vD, ve))                       # D⊂E  [HONNÊTE]
    corps = conjonction_intro(conjonction_intro(conjonction_intro(
        N.reflexivite(p), h_incl), d_infini(d)), psi_bijection(d))
    #   (∃φ) puis (∃S) : témoins ψ puis D  (liants S/phi de l'axiome-frame)
    vS, vphi = var("S"), var("phi")
    body_phi = et(et(et(egal(p, E.couple(vD, vphi)), inclus(vD, ve)),
                     est_infini_ensemble(vD)),
                  est_bijection_de(vphi, E.produit(vD, vD), vD))
    ex_phi = N.modus_ponens(corps, N.s5(body_phi, psi, "phi"))
    body_S = et(et(et(egal(p, E.couple(vS, vphi)), inclus(vS, ve)),
                   est_infini_ensemble(vS)),
                est_bijection_de(vphi, E.produit(vS, vS), vS))
    ex_S = N.modus_ponens(ex_phi, N.s5(existe("phi", body_S), vD, "S"))
    assert ex_S.conclusion == _corps_frame(ve, p), "temoin_frame : corps"
    p_in = N.modus_ponens(ex_S, equivalence_arriere(_frame_membre_t(ve, p)))
    res = N.modus_ponens(p_in,
        N.s5(appartient(var("x"), frame_pair(ve)), p, "x"))
    assert res.conclusion == residu_H1(e), "temoin_frame : forme"
    assert len(res.hypotheses) == 2, "temoin_frame : hyps ≠ 2"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.22-25 | PDF p.151  (« 𝔐 n'est pas vide » —
#   l'amorçage de Zorn par les Lemmes 1 et 2, ici déchargé)
def h1_decharge(e="Eld", d="Dld"):
    """🎯 H1 : { est_infini(Card E) } ⊢ (∃x)( x ∈ 𝔉(E) )   [1 hyp].

    Le Lemme 1 fournit (∃D)(D⊂E ∧ Eq(D,ℕ)) ; sous son corps, temoin_frame
    conclut ; élimination du témoin D."""
    ve, vD = _t(e), _t(d)
    NN = ensemble_NN()
    corps_l1 = et(inclus(vD, ve), equipotent(vD, NN))
    h_c = N.assume(corps_l1)
    b = _cut(conjonction_elim_gauche(h_c), inclus(vD, ve), temoin_frame(d, e))
    b = _cut(conjonction_elim_droite(h_c), equipotent(vD, NN), b)
    imp = N.loi_deduction(corps_l1, b)
    ex = existe_elimination(imp, d if isinstance(d, str) else d.nom)
    res = N.modus_ponens(lemme_1(e), ex)
    assert res.conclusion == residu_H1(e), "h1_decharge : forme"
    assert list(res.hypotheses) == [est_infini(cardinal(ve))], \
        "h1_decharge : hyps"
    return res


__all__ = ["eq_DD_D", "psi_de", "psi_bijection", "d_infini",
           "temoin_frame", "h1_decharge"]
