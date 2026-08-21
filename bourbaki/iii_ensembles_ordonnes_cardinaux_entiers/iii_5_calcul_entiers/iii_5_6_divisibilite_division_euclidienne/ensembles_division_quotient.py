# -*- coding: utf-8 -*-
"""§III.5.6 — LE QUOTIENT CARACTÉRISÉ : (a = b·q) ⇒ (q = a/b).   (E III.39.)

Le livre, ligne sous la Déf. 1 : « Les relations a = bq et q = a/b sont
équivalentes (si b > 0). »  — sous la CONVENTION énoncée juste avant :
« le seul fait d'écrire a/b implique que b divise a ».  La formalisation
fidèle est donc en deux moitiés ; ce fichier livre la PREMIÈRE :

    ⊢ {Fini b, Fini q, Fini (a/b), 0 < b, + résidus C61}
        ( a = b·q ) ⇒ ( q = a/b )

où a/b := quotient_cardinal(a, b) — le τ canonique de la Déf. 1.  PREMIÈRE
CONSOMMATION du Théorème 1 complet : c'est l'UNICITÉ qui identifie q au τ.

Stratégie (chaque pas jugé noyau) :
  1. a = b·q  →[symétrie + neutre droit a+0=a]  b·q + 0 = a ; avec 0 < b le
     couple (q, 0) satisfait la relation de division ;
  2. ∃-intro ×2 (S5) → (∃q')(∃r)( b·q'+r = a et r < b ) ;
  3. existe_temoin (l'identité-τ du noyau) → le τ T = a/b satisfait
     (∃r)( b·T + r = a et r < b ) ;
  4. sous ce reste r : Fini r par fini_downward (r < b, Fini b), puis
     l'UNICITÉ du Th.1 sur (q, 0) et (T, r) donne q = T ; l'∃ du reste est
     éliminé (r non libre dans q = T).

RÉSIDUS HONNÊTES, tous déclarés : Fini(a/b) — le livre dit « les entiers q
et r », la finitude du τ-quotient est prise en hypothèse (la dériver
demanderait l'inversion de finitude du produit, chantier séparé) ; et les
résidus C61 standard (principe_recurrence, cardinal_pas_entre) hérités de
fini_downward — la même classe que le Th.1 lui-même.

⚠️ DETTE DE RANGEMENT, signalée : le dossier division compte déjà 11 entrées
(convention 10) ; ce fichier y va parce que c'est sa place sémantique.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, existe, tau, impl)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, ZERO)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    fini_downward_thm)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_zero_neutre_droite)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_binaire_entier)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence import (
    _bqr)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_definitions import (
    quotient_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_unicite import (
    _unicite)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, P, pr):
    """Décharge l'hypothèse P de `thm` en la remplaçant par sa preuve `pr`."""
    return N.modus_ponens(pr, N.loi_deduction(P, thm))


def _inst2(thm_libre, noms, termes):
    """∀-clôture d'un lemme à variables libres, puis instances aux TERMES
    (jamais var() sur un Terme — piège mesuré le 21 août)."""
    th = thm_libre
    for n in noms:
        th = N.generalisation(n, th)
    for t in termes:
        th = instancie(th, t)
    return th


def enonce_quotient_de_produit(a="aqt", b="bqt", q="qqt"):
    va, vb, vq = _t(a), _t(b), _t(q)
    return impl(egal(va, produit_cardinal_binaire(vb, vq)),
                egal(vq, quotient_cardinal(va, vb)))


# @livre Ch.III §5.6 Rem.- | E III.39 L.30-30 | PDF p.142
def quotient_de_produit(a="aqt", b="bqt", q="qqt"):
    """🎯 ⊢ ( a = b·q ) ⇒ ( q = a/b ).   (Première moitié de l'équivalence du livre.)"""
    va, vb, vq = _t(a), _t(b), _t(q)
    PCBbq = produit_cardinal_binaire(vb, vq)
    T = quotient_cardinal(va, vb)                        # a/b = τqd(∃rr(...))
    vr = var("rr")

    #   sanité : le τ rebâti coïncide avec la Déf. 1 (égalité d'assemblages)
    R_q = existe("rr", et(egal(_bqr(vb, var("qd"), vr), va),
                          inf_strict_card(vr, vb)))
    assert tau("qd", R_q) == T, "quotient_de_produit : τ ≠ Déf.1"

    #   hypothèses (du livre, et résidus déclarés)
    h_eq = N.assume(egal(va, PCBbq))                     # a = b·q
    fin_b = N.assume(est_fini(vb))
    fin_q = N.assume(est_fini(vq))
    b_pos = N.assume(inf_strict_card(ZERO, vb))          # b > 0

    #   1. b·q + 0 = a
    bq_eq_a = N.modus_ponens(h_eq, symetrie(va, PCBbq))  # b·q = a
    fini_bq = N.modus_ponens(
        conjonction_intro(fin_b, fin_q),
        _inst2(produit_binaire_entier("Apbe3", "Bpbe3"), ["Apbe3", "Bpbe3"],
               [vb, vq]))                                # Fini(b·q)
    card_bq = N.modus_ponens(fini_bq, fini_implique_cardinal(PCBbq))
    neutre = N.modus_ponens(card_bq, somme_zero_neutre_droite(PCBbq))
    bq0_eq_a = composer_egalites(neutre, bq_eq_a)        # b·q + 0 = a

    #   2. ∃-intro ×2 : le couple (q, 0) témoigne
    R_r_at_q = et(egal(_bqr(vb, vq, vr), va), inf_strict_card(vr, vb))
    w = conjonction_intro(bq0_eq_a, b_pos)               # (0|rr) R_r_at_q
    ex_r = N.modus_ponens(w, N.s5(R_r_at_q, ZERO, "rr"))
    ex_qr = N.modus_ponens(ex_r, N.s5(R_q, vq, "qd"))    # (∃qd) R_q

    #   3. l'identité-τ : le quotient satisfait sa propriété
    t_prop = N.modus_ponens(ex_qr, N.existe_temoin(R_q, "qd"))
    #        = (∃rr)( b·T + rr = a  et  rr < b )

    #   4. sous le reste : unicité ⇒ q = T, puis élimination de l'∃
    m_T = et(egal(_bqr(vb, T, vr), va), inf_strict_card(vr, vb))
    hT = N.assume(m_T)
    r_lt_b = conjonction_elim_droite(hT)                 # rr < b
    fini_rr = N.modus_ponens(
        conjonction_intro(conjonction_elim_gauche(r_lt_b), fin_b),
        instancie(instancie(fini_downward_thm(), vr), vb))   # Fini rr  [C61]
    uni = _unicite(va, vb, vq, T, ZERO, "rr")
    uni = _cut(uni, est_fini(ZERO), fini_zero())         # Fini 0, dérivé
    uni = _cut(uni, est_fini(vr), fini_rr)               # Fini rr, via m_T
    ante = conjonction_intro(
        conjonction_intro(conjonction_intro(bq0_eq_a, b_pos),
                          conjonction_elim_gauche(hT)), r_lt_b)
    q_eq_T = conjonction_elim_gauche(N.modus_ponens(ante, uni))   # q = T
    step = N.loi_deduction(m_T, q_eq_T)
    q_eq_T_libre = N.modus_ponens(t_prop, existe_elimination(step, "rr"))

    res = N.loi_deduction(egal(va, PCBbq), q_eq_T_libre)
    assert res.conclusion == enonce_quotient_de_produit(a, b, q), \
        "quotient_de_produit : conclusion inattendue"
    return res


__all__ = ["enonce_quotient_de_produit", "quotient_de_produit"]
