"""§III.5.6 Th.1 — DIVISION EUCLIDIENNE, UNICITÉ du quotient et du reste (E III.39).

⊢ {Fini a, Fini b, b≠0} ⊢ ( b·q+r=a et r<b et b·q'+r'=a et r'<b ) ⇒ ( q=q' et r=r' ).

Bâti INCRÉMENTALEMENT (sous-lemmes testables) à partir de briques CLOSES :
  · _gap        : q<q' ⇒ succ(q) ≤ q'   (gap successeur des entiers) ;
  · _lt_chain   : q<q' ⇒ b·q+r < b·q'+r'   (le cœur : la « marche » b entre q et q+1) ;
  · unicite     : trichotomie sur q,q' + simplification additive pour r=r'.

Route SANS commutativité du produit (produit_cardinale_monotone_droite fixe le facteur
gauche b).  « CLOS modulo C61 » : résidus honnêtes b≠0 + C61 (via successeur_ordre_strict).
theorie == 22 ; NOMS FRAIS.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, ou, impl, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, contraposition, cas)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import successeur_ordre_strict
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card, inf_egal_reflexif_general)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import trichotomie_finis
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
    strict_implique_inf_egal, _ex_falso, strict_inf_egal_compose, strict_irreflexif)
# — briques _lt_chain (route SANS commutativité) —
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, somme_cardinale_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop4_strict_iii5 import (
    prop4_translation_stricte, prop4_translation_injective)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_binaire_entier, produit_succ_distribue)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinal_ordre_props import produit_cardinale_monotone_droite
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import inf_egal_somme_gauche_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import inf_egal_transitive_general


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_gen(thm, noms, termes):
    g = thm
    for nom in reversed(noms):
        g = N.generalisation(nom, g)
    for t in termes:
        g = instancie(g, t)
    return g


def _cut(thm, P, pr):
    return N.modus_ponens(pr, N.loi_deduction(P, thm))


def _ec(Z):
    """⊢ est_cardinal(Card Z)   (tout Card d'un terme est un cardinal ; témoin Z)."""
    cZ = cardinal(Z)
    ecf = est_cardinal(cZ)                    # existe(X, cZ = Card X)
    return N.modus_ponens(N.reflexivite(cZ), N.s5(ecf.sous[0], Z, ecf.lieur))


def _reecrit(thm, egalite, gauche, droite, contexte_hole):
    """Réécrit `gauche`↦`droite` dans thm via l'égalité (gauche=droite) et s6 ; contexte_hole
    est la formule-contexte avec le trou var('__h'). thm doit conclure contexte[gauche]."""
    leib = N.s6(gauche, droite, "__h", contexte_hole)
    return N.modus_ponens(thm, equivalence_avant(N.modus_ponens(egalite, leib)))


def enonce_gap(q="qu", qp="qpu"):
    vq, vqp = var(q), var(qp)
    return impl(inf_strict_card(vq, vqp), inf_egal_card(successeur(vq), vqp))


# @livre Ch.III §5.6 Demo.- | E III.39 L.10-19 | PDF p.142   (gap successeur : q<q' ⇒ q+1≤q')
def _gap(q="qu", qp="qpu"):
    """⊢ {card q, card q', Fini q} ⊢ ( q < q' ) ⇒ ( succ(q) ≤ q' ).

    q<q' ⇒ ¬(q'≤q) [antisymétrie] ⇒ ¬(q'<q+1) [successeur_ordre_strict] ; puis trichotomie
    sur (succ q, q') élimine le cas impossible q'<succ q (_ex_falso)."""
    vq, vqp = _t(q), _t(qp)
    sq = successeur(vq)
    card_q = N.assume(est_cardinal(vq))
    card_qp = N.assume(est_cardinal(vqp))
    fini_q = N.assume(est_fini(vq))
    h_lt = N.assume(inf_strict_card(vq, vqp))                 # q < q'
    q_le_qp = conjonction_elim_gauche(h_lt)                   # q ≤ q'
    q_ne_qp = conjonction_elim_droite(h_lt)                   # ¬(q = q')

    # ¬(q' ≤ q) : (q'≤q) ⇒ q'=q [antisym] ⇒ q=q' [sym], contredit ¬(q=q')
    antisym = instancie(instancie(inf_egal_antisymetrique_card(), vqp), vq)   # (q'≤q et q≤q' et card q' et card q)⇒q'=q
    h_qple = N.assume(inf_egal_card(vqp, vq))
    qp_eq_q = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(h_qple, q_le_qp), card_qp), card_q), antisym)      # q'=q
    q_eq_qp = N.modus_ponens(qp_eq_q, symetrie(vqp, vq))                     # q=q'
    imp_qple_eq = N.loi_deduction(inf_egal_card(vqp, vq), q_eq_qp)           # (q'≤q)⇒(q=q')
    not_qple = N.modus_ponens(q_ne_qp, contraposition(imp_qple_eq))          # ¬(q'≤q)

    # ¬(q' < succ q) : successeur_ordre_strict(q',q) : (q'<q+1)⟺(q'≤q)
    sos = N.modus_ponens(conjonction_intro(card_qp, fini_q), successeur_ordre_strict(qp, q))
    not_qp_lt_sq = N.modus_ponens(not_qple, contraposition(equivalence_avant(sos)))  # ¬(q'<succ q)

    # trichotomie_finis(succ q, q') = (succ q<q') OU ((succ q=q') OR (q'<succ q))
    trich = trichotomie_finis(sq, vqp)
    lt_sqqp = inf_strict_card(sq, vqp)
    eq_sqqp = egal(sq, vqp)
    lt_qpsq = inf_strict_card(vqp, sq)
    target = inf_egal_card(sq, vqp)

    br1 = N.loi_deduction(lt_sqqp,
        N.modus_ponens(N.assume(lt_sqqp), strict_implique_inf_egal(sq, vqp)))   # (succ q<q')⇒succ q≤q'
    refl_sq = instancie(inf_egal_reflexif_general(), sq)                        # succ q ≤ succ q
    h_eq = N.assume(eq_sqqp)
    leibg = N.s6(sq, vqp, "wg", inf_egal_card(sq, var("wg")))                   # (succ q=q')⇒(succ q≤succ q ⟺ succ q≤q')
    br_eq = N.loi_deduction(eq_sqqp,
        N.modus_ponens(refl_sq, equivalence_avant(N.modus_ponens(h_eq, leibg))))  # (succ q=q')⇒succ q≤q'
    br_lt2 = N.loi_deduction(lt_qpsq, _ex_falso(N.assume(lt_qpsq), not_qp_lt_sq, target))  # (q'<succ q)⇒succ q≤q'
    inner_disj = ou(eq_sqqp, lt_qpsq)
    br_rest = N.loi_deduction(inner_disj, cas(N.assume(inner_disj), br_eq, br_lt2))
    R_target = cas(trich, br1, br_rest)                                        # succ q ≤ q'
    res = N.loi_deduction(inf_strict_card(vq, vqp), R_target)                  # (q<q') ⇒ (succ q ≤ q')
    assert res.conclusion == enonce_gap(q, qp), "_gap : conclusion inattendue"
    return res


def enonce_lt_chain(b="blc", q="qlc", qp="qplc", r="rlc", rp="rplc"):
    vb, vq, vqp, vr, vrp = var(b), var(q), var(qp), var(r), var(rp)
    scb, pcb = somme_cardinale_binaire, produit_cardinal_binaire
    return inf_strict_card(scb(pcb(vb, vq), vr), scb(pcb(vb, vqp), vrp))


# @livre Ch.III §5.6 Demo.- | E III.39 L.10-19 | PDF p.142   (le cœur : b·q+r < b·q'+r' si q<q')
def _lt_chain(b="blc", q="qlc", qp="qplc", r="rlc", rp="rplc"):
    """⊢ {Fini b, Fini q, Fini q', Fini r ; q<q' ; r<b} ⊢ b·q+r < b·q'+r'.   (SANS commutativité.)"""
    vb, vq, vqp, vr, vrp = _t(b), _t(q), _t(qp), _t(r), _t(rp)
    scb, pcb = somme_cardinale_binaire, produit_cardinal_binaire
    bq = pcb(vb, vq); bqp = pcb(vb, vqp); sq = successeur(vq); bsq = pcb(vb, sq)
    bq_r = scb(bq, vr); bq_b = scb(bq, vb); bqp_rp = scb(bqp, vrp)
    fin_b = N.assume(est_fini(vb)); fin_q = N.assume(est_fini(vq))
    fin_qp = N.assume(est_fini(vqp)); fin_r = N.assume(est_fini(vr))
    h_qlt = N.assume(inf_strict_card(vq, vqp)); h_rlt = N.assume(inf_strict_card(vr, vb))
    card_b = N.modus_ponens(fin_b, fini_implique_cardinal(vb))
    card_q = N.modus_ponens(fin_q, fini_implique_cardinal(vq))
    card_qp = N.modus_ponens(fin_qp, fini_implique_cardinal(vqp))
    card_r = N.modus_ponens(fin_r, fini_implique_cardinal(vr))
    pbe = _inst_gen(produit_binaire_entier("Apbe", "Bpbe"), ["Apbe", "Bpbe"], [vb, vq])   # (Fini b,Fini q)⇒Fini(b·q)
    fin_bq = N.modus_ponens(conjonction_intro(fin_b, fin_q), pbe)                          # Fini(b·q)

    # S1 : b·q+r < b·q+b   (prop4_translation_stricte, a=b·q fixe à gauche — PAS de commute)
    pts = _inst_gen(prop4_translation_stricte("Apts", "Xpts", "Xppts"),
                    ["Apts", "Xpts", "Xppts"], [bq, vr, vb])
    s1 = N.modus_ponens(h_rlt, N.modus_ponens(
        conjonction_intro(conjonction_intro(fin_bq, card_r), card_b), pts))              # b·q+r < b·q+b
    # b·q+b = b·(q+1)
    psd = N.modus_ponens(conjonction_intro(card_b, card_q), produit_succ_distribue(vb, vq))  # b·(q+1)=b·q+b
    bqb_eq_bsq = N.modus_ponens(psd, symetrie(bsq, bq_b))                                 # b·q+b = b·(q+1)
    s1b = _reecrit(s1, bqb_eq_bsq, bq_b, bsq, inf_strict_card(bq_r, var("__h")))          # b·q+r < b·(q+1)

    # S2 : b·(q+1) ≤ b·q'
    succ_le = N.modus_ponens(h_qlt, _gap(q, qp))                                          # succ q ≤ q'
    succ_le = _cut(succ_le, est_cardinal(vq), card_q)
    succ_le = _cut(succ_le, est_cardinal(vqp), card_qp)
    pcmd = _inst_gen(produit_cardinale_monotone_droite("Bpm", "B1pm", "Cpm"),
                     ["Bpm", "B1pm", "Cpm"], [sq, vqp, vb])                               # (succ q≤q')⇒ b·(q+1)≤b·q'
    s2 = N.modus_ponens(succ_le, pcmd)                                                    # b·(q+1) ≤ b·q'

    # S3 : b·q' ≤ b·q'+r'
    isgb = _inst_gen(inf_egal_somme_gauche_binaire("Aisg", "Bisg"), ["Aisg", "Bisg"], [bqp, vrp])  # Card(b·q')≤b·q'+r'
    cdc = N.modus_ponens(_ec(E.produit(vb, vqp)), cardinal_de_cardinal(bqp))              # Card(b·q')=b·q'
    s3 = _reecrit(isgb, cdc, cardinal(bqp), bqp, inf_egal_card(var("__h"), bqp_rp))       # b·q' ≤ b·q'+r'

    # combine : b·(q+1) ≤ b·q'+r'  puis  b·q+r < b·q'+r'
    itg = instancie(instancie(instancie(                                                 # déjà ∀-clos : instancier direct
        inf_egal_transitive_general("Xit", "Yit", "Zit"), bsq), bqp), bqp_rp)
    s23 = N.modus_ponens(conjonction_intro(s2, s3), itg)                                  # b·(q+1) ≤ b·q'+r'
    sic = strict_inf_egal_compose(bq_r, bsq, bqp_rp)                                      # (a<b,b≤c,cards)⇒a<c
    ec1, ec2, ec3 = _ec(somme_disjointe(bq, vr)), _ec(E.produit(vb, sq)), _ec(somme_disjointe(bqp, vrp))
    res = N.modus_ponens(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(s1b, s23), ec1), ec2), ec3), sic)                              # b·q+r < b·q'+r'
    assert res.conclusion == enonce_lt_chain(b, q, qp, r, rp), "_lt_chain : conclusion inattendue"
    return res


def enonce_unicite(a="auc", b="buc", q="quc", qp="qpuc", r="ruc", rp="rpuc"):
    va, vb, vq, vqp, vr, vrp = var(a), var(b), var(q), var(qp), var(r), var(rp)
    scb, pcb = somme_cardinale_binaire, produit_cardinal_binaire
    bqr = scb(pcb(vb, vq), vr); bqprp = scb(pcb(vb, vqp), vrp)
    ante = et(et(et(egal(bqr, va), inf_strict_card(vr, vb)),
                 egal(bqprp, va)), inf_strict_card(vrp, vb))
    return impl(ante, et(egal(vq, vqp), egal(vr, vrp)))


# @livre Ch.III §5.6 Th.1 | E III.39 L.10-19 | PDF p.142   (UNICITÉ de q et r)
def _unicite(a="auc", b="buc", q="quc", qp="qpuc", r="ruc", rp="rpuc"):
    """⊢ {Fini b, Fini q, Fini q', Fini r, Fini r'} ⊢
         ( b·q+r=a et r<b et b·q'+r'=a et r'<b ) ⇒ ( q=q' et r=r' ).   (« CLOS modulo C61 ».)"""
    va, vb, vq, vqp, vr, vrp = _t(a), _t(b), _t(q), _t(qp), _t(r), _t(rp)
    scb, pcb = somme_cardinale_binaire, produit_cardinal_binaire
    bqr = scb(pcb(vb, vq), vr); bqprp = scb(pcb(vb, vqp), vrp)
    fin_b = N.assume(est_fini(vb)); fin_q = N.assume(est_fini(vq)); fin_qp = N.assume(est_fini(vqp))
    fin_r = N.assume(est_fini(vr)); fin_rp = N.assume(est_fini(vrp))
    ante = et(et(et(egal(bqr, va), inf_strict_card(vr, vb)), egal(bqprp, va)), inf_strict_card(vrp, vb))
    h = N.assume(ante)
    h_eq1 = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))   # b·q+r = a
    h_r = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))      # r < b
    h_eq2 = conjonction_elim_droite(conjonction_elim_gauche(h))                             # b·q'+r' = a
    h_rp = conjonction_elim_droite(h)                                                       # r' < b
    # b·q+r = b·q'+r'
    eq_bb = composer_egalites(h_eq1, N.modus_ponens(h_eq2, symetrie(bqprp, va)))            # bqr = bqprp
    eq_bb_sym = N.modus_ponens(eq_bb, symetrie(bqr, bqprp))                                 # bqprp = bqr
    eq_qqp = egal(vq, vqp)

    # CAS q<q' : _lt_chain ⇒ bqr<bqprp = bqr<bqr (contra)
    lc1 = _lt_chain(b, q, qp, r, rp)                                                        # {…,q<q',r<b} bqr<bqprp
    lc1_rw = _reecrit(lc1, eq_bb_sym, bqprp, bqr, inf_strict_card(bqr, var("__h")))         # bqr < bqr
    br_lt = N.loi_deduction(inf_strict_card(vq, vqp),
        _ex_falso(lc1_rw, strict_irreflexif(bqr), eq_qqp))                                  # (q<q')⇒(q=q')
    # CAS q'<q : _lt_chain sens inverse ⇒ bqprp<bqr = bqr<bqr (contra)  [via bqprp=bqr]
    lc2 = _lt_chain(b, qp, q, rp, r)                                                        # {…,q'<q,r'<b} bqprp<bqr
    lc2_rw = _reecrit(lc2, eq_bb, bqr, bqprp, inf_strict_card(bqprp, var("__h")))           # bqprp < bqprp
    br_ltp = N.loi_deduction(inf_strict_card(vqp, vq),
        _ex_falso(lc2_rw, strict_irreflexif(bqprp), eq_qqp))                                # (q'<q)⇒(q=q')
    # CAS q=q'
    br_eq = N.loi_deduction(eq_qqp, N.assume(eq_qqp))                                       # (q=q')⇒(q=q')
    trich = trichotomie_finis(vq, vqp)                                                      # (q<q')OU((q=q')OR(q'<q))
    inner = ou(eq_qqp, inf_strict_card(vqp, vq))
    q_eq = cas(trich, br_lt, N.loi_deduction(inner, cas(N.assume(inner), br_eq, br_ltp)))   # q = q'

    # r = r' : b·q+r = b·q+r' [réécrire q'→q] puis prop4_translation_injective
    eq_bqr_bqrp = _reecrit(eq_bb, N.modus_ponens(q_eq, symetrie(vq, vqp)), vqp, vq,
                           egal(bqr, scb(pcb(vb, var("__h")), vrp)))                        # b·q+r = b·q+r'
    pti = _inst_gen(prop4_translation_injective("Api", "Xpi", "Xppi"),
                    ["Api", "Xpi", "Xppi"], [pcb(vb, vq), vr, vrp])                          # (ent b·q,card r,card r')⇒(b·q+r=b·q+r'⇒r=r')
    pbe = _inst_gen(produit_binaire_entier("Apbe2", "Bpbe2"), ["Apbe2", "Bpbe2"], [vb, vq])
    fin_bq = N.modus_ponens(conjonction_intro(fin_b, fin_q), pbe)                           # Fini(b·q)
    card_r = N.modus_ponens(fin_r, fini_implique_cardinal(vr))
    card_rp = N.modus_ponens(fin_rp, fini_implique_cardinal(vrp))
    r_eq = N.modus_ponens(eq_bqr_bqrp, N.modus_ponens(
        conjonction_intro(conjonction_intro(fin_bq, card_r), card_rp), pti))                # r = r'

    res = N.loi_deduction(ante, conjonction_intro(q_eq, r_eq))
    assert res.conclusion == enonce_unicite(a, b, q, qp, r, rp), "_unicite : conclusion inattendue"
    return res


__all__ = ["enonce_gap", "_gap", "enonce_lt_chain", "_lt_chain", "enonce_unicite", "_unicite"]
