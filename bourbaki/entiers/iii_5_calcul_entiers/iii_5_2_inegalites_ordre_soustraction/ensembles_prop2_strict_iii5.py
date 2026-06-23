"""§III.5.2 — PROPOSITION 2 (INÉGALITÉS STRICTES ENTRE ENTIERS) : a < b ⟺ ∃c>0, b=a+c.

🎯🎯 ÉQUIVALENCE bourbakiste EXACTE (E III.36, Prop. 2, LUE au PDF source) :

    « PROPOSITION 2. — Soient a et b deux entiers ; pour que l'on ait a < b, il faut
      et il suffit qu'il existe un entier c > 0 tel que b = a + c. »

soit, littéralement (c > 0 := c ≠ 0, l'ordre strict sur les cardinaux) :

    prop2_strict_equivalence(a, b) :
        ⊢ ( est_entier(a) et est_entier(b) )
              ⇒ ( a < b  ⟺  (∃c)( est_entier(c) et c ≠ 0 et b = a + c ) ).

────────────────────────────────────────────────────────────────────────────────
PREUVE (Bourbaki, E III.36) :

⇒  (a < b ⇒ ∃c>0, b=a+c) : a < b = (a ≤ b et a ≠ b).  De a ≤ b, la PROPOSITION 13
   §III.3.6 (`prop13_equivalence`, appelée avec rôles échangés (b,a) pour obtenir le
   sens a≤b ⟺ ∃c card c, b=a+c) donne (∃c)( card c et b = a+c ).  Pour ce témoin c :
     • c ≠ 0 : (c=0) ⇒ b = a+0 = a (somme_zero_neutre_droite sous card a) ⇒ a=b ;
       contraposition de a≠b ;
     • c entier : c ≤ a+c = b (inf_egal_somme_droite + transport cardinal, sous card c,
       puis réécriture a+c↦b), et b entier ⇒ c entier (fini_downward CLOS).

⇐  (∃c>0, b=a+c ⇒ a < b) : pour le témoin c (entier, ≠0, b=a+c) :
     • a ≤ b : b = a+c et a ≤ a+c (sous card a) ⇒ a ≤ b ;
     • a ≠ b : (a=b) ⇒ a+c = a = a+0, et la SIMPLIFICATION ADDITIVE des entiers
       (`simplification_additive_finie`, Cor. 3 §III.5) donne c = 0 ; contraposition de c≠0.
   D'où a < b.

⚠️ INVARIANT : theorie_ensembles() = 22.  RIEN POSTULÉ : tout DÉRIVE de théorèmes
   CLOS (prop13_equivalence, simplification_additive_finie, fini_downward [garde
   est_cardinal déchargée + résidu pfu déchargé par predecesseur_fini_universel_preuve],
   somme_zero_neutre_droite, inf_egal_somme_droite/gauche).  Gardes HONNÊTES : a, b
   entiers (l'énoncé bourbakiste « a et b entiers »).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, non, et, impl, existe, equiv, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, contraposition,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
    inf_egal_transporte_cardinal,
)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_cardinaux_bornes_somme import (
    inf_egal_somme_droite, inf_egal_somme_gauche,
)

from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_entier, est_fini, ZERO
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)

# briques CLOSES — Prop 13, simplification additive, downward-closure
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_full_iii3 import prop13_equivalence
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_simplification_additive import (
    simplification_additive_finie,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_zero_neutre_droite
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import fini_downward_garde_thm
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    predecesseur_fini_universel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cesc_t(tx):
    """⊢ est_cardinal(x) ⇒ Card x = x  pour un TERME x (capture-safe)."""
    gen = N.generalisation("xcesc2", _cardinal_est_son_cardinal("xcesc2"))
    return instancie(gen, _t(tx))


# ──────────────────────────────────────────────────────────────────────────────
#  micro-Leibniz : réécriture d'un membre d'une relation binaire (cf. prop13)
# ──────────────────────────────────────────────────────────────────────────────
def _reecrire(thm, eq_old_new, old, new, build, hole="w2r"):
    vhole = var(hole)
    schema = build(vhole)
    equivf = N.modus_ponens(eq_old_new, N.s6(old, new, hole, schema))
    return N.modus_ponens(thm, equivalence_avant(equivf))


def _reecrire_gauche(thm, eq_old_new, old, new, rhs_fixe, rel, hole="w2r"):
    return _reecrire(thm, eq_old_new, old, new, lambda h: rel(h, rhs_fixe), hole)


def _reecrire_droite(thm, eq_old_new, old, new, lhs_fixe, rel, hole="w2r"):
    return _reecrire(thm, eq_old_new, old, new, lambda h: rel(lhs_fixe, h), hole)


# ──────────────────────────────────────────────────────────────────────────────
#  briques term-safe
# ──────────────────────────────────────────────────────────────────────────────
def _inf_egal_transporte_cardinal_t(tX, tY):
    gen = N.generalisation("Xtc2", N.generalisation("Ytc2",
            inf_egal_transporte_cardinal("Xtc2", "Ytc2")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def _c_inf_egal_a_plus_c(a, c):
    """⊢ est_cardinal(c) ⇒ ( c ≤ a + c )   pour des TERMES a, c.

    inf_egal_somme_droite : c ≤ a⊔c ; transport cardinal : Card c ≤ Card(a⊔c)=a+c ;
    sous est_cardinal(c), Card c = c ⇒ c ≤ a+c."""
    va, vc = _t(a), _t(c)
    asc = somme_disjointe(va, vc)
    ac = somme_cardinale_binaire(va, vc)
    gen = N.generalisation("Asd2", N.generalisation("Csd2",
            inf_egal_somme_droite("Asd2", "Csd2")))
    le_set = instancie(instancie(gen, va), vc)                       # c ≤ a⊔c
    hcard = N.assume(est_cardinal(vc))
    le_card = N.modus_ponens(le_set, _inf_egal_transporte_cardinal_t(vc, asc))  # Card c ≤ a+c
    cardc_eq_c = N.modus_ponens(hcard, _cesc_t(vc))                  # Card c = c
    le_c = _reecrire_gauche(le_card, cardc_eq_c, cardinal(vc), vc, ac, inf_egal_card)
    return N.loi_deduction(est_cardinal(vc), le_c)


def _a_inf_egal_a_plus_c(a, c):
    """⊢ est_cardinal(a) ⇒ ( a ≤ a + c )   (miroir gauche : a ≤ a⊔c)."""
    va, vc = _t(a), _t(c)
    asc = somme_disjointe(va, vc)
    ac = somme_cardinale_binaire(va, vc)
    gen = N.generalisation("Asg2", N.generalisation("Csg2",
            inf_egal_somme_gauche("Asg2", "Csg2")))
    le_set = instancie(instancie(gen, va), vc)                       # a ≤ a⊔c
    hcard = N.assume(est_cardinal(va))
    le_card = N.modus_ponens(le_set, _inf_egal_transporte_cardinal_t(va, asc))  # Card a ≤ a+c
    carda_eq_a = N.modus_ponens(hcard, _cesc_t(va))                  # Card a = a
    le_a = _reecrire_gauche(le_card, carda_eq_a, cardinal(va), va, ac, inf_egal_card)
    return N.loi_deduction(est_cardinal(va), le_a)


def _fini_downward_garde(c, x="xFD2c"):
    """⊢ est_cardinal(c) ⇒ ( c ≤ x_terme et Fini x_terme ) ⇒ Fini c  — pour le TERME c,
    instancié au TERME x.  La garde est_cardinal(c) reste honnête ; résidu pfu DÉCHARGÉ.

    Renvoie le théorème universel (∀x') gardé par est_cardinal(c) après décharge de pfu."""
    cname = "aFD2c"
    t = fini_downward_garde_thm(cname, x)             # {est_cardinal(c'), pfu} ⊢ (∀x)(c'≤x et Fini x ⇒ Fini c')
    pfu = predecesseur_fini_universel()
    pre = predecesseur_fini_universel_preuve()
    t = N.modus_ponens(pre, N.loi_deduction(pfu, t))  # {est_cardinal(c')} ⊢ (∀x)(...)
    return t, cname


# ══════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉ
# ══════════════════════════════════════════════════════════════════════════════
def _rhs(a, b, c):
    """(∃c)( est_entier(c) et ( c ≠ 0 et b = a+c ) )."""
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    body = et(est_entier(vc), et(non(egal(vc, ZERO)),
                                 egal(vb, somme_cardinale_binaire(va, vc))))
    return existe(cname, body)


def prop2_strict_equivalence_enonce(a="aP2", b="bP2", c="cP2"):
    va, vb = _t(a), _t(b)
    return impl(et(est_entier(va), est_entier(vb)),
                equiv(inf_strict_card(va, vb), _rhs(a, b, c)))


# ══════════════════════════════════════════════════════════════════════════════
#  SENS ⇒   :  a < b  ⇒  ∃c( entier c et c≠0 et b=a+c )
# ══════════════════════════════════════════════════════════════════════════════
def prop2_strict_forward(a="aP2", b="bP2", c="cP2"):
    """⊢ ( est_entier(a) et est_entier(b) ) ⇒ ( a < b ⇒ ∃c(entier c et c≠0 et b=a+c) ).  (CLOS.)"""
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    ac = somme_cardinale_binaire(va, vc)

    ante = et(est_entier(va), est_entier(vb))
    h = N.assume(ante)
    h_ent_a = conjonction_elim_gauche(h)
    h_ent_b = conjonction_elim_droite(h)
    h_card_a = conjonction_elim_gauche(h_ent_a)       # est_cardinal(a)
    h_card_b = conjonction_elim_gauche(h_ent_b)       # est_cardinal(b)

    hlt = N.assume(inf_strict_card(va, vb))           # a≤b et a≠b
    h_le = conjonction_elim_gauche(hlt)               # a ≤ b
    h_ne = conjonction_elim_droite(hlt)               # ¬(a = b)

    # Prop 13 (rôles échangés (b,a)) : (card b et card a) ⇒ ( a≤b ⟺ ∃c card c, b=a+c )
    p13 = prop13_equivalence(b, a, c)
    iff = N.modus_ponens(conjonction_intro(h_card_b, h_card_a), p13)
    ex_card = N.modus_ponens(h_le, equivalence_avant(iff))   # ∃c( card c et b=a+c )

    # per-témoin c : card c et b=a+c  ⊢  entier c et c≠0 et b=a+c
    body_src = et(est_cardinal(vc), egal(vb, ac))
    hbody = N.assume(body_src)
    h_card_c = conjonction_elim_gauche(hbody)         # card c
    h_b_eq_ac = conjonction_elim_droite(hbody)        # b = a+c

    # ── c ≠ 0 :  (c=0) ⇒ b=a+0=a ⇒ a=b ;  contraposition(a≠b)
    h_c0 = N.assume(egal(vc, ZERO))                   # c = 0
    a0 = somme_cardinale_binaire(va, ZERO)            # a + 0
    b_eq_a0 = _reecrire(h_b_eq_ac, h_c0, vc, ZERO,
                        lambda hh: egal(vb, somme_cardinale_binaire(va, hh)),
                        hole="wc0")                   # b = a+0
    a0_eq_a = N.modus_ponens(h_card_a, somme_zero_neutre_droite(va))  # a+0 = a
    b_eq_a = composer_egalites(b_eq_a0, a0_eq_a)      # b = a
    a_eq_b = N.modus_ponens(b_eq_a, symetrie(vb, va)) # a = b
    c0_imp_aeqb = N.loi_deduction(egal(vc, ZERO), a_eq_b)   # (c=0) ⇒ (a=b)
    c_ne0 = N.modus_ponens(h_ne, contraposition(c0_imp_aeqb))   # ¬(c=0)

    # ── entier c :  c ≤ a+c = b ; fini_downward(b) ⇒ Fini c
    le_c_ac = N.modus_ponens(h_card_c, _c_inf_egal_a_plus_c(va, vc))  # c ≤ a+c
    ac_eq_b = N.modus_ponens(h_b_eq_ac, symetrie(vb, ac))            # a+c = b
    le_c_b = _reecrire_droite(le_c_ac, ac_eq_b, ac, vb, vc, inf_egal_card)  # c ≤ b
    dwn, dname = _fini_downward_garde(vc)             # {card c'} ⊢ (∀x)(c'≤x et Fini x ⇒ Fini c')
    # généralise sur la garde c' puis instancie au TERME c (capture-safe), puis sur x:=b
    dwn_gen = N.generalisation(dname, N.loi_deduction(est_cardinal(var(dname)), dwn))
    dwn_c = N.modus_ponens(h_card_c, instancie(dwn_gen, vc))   # (∀x)(c≤x et Fini x ⇒ Fini c)
    dwn_cb = instancie(dwn_c, vb)                     # (c≤b et Fini b) ⇒ Fini c
    fini_c = N.modus_ponens(conjonction_intro(le_c_b, h_ent_b), dwn_cb)  # Fini c = est_entier c

    # assemble témoin : entier c et ( c≠0 et b=a+c )
    body_tgt = et(est_entier(vc), et(non(egal(vc, ZERO)), egal(vb, ac)))
    conj = conjonction_intro(fini_c, conjonction_intro(c_ne0, h_b_eq_ac))
    assert conj.conclusion == body_tgt, "forward : corps témoin mal formé"
    ex_tgt = N.modus_ponens(conj, N.s5(body_tgt, vc, cname))
    imp_body = N.loi_deduction(body_src, ex_tgt)      # body_src ⇒ rhs
    rhs = N.modus_ponens(ex_card, existe_elimination(imp_body, cname))   # rhs
    imp_lt = N.loi_deduction(inf_strict_card(va, vb), rhs)   # (a<b) ⇒ rhs
    return N.loi_deduction(ante, imp_lt)


# ══════════════════════════════════════════════════════════════════════════════
#  SENS ⇐   :  ∃c( entier c et c≠0 et b=a+c )  ⇒  a < b
# ══════════════════════════════════════════════════════════════════════════════
def prop2_strict_backward(a="aP2", b="bP2", c="cP2"):
    """⊢ ( est_entier(a) et est_entier(b) ) ⇒ ( ∃c(entier c et c≠0 et b=a+c) ⇒ a < b ).  (CLOS.)"""
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    ac = somme_cardinale_binaire(va, vc)

    ante = et(est_entier(va), est_entier(vb))
    h = N.assume(ante)
    h_ent_a = conjonction_elim_gauche(h)
    h_card_a = conjonction_elim_gauche(h_ent_a)       # est_cardinal(a)

    rhs = _rhs(a, b, c)
    hrhs = N.assume(rhs)

    # per-témoin c : entier c et ( c≠0 et b=a+c )  ⊢  a < b
    body = et(est_entier(vc), et(non(egal(vc, ZERO)), egal(vb, ac)))  # corps de rhs
    hbody = N.assume(body)
    h_ent_c = conjonction_elim_gauche(hbody)          # entier c
    h_rest = conjonction_elim_droite(hbody)           # c≠0 et b=a+c
    h_c_ne0 = conjonction_elim_gauche(h_rest)         # ¬(c=0)
    h_b_eq_ac = conjonction_elim_droite(h_rest)       # b = a+c
    h_card_c = conjonction_elim_gauche(h_ent_c)       # est_cardinal(c)

    # ── a ≤ b :  a ≤ a+c = b
    le_a_ac = N.modus_ponens(h_card_a, _a_inf_egal_a_plus_c(va, vc))  # a ≤ a+c
    ac_eq_b = N.modus_ponens(h_b_eq_ac, symetrie(vb, ac))            # a+c = b
    le_a_b = _reecrire_droite(le_a_ac, ac_eq_b, ac, vb, va, inf_egal_card)  # a ≤ b

    # ── a ≠ b :  (a=b) ⇒ a+c=a=a+0 ⇒ (simplification, card c, card 0) c=0 ; contraposition(c≠0)
    h_ab = N.assume(egal(va, vb))                     # a = b
    # a+c = a  :  de b=a+c (sym) a+c=b, et b=a (sym de a=b) ⇒ a+c=a
    b_eq_a = N.modus_ponens(h_ab, symetrie(va, vb))   # b = a
    ac_eq_a = composer_egalites(ac_eq_b, b_eq_a)      # a+c = a
    a0 = somme_cardinale_binaire(va, ZERO)            # a+0
    a0_eq_a = N.modus_ponens(h_card_a, somme_zero_neutre_droite(va))  # a+0 = a
    a_eq_a0 = N.modus_ponens(a0_eq_a, symetrie(a0, va))   # a = a+0
    ac_eq_a0 = composer_egalites(ac_eq_a, a_eq_a0)    # a+c = a+0
    # simplification_additive_finie(a) : entier a ⇒ (∀c)(∀c')((card c et card c' et a+c=a+c') ⇒ c=c')
    saf = simplification_additive_finie("aSAF2")
    saf_a = instancie(N.generalisation("aSAF2", saf), va)            # entier a ⇒ P(a)
    P_a = N.modus_ponens(h_ent_a, saf_a)                            # (∀c)(∀c')(...⇒c=c')
    Pcc = instancie(instancie(P_a, vc), ZERO)        # (card c et card 0 et a+c=a+0) ⇒ c=0
    card0 = _est_cardinal_zero()                     # est_cardinal(0)
    c_eq_0 = N.modus_ponens(conjonction_intro(conjonction_intro(h_card_c, card0), ac_eq_a0), Pcc)  # c = 0
    ab_imp_c0 = N.loi_deduction(egal(va, vb), c_eq_0)   # (a=b) ⇒ (c=0)
    a_ne_b = N.modus_ponens(h_c_ne0, contraposition(ab_imp_c0))      # ¬(a=b)

    lt = conjonction_intro(le_a_b, a_ne_b)            # a≤b et a≠b = a<b
    imp_body = N.loi_deduction(body, lt)              # body ⇒ a<b
    res = N.modus_ponens(hrhs, existe_elimination(imp_body, cname))  # a<b
    imp_rhs = N.loi_deduction(rhs, res)               # rhs ⇒ a<b
    return N.loi_deduction(ante, imp_rhs)


def _est_cardinal_zero():
    """⊢ est_cardinal(0)   (0 = Card∅)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import zero_est_un_cardinal
    return zero_est_un_cardinal()


# ══════════════════════════════════════════════════════════════════════════════
#  🎯🎯 PROPOSITION 2 §III.5.2 — ÉQUIVALENCE COMPLÈTE
# ══════════════════════════════════════════════════════════════════════════════
def prop2_strict_equivalence(a="aP2", b="bP2", c="cP2"):
    """🎯🎯 ⊢ ( est_entier(a) et est_entier(b) )
                ⇒ ( a < b  ⟺  (∃c)( est_entier(c) et c≠0 et b = a+c ) ).   (CLOS.)

    PROPOSITION 2 §III.5.2 (E III.36), équivalence bourbakiste EXACTE.
    ⇒ = prop2_strict_forward, ⇐ = prop2_strict_backward, sous la garde « a, b entiers »."""
    va, vb = _t(a), _t(b)
    ante = et(est_entier(va), est_entier(vb))
    h = N.assume(ante)

    fwd = N.modus_ponens(h, prop2_strict_forward(a, b, c))   # (a<b) ⇒ rhs
    bwd = N.modus_ponens(h, prop2_strict_backward(a, b, c))  # rhs ⇒ (a<b)
    iff = conjonction_intro(fwd, bwd)                        # ⟺
    out = N.loi_deduction(ante, iff)
    assert out.conclusion == prop2_strict_equivalence_enonce(a, b, c), \
        "prop2_strict_equivalence : conclusion ≠ énoncé attendu"
    return out


__all__ = [
    "prop2_strict_forward", "prop2_strict_backward",
    "prop2_strict_equivalence", "prop2_strict_equivalence_enonce",
]
