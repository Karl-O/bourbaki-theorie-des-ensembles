"""§III.5.6 Th.1 — division euclidienne, ASSEMBLAGE par récurrence forte (suite).

Ce module bâtit les briques manquantes au-dessus de ensembles_division_existence
(_pas_petit, _pas_grand, _assoc_binaire) pour clore l'EXISTENCE :
  · _diff_inf_egal  : (a−b) ≤ a  (niveau ENSEMBLE, sans est_cardinal(a−b)) ;
  · [à venir] _diff_est_fini, _diff_strict, _strong_step, division_existence.

CLEF anti-circularité (tick 55) : on obtient (a−b) ≤ a au niveau ENSEMBLE via
inf_egal_somme_droite (injection droite a−b ↪ b⊔(a−b)) transportée le long de
Eq(b⊔(a−b), a) [equipotent_son_cardinal + Card(b⊔(a−b)) = a par soustraction], SANS
jamais supposer est_cardinal(a−b).  De là fini_downward donnera est_fini(a−b).
theorie == 22 ; NOMS FRAIS pour tout appel sensible (leçon collision).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non, et, Terme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie, equivalence_avant, contraposition)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal, cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, somme_cardinale_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import somme_cardinale_commutative
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    diff_somme, soustraction_caracterisation)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop2_strict_iii5 import (
    prop2_strict_backward, _rhs)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_cardinaux_bornes_somme import inf_egal_somme_droite
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_props_diverses import inf_egal_invariant_equipotence
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import equipotence_reflexive
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, est_entier, ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import fini_downward_thm
# — briques de la route SANS commutativité pour _diff_strict (évite le verrou-τ) —
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop3_strict_mono_iii5 import (
    somme_strict_monotone, somme_strict_monotone_enonce)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import fini_zero, cardinal_vide_egale_vide
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_zero import card_somme_zero_neutre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_bornes import cardinal_zero_inf_egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import strict_irreflexif


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_gen(thm, noms, termes):
    g = thm
    for nom in reversed(noms):
        g = N.generalisation(nom, g)
    out = g
    for t in termes:
        out = instancie(out, t)
    return out


def enonce_diff_inf_egal(a="adf", b="bdf"):
    va, vb = var(a), var(b)
    diff = diff_somme(va, vb, "c")
    return inf_egal_card(diff, va)


# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142   (a−b ≤ a, niveau ensemble)
def _diff_inf_egal(a="adf", b="bdf"):
    """⊢ {est_cardinal a, est_cardinal b, b≤a}  (a−b) ≤ a.   (SANS est_cardinal(a−b).)

    inf_egal_somme_droite : (a−b) ≤ b⊔(a−b) [injection droite] ; transport le long de
    Eq(b⊔(a−b), a) [equipotent_son_cardinal + Card(b⊔(a−b))=a par soustraction]."""
    va, vb = _t(a), _t(b)
    diff = diff_somme(va, vb, "c")                       # a−b  (binder 'c' = celui de soustraction_caracterisation)
    S = somme_disjointe(vb, diff)                        # b⊔(a−b)
    card_a = N.assume(est_cardinal(va))
    card_b = N.assume(est_cardinal(vb))
    h_le = N.assume(inf_egal_card(vb, va))               # b≤a

    # (a−b) ≤ b⊔(a−b)   (inf_egal_somme_droite(A,B) ⊢ B ≤ A⊔B ; A=b, B=a−b ; noms frais)
    le_set = _inst_gen(inf_egal_somme_droite("Adis", "Bdis"), ["Adis", "Bdis"], [vb, diff])

    # Card(b⊔(a−b)) = a   (soustraction_caracterisation(A,B)⊢(card A,card B,A≤B)⇒A+(B−A)=B ; A=b,B=a)
    sc = _inst_gen(soustraction_caracterisation("Asc", "Bsc"), ["Asc", "Bsc"], [vb, va])
    card_S_eq_a = N.modus_ponens(
        conjonction_intro(conjonction_intro(card_b, card_a), h_le), sc)   # b+(a−b)=a  (= Card(S)=a)

    # Eq(S, a) : Eq(S, Card S) [equipotent_son_cardinal] réécrit Card S → a
    eq_S_cardS = _inst_gen(equipotent_son_cardinal("Xesc"), ["Xesc"], [S])   # Eq(S, Card S)
    cS = cardinal(S)
    leib = N.s6(cS, va, "wS", equipotent(S, var("wS")))   # (Card S=a)⇒(Eq(S,Card S)⇔Eq(S,a))
    eq_S_a = N.modus_ponens(eq_S_cardS, equivalence_avant(N.modus_ponens(card_S_eq_a, leib)))  # Eq(S,a)

    # transport : (Eq(a−b,a−b) et Eq(S,a)) ⇒ ((a−b≤S) ⇒ (a−b≤a))
    refl = _inst_gen(equipotence_reflexive("Xref"), ["Xref"], [diff])       # Eq(a−b, a−b)
    inv = _inst_gen(inf_egal_invariant_equipotence("Xiv", "Xpiv", "Yiv", "Ypiv"),
                    ["Xiv", "Xpiv", "Yiv", "Ypiv"], [diff, diff, S, va])
    imp = N.modus_ponens(conjonction_intro(refl, eq_S_a), inv)             # (a−b≤S)⇒(a−b≤a)
    res = N.modus_ponens(le_set, imp)                                       # (a−b) ≤ a
    assert res.conclusion == enonce_diff_inf_egal(a, b), "_diff_inf_egal : conclusion inattendue"
    return res


def enonce_diff_est_fini(a="adf", b="bdf"):
    va, vb = var(a), var(b)
    return est_fini(diff_somme(va, vb, "c"))


# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142   (a−b fini)
def _diff_est_fini(a="adf", b="bdf"):
    """⊢ {est_cardinal a, est_cardinal b, b≤a, Fini a, + résidus C61} ⊢ Fini(a−b).

    (a−b)≤a [_diff_inf_egal] + fini_downward_thm : (a−b≤a et Fini a) ⇒ Fini(a−b).
    Résidus HÉRITÉS de fini_downward_thm : principe_recurrence(P) et (∀c∀b)cardinal_pas_entre
    (= bon ordre des cardinaux / C61, les MÊMES qui conditionnent l'existence de ℕ)."""
    va, vb = _t(a), _t(b)
    diff = diff_somme(va, vb, "c")
    le = _diff_inf_egal(a, b)                                  # (a−b) ≤ a
    fdt = fini_downward_thm()                                  # (∀a)(∀x)((a≤x et Fini x)⇒Fini a)
    inst = instancie(instancie(fdt, diff), va)                # (a−b≤a et Fini a) ⇒ Fini(a−b)
    fin_a = N.assume(est_fini(va))                            # Fini a
    res = N.modus_ponens(conjonction_intro(le, fin_a), inst)  # Fini(a−b)
    assert res.conclusion == enonce_diff_est_fini(a, b), "_diff_est_fini : conclusion inattendue"
    return res


def enonce_diff_strict(a="adf", b="bdf"):
    va, vb = var(a), var(b)
    return inf_strict_card(diff_somme(va, vb, "c"), va)


# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142   (a−b < a  quand b≠0)
def _diff_strict(a="adf", b="bdf"):
    """⊢ {card a, card b, b≤a, Fini a, Fini b, b≠0} ⊢ (a−b) < a.   (SANS résidu C61 — route commute-free.)

    ROUTE SANS COMMUTATIVITÉ (évite le verrou-τ ; cf. mémoire bourbaki-commute-ordre-dependant).
    (a−b) ≤ a est _diff_inf_egal.  Pour (a−b) ≠ a : PAR L'ABSURDE.  Si a−b = a, alors b+(a−b)=a
    [soustraction_caracterisation(vb,va), PAS de commute] devient b+a=a [congruence a−b↦a] ; or
    somme_strict_monotone(0,b,a) [⊢ 0+a < b+a, quand 0<b] avec 0+a=a [card_somme_zero_neutre + ZERO=∅
    + Card a=a] donne a < b+a = a, contredit strict_irreflexif (¬(a<a)) ⇒ ¬(a−b=a).
    ⚠️ CLEF verrou-τ : somme_strict_monotone appliqué à ZERO (τ Card-valué) DIRECTEMENT rebute ; on passe
    par _inst_gen (théorème symbolique CLOS puis substitution PURE de ZERO — pas de bijection reconstruite)."""
    va, vb = _t(a), _t(b)
    diff = diff_somme(va, vb, "c")                             # a−b
    ZA = somme_cardinale_binaire(ZERO, va)                     # 0+a
    BA = somme_cardinale_binaire(vb, va)                       # b+a
    card_a = N.assume(est_cardinal(va))
    card_b = N.assume(est_cardinal(vb))
    h_le = N.assume(inf_egal_card(vb, va))
    fin_a = N.assume(est_fini(va))
    fin_b = N.assume(est_fini(vb))
    b_ne0 = N.assume(non(egal(vb, ZERO)))

    le1 = _diff_inf_egal(a, b)                                 # (a−b) ≤ a   (Partie 1)

    # ── 0+a = a  (indépendant de l'absurde) : scb(ZERO,va) = scb(∅,va) = Card(va) = va ──
    cve = cardinal_vide_egale_vide()                          # Card(∅) = ∅ , i.e. ZERO = ∅
    VIDE = cve.conclusion.termes[1]
    eq1 = N.modus_ponens(cve, congruence_terme(ZERO, VIDE, somme_cardinale_binaire(var("wz"), va), "wz"))  # scb(ZERO,va)=scb(∅,va)
    eq2 = card_somme_zero_neutre(va)                          # scb(∅,va) = Card(va)
    eq3 = N.modus_ponens(card_a, cardinal_de_cardinal(va))    # Card(va) = va
    zero_a_eq = composer_egalites(composer_egalites(eq1, eq2), eq3)   # 0+a = a

    # ── 0 < b  : inf_egal(ZERO,vb) [cardinal_zero_inf_egal + Card b=b] et ZERO≠vb [b≠0 symétrisé] ──
    czi = cardinal_zero_inf_egal(vb)                          # ZERO ≤ Card(vb)
    vb_card = N.modus_ponens(card_b, cardinal_de_cardinal(vb))   # Card(vb) = vb
    leibvb = N.s6(cardinal(vb), vb, "wb", inf_egal_card(ZERO, var("wb")))  # (Card vb=vb)⇒(0≤Card vb ⇔ 0≤vb)
    le_0b = N.modus_ponens(czi, equivalence_avant(N.modus_ponens(vb_card, leibvb)))   # ZERO ≤ vb
    ne_0b = N.modus_ponens(b_ne0, contraposition(symetrie(ZERO, vb)))   # ¬(ZERO = vb)
    lt_0b = conjonction_intro(le_0b, ne_0b)                   # 0 < b

    # ── 0+a < b+a  (somme_strict_monotone, ZERO via _inst_gen : PAS de verrou-τ) ──
    sm = _inst_gen(somme_strict_monotone("Asm", "Bsm", "Csm", "Dsm"),
                   ["Asm", "Bsm", "Csm"], [ZERO, vb, va])     # (ent0,entb,enta,0<b) ⇒ 0+a < b+a
    ante_sm = conjonction_intro(fini_zero(), conjonction_intro(fin_b, conjonction_intro(fin_a, lt_0b)))
    lt0 = N.modus_ponens(ante_sm, sm)                         # inf_strict_card(0+a, b+a)
    # réécrire 0+a ↦ a : inf_strict_card(a, b+a)
    leibA = N.s6(ZA, va, "wA", inf_strict_card(var("wA"), BA))
    lt1 = N.modus_ponens(lt0, equivalence_avant(N.modus_ponens(zero_a_eq, leibA)))   # a < b+a

    # ── ABSURDE : si a−b = a alors b+a = a, donc a < b+a = a, contredit ¬(a<a) ──
    h_diff = N.assume(egal(diff, va))                         # a−b = a
    sc = soustraction_caracterisation(vb, va, "c")            # (card b,card a,b≤a) ⇒ scb(vb,a−b)=a
    sc_eq = N.modus_ponens(conjonction_intro(conjonction_intro(card_b, card_a), h_le), sc)  # scb(vb,diff)=va
    leibD = N.s6(diff, va, "wd", egal(somme_cardinale_binaire(vb, var("wd")), va))
    ba_eq = N.modus_ponens(sc_eq, equivalence_avant(N.modus_ponens(h_diff, leibD)))   # b+a = a  (scb(vb,va)=va)
    leibB = N.s6(BA, va, "wB", inf_strict_card(va, var("wB")))
    lt_aa = N.modus_ponens(lt1, equivalence_avant(N.modus_ponens(ba_eq, leibB)))      # a < a   [sous h_diff]
    imp_absurd = N.loi_deduction(egal(diff, va), lt_aa)       # (a−b=a) ⇒ (a<a)
    nlt = strict_irreflexif(va)                              # ¬(a < a)
    ne = N.modus_ponens(nlt, contraposition(imp_absurd))     # ¬(a−b = a)   (Partie 2)

    res = conjonction_intro(le1, ne)                         # (a−b) ≤ a  et  a−b ≠ a  =  (a−b) < a
    assert res.conclusion == enonce_diff_strict(a, b), "_diff_strict : conclusion inattendue"
    return res


__all__ = ["enonce_diff_inf_egal", "_diff_inf_egal",
           "enonce_diff_est_fini", "_diff_est_fini",
           "enonce_diff_strict", "_diff_strict"]
