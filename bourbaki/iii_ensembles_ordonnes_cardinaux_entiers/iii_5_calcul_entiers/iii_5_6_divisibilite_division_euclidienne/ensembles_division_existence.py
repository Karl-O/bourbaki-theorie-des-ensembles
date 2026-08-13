"""§III.5.6 Th.1 — DIVISION EUCLIDIENNE, existence (assemblage, campagne complétion).

Bourbaki (E III.39, Th.1) : pour a, b entiers avec b ≠ 0, il existe q, r entiers tels
que a = b·q + r et r < b.

ASSEMBLAGE par RÉCURRENCE FORTE (C61) sur a, à b fixé ≠ 0 :
  · R{a}  :=  (∃q)(∃r)( b·q + r = a  et  r < b )      (opérations RÉELLES :
    b·q = produit_cardinal_binaire, b·q+r = somme_cardinale_binaire) ;
  · cas a < b   : q=0, r=a  → division_cas_petit (base, CLOS) ;
  · cas a ≥ b   : a−b < a, l'HR forte donne R{a−b} = (b·q'+r'=a−b, r'<b), puis
    a = b + (a−b) = b + b·q' + r' = b·(q'+1) + r'  → division_pas_recomposition +
    division_successeur (q = q'+1, r = r').

BRIQUE 1 (ce commit) : `_pas_petit` — {a fini} ⊢ (a < b) ⇒ R{a}, obtenu de
division_cas_petit (qui conclut « = Card a ») par le pont Card a = a (a fini est un
cardinal : fini_implique_cardinal + cardinal_de_cardinal), réécrit sous les ∃∃.
theorie == 22.  Tests FICHIER SEUL (le pont récurrence-forte viendra en briques ≥3).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, impl, egal, existe, tau, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card, est_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_cardinale_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_cas_petit import division_cas_petit
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, equivalence_arriere, instancie, conjonction_intro)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import congruence_existe
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites, congruence_terme, symetrie
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_elim_gauche, conjonction_elim_droite
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import diff_somme
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_pas import division_pas_recomposition
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_successeur import division_successeur
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import somme_cardinale_associative
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import somme_cardinale_bien_definie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import equipotence_reflexive


def _eq_sym_t(t1, t2):
    """De ⊢ Eq(t1,t2), fabrique ⊢ Eq(t2,t1)  (equipotence_symetrique DÉFAUTS+gen/inst)."""
    base = equipotence_symetrique()                          # Eq(X,Y) ⇒ Eq(Y,X)
    g = N.generalisation("X", N.generalisation("Y", base))
    return instancie(instancie(g, t1), t2)                   # Eq(t1,t2) ⇒ Eq(t2,t1)


def _bien_def(A, B, A1, B1, eqA, eqB):
    """De ⊢ Eq(A,A1) et ⊢ Eq(B,B1), déduit ⊢ Card(A⊔B) = Card(A1⊔B1)."""
    base = somme_cardinale_bien_definie()                    # (Eq(A,A1) et Eq(B,B1)) ⇒ Card(A⊔B)=Card(A1⊔B1)
    g = N.generalisation("A", N.generalisation("B", N.generalisation("A1", N.generalisation("B1", base))))
    inst = instancie(instancie(instancie(instancie(g, A), B), A1), B1)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    return N.modus_ponens(conjonction_intro(eqA, eqB), inst)


def _assoc_binaire(x="xAB", y="yAB", z="zAB"):
    """⊢ (x + y) + z = x + (y + z)   (associativité de la somme cardinale BINAIRE, forme Card-wrappée).

    somme_cardinale_associative donne Card((x⊔y)⊔z)=Card(x⊔(y⊔z)) [somme_disjointe brute] ;
    on pontifie les deux bouts vers la forme binaire Card(Card(x⊔y)⊔z) / Card(x⊔Card(y⊔z))
    par la bien-définition (Eq(Card(x⊔y),x⊔y), Eq(y⊔z,Card(y⊔z)) via equipotent_son_cardinal)."""
    vx, vy, vz = var(x), var(y), var(z)
    xy = somme_disjointe(vx, vy)
    yz = somme_disjointe(vy, vz)
    Cxy = cardinal(xy)
    Cyz = cardinal(yz)
    # (A) Card(Card(x⊔y) ⊔ z) = Card((x⊔y) ⊔ z)
    eqA = N.modus_ponens(equipotent_son_cardinal_t(xy), _eq_sym_t(xy, Cxy))   # Eq(Card(x⊔y), x⊔y)
    eqZ = equipotence_reflexive_t(vz)                                          # Eq(z,z)
    stepA = _bien_def(Cxy, vz, xy, vz, eqA, eqZ)             # Card(Cxy⊔z)=Card(xy⊔z)
    # (B) associativité brute : Card((x⊔y)⊔z) = Card(x⊔(y⊔z))
    stepB = somme_cardinale_associative(x, y, z)
    # (C) Card(x⊔(y⊔z)) = Card(x ⊔ Card(y⊔z))
    eqX = equipotence_reflexive_t(vx)                                          # Eq(x,x)
    eqC = equipotent_son_cardinal_t(yz)                                        # Eq(y⊔z, Card(y⊔z))
    stepC = _bien_def(vx, yz, vx, Cyz, eqX, eqC)            # Card(x⊔yz)=Card(x⊔Cyz)
    return composer_egalites(composer_egalites(stepA, stepB), stepC)


def equipotent_son_cardinal_t(t):
    """⊢ Eq(t, Card t) pour un TERME t (DÉFAUTS+gen/inst d'equipotent_son_cardinal)."""
    base = equipotent_son_cardinal("X")
    return instancie(N.generalisation("X", base), t)


def equipotence_reflexive_t(t):
    """⊢ Eq(t, t) pour un TERME t (DÉFAUTS+gen/inst)."""
    base = equipotence_reflexive("X")
    return instancie(N.generalisation("X", base), t)

_Q, _R = "qDE", "rDE"                    # mêmes liants frais que division_cas_petit


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _bqr(vb, q_term, r_term):
    """b·q + r  (opérations cardinales binaires réelles)."""
    return somme_cardinale_binaire(produit_cardinal_binaire(vb, q_term), r_term)


def _phi(vb, cible, q_term, r_term):
    """b·q + r = cible  et  r < b."""
    return et(egal(_bqr(vb, q_term, r_term), cible), inf_strict_card(r_term, vb))


def _R_rel(vb, cible):
    """R{cible} := (∃q)(∃r)( b·q + r = cible  et  r < b )."""
    return existe(_Q, existe(_R, _phi(vb, cible, var(_Q), var(_R))))


def _card_egal_soi(a):
    """{a fini} ⊢ Card a = a   (fini ⇒ cardinal ⇒ Card a = a)."""
    va = _t(a)
    fini_a = N.assume(est_fini(va))
    card_a = N.modus_ponens(fini_a, fini_implique_cardinal(va))       # est_cardinal(a)
    return N.modus_ponens(card_a, cardinal_de_cardinal(va))          # {a fini} ⊢ Card a = a


def enonce_pas_petit(a="a", b="b"):
    va, vb = var(a), var(b)
    return impl(inf_strict_card(va, vb), _R_rel(vb, va))


# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142   (cas a<b, relation sur l'entier a)
def _pas_petit(a="a", b="b"):
    """⊢ {a fini}  (a < b) ⇒ R{a}.

    division_cas_petit : (Card a<b) ⇒ (∃q,r)(b·q+r=Card a et r<b).  Pont Card a=a (a fini) :
    réécrit a<b → Card a<b (Leibniz) et, sous les ∃∃, b·q+r=Card a → b·q+r=a (congruence_existe)."""
    va, vb = var(a), var(b)
    ca = cardinal(va)
    eq = _card_egal_soi(a)                               # {a fini} ⊢ Card a = a

    # a<b ⇒ Card a<b :  (Card a=a) ⇒ (inf_strict(Card a,b) ⇔ inf_strict(a,b))
    h_ab = N.assume(inf_strict_card(va, vb))
    lt_equiv = N.modus_ponens(eq, N.s6(ca, va, "wlt", inf_strict_card(var("wlt"), vb)))
    card_lt = N.modus_ponens(h_ab, equivalence_arriere(lt_equiv))    # {a fini, a<b} ⊢ Card a<b
    petit = N.modus_ponens(card_lt, division_cas_petit(a, b))        # (∃q,r)(b·q+r=Card a et r<b)

    # réécrire Card a → a sous ∃q∃r :  (b·q+r=Card a) ⇔ (b·q+r=a)  via Card a=a
    matrice_equiv = N.modus_ponens(eq, N.s6(ca, va, "weq",
        et(egal(_bqr(vb, var(_Q), var(_R)), var("weq")), inf_strict_card(var(_R), vb))))
    cong_r = congruence_existe(matrice_equiv, _R)        # (∃r)(…=Card a…) ⇔ (∃r)(…=a…)
    cong_qr = congruence_existe(cong_r, _Q)              # (∃q)(∃r)(…=Card a…) ⇔ (∃q)(∃r)(…=a…)
    Ra = N.modus_ponens(petit, equivalence_avant(cong_qr))          # R{a}

    res = N.loi_deduction(inf_strict_card(va, vb), Ra)   # {a fini} ⊢ (a<b) ⇒ R{a}
    assert res.conclusion == enonce_pas_petit(a, b), "_pas_petit : conclusion ≠ énoncé attendu"
    return res


def _inst_gen(thm, noms, termes):
    """Généralise `thm` sur `noms` puis l'instancie à `termes` (DÉFAUTS → termes)."""
    g = thm
    for nom in reversed(noms):
        g = N.generalisation(nom, g)
    out = g
    for t in termes:
        out = instancie(out, t)
    return out


def enonce_pas_grand(a="a", b="b"):
    va, vb = var(a), var(b)
    diff = diff_somme(va, vb, "c")
    return et(et(et(est_fini(va), est_fini(vb)), inf_egal_card(vb, va)), _R_rel(vb, diff)), _R_rel(vb, va)


# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142   (cas a≥b : recomposition via HR sur a−b)
def _pas_grand(a="a", b="b"):
    """⊢ {a fini, b fini, b≤a, R{a−b}}  R{a}.   (pas de récurrence forte, cas a≥b.)

    Extrait (Q0,R0) de R{a−b} (b·Q0+R0=a−b, R0<b) ; division_pas_recomposition donne
    b+(b·Q0+R0)=a ; division_successeur + _assoc_binaire recomposent b·(Q0+1)+R0=a ;
    ∃-intro (q=succ Q0, r=R0).

    NB (tick 52) : division_successeur est appelée avec des NOMS FRAIS ('Bdiv','Qdiv') puis
    généralisée+instanciée aux termes — sinon 'b'/'q' collisionnent les liants internes de
    distributivite_cardinale (le « verrou-τ » supposé bloquant était en fait une simple collision
    de NOMS d'arguments ; avec des noms frais tout est clos)."""
    va, vb = var(a), var(b)
    diff = diff_somme(va, vb, "c")                       # a−b = τc(a=b+c)
    card_a = N.modus_ponens(N.assume(est_fini(va)), fini_implique_cardinal(va))
    card_b = N.modus_ponens(N.assume(est_fini(vb)), fini_implique_cardinal(vb))
    h_le = N.assume(inf_egal_card(vb, va))               # b≤a
    h_R = N.assume(_R_rel(vb, diff))                     # R{a−b}

    # (1) extraire Q0, R0
    inner = existe(_R, _phi(vb, diff, var(_Q), var(_R)))
    Q0 = tau(_Q, inner)
    et1 = N.modus_ponens(h_R, N.existe_temoin(inner, _Q))    # ∃rDE φ[qDE:=Q0]
    phiQ = _phi(vb, diff, Q0, var(_R))
    R0 = tau(_R, phiQ)
    phiQR = N.modus_ponens(et1, N.existe_temoin(phiQ, _R))   # b·Q0+R0=a−b et R0<b
    eq_bqr = conjonction_elim_gauche(phiQR)              # b·Q0+R0 = a−b
    r0_lt = conjonction_elim_droite(phiQR)              # R0 < b
    bQ0R0 = _bqr(vb, Q0, R0)                             # b·Q0+R0
    diff_eq = N.modus_ponens(eq_bqr, symetrie(bQ0R0, diff))   # a−b = b·Q0+R0

    # (2) division_pas_recomposition (générique q,r) → décharge HR, généralise, instancie Q0,R0
    P = division_pas_recomposition(a, b, "qDE", "rDE")   # {ante, a−b=b·q+r} ⊢ b+(b·q+r)=a
    ante = et(et(est_cardinal(vb), est_cardinal(va)), inf_egal_card(vb, va))
    P1 = N.loi_deduction(egal(diff, _bqr(vb, var(_Q), var(_R))), P)   # {ante} ⊢ (a−b=b·q+r)⇒b+(b·q+r)=a
    P2 = _inst_gen(P1, [_Q, _R], [Q0, R0])              # {ante} ⊢ (a−b=b·Q0+R0)⇒b+(b·Q0+R0)=a
    rec = N.modus_ponens(diff_eq, P2)                   # {ante} ⊢ b+(b·Q0+R0)=a
    rec = N.modus_ponens(conjonction_intro(conjonction_intro(card_b, card_a), h_le),
                         N.loi_deduction(ante, rec))    # {card_a,card_b,b≤a} ⊢ b+(b·Q0+R0)=a

    # (3) division_successeur → b·succ(Q0) = b + b·Q0   (NOMS FRAIS Bdiv,Qdiv puis gen+inst,
    #     sinon 'b'/'q' collisionnent les liants internes de distributivite_cardinale)
    succ_eq = _inst_gen(division_successeur("Bdiv", "Qdiv"), ["Bdiv", "Qdiv"], [vb, Q0])  # b·succ(Q0)=b+b·Q0
    bqsucc = _bqr(vb, successeur(Q0), R0)               # b·succ(Q0)+R0
    b_bQ0 = somme_cardinale_binaire(vb, produit_cardinal_binaire(vb, Q0))  # b+b·Q0
    # (4) congruence : b·succ(Q0)+R0 = (b+b·Q0)+R0
    ctx = somme_cardinale_binaire(var("wcg"), R0)
    cong = N.modus_ponens(succ_eq, congruence_terme(produit_cardinal_binaire(vb, successeur(Q0)),
                                                     b_bQ0, ctx, "wcg"))
    # (5) _assoc_binaire(b, b·Q0, R0) : (b+b·Q0)+R0 = b+(b·Q0+R0)
    assoc = _inst_gen(_assoc_binaire(), ["xAB", "yAB", "zAB"],
                      [vb, produit_cardinal_binaire(vb, Q0), R0])
    # chaîne : b·succ(Q0)+R0 = (b+b·Q0)+R0 = b+(b·Q0+R0) = a
    eq_final = composer_egalites(composer_egalites(cong, assoc), rec)   # b·succ(Q0)+R0 = a

    # (6) ∃-intro : R{a}
    phi_a = _phi(vb, va, successeur(Q0), var(_R))
    ex_r = N.modus_ponens(conjonction_intro(eq_final, r0_lt), N.s5(phi_a, R0, _R))
    ex_qr = N.modus_ponens(ex_r, N.s5(existe(_R, _phi(vb, va, var(_Q), var(_R))), successeur(Q0), _Q))
    assert ex_qr.conclusion == enonce_pas_grand(a, b)[1], "_pas_grand : conclusion ≠ R{a}"
    return ex_qr


__all__ = ["_R_rel", "enonce_pas_petit", "_pas_petit", "_assoc_binaire", "enonce_pas_grand", "_pas_grand"]
