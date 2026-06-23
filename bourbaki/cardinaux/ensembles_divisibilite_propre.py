"""§III.5 — DIVISIBILITÉ / PARITÉ « propres » sur le PRODUIT CARDINAL RÉEL.

🎯 Fondation ℕ pour l'injection de couplage (m,n) ↦ 2^m·3^n (vers ℵ₀·ℵ₀ = ℵ₀).

⚠️ Tout est construit sur le VRAI produit cardinal binaire
   produit_cardinal_binaire(b, q) := Card(b × q)  (E.III.3.3, opération bien
   définie sur les cardinaux), et JAMAIS sur l'opaque app("prod_ent") du noyau
   entiers (`divise` de ensembles_entiers.py est vacuous sur cet opérateur).

Prédicat de divisibilité PROPRE :

    divise_propre(b, a) := (∃q)( est_fini(q) ∧ a = produit_cardinal_binaire(b, q) ).

    « b divise a » : il existe un quotient ENTIER q tel que a = b·q.

Parité :

    est_pair_propre(n)   := divise_propre(2, n)
    est_impair_propre(n) := ¬ divise_propre(2, n)

LEMMES CLOS (theorie=22, noyau intact) :
  • divise_propre_reflexif(a)  ⊢ est_cardinal(a) ⇒ divise_propre(a, a)   (a = a·1, q=1) ;
  • pair_ou_impair(n)          ⊢ est_fini(n) ⇒ (est_pair_propre(n) ∨ est_impair_propre(n))
                                 (tiers exclu) ;
  • deux_divise_double(y)      ⊢ est_fini(y) ⇒ divise_propre(2, produit_cardinal_binaire(2, y))
                                 (= est_pair_propre(2·y) : 2·y est PAIR, témoin q=y).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, ou, non, existe, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    tiers_exclu,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_petits import (
    produit_cardinal_un,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, DEUX, UN
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import fini_un, un_egale_card_singleton
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
#  DÉFINITION — divise_propre / parité
# ══════════════════════════════════════════════════════════════════════════════
def divise_propre(b, a, q="qdiv"):
    """b | a  :=  (∃q)( est_fini(q) ∧ a = produit_cardinal_binaire(b, q) ).

    Divisibilité PROPRE (sur le vrai produit cardinal Card(b×q))."""
    vb, va = _t(b), _t(a)
    vq = var(q)
    return existe(q, et(est_fini(vq), egal(va, produit_cardinal_binaire(vb, vq))))


def est_pair_propre(n, q="qdiv"):
    """n est PAIR  :=  2 | n  =  divise_propre(2, n)."""
    return divise_propre(DEUX, _t(n), q=q)


def est_impair_propre(n, q="qdiv"):
    """n est IMPAIR  :=  ¬ (2 | n)  =  ¬ divise_propre(2, n)."""
    return non(est_pair_propre(n, q=q))


# ── outils TERME capture-safe ────────────────────────────────────────────────
def _card_de_card_t(tx):
    """⊢ est_cardinal(x) ⇒ Card(x) = x  (version TERME)."""
    gen = N.generalisation("xpccd", cardinal_de_cardinal("xpccd"))
    return instancie(gen, _t(tx))


def _pcbd_t(tX, tY, ta, tb):
    """produit_cardinal_bien_defini version TERME capture-safe (généralise+instancie).

    ⊢ (Card X = a et Card Y = b) ⇒ Card(X×Y) = produit_cardinal_binaire(a, b)."""
    g = produit_cardinal_bien_defini("Xpcbd", "Ypcbd", "apcbd", "bpcbd")
    gen = N.generalisation("Xpcbd", N.generalisation("Ypcbd",
          N.generalisation("apcbd", N.generalisation("bpcbd", g))))
    return instancie(instancie(instancie(instancie(gen, _t(tX)), _t(tY)),
                     _t(ta)), _t(tb))


def _produit_cardinal_un_t(ta):
    """⊢ Card(a×{∅}) = Card(a)  (version TERME de produit_cardinal_un)."""
    gen = N.generalisation("Apcu", produit_cardinal_un("Apcu"))
    return instancie(gen, _t(ta))


# ══════════════════════════════════════════════════════════════════════════════
#  (1) RÉFLEXIVITÉ — a | a  (témoin q = 1, a = a·1)
# ══════════════════════════════════════════════════════════════════════════════
def divise_propre_reflexif_cible(a="adr"):
    """Cible : est_cardinal(a) ⇒ divise_propre(a, a)."""
    va = _t(a)
    return impl(est_cardinal(va), divise_propre(va, va))


def divise_propre_reflexif(a="adr"):
    """🎯 ⊢ est_cardinal(a) ⇒ divise_propre(a, a).   (a | a, témoin q = 1.)

    a = a·1 :  Card(a×{∅}) = Card(a) = a  (produit_cardinal_un + Card a = a),
    et Card(a×{∅}) = produit_cardinal_binaire(a, 1)  (produit_cardinal_bien_defini
    avec Card{∅} = 1).  Donc a = a·1, et 1 = UN est fini (fini_un)."""
    va = _t(a)
    sing = E.singleton(E.VIDE)              # {∅}
    Card_a_sing = cardinal(E.produit(va, sing))   # Card(a×{∅})

    h = N.assume(est_cardinal(va))
    card_a = N.modus_ponens(h, _card_de_card_t(va))     # Card a = a

    # Card{∅} = 1 = UN  (symétrie de un_egale_card_singleton : 1 = Card{∅})
    un_eq = un_egale_card_singleton()                   # 1 = Card({∅})
    card_sing_eq_un = N.modus_ponens(un_eq, symetrie(UN, cardinal(sing)))   # Card{∅} = 1

    # produit_cardinal_bien_defini(a, {∅}, a, UN) :
    #   (Card a = a et Card{∅} = UN) ⇒ Card(a×{∅}) = produit_cardinal_binaire(a, UN)
    bd = _pcbd_t(va, sing, va, UN)
    eq_prod = N.modus_ponens(conjonction_intro(card_a, card_sing_eq_un), bd)  # Card(a×{∅}) = a·1

    # produit_cardinal_un : Card(a×{∅}) = Card a ;  puis Card a = a
    pcu = _produit_cardinal_un_t(va)                    # Card(a×{∅}) = Card a
    casing_eq_a = composer_egalites(pcu, card_a)        # Card(a×{∅}) = a

    # a = Card(a×{∅}) = a·1
    a_eq_casing = N.modus_ponens(casing_eq_a, symetrie(Card_a_sing, va))     # a = Card(a×{∅})
    a_eq_prod = composer_egalites(a_eq_casing, eq_prod)  # a = produit_cardinal_binaire(a, UN)

    # ∃q (Fini q et a = a·q)  via S5 (témoin UN)
    fini_q = fini_un()                                   # Fini(UN)
    conj = conjonction_intro(fini_q, a_eq_prod)          # Fini(UN) et a = a·UN
    matrice = et(est_fini(var("qdiv")),
                 egal(va, produit_cardinal_binaire(va, var("qdiv"))))
    s5 = N.s5(matrice, UN, "qdiv")                       # [matrice]_{q:=UN} ⇒ (∃q) matrice
    exists = N.modus_ponens(conj, s5)                    # divise_propre(a, a)

    out = N.loi_deduction(est_cardinal(va), exists)
    cible = divise_propre_reflexif_cible(a)
    assert out.conclusion == cible, \
        f"divise_propre_reflexif : conclusion inattendue\n{out.conclusion}\n{cible}"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  (2) PARITÉ — tiers exclu
# ══════════════════════════════════════════════════════════════════════════════
def pair_ou_impair_cible(n="npi"):
    vn = _t(n)
    return impl(est_fini(vn), ou(est_pair_propre(vn), est_impair_propre(vn)))


def pair_ou_impair(n="npi"):
    """🎯 ⊢ est_fini(n) ⇒ (est_pair_propre(n) ∨ est_impair_propre(n)).

    Tiers exclu sur la formule divise_propre(2, n)."""
    vn = _t(n)
    te = tiers_exclu(est_pair_propre(vn))    # P ∨ ¬P  =  pair ∨ impair
    out = N.loi_deduction(est_fini(vn), te)
    cible = pair_ou_impair_cible(n)
    assert out.conclusion == cible, \
        f"pair_ou_impair : conclusion inattendue\n{out.conclusion}\n{cible}"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  (3) 2·y EST PAIR  —  2 | (2·y)   (témoin q = y)
# ══════════════════════════════════════════════════════════════════════════════
def deux_divise_double_cible(y="ydd"):
    vy = _t(y)
    return impl(est_fini(vy), est_pair_propre(produit_cardinal_binaire(DEUX, vy)))


def deux_divise_double(y="ydd"):
    """🎯 ⊢ est_fini(y) ⇒ est_pair_propre(2·y).   (2·y est PAIR, témoin q = y.)

    2·y = produit_cardinal_binaire(2, y) ; le témoin q := y donne directement
    (2·y) = produit_cardinal_binaire(2, y) par RÉFLEXIVITÉ, et y est fini (hyp)."""
    vy = _t(y)
    prod = produit_cardinal_binaire(DEUX, vy)     # 2·y

    hfy = N.assume(est_fini(vy))
    refl = N.reflexivite(prod)                    # 2·y = 2·y  =  (2·y) = produit_cardinal_binaire(2, y)
    conj = conjonction_intro(hfy, refl)           # Fini y et (2·y = 2·y)

    matrice = et(est_fini(var("qdiv")),
                 egal(prod, produit_cardinal_binaire(DEUX, var("qdiv"))))
    s5 = N.s5(matrice, vy, "qdiv")                 # [matrice]_{q:=y} ⇒ (∃q) matrice
    exists = N.modus_ponens(conj, s5)              # divise_propre(2, 2·y) = est_pair_propre(2·y)

    out = N.loi_deduction(est_fini(vy), exists)
    cible = deux_divise_double_cible(y)
    assert out.conclusion == cible, \
        f"deux_divise_double : conclusion inattendue\n{out.conclusion}\n{cible}"
    return out


__all__ = [
    "divise_propre", "est_pair_propre", "est_impair_propre",
    "divise_propre_reflexif", "divise_propre_reflexif_cible",
    "pair_ou_impair", "pair_ou_impair_cible",
    "deux_divise_double", "deux_divise_double_cible",
]
