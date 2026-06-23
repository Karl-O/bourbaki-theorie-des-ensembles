"""§III.3.4 — PROPOSITION 7 (produit cardinal non nul), forme binaire.

Module NEUF (campagne III.3 props 7/13).  Énoncé Bourbaki (E.III.3.4, Prop 7, cas
à deux indices) : « pour que ∏ a_ι ≠ 0 il faut et il suffit que a_ι ≠ 0 pour tout
ι », soit pour deux cardinaux :

        a · b = 0  ⟺  (a = 0  ou  b = 0)        (forme « produit nul »),
   donc a · b ≠ 0  ⟺  (a ≠ 0  et  b ≠ 0).

Ici 0 = Card(∅) et a·b = produit_cardinal_binaire(a,b) = Card(a×b).

PROUVÉ INCONDITIONNELLEMENT ici, sur les ENSEMBLES A, B (Card fidèle à
l'équipotence), en chaînant trois équivalences déjà disponibles ou prouvées :
  (i)   Card(A×B) = Card(∅)  ⟺  (A×B) = ∅       [cardinal_egal_zero_ssi_vide] ;
  (ii)  (A×B) = ∅            ⟺  (A=∅ ou B=∅)     [produit_vide, E.II.34] ;
  (iii) A = ∅  ⟺  Card A = Card(∅)               [cardinal_egal_zero_ssi_vide].
La transitivité des équivalences donne
        Card(A×B) = Card(∅)  ⟺  (Card A = Card(∅) ou Card B = Card(∅)),
c.-à-d. a·b = 0 ⟺ (a=0 ou b=0).  Sa NÉGATION (forme « non nul ») suit par
contraposée (congruence du « non » sur les deux membres).

LEMME-CLÉ prouvé ici : `cardinal_egal_zero_ssi_vide`
        ⊢ (Card X = Card ∅) ⟺ (X = ∅).
  • ⇐ : X=∅ ⇒ Card X = Card ∅  (congruence du terme Card(·)) ;
  • ⇒ : Card X = Card ∅ ⇒ Eq(X,∅) (Proposition 1) ⇒ Eq(∅,X) (symétrie) ; une
        bijection ∅→X a pour image ∅ (image_sur_vide) ET X (surjectivité) ⇒ X=∅.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, equiv,
                                       appartient)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    equivalence_symetrie, instancie, ou_congruence, equiv_neg, demorgan_ou)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_cardinaux import (cardinal, est_bijection_de,
                               equipotent)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    cardinal_egal_si_equipotent, equipotent_si_cardinal_egal)
from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
from bourbaki.cardinaux.ensembles_vide_singleton import image_sur_vide
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _eq_son_cardinal_terme
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import produit_vide


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
#  LEMME : Eq(X, ∅) ⇒ X = ∅   (un ensemble équipotent au vide EST vide)
# ══════════════════════════════════════════════════════════════════════════════
def equipotent_vide_implique_vide(x="X"):
    """⊢ Eq(X, ∅) ⇒ (X = ∅).   (seul le vide est équipotent au vide.)

    Eq(X,∅) ⇒ Eq(∅,X) (symétrie) ; une bijection G : ∅ → X est SURJECTIVE
    (image(G,∅) = X) ; or l'image du vide est vide (image_sur_vide : image(G,∅)=∅) ;
    donc X = ∅.  G non libre dans « X=∅ » → ∃-élimination conclut."""
    vX = _t(x)
    vF = var("F")
    # Eq(X,∅) ⇒ Eq(∅,X)   (le témoin interne de Eq(∅,X) est lié par « F »)
    sym = equipotence_symetrique("F", vX, E.VIDE)        # Eq(X,∅) ⇒ Eq(∅,X)
    hxv = N.assume(equipotent(vX, E.VIDE))
    eq_vx = N.modus_ponens(hxv, sym)                      # Eq(∅,X) = (∃F)bij(F,∅,X)
    # per-témoin F de Eq(∅,X) : bijection ∅→X
    bij = est_bijection_de(vF, E.VIDE, vX)
    hbij = N.assume(bij)
    surj = conjonction_elim_droite(conjonction_elim_droite(hbij))   # image(F,∅) = X
    img_vide = image_sur_vide("F")                        # image(F,∅) = ∅
    x_eq_img = N.modus_ponens(surj, symetrie(E.image(vF, E.VIDE), vX))   # X = image(F,∅)
    x_eq_vide = composer_egalites(x_eq_img, img_vide)     # X = ∅
    imp = N.loi_deduction(bij, x_eq_vide)                 # bij ⇒ (X=∅)
    elim = existe_elimination(imp, "F")                   # Eq(∅,X) ⇒ (X=∅)
    x_vide = N.modus_ponens(eq_vx, elim)                  # X = ∅   [sous Eq(X,∅)]
    return N.loi_deduction(equipotent(vX, E.VIDE), x_vide)


# ══════════════════════════════════════════════════════════════════════════════
#  LEMME-CLÉ : (Card X = Card ∅) ⟺ (X = ∅)   (« Card X = 0 ⟺ X vide »)
# ══════════════════════════════════════════════════════════════════════════════
def cardinal_egal_zero_ssi_vide(x="X"):
    """⊢ (Card X = Card ∅) ⟺ (X = ∅).   (« a = 0 ⟺ a vide », 0 = Card ∅.)

    ⇒ : Card X = Card ∅ ⇒ Eq(X,∅) (Prop 1 réciproque) ⇒ X=∅
        (equipotent_vide_implique_vide) ;
    ⇐ : X=∅ ⇒ Card X = Card ∅  (congruence du terme Card(·))."""
    vX = _t(x)
    cX, cVide = cardinal(vX), cardinal(E.VIDE)
    # ⇒
    h_card = N.assume(egal(cX, cVide))
    eq = N.modus_ponens(h_card, _equipotent_si_cardinal_egal_t(vX, E.VIDE))   # Eq(X,∅)
    x_vide = N.modus_ponens(eq, equipotent_vide_implique_vide(x))          # X=∅
    fwd = N.loi_deduction(egal(cX, cVide), x_vide)        # (Card X=Card∅) ⇒ (X=∅)
    # ⇐
    h_vide = N.assume(egal(vX, E.VIDE))
    card_eq = N.modus_ponens(h_vide, congruence_terme(vX, E.VIDE, cardinal(var("w"))))  # Card X=Card∅
    bwd = N.loi_deduction(egal(vX, E.VIDE), card_eq)      # (X=∅) ⇒ (Card X=Card∅)
    return conjonction_intro(fwd, bwd)


def _equipotent_si_cardinal_egal_t(tX, tY):
    """⊢ (Card X = Card Y) ⇒ Eq(X, Y)  pour des TERMES X, Y (Prop 1 réciproque)."""
    gen = N.generalisation("X", N.generalisation("Y",
        equipotent_si_cardinal_egal("X", "Y")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


# ══════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 7 (binaire) — forme « produit nul » et « produit non nul »
# ══════════════════════════════════════════════════════════════════════════════
def prop7_produit_nul(a="A", b="B"):
    """⊢ (Card(A×B) = Card ∅) ⟺ (Card A = Card ∅ ou Card B = Card ∅).

    PROPOSITION 7 (E.III.3.4), forme « a·b = 0 ⟺ (a=0 ou b=0) » (0 = Card ∅,
    a·b = Card(A×B)).  Chaîne d'équivalences :
        Card(A×B)=Card∅  ⟺  A×B=∅            [cardinal_egal_zero_ssi_vide]
                         ⟺  (A=∅ ou B=∅)      [produit_vide, E.II.34]
                         ⟺  (CardA=Card∅ ou CardB=Card∅)  [cardinal_egal_zero_ssi_vide × 2].
    """
    vA, vB = _t(a), _t(b)
    AB = E.produit(vA, vB)
    # (i) Card(A×B)=Card∅ ⟺ A×B=∅
    e1 = cardinal_egal_zero_ssi_vide(AB)                  # (Card(A×B)=Card∅) ⟺ (A×B=∅)
    # (ii) A×B=∅ ⟺ (A=∅ ou B=∅)
    e2 = produit_vide(a, b)                               # (A×B=∅) ⟺ (A=∅ ou B=∅)
    # (iii) (A=∅ ou B=∅) ⟺ (CardA=Card∅ ou CardB=Card∅)  : congruence du « ou »
    cA = equivalence_symetrie(cardinal_egal_zero_ssi_vide(a))   # (A=∅) ⟺ (CardA=Card∅)
    cB = equivalence_symetrie(cardinal_egal_zero_ssi_vide(b))   # (B=∅) ⟺ (CardB=Card∅)
    e3 = ou_congruence(cA, cB)                            # (A=∅ ou B=∅) ⟺ (CardA=Card∅ ou CardB=Card∅)
    return equivalence_transitivite(e1, equivalence_transitivite(e2, e3))


def prop7_produit_non_nul(a="A", b="B"):
    """⊢ ¬(Card(A×B) = Card ∅) ⟺ (¬(Card A = Card ∅) et ¬(Card B = Card ∅)).

    PROPOSITION 7, forme « a·b ≠ 0 ⟺ (a≠0 et b≠0) » — l'énoncé EXACT de Bourbaki
    (E.III.3.4).  Contraposée de prop7_produit_nul : ¬(P⟺(Q ou R)) ⟺ (¬P ⟺ (¬Q et
    ¬R)) via négation des deux membres (De Morgan sur le « ou »)."""
    vA, vB = _t(a), _t(b)
    AB = E.produit(vA, vB)
    cAB0 = egal(cardinal(AB), cardinal(E.VIDE))           # P = (a·b = 0)
    cA0 = egal(cardinal(vA), cardinal(E.VIDE))            # Q = (a = 0)
    cB0 = egal(cardinal(vB), cardinal(E.VIDE))            # R = (b = 0)
    base = prop7_produit_nul(a, b)                        # P ⟺ (Q ou R)
    # ¬P ⟺ ¬(Q ou R)
    neg_equiv = equiv_neg(base)                           # ¬P ⟺ ¬(Q ou R)
    # ¬(Q ou R) ⟺ (¬Q et ¬R)  (De Morgan)
    demorgan = demorgan_ou(cA0, cB0)                      # ¬(Q ou R) ⟺ (¬Q et ¬R)
    return equivalence_transitivite(neg_equiv, demorgan)  # ¬P ⟺ (¬Q et ¬R)


__all__ = [
    "equipotent_vide_implique_vide", "cardinal_egal_zero_ssi_vide",
    "prop7_produit_nul", "prop7_produit_non_nul",
]
