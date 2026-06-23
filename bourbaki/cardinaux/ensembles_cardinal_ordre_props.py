"""§III.3.2-3.3 — MONOTONIE de l'ordre ≤ des cardinaux, au niveau des CARDINAUX de
la somme et du produit (compléments « niveau cardinal » de la monotonie déjà close
au niveau des SUPPORTS ensemblistes).

CONTEXTE.  La monotonie ENSEMBLISTE de ≤ est déjà certifiée ailleurs :
  • somme :   inf_egal_somme_invariant  ⊢ (A ≤ A₁ et B ≤ B₁) ⇒ (A⊔B ≤ A₁⊔B₁)
              (ensembles_somme_monotone) ;
  • produit : inf_egal_produit_invariant ⊢ (A ≤ A₁ et B ≤ B₁) ⇒ (A×B ≤ A₁×B₁),
              inf_egal_produit_gauche / inf_egal_produit_droite (facteur fixe)
              (ensembles_arith_cardinale_props_produit_monotone).
Le PRODUIT possède déjà son emballage « niveau cardinal »
(cardinal_inf_egal_produit_invariant : a≤a₁ et b≤b₁ ⇒ Card(a×b) ≤ Card(a₁×b₁)),
mais la SOMME n'en a PAS, et NI la somme NI le produit n'ont la version
« Card(·) du support » à FACTEUR / SOMMANT FIXE.  On comble ces trous ici.

L'outil de passage est l'INVARIANCE de ≤ sous Card, elle aussi déjà close :
  inf_egal_transporte_cardinal  ⊢ (X ≤ Y) ⇒ (Card X ≤ Card Y)
(ensembles_arith_cardinale_props_exposant_monotone, contenu réel : Card X ≤ X ≤ Y
≤ Card Y).  De l'inégalité ENSEMBLISTE  U ≤ V  on tire donc  Card U ≤ Card V.

THÉORÈMES (chacun CLOS, theorie=22 ; rien postulé ; cf. test_cardinal_ordre_props) :

  (1) `somme_cardinale_additive`  ⊢ (A ≤ A₁ et B ≤ B₁) ⇒ Card(A⊔B) ≤ Card(A₁⊔B₁).
      ADDITIVITÉ de ≤ pour la somme cardinale (= a≤a₁ et b≤b₁ ⇒ a+b ≤ a₁+b₁, où
      a+b := Card(A⊔B)).  Miroir SOMME du produit cardinal_inf_egal_produit_invariant.
      Preuve : inf_egal_somme_invariant donne A⊔B ≤ A₁⊔B₁ (ensembliste) ;
      inf_egal_transporte_cardinal aux termes A⊔B, A₁⊔B₁ donne Card(A⊔B) ≤ Card(A₁⊔B₁).
      NON tautologique : antécédent = ≤ des sommants, conséquent = ≤ des cardinaux
      des sommes ; le pont est le transport.

  (2) `cardinal_inf_egal_somme_additive`  ⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁) ⇒
      Card(Card A ⊔ Card B) ≤ Card(Card A₁ ⊔ Card B₁).   (= a≤a₁ et b≤b₁ ⇒ a+b≤a₁+b₁
      sur les CARDINAUX a=Card A, …, avec a+b = somme_cardinale_binaire(Card A, Card B).)
      (1) généralisé en (∀A)(∀B)(∀A₁)(∀B₁) puis INSTANCIÉ aux termes Card·.  Miroir
      EXACT de cardinal_inf_egal_produit_invariant côté somme.

  (3) `somme_cardinale_monotone_gauche`  ⊢ (A ≤ A₁) ⇒ Card(A⊔C) ≤ Card(A₁⊔C).
      Monotonie à SOMMANT DROIT FIXE C (= a≤a₁ ⇒ a+c ≤ a₁+c).  Cas de (1) avec
      B:=C, B₁:=C et C≤C (réflexivité de ≤, inf_egal_reflexif au terme C).

  (4) `somme_cardinale_monotone_droite`  ⊢ (B ≤ B₁) ⇒ Card(C⊔B) ≤ Card(C⊔B₁).
      Monotonie à SOMMANT GAUCHE FIXE C (= b≤b₁ ⇒ c+b ≤ c+b₁).  Symétrique de (3).

  (5) `produit_cardinale_monotone_gauche`  ⊢ (A ≤ A₁) ⇒ Card(A×C) ≤ Card(A₁×C).
      Emballage « niveau cardinal » de inf_egal_produit_gauche (facteur droit fixe C).
      Preuve : inf_egal_produit_gauche donne A×C ≤ A₁×C (ensembliste) ; transport
      par Card aux termes A×C, A₁×C.  (= a≤a₁ ⇒ a·c ≤ a₁·c, Card(·) des supports.)

  (6) `produit_cardinale_monotone_droite`  ⊢ (B ≤ B₁) ⇒ Card(C×B) ≤ Card(C×B₁).
      Emballage « niveau cardinal » de inf_egal_produit_droite (facteur gauche fixe).

──────────────────────────────────────────────────────────────────────────────
INDÉPENDANT de ℕ et de l'arithmétique cardinale INFINIE.  Réflexivité de ≤ est
certifiée ailleurs (ensembles_cardinaux_theoremes.inf_egal_reflexif) — non dupliquée.
Aucune machinerie ensembliste nouvelle : on COMPOSE des théorèmes déjà clos.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, instancie)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale_props_exposant_monotone import (
    inf_egal_transporte_cardinal)
from bourbaki.cardinaux.arithmetique.ensembles_somme_monotone import inf_egal_somme_invariant
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale_props_produit_monotone import (
    inf_egal_produit_gauche, inf_egal_produit_droite, inf_egal_produit_invariant)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _transporte_t(tU, tV):
    """⊢ (U ≤ V) ⇒ (Card U ≤ Card V)  pour des TERMES U, V quelconques.

    inf_egal_transporte_cardinal (clos, contenu réel) généralisé en X,Y puis
    instancié aux termes U, V (renommage déterministe → robuste aux τ-cardinaux)."""
    gen = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))      # (∀X)(∀Y)(X≤Y ⇒ Card X≤Card Y)
    return instancie(instancie(gen, _t(tU)), _t(tV))  # (U≤V) ⇒ Card U ≤ Card V


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  ADDITIVITÉ de ≤ pour la SOMME cardinale (niveau Card des supports)
# ═══════════════════════════════════════════════════════════════════════════════
def somme_cardinale_additive(a="A", b="B", a1="A1", b1="B1"):
    """⊢ (A ≤ A₁ et B ≤ B₁) ⇒ Card(A⊔B) ≤ Card(A₁⊔B₁).   (additivité de ≤ ; clos.)

    inf_egal_somme_invariant donne l'inégalité ENSEMBLISTE A⊔B ≤ A₁⊔B₁ sous
    (A ≤ A₁ et B ≤ B₁) ; le transport par Card (aux termes A⊔B, A₁⊔B₁) conclut
    Card(A⊔B) ≤ Card(A₁⊔B₁).  Miroir SOMME de cardinal_inf_egal_produit_invariant."""
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    AB = somme_disjointe(va, vb)            # A⊔B
    A1B1 = somme_disjointe(va1, vb1)        # A₁⊔B₁
    # ensembliste : (A≤A₁ et B≤B₁) ⇒ A⊔B ≤ A₁⊔B₁   (signature : B₁:=A₁, N₁:=B₁)
    inv = inf_egal_somme_invariant("F", "G", va, vb, va1, vb1)
    hyp = et(inf_egal_card(va, va1), inf_egal_card(vb, vb1))
    h = N.assume(hyp)
    le_ens = N.modus_ponens(h, inv)        # A⊔B ≤ A₁⊔B₁   [sous hyp]
    transp = _transporte_t(AB, A1B1)       # (A⊔B ≤ A₁⊔B₁) ⇒ Card(A⊔B) ≤ Card(A₁⊔B₁)
    le_card = N.modus_ponens(le_ens, transp)
    return N.loi_deduction(hyp, le_card)


def cardinal_inf_egal_somme_additive(a="A", b="B", a1="A1", b1="B1"):
    """⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁) ⇒
          Card(Card A ⊔ Card B) ≤ Card(Card A₁ ⊔ Card B₁).   (= a≤a₁ et b≤b₁ ⇒ a+b≤a₁+b₁.)

    (1) généralisé en (∀A)(∀B)(∀A₁)(∀B₁) puis INSTANCIÉ aux TERMES Card A, …, Card B₁.
    Card(Card A ⊔ Card B) = somme_cardinale_binaire(Card A, Card B) = « a + b ».
    Miroir EXACT de cardinal_inf_egal_produit_invariant côté somme."""
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    gen = N.generalisation("A", N.generalisation("B", N.generalisation("A1",
        N.generalisation("B1", somme_cardinale_additive("A", "B", "A1", "B1")))))
    return instancie(instancie(instancie(instancie(gen, cardinal(va)), cardinal(vb)),
                               cardinal(va1)), cardinal(vb1))


# ═══════════════════════════════════════════════════════════════════════════════
# (3)-(4)  Monotonie de la SOMME cardinale à SOMMANT FIXE C
# ═══════════════════════════════════════════════════════════════════════════════
def somme_cardinale_monotone_gauche(a="A", a1="A1", c="C"):
    """⊢ (A ≤ A₁) ⇒ Card(A⊔C) ≤ Card(A₁⊔C).   (sommant droit fixe C ; clos.)

    Cas de (1) avec B:=C, B₁:=C et C≤C (réflexivité de ≤, inf_egal_reflexif au
    terme C) : de A≤A₁ on tire Card(A⊔C) ≤ Card(A₁⊔C).  (= a≤a₁ ⇒ a+c ≤ a₁+c.)"""
    va, va1, vc = _t(a), _t(a1), _t(c)
    hAA1 = N.assume(inf_egal_card(va, va1))                    # A ≤ A₁
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))  # (∀X) X ≤ X
    refl_c = instancie(refl_all, vc)                          # C ≤ C
    add = somme_cardinale_additive(va, vc, va1, vc)           # (A≤A₁ et C≤C) ⇒ Card(A⊔C)≤Card(A₁⊔C)
    le = N.modus_ponens(conjonction_intro(hAA1, refl_c), add)
    return N.loi_deduction(inf_egal_card(va, va1), le)


def somme_cardinale_monotone_droite(b="B", b1="B1", c="C"):
    """⊢ (B ≤ B₁) ⇒ Card(C⊔B) ≤ Card(C⊔B₁).   (sommant gauche fixe C ; clos.)

    Cas de (1) avec A:=C, A₁:=C et C≤C (réflexivité de ≤) : de B≤B₁ on tire
    Card(C⊔B) ≤ Card(C⊔B₁).  (= b≤b₁ ⇒ c+b ≤ c+b₁.)"""
    vb, vb1, vc = _t(b), _t(b1), _t(c)
    hBB1 = N.assume(inf_egal_card(vb, vb1))                    # B ≤ B₁
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))  # (∀X) X ≤ X
    refl_c = instancie(refl_all, vc)                          # C ≤ C
    add = somme_cardinale_additive(vc, vb, vc, vb1)           # (C≤C et B≤B₁) ⇒ Card(C⊔B)≤Card(C⊔B₁)
    le = N.modus_ponens(conjonction_intro(refl_c, hBB1), add)
    return N.loi_deduction(inf_egal_card(vb, vb1), le)


# ═══════════════════════════════════════════════════════════════════════════════
# (5)-(6)  Monotonie du PRODUIT cardinal à FACTEUR FIXE C, niveau Card du support
# ═══════════════════════════════════════════════════════════════════════════════
def produit_cardinale_monotone_gauche(a="A", a1="A1", c="C"):
    """⊢ (A ≤ A₁) ⇒ Card(A×C) ≤ Card(A₁×C).   (facteur droit fixe C ; clos.)

    inf_egal_produit_gauche donne A×C ≤ A₁×C (ensembliste) sous A≤A₁ ; le transport
    par Card (aux termes A×C, A₁×C) conclut Card(A×C) ≤ Card(A₁×C).  Emballage
    « niveau cardinal » de la monotonie produit à facteur fixe.  (= a≤a₁ ⇒ a·c≤a₁·c.)"""
    va, va1, vc = _t(a), _t(a1), _t(c)
    AC = E.produit(va, vc)                 # A×C
    A1C = E.produit(va1, vc)               # A₁×C
    pg = inf_egal_produit_gauche(va, va1, vc)   # (A≤A₁) ⇒ A×C ≤ A₁×C
    hAA1 = N.assume(inf_egal_card(va, va1))     # A ≤ A₁
    le_ens = N.modus_ponens(hAA1, pg)           # A×C ≤ A₁×C   [sous hyp]
    transp = _transporte_t(AC, A1C)             # (A×C ≤ A₁×C) ⇒ Card(A×C) ≤ Card(A₁×C)
    le_card = N.modus_ponens(le_ens, transp)
    return N.loi_deduction(inf_egal_card(va, va1), le_card)


def produit_cardinale_monotone_droite(b="B", b1="B1", c="C"):
    """⊢ (B ≤ B₁) ⇒ Card(C×B) ≤ Card(C×B₁).   (facteur gauche fixe C ; clos.)

    inf_egal_produit_droite donne C×B ≤ C×B₁ (ensembliste) sous B≤B₁ ; transport
    par Card (aux termes C×B, C×B₁).  (= b≤b₁ ⇒ c·b ≤ c·b₁.)"""
    vb, vb1, vc = _t(b), _t(b1), _t(c)
    CB = E.produit(vc, vb)                 # C×B
    CB1 = E.produit(vc, vb1)               # C×B₁
    pd = inf_egal_produit_droite(vb, vb1, vc)   # (B≤B₁) ⇒ C×B ≤ C×B₁
    hBB1 = N.assume(inf_egal_card(vb, vb1))     # B ≤ B₁
    le_ens = N.modus_ponens(hBB1, pd)           # C×B ≤ C×B₁   [sous hyp]
    transp = _transporte_t(CB, CB1)             # (C×B ≤ C×B₁) ⇒ Card(C×B) ≤ Card(C×B₁)
    le_card = N.modus_ponens(le_ens, transp)
    return N.loi_deduction(inf_egal_card(vb, vb1), le_card)


# ═══════════════════════════════════════════════════════════════════════════════
# (7)  ADDITIVITÉ de ≤ pour le PRODUIT cardinal (both vary, niveau Card du support)
#      — miroir EXACT de somme_cardinale_additive, comblant le trou symétrique.
# ═══════════════════════════════════════════════════════════════════════════════
def produit_cardinale_additive(a="A", b="B", a1="A1", b1="B1"):
    """⊢ (A ≤ A₁ et B ≤ B₁) ⇒ Card(A×B) ≤ Card(A₁×B₁).   (Prop. 14 PRODUIT ; clos.)

    Pendant BOTH-VARY au niveau Card du support, exact miroir de
    somme_cardinale_additive : inf_egal_produit_invariant donne l'inégalité
    ENSEMBLISTE A×B ≤ A₁×B₁ sous (A ≤ A₁ et B ≤ B₁) ; le transport par Card (aux
    termes A×B, A₁×B₁) conclut Card(A×B) ≤ Card(A₁×B₁), i.e. a·b ≤ a₁·b₁ où
    a·b := produit_cardinal_binaire(A,B) = Card(A×B).  NON tautologique : antécédent
    = ≤ des facteurs, conséquent = ≤ des cardinaux des produits ; le pont est le
    transport.  (Combinaison de théorèmes clos ; aucune machinerie nouvelle.)"""
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    AB = E.produit(va, vb)                 # A×B
    A1B1 = E.produit(va1, vb1)             # A₁×B₁
    inv = inf_egal_produit_invariant("F", "G", va, vb, va1, vb1)   # (A≤A₁ et B≤B₁) ⇒ A×B ≤ A₁×B₁
    hyp = et(inf_egal_card(va, va1), inf_egal_card(vb, vb1))
    h = N.assume(hyp)
    le_ens = N.modus_ponens(h, inv)        # A×B ≤ A₁×B₁   [sous hyp]
    transp = _transporte_t(AB, A1B1)       # (A×B ≤ A₁×B₁) ⇒ Card(A×B) ≤ Card(A₁×B₁)
    le_card = N.modus_ponens(le_ens, transp)
    return N.loi_deduction(hyp, le_card)


def cardinal_inf_egal_produit_additive(a="A", b="B", a1="A1", b1="B1"):
    """⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁) ⇒
          produit_cardinal_binaire(Card A, Card B) ≤ produit_cardinal_binaire(Card A₁, Card B₁).
       (= a≤a₁ et b≤b₁ ⇒ a·b ≤ a₁·b₁ sur les CARDINAUX a=Card A, …, avec
        a·b = produit_cardinal_binaire(Card A, Card B) = Card(Card A × Card B).)

    🎯 PROPOSITION 14 §III.3 (PRODUIT), forme OPÉRATION sur les cardinaux : (7)
    généralisé en (∀A)(∀B)(∀A₁)(∀B₁) puis INSTANCIÉ aux termes Card·.  Conséquent
    LITTÉRALEMENT phrasé avec produit_cardinal_binaire (= Card(·×·)).  Miroir EXACT
    de cardinal_inf_egal_somme_additive côté produit ; clos, theorie=22."""
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    gen = N.generalisation("A", N.generalisation("B", N.generalisation("A1",
        N.generalisation("B1", produit_cardinale_additive("A", "B", "A1", "B1")))))
    return instancie(instancie(instancie(instancie(gen, cardinal(va)), cardinal(vb)),
                               cardinal(va1)), cardinal(vb1))


__all__ = ["somme_cardinale_additive", "cardinal_inf_egal_somme_additive",
           "somme_cardinale_monotone_gauche", "somme_cardinale_monotone_droite",
           "produit_cardinale_monotone_gauche", "produit_cardinale_monotone_droite",
           "produit_cardinale_additive", "cardinal_inf_egal_produit_additive"]
