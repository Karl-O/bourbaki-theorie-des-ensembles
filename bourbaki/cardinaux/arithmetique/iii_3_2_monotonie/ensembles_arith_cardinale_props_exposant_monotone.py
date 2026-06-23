"""§III.3.2 / III.3.5 — MONOTONIE de l'EXPONENTIATION cardinale pour l'ordre ≤,
PAR RÉDUCTION à la monotonie au niveau des SUPPORTS (ensembles d'applications).

Énoncés de Bourbaki visés (E.III.3.5) :  a ≤ b ⇒ a^c ≤ b^c  (monotonie en la BASE),
et  c ≤ d ⇒ a^c ≤ a^d  (monotonie en l'EXPOSANT, pour a ≠ 0).

On fournit ici la BRIQUE INCONDITIONNELLE de transport, et les deux énoncés sous
forme CONDITIONNELLE (hypothèse explicite = l'injection au niveau des ENSEMBLES
d'applications, dont la CONSTRUCTION est le verrou dur reporté).  Rien n'est
postulé, theorie=22.

  (0) `inf_egal_transporte_cardinal`  ⊢ (X ≤ Y) ⇒ (Card X ≤ Card Y).   INCONDITIONNEL.
      Brique réutilisable, contenu RÉEL (PAS une tautologie) : tout ensemble est
      équipotent à son cardinal (Eq(X, Card X), equipotent_son_cardinal), une
      équipotence est une injection (equipotence_implique_inf_egal), et ≤ est
      transitive (inf_egal_transitive).  D'où la chaîne
          Card X  ≤  X  ≤  Y  ≤  Card Y
      (Card X ≤ X par Eq(Card X, X) = sym de Eq(X, Card X) ; Y ≤ Card Y par
       Eq(Y, Card Y)), et deux transitivités concluent Card X ≤ Card Y.  C'est
      l'invariance de ≤ sous Card (le pendant de la Proposition 1 pour l'ordre).

  (1) `exposant_monotone_base_conditionnel`  ⊢ (𝓕(C;A) ≤ 𝓕(C;B)) ⇒ (a^c ≤ b^c),
      où a^c = Card(𝓕(C;A)), b^c = Card(𝓕(C;B)) (a=Card A, b=Card B, c=Card C).
      RÉDUCTION : l'hypothèse 𝓕(C;A) ≤ 𝓕(C;B) (injection au niveau des SUPPORTS),
      transportée par (0), donne Card(𝓕(C;A)) ≤ Card(𝓕(C;B)) = a^c ≤ b^c.  NON
      tautologique : la conclusion porte sur les CARDINAUX des supports, l'hypothèse
      sur les supports eux-mêmes ; le pont est (0).

  (2) `exposant_monotone_exposant_conditionnel`  ⊢ (𝓕(C;A) ≤ 𝓕(D;A)) ⇒ (a^c ≤ a^d),
      où a^c = Card(𝓕(C;A)), a^d = Card(𝓕(D;A)).  Même réduction par (0) ; même
      hypothèse de support (injection 𝓕(C;A) ↪ 𝓕(D;A)).

──────────────────────────────────────────────────────────────────────────────
REPORTÉ (verrou dur, anti-faux-résultat) : la DÉCHARGE des hypothèses (1)-(2),
c.-à-d. la CONSTRUCTION INCONDITIONNELLE des injections d'ESPACES DE FONCTIONS
    (A ≤ B)  ⇒  𝓕(C;A) ≤ 𝓕(C;B)        [monotonie en la base]
    (C ≤ D)  ⇒  𝓕(C;A) ≤ 𝓕(D;A)  (A≠∅)  [monotonie en l'exposant]
Elle exige une injection W au niveau des TRIPLES ((G,C),A) ↦ ((G',C),B) où G'
recompose le graphe G avec l'injection j:A↪B (resp. prolonge le domaine C↪D par
une valeur-défaut a₀∈A), avec bonne-définition via le PONT « valeur d'application »
(ensembles_application_valeur) et injectivité back-and-forth — exactement la
machinerie lourde déployée pour Prop 9/10.  Tractable mais hors budget de cette
passe ; les énoncés conditionnels ci-dessus la rendent « plug-in » dès que les
deux injections de supports seront prouvées.  (Cantor a<2^a est DÉJÀ clos :
ensembles_cantor.cantor_strict ; produit-monotonie est close :
ensembles_arith_cardinale_props_produit_monotone.inf_egal_produit_invariant.)
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, impl, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_intro, instancie
from bourbaki.cardinaux.ensembles_cardinaux import (equipotent, cardinal, inf_egal_card)
from bourbaki.cardinaux.ensembles_cardinaux_ordre import (equipotence_implique_inf_egal,
                               inf_egal_transitive)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import exposant_cardinal_binaire


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# (0)  Transport de ≤ par Card :  (X ≤ Y) ⇒ (Card X ≤ Card Y)   (INCONDITIONNEL)
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_transporte_cardinal(x="X", y="Y"):
    """⊢ (X ≤ Y) ⇒ (Card X ≤ Card Y).   (invariance de ≤ sous Card ; clos, contenu réel.)

    Card X ≤ X (Eq(Card X, X) = sym de Eq(X, Card X), puis equipotence⇒≤) ;
    Y ≤ Card Y (Eq(Y, Card Y), equipotence⇒≤) ; sous X ≤ Y, deux transitivités
    donnent Card X ≤ X ≤ Y ≤ Card Y."""
    vX, vY = _t(x), _t(y)
    cX, cY = cardinal(vX), cardinal(vY)
    # equipotence ⇒ ≤  (généralisé puis instancié aux termes Card·/·)
    eii_all = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))
    sym_all = N.generalisation("X", N.generalisation("Y",
        equipotence_symetrique("F", "X", "Y")))
    trans_all = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    # Card X ≤ X   (Eq(X, Card X) → sym → Eq(Card X, X) → equipotence⇒≤)
    eqXcX = _eq_son_card(vX)                                                 # Eq(X, Card X)
    eq_cX_X = N.modus_ponens(eqXcX, instancie(instancie(sym_all, vX), cX))   # Eq(Card X, X)
    le_cX_X = N.modus_ponens(eq_cX_X, instancie(instancie(eii_all, cX), vX))  # Card X ≤ X
    # Y ≤ Card Y
    eqYcY = _eq_son_card(vY)                                                 # Eq(Y, Card Y)
    le_Y_cY = N.modus_ponens(eqYcY, instancie(instancie(eii_all, vY), cY))    # Y ≤ Card Y
    # sous X ≤ Y : Card X ≤ Y ≤ Card Y
    hXY = N.assume(inf_egal_card(vX, vY))
    t1 = instancie(instancie(instancie(trans_all, cX), vX), vY)              # (CardX≤X et X≤Y)⇒CardX≤Y
    le_cX_Y = N.modus_ponens(conjonction_intro(le_cX_X, hXY), t1)            # Card X ≤ Y
    t2 = instancie(instancie(instancie(trans_all, cX), vY), cY)             # (CardX≤Y et Y≤CardY)⇒CardX≤CardY
    le_cX_cY = N.modus_ponens(conjonction_intro(le_cX_Y, le_Y_cY), t2)       # Card X ≤ Card Y
    return N.loi_deduction(inf_egal_card(vX, vY), le_cX_cY)


def _eq_son_card(t):
    """⊢ Eq(t, Card t)  pour un TERME t quelconque (instance-terme de equipotent_son_cardinal)."""
    gen = N.generalisation("X", equipotent_son_cardinal("X"))   # (∀X) Eq(X, Card X)
    return instancie(gen, t)


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  Monotonie en la BASE (conditionnelle au support) :
#      (𝓕(C;A) ≤ 𝓕(C;B)) ⇒ (a^c ≤ b^c)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_monotone_base_conditionnel(a="A", b="B", c="C"):
    """⊢ (𝓕(C;A) ≤ 𝓕(C;B)) ⇒ (a^c ≤ b^c).   (monotonie en la base, CONDITIONNELLE au
    support ; clos sous la SEULE hypothèse explicite « injection 𝓕(C;A) ↪ 𝓕(C;B) ».)

    a^c := exposant_cardinal_binaire(Card A, Card C) = Card(𝓕(C;A)),
    b^c := Card(𝓕(C;B)).  De 𝓕(C;A) ≤ 𝓕(C;B) (HYP de support), le transport (0)
    donne Card(𝓕(C;A)) ≤ Card(𝓕(C;B)), i.e. a^c ≤ b^c.  L'hypothèse est NON
    circulaire (elle porte sur les supports, la conclusion sur leurs cardinaux ;
    sa décharge = construction de l'injection d'espaces de fonctions, reportée)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    FCA = E.applications(vc, va)             # 𝓕(C; A)  (support de a^c)
    FCB = E.applications(vc, vb)             # 𝓕(C; B)  (support de b^c)
    # transport (0) instancié aux supports : (𝓕(C;A) ≤ 𝓕(C;B)) ⇒ Card 𝓕(C;A) ≤ Card 𝓕(C;B)
    transp_all = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))
    return instancie(instancie(transp_all, FCA), FCB)   # (𝓕(C;A)≤𝓕(C;B)) ⇒ (a^c ≤ b^c)


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  Monotonie en l'EXPOSANT (conditionnelle au support) :
#      (𝓕(C;A) ≤ 𝓕(D;A)) ⇒ (a^c ≤ a^d)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_monotone_exposant_conditionnel(a="A", c="C", d="D"):
    """⊢ (𝓕(C;A) ≤ 𝓕(D;A)) ⇒ (a^c ≤ a^d).   (monotonie en l'exposant, CONDITIONNELLE
    au support ; clos sous la SEULE hypothèse « injection 𝓕(C;A) ↪ 𝓕(D;A) ».)

    a^c := Card(𝓕(C;A)), a^d := Card(𝓕(D;A)).  Même réduction par le transport (0)
    appliqué aux supports 𝓕(C;A), 𝓕(D;A).  (Bourbaki : valable pour a ≠ 0 ; la
    restriction a≠0 réapparaîtra dans la CONSTRUCTION de l'injection de support,
    reportée — pour C↪D il faut une valeur-défaut a₀∈A donc A ≠ ∅.)"""
    va, vc, vd = _t(a), _t(c), _t(d)
    FCA = E.applications(vc, va)             # 𝓕(C; A)
    FDA = E.applications(vd, va)             # 𝓕(D; A)
    transp_all = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))
    return instancie(instancie(transp_all, FCA), FDA)   # (𝓕(C;A)≤𝓕(D;A)) ⇒ (a^c ≤ a^d)


__all__ = ["inf_egal_transporte_cardinal",
           "exposant_monotone_base_conditionnel",
           "exposant_monotone_exposant_conditionnel"]
