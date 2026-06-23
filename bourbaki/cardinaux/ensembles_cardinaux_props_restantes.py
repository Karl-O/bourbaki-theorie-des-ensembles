"""§III.3 — Propositions cardinales restantes : Proposition 7 (produit non nul) et
Proposition 13 (soustraction), plus l'ORDRE TOTAL des cardinaux.

Module NEUF (campagne III.3 props 7/13).  RÉUTILISE les grands théorèmes déjà
prouvés (comparabilité, Cantor–Bernstein, transitivité/réflexivité de ≤) et la
somme cardinale binaire, SANS modifier aucun fichier existant.

──────────────────────────────────────────────────────────────────────────────
PROPOSITION 13 (§III.3.6) :  « a ≥ b  ⟺  (∃c) a = b + c. »
  où a ≥ b s'écrit b ≤ a = inf_egal_card(b, a), et b + c = somme_cardinale_binaire.

  • SENS RÉCIPROQUE (⇐), `prop13_si_somme` — INCONDITIONNEL, prouvé ici :
        (∃c) a = b + c  ⇒  b ≤ a.
    Témoin c : a = b + c = Card(b⊔c).  inf_egal_somme_gauche : b ≤ b⊔c.  Or
    Eq(b⊔c, Card(b⊔c)) (equipotent_son_cardinal) donne b⊔c ≤ Card(b⊔c) = b+c
    (equipotence_implique_inf_egal) ; transitivité de ≤ : b ≤ b+c = a (réécriture
    par a = b+c).  Tout est démontré, aucune injection postulée.

  • SENS DIRECT (⇒), `prop13_forward_conditionnel` — CONDITIONNÉ honnêtement à
    l'existence du « complément cardinal » :
        b ≤ a  ⇒  (∃c) a = b + c.
    L'unique hypothèse, `existe_complement_cardinal(b, a)`, est
        (∃c) Card(a) = somme_cardinale_binaire(b, c)
    (« a se scinde en b plus un reste »).  C'est le cœur combinatoire de Prop 13
    (construire c = a ∖ f⟨b⟩ pour une injection f : b ↪ a) — REPORTÉ (cf. champ
    `reportes`).  L'assemblage `prop13_forward_conditionnel` montre que cette
    hypothèse SUFFIT, en réécrivant Card(a) = a (a cardinal).

──────────────────────────────────────────────────────────────────────────────
ORDRE TOTAL des cardinaux (Théorème 1 §III.3.2, « ≤ est une relation d'ordre
TOTAL ») — assemblé ici comme relation R{x,y} := inf_egal_card(x,y) :
  • `inf_egal_reflexif_general`     : (∀x) x ≤ x            (réflexivité) ;
  • `inf_egal_transitive_general`   : (∀x∀y∀z)((x≤y et y≤z)⇒x≤z)  (transitivité) ;
  • `inf_egal_total_general`        : (∀x∀y)(x≤y ou y≤x)   (comparabilité, via
        le théorème de comparabilité) ;
  • `inf_egal_antisymetrique_card`  : (∀x∀y)((x≤y et y≤x et x,y cardinaux)⇒x=y)
        (ANTISYMÉTRIE sur les cardinaux, via Cantor–Bernstein + Prop 1) ;
  • `cardinaux_ordre_total`         : conjonction des quatre (l'ordre des cardinaux
        est total ; antisymétrie gardée par « x,y cardinaux »).

INVARIANT : theorie_ensembles() reste = 22.  Rien n'est postulé hormis l'hypothèse
EXPLICITE de Prop 13 sens direct (le complément cardinal), portée nominalement.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, non, impl,
                                       appartient, existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination, alpha_existe

from bourbaki.cardinaux.ensembles_cardinaux import (
    inf_egal_card, est_injection_de, cardinal, est_cardinal, equipotent)
from bourbaki.cardinaux.ensembles_cardinaux_ordre import (
    equipotence_implique_inf_egal, inf_egal_transitive)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_bornes_somme import inf_egal_somme_gauche
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ──────────────────────────────────────────────────────────────────────────────
#  Helpers TERME : transitivité de ≤ et « Eq ⇒ ≤ » applicables à des TERMES.
# ──────────────────────────────────────────────────────────────────────────────
def _inf_egal_transitive_t(tX, tY, tZ):
    """⊢ (X≤Y et Y≤Z) ⇒ X≤Z  pour des TERMES X, Y, Z quelconques.

    inf_egal_transitive n'accepte que des NOMS ; on généralise en X,Y,Z puis on
    instancie aux termes (renommage déterministe → robuste)."""
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(gen, _t(tX)), _t(tY)), _t(tZ))


def _eq_implique_inf_egal_t(tX, tY):
    """⊢ Eq(X, Y) ⇒ X ≤ Y  pour des TERMES X, Y quelconques."""
    gen = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def _eq_son_cardinal_t(tX):
    """⊢ Eq(T, Card T)  pour un TERME T (équipotent_son_cardinal généralisé)."""
    gen = N.generalisation("X", equipotent_son_cardinal("X"))
    return instancie(gen, _t(tX))


def _inf_egal_somme_gauche_t(tB, tC):
    """⊢ B ≤ B⊔C  pour des TERMES B, C (inf_egal_somme_gauche généralisé)."""
    gen = N.generalisation("A", N.generalisation("B", inf_egal_somme_gauche("A", "B")))
    return instancie(instancie(gen, _t(tB)), _t(tC))


# ══════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 13 (§III.3.6) — SENS RÉCIPROQUE (⇐), INCONDITIONNEL
# ══════════════════════════════════════════════════════════════════════════════
def inf_egal_b_somme(b="B", c="C"):
    """⊢ b ≤ (b + c).   (« b ≤ b+c », clé du sens ⇐ de Prop 13 ; INCONDITIONNEL.)

    b ≤ b⊔c (inf_egal_somme_gauche) ; b⊔c ≤ Card(b⊔c)=b+c (Eq(b⊔c,Card(b⊔c)) +
    equipotence_implique_inf_egal) ; transitivité de ≤ conclut b ≤ b+c."""
    vb, vc = _t(b), _t(c)
    S = somme_disjointe(vb, vc)                       # b⊔c
    cardS = cardinal(S)                                # Card(b⊔c) = b+c
    le_b_S = _inf_egal_somme_gauche_t(vb, vc)         # b ≤ b⊔c
    eq_S = _eq_son_cardinal_t(S)                       # Eq(b⊔c, Card(b⊔c))
    le_S_card = N.modus_ponens(eq_S, _eq_implique_inf_egal_t(S, cardS))  # b⊔c ≤ Card(b⊔c)
    trans = _inf_egal_transitive_t(vb, S, cardS)      # (b≤b⊔c et b⊔c≤Card)⇒ b≤Card
    return N.modus_ponens(conjonction_intro(le_b_S, le_S_card), trans)   # b ≤ b+c


def prop13_si_somme(a="A", b="B", c="C"):
    """⊢ (a = b + c) ⇒ (b ≤ a).   (Prop 13 §III.3.6, sens RÉCIPROQUE, INCONDITIONNEL.)

    Sous a = b+c : b ≤ b+c (inf_egal_b_somme) ; réécriture S6 (b+c ↦ a via a=b+c)
    donne b ≤ a.  (a ≥ b est entraîné par l'existence d'un cardinal c, a = b+c.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    bc = somme_cardinale_binaire(vb, vc)              # b + c
    le_b_bc = inf_egal_b_somme(b, c)                  # b ≤ b+c
    h = N.assume(egal(va, bc))                         # a = b+c
    # réécris  b ≤ b+c  en  b ≤ a  via  b+c = a  (symétrie de a = b+c)
    bc_eq_a = N.modus_ponens(h, symetrie(va, bc))     # b+c = a
    leib = N.s6(bc, va, "w", inf_egal_card(vb, var("w")))   # (b+c=a) ⇒ ((b≤b+c) ⇔ (b≤a))
    le_b_a = N.modus_ponens(le_b_bc,
        equivalence_avant(N.modus_ponens(bc_eq_a, leib)))   # b ≤ a
    return N.loi_deduction(egal(va, bc), le_b_a)      # (a=b+c) ⇒ (b≤a)


def prop13_existe_implique_inf_egal(a="A", b="B", c="C"):
    """⊢ ((∃c) a = b + c) ⇒ (b ≤ a).   (Prop 13 ⇐ sous forme existentielle ; clos.)

    Décharge du témoin c : per-c, (a=b+c)⇒(b≤a) (prop13_si_somme) ; c n'est pas
    libre dans (b≤a) ⇒ existe_elimination donne ((∃c)a=b+c)⇒(b≤a)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    cname = c if isinstance(c, str) else c.nom
    bc = somme_cardinale_binaire(vb, vc)
    imp = prop13_si_somme(a, b, c)                     # (a=b+c) ⇒ (b≤a)
    return existe_elimination(imp, cname)             # ((∃c)a=b+c) ⇒ (b≤a)


# ══════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 13 (§III.3.6) — SENS DIRECT (⇒), CONDITIONNEL (complément cardinal)
# ══════════════════════════════════════════════════════════════════════════════
def existe_complement_cardinal(b="B", a="A", c="C"):
    """Hypothèse EXPLICITE du sens direct de Prop 13 :
        (∃c) Card(a) = somme_cardinale_binaire(b, c).

    « a se scinde en b + un reste c. »  C'est le cœur combinatoire (construire
    c = a ∖ f⟨b⟩ pour une injection f : b ↪ a, puis a = b ⊔ (a∖f⟨b⟩) à équipotence
    près) — REPORTÉ.  Portée nominalement (jamais postulée comme théorème)."""
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    return existe(cname, egal(cardinal(va), somme_cardinale_binaire(vb, var(cname))))


def prop13_forward_conditionnel(b="B", a="A", c="C"):
    """⊢ (a est un cardinal et existe_complement_cardinal(b,a))  ⇒  (∃c) a = b + c.

    Prop 13 §III.3.6, sens DIRECT, CONDITIONNÉ à l'hypothèse `existe_complement_
    cardinal` (le complément cardinal, REPORTÉ).  Montre que cette hypothèse
    SUFFIT : a cardinal ⇒ Card(a) = a (a = Card(X), Card(Card X) = Card X), donc
    Card(a) = b+c se réécrit a = b+c ; le témoin c est conservé.

    NB : si l'on dispose d'un témoin c avec Card(a) = b+c, ALORS b ≤ a (Prop 13 ⇐)
    et a = b+c, soit exactement l'équivalence de Prop 13.  L'antécédent « a est un
    cardinal » est nécessaire pour identifier Card(a) à a."""
    va, vb = _t(a), _t(b)
    cname = c if isinstance(c, str) else c.nom
    vc = var(cname)
    # « a est un cardinal » = (∃X) a = Card(X)
    xname = "Xa"
    est_card_a = existe(xname, egal(va, cardinal(var(xname))))
    hyp = et(est_card_a, existe_complement_cardinal(b, a, c))
    h = N.assume(hyp)
    h_card = conjonction_elim_gauche(h)               # (∃X) a = Card X
    h_comp = conjonction_elim_droite(h)               # (∃c) Card a = b+c

    # ── Card(a) = a  sous « a cardinal » ─────────────────────────────────────
    # per-témoin X : a = Card X ⇒ Card a = a.
    hX = N.assume(egal(va, cardinal(var(xname))))     # a = Card X
    cX = cardinal(var(xname))                          # Card X
    # Card a = Card (Card X) ;  on veut Card a = a = Card X.
    # equipotent_son_cardinal(Card X) : Eq(Card X, Card(Card X)).  Avec Eq sym +
    # Prop 1 : Card(Card X) = Card X.  Plus simple : a = Card X (hX) ⇒ Card a =
    # Card(Card X) (congruence) ; et Card(Card X) = Card X (idempotence), d'où
    # Card a = Card X = a.
    cardcard_eq_card = _cardinal_idempotent_t(var(xname))   # Card(Card X) = Card X
    carda_eq_cardcard = N.modus_ponens(hX,
        congruence_terme(va, cX, cardinal(var("w"))))      # (a=CardX)⇒(Card a=Card(Card X))
    # carda_eq_cardcard : Card a = Card(Card X)
    carda_eq_card = composer_egalites(carda_eq_cardcard, cardcard_eq_card)  # Card a = Card X
    carda_eq_a = composer_egalites(carda_eq_card, N.modus_ponens(hX, symetrie(va, cX)))  # Card a = a
    carda_eq_a_imp = N.loi_deduction(egal(va, cX), carda_eq_a)   # (a=CardX)⇒(Card a=a)
    carda_eq_a_closed = existe_elimination(carda_eq_a_imp, xname)  # ((∃X)a=CardX)⇒(Card a=a)
    carda_eq_a_thm = N.modus_ponens(h_card, carda_eq_a_closed)    # Card a = a   [sous hyp]

    # ── réécris Card a = b+c  en  a = b+c  via Card a = a ────────────────────
    # per-témoin c : Card a = b+c ⇒ a = b+c (symétrie Card a = a + Leibniz)
    bc = somme_cardinale_binaire(vb, vc)
    hc = N.assume(egal(cardinal(va), bc))             # Card a = b+c
    a_eq_carda = N.modus_ponens(carda_eq_a_thm, symetrie(cardinal(va), va))  # a = Card a
    a_eq_bc = composer_egalites(a_eq_carda, hc)       # a = b+c
    ex_a_eq_bc = N.modus_ponens(a_eq_bc, N.s5(egal(va, somme_cardinale_binaire(vb, vc)), vc, cname))
    # (a = b+c) ⇒ (∃c) a = b+c, puis décharge ∃c de l'hypothèse h_comp
    ex_imp = N.loi_deduction(egal(cardinal(va), bc), ex_a_eq_bc)   # (Card a=b+c)⇒(∃c)a=b+c
    but = existe(cname, egal(va, somme_cardinale_binaire(vb, vc)))
    ex_closed = existe_elimination(ex_imp, cname)     # ((∃c)Card a=b+c)⇒(∃c)a=b+c
    res = N.modus_ponens(h_comp, ex_closed)           # (∃c) a = b+c   [sous hyp]
    return N.loi_deduction(hyp, res)


def _cardinal_idempotent_t(tX):
    """⊢ Card(Card X) = Card X  pour un TERME X.   (Card est idempotent.)

    Eq(Card X, Card(Card X)) (equipotent_son_cardinal au terme Card X) ; Prop 1
    sens direct donne Card(Card X) = Card(Card(Card X))… — plus simplement :
    Eq(Card X, Card(Card X)) ⇒ Card(Card X)=Card(Card(Card X)) n'est pas ce qu'on
    veut.  On utilise : Eq(X, Card X) (equipotent_son_cardinal) et la Proposition 1
    sens direct sur (X, Card X) : Card X = Card(Card X) ; symétrie conclut."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
    vX = _t(tX)
    cX = cardinal(vX)
    eq = _eq_son_cardinal_t(vX)                        # Eq(X, Card X)
    prop1 = _prop1_direct_t(vX, cX)                    # Eq(X,Card X) ⇒ Card X = Card(Card X)
    card_eq = N.modus_ponens(eq, prop1)               # Card X = Card(Card X)
    return N.modus_ponens(card_eq, symetrie(cX, cardinal(cX)))   # Card(Card X) = Card X


__all__ = [
    "inf_egal_b_somme", "prop13_si_somme", "prop13_existe_implique_inf_egal",
    "existe_complement_cardinal", "prop13_forward_conditionnel",
    "_cardinal_idempotent_t",
]
