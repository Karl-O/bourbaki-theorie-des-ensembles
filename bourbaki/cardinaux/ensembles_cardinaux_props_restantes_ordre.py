"""§III.3.2 — L'ORDRE ≤ DES CARDINAUX EST UN ORDRE TOTAL (Théorème 1).

Module NEUF (campagne III.3 props 7/13).  Assemble, comme propriétés de la
relation R{x,y} := inf_egal_card(x,y), les quatre composantes de l'ordre total
des cardinaux (E.III.3.2, Théorème 1 : « R{x,y} : x,y cardinaux et x équipotent à
une partie de y est une relation de BON ORDRE » — ici sa partie ORDRE TOTAL) :

  • RÉFLEXIVITÉ      `inf_egal_reflexif_general`    : (∀x) x ≤ x ;
  • TRANSITIVITÉ     `inf_egal_transitive_general`  : (∀x∀y∀z)((x≤y et y≤z)⇒x≤z) ;
  • COMPARABILITÉ    `inf_egal_total_general`       : (∀x∀y)(x≤y ou y≤x)
        — c'est le THÉORÈME DE COMPARABILITÉ (comparabilite_cardinaux, via Zorn) ;
  • ANTISYMÉTRIE     `inf_egal_antisymetrique_card` : (∀x∀y)((x≤y et y≤x et x,y
        cardinaux) ⇒ x=y) — c'est CANTOR–BERNSTEIN (antisymétrie de ≤) suivi de la
        Proposition 1 (Eq ⇒ Card égaux) et de l'idempotence de Card (un cardinal
        est son propre cardinal).

Et l'assemblage final :
  • `cardinaux_ordre_total` : conjonction des quatre — « ≤ est un ordre total sur
        les cardinaux » (antisymétrie GARDÉE par « x, y cardinaux », fidèle au
        Théorème 1 dont R porte la garde « x et y sont des cardinaux »).

L'antisymétrie est NÉCESSAIREMENT gardée : sur des ensembles quelconques X, Y,
(X≤Y et Y≤X) donne Eq(X,Y) (Cantor–Bernstein), pas X=Y ; l'égalité ne vaut qu'au
niveau des CARDINAUX (objets τ-canoniques).  La garde reproduit exactement la
relation R du Théorème 1.

INVARIANT : theorie_ensembles() = 22.  Tout vient de théorèmes déjà prouvés ; rien
n'est postulé.  NB : comparabilité et Cantor–Bernstein sont coûteux (Zorn, point
fixe) — les fonctions d'assemblage les invoquent une fois.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, ou, impl, existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination

from bourbaki.cardinaux.ensembles_cardinaux import (inf_egal_card, est_cardinal,
                               cardinal, equipotent)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    inf_egal_reflexif, cardinal_egal_si_equipotent)
from bourbaki.cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
from bourbaki.cardinaux.ensembles_comparabilite import comparabilite_cardinaux
from bourbaki.cardinaux.ensembles_cantor_bernstein_final._recollement import cantor_bernstein
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes import _cardinal_idempotent_t


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
#  (1) RÉFLEXIVITÉ :  (∀x) x ≤ x
# ══════════════════════════════════════════════════════════════════════════════
def inf_egal_reflexif_general(x="X"):
    """⊢ (∀X) X ≤ X.   (RÉFLEXIVITÉ de ≤ sur les cardinaux, E.III.3.2.)

    inf_egal_reflexif("X") ⊢ X ≤ X (l'identité Δ_X injecte X dans X) ; clôture
    universelle (généralisation).  Binder « X » (les liants internes de la
    diagonale sont z, t ≠ x, mais collisionnent avec un « x » minuscule)."""
    return N.generalisation(x, inf_egal_reflexif(x))


# ══════════════════════════════════════════════════════════════════════════════
#  (2) TRANSITIVITÉ :  (∀x∀y∀z)((x≤y et y≤z) ⇒ x≤z)
# ══════════════════════════════════════════════════════════════════════════════
def inf_egal_transitive_general(x="X", y="Y", z="Z"):
    """⊢ (∀X∀Y∀Z)((X≤Y et Y≤Z) ⇒ X≤Z).   (TRANSITIVITÉ de ≤, E.III.3.2.)

    inf_egal_transitive ⊢ (X≤Y et Y≤Z)⇒X≤Z (composée de deux injections) ; clôture
    universelle en X, Y, Z."""
    return N.generalisation(x, N.generalisation(y, N.generalisation(z,
        inf_egal_transitive("F", "G", x, y, z))))


# ══════════════════════════════════════════════════════════════════════════════
#  (3) COMPARABILITÉ :  (∀x∀y)(x≤y ou y≤x)
# ══════════════════════════════════════════════════════════════════════════════
def inf_egal_total_general(x="X", y="Y"):
    """⊢ (∀X∀Y)(X≤Y ou Y≤X).   (COMPARABILITÉ : l'ordre des cardinaux est TOTAL.)

    comparabilite_cardinaux ⊢ X≤Y ou Y≤X (théorème de comparabilité via Zorn) ;
    clôture universelle en X, Y."""
    return N.generalisation(x, N.generalisation(y, comparabilite_cardinaux(x, y)))


# ══════════════════════════════════════════════════════════════════════════════
#  (4) ANTISYMÉTRIE (gardée par « cardinaux ») :
#        (∀x∀y)((x≤y et y≤x et est_cardinal(x) et est_cardinal(y)) ⇒ x=y)
# ══════════════════════════════════════════════════════════════════════════════
def _cardinal_est_son_cardinal(x, witness="X"):
    """⊢ est_cardinal(x) ⇒ (Card x = x).   (un cardinal est son propre cardinal.)

    est_cardinal(x) = (∃W) x = Card W (W = `witness`, ≠ nom de x).  Per-témoin W :
    x = Card W ⇒ Card x = Card(Card W) (congruence) = Card W (idempotence) = x
    (symétrie).  W non libre dans « Card x = x » ⇒ ∃-élimination donne l'antécédent
    est_cardinal(x) avec le binder `witness`."""
    vx = _t(x)
    vW = var(witness)
    cW = cardinal(vW)
    hW = N.assume(egal(vx, cW))                          # x = Card W
    cardx_eq_cardcard = N.modus_ponens(hW,
        congruence_terme(vx, cW, cardinal(var("w"))))   # (x=CardW)⇒(Card x=Card(Card W))
    cardcard_eq_cardW = _cardinal_idempotent_t(vW)       # Card(Card W) = Card W
    cardx_eq_cardW = composer_egalites(cardx_eq_cardcard, cardcard_eq_cardW)  # Card x = Card W
    cardx_eq_x = composer_egalites(cardx_eq_cardW, N.modus_ponens(hW, symetrie(vx, cW)))  # Card x = x
    imp = N.loi_deduction(egal(vx, cW), cardx_eq_x)      # (x=CardW)⇒(Card x=x)
    return existe_elimination(imp, witness)              # est_cardinal(x) ⇒ (Card x=x)


def _cantor_bernstein_t(tX, tY):
    """⊢ (X≤Y et Y≤X) ⇒ Eq(X,Y)  pour des TERMES X, Y (Cantor–Bernstein, idempotent
    via généralisation/instanciation pour accepter n'importe quels termes)."""
    gen = N.generalisation("A", N.generalisation("B", cantor_bernstein("A", "B")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def inf_egal_antisymetrique_card(x="a", y="b"):
    """⊢ (∀a∀b)((a≤b et b≤a et est_cardinal(a) et est_cardinal(b)) ⇒ a=b).

    ANTISYMÉTRIE de ≤ sur les CARDINAUX (E.III.3.2 ; antisymétrie de la relation
    d'ordre du Théorème 1).  De (a≤b et b≤a) : Eq(a,b) (CANTOR–BERNSTEIN) ⇒ Card a =
    Card b (Proposition 1, sens direct).  Si a, b sont des cardinaux, Card a = a et
    Card b = b (_cardinal_est_son_cardinal, witness « X » ≠ a,b), donc
    a = Card a = Card b = b.  Binders a, b minuscules (≠ « X » interne de
    est_cardinal et ≠ « A », « B » internes de Cantor–Bernstein)."""
    vx, vy = _t(x), _t(y)
    hyp = et(et(et(inf_egal_card(vx, vy), inf_egal_card(vy, vx)),
                est_cardinal(vx)), est_cardinal(vy))
    h = N.assume(hyp)
    le_xy = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # a≤b
    le_yx = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # b≤a
    card_x = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_cardinal(a)
    card_y = conjonction_elim_droite(h)                           # est_cardinal(b)
    # Eq(a,b) via Cantor–Bernstein
    cb = _cantor_bernstein_t(vx, vy)                     # (a≤b et b≤a) ⇒ Eq(a,b)
    eq_xy = N.modus_ponens(conjonction_intro(le_xy, le_yx), cb)   # Eq(a,b)
    # Card a = Card b (Proposition 1 sens direct, version TERME)
    cardeq = N.modus_ponens(eq_xy, _prop1_direct_t(vx, vy))       # Card a = Card b
    # Card a = a , Card b = b
    cx_eq_x = N.modus_ponens(card_x, _cardinal_est_son_cardinal(x))   # Card a = a
    cy_eq_y = N.modus_ponens(card_y, _cardinal_est_son_cardinal(y))   # Card b = b
    # a = Card a = Card b = b
    x_eq_cardx = N.modus_ponens(cx_eq_x, symetrie(cardinal(vx), vx))  # a = Card a
    x_eq_y = composer_egalites(composer_egalites(x_eq_cardx, cardeq), cy_eq_y)  # a = b
    body = N.loi_deduction(hyp, x_eq_y)
    return N.generalisation(x, N.generalisation(y, body))


def _prop1_direct_t(tX, tY):
    """⊢ Eq(X, Y) ⇒ (Card X = Card Y)  pour des TERMES X, Y (Prop 1 sens direct)."""
    gen = N.generalisation("X", N.generalisation("Y",
        cardinal_egal_si_equipotent("X", "Y")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


# ══════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE : « ≤ est un ordre total sur les cardinaux »
# ══════════════════════════════════════════════════════════════════════════════
def cardinaux_ordre_total():
    """⊢  ((∀X) X≤X)
        et ((∀X∀Y∀Z)((X≤Y et Y≤Z)⇒X≤Z))
        et ((∀a∀b)((a≤b et b≤a et a,b cardinaux)⇒a=b))
        et ((∀X∀Y)(X≤Y ou Y≤X)).

    L'ORDRE ≤ DES CARDINAUX EST TOTAL (Théorème 1 §III.3.2) : réflexif, transitif,
    antisymétrique (sur les cardinaux) et total (comparabilité).  Conjonction des
    quatre composantes prouvées ci-dessus.  Rien postulé.  (Antisymétrie gardée par
    « a, b cardinaux » avec binders a, b — fidèle à la garde « cardinaux » de R.)"""
    refl = inf_egal_reflexif_general("X")
    trans = inf_egal_transitive_general("X", "Y", "Z")
    antisym = inf_egal_antisymetrique_card("a", "b")
    total = inf_egal_total_general("X", "Y")
    return conjonction_intro(conjonction_intro(conjonction_intro(refl, trans), antisym), total)


__all__ = [
    "inf_egal_reflexif_general", "inf_egal_transitive_general",
    "inf_egal_total_general", "inf_egal_antisymetrique_card",
    "cardinaux_ordre_total",
]
