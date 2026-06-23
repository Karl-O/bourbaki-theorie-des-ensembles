"""§III.5.6 / §III.5.7 — Calcul sur les entiers : NOTIONS COMPLÉMENTAIRES (abrégées).

Module de NOTIONS (round III56-entiers) : introduit, comme TERMES / prédicats
FIDÈLES, les notions de §III.5.6 (Définition 1 : multiple, diviseur, quotient a/b,
partie entière du quotient) et §III.5.7 (développement de base b : chiffre, symbole
numérique) ABSENTES des modules existants, ainsi que la PUISSANCE SUR LES ENTIERS
(Corollaire 3 de la Prop. 1, §III.5.1) et la DIVISION EUCLIDIENNE comme couple (q, r).

⚠ AUCUN MODULE EXISTANT N'EST MODIFIÉ.  Ce module COMPLÈTE ensembles_entiers.py (qui
introduit déjà : divise, est_pair, est_impair, reste_division, quotient_division,
factorielle, coefficient_binomial, difference_entiers, intervalle_entiers,
fonction_caracteristique, est_suite_finie, longueur_suite, inf_strict_entiers) — on
RÉ-IMPORTE divise/quotient_division/reste_division de là pour ne pas dupliquer.

ÉNONCÉS VERBATIM (ROADMAP_chap2-4.md, §III.5) :

  • §III.5.6 — Définition 1 (reste, multiple, diviseur, quotient) : « … on dit que r
    est le reste de la division de a par b.  Si r = 0, on dit que a est multiple de b,
    ou que a est divisible par b, ou que b est un diviseur de a, ou que b divise a ;
    le nombre q s'appelle alors le quotient de a par b et se note a/b ou (a)/(b).
    Lorsque a n'est pas multiple de b, le nombre q s'appelle la partie entière du
    quotient de a par b. »

  • §III.5.6 — Division euclidienne (codage) : (q, r) = divmod(a, b).

  • §III.5.7 — Développement de base b : « … il existe une suite finie (r_h)_{0≤h≤k−1}
    telle que 0 ≤ r_h ≤ b − 1 …, et a = Σ_{h=0}^{k−1} r_h b^{k−h−1} ; … Chaque entier
    < b est représenté par un symbole distinctif appelé chiffre ; la suite des chiffres
    r_0, r_1, …, r_{k−1} … est le symbole numérique associé à a … »

  • §III.5.1 — Corollaire 3 (de prop. 1) : « Si a et b sont des entiers, a^b est un
    entier. »  (→ la puissance a^b sur les entiers, comme exponentiation cardinale.)

NIVEAU DE FIDÉLITÉ ET RÉSERVES D'HONNÊTETÉ — comme dans ensembles_entiers.py, la
plupart de ces notions reposent sur l'ARITHMÉTIQUE CARDINALE BINAIRE (b·q + r) et/ou
la DIVISION EUCLIDIENNE (th. 1, bon ordre de ℕ + récurrence C61), NON disponibles ;
on les introduit donc comme TERMES ABRÉVIATEURS opaques (app(...)) ou comme prédicats
construits sur les notions existantes, SANS axiome caractérisant — l'important est que
la NOTION existe et soit fidèle à l'énoncé.  Les propriétés (Prop. 1-15) sont REPORTÉES.

THÉORÈMES DIRECTS certifiés (bonus, niveau abrégé pur — synonymies définitionnelles) :
  • multiple_ssi_divise          ⊢ (a multiple de b) ⇒ (b divise a)   [Déf. 1, identité]
  • divise_ssi_multiple          ⊢ (b divise a) ⇒ (a multiple de b)   [Déf. 1, identité]
  • diviseur_ssi_divise          ⊢ (b diviseur de a) ⇒ (b divise a)   [Déf. 1, identité]
  • divisible_ssi_multiple       ⊢ (a divisible par b) ⇒ (a multiple de b) [Déf. 1]
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, non, impl, existe,
                                       pourtout, appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (cardinal, est_cardinal,
                                                    inf_egal_card, inf_strict_card)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
# NE PAS dupliquer : on RÉ-IMPORTE les notions DÉJÀ posées dans ensembles_entiers.
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (divise, quotient_division,
                                                reste_division, est_entier, ZERO,
                                                DEUX, successeur, difference_entiers)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5.6 — Définition 1 : multiple, divisible, diviseur, quotient a/b
# ═══════════════════════════════════════════════════════════════════════════════
# « Si r = 0, on dit que a est multiple de b, ou que a est divisible par b, ou que
#   b est un diviseur de a, ou que b divise a. »  → CES QUATRE FORMULATIONS sont,
#   par l'énoncé même, ÉQUIVALENTES (synonymes) au prédicat divise(b, a) déjà posé.

def est_multiple(a, b):
    """« a est multiple de b » := b divise a   (E.III.5.6, Déf. 1).

    Synonyme verbatim de divise(b, a) (réutilise la notion existante, sans dupliquer).
    Bourbaki : « Si r = 0 … on dit que a est multiple de b … ou que b divise a »."""
    return divise(_t(b), _t(a))


def est_divisible_par(a, b):
    """« a est divisible par b » := b divise a   (E.III.5.6, Déf. 1).

    Troisième formulation verbatim, synonyme de est_multiple(a, b) = divise(b, a)."""
    return divise(_t(b), _t(a))


def est_diviseur(b, a):
    """« b est un diviseur de a » := b divise a   (E.III.5.6, Déf. 1).

    Formulation duale (sujet b) : « b est un diviseur de a, ou que b divise a »."""
    return divise(_t(b), _t(a))


def quotient_a_sur_b(a, b):
    """a/b := le quotient q de a par b   (E.III.5.6, Déf. 1, notation a/b ou (a)/(b)).

    « le nombre q s'appelle alors le quotient de a par b et se note a/b ou (a)/(b). »
    Le quotient q est déjà introduit (quotient_division) ; la NOTATION a/b implique,
    dans ce chapitre, que b divise a (« le seul fait d'écrire a/b … implique que b
    divise a »).  On la réifie comme le même terme que le quotient de la division."""
    return quotient_division(_t(a), _t(b))


def notation_quotient_implique_divise(a, b):
    """Convention §III.5.6 : « le seul fait d'écrire a/b … implique que b divise a ».

    Prédicat de la convention : écrire a/b PRÉSUPPOSE (b divise a).  On l'expose comme
    la formule (b divise a), à fournir comme hypothèse lorsqu'on emploie a/b."""
    return divise(_t(b), _t(a))


def partie_entiere_quotient(a, b):
    """« partie entière du quotient de a par b » := q (E.III.5.6, Déf. 1).

    « Lorsque a n'est pas multiple de b, le nombre q s'appelle la partie entière du
    quotient de a par b. »  C'est le MÊME q (quotient de la division euclidienne),
    nommé « partie entière » dans le cas où a n'est pas multiple de b."""
    return quotient_division(_t(a), _t(b))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5.6 — Division euclidienne comme COUPLE (q, r)   (« divmod »)
# ═══════════════════════════════════════════════════════════════════════════════
def division_euclidienne(a, b):
    """divmod(a, b) := (q, r), couple (quotient, reste) de la division de a par b
       (E.III.5.6, codage).  q = quotient_division(a,b), r = reste_division(a,b).

    Bourbaki/codage : (q, r) = (μq. a < b(q+1),  a − b·μq. a < b(q+1)), uniques sous
    a = bq + r, r < b (th. 1, REPORTÉ).  On RÉIFIE le couple ⟨q, r⟩ avec les termes
    quotient/reste DÉJÀ posés, sans les redéfinir."""
    return E.couple(quotient_division(_t(a), _t(b)), reste_division(_t(a), _t(b)))


def condition_division_euclidienne(a, b, q, r):
    """Condition du th. 1 : a = b·q + r  et  r < b   (E.III.5.6, th. 1).

    Caractérisation (q, r) « uniques » : on l'expose comme la FORMULE conjuguée
    (a = b·q + r) ∧ (r < b), avec b·q + r codé par le terme abréviateur opaque
    app('plus_ent', app('prod_ent', b, q), r) — l'arithmétique cardinale binaire
    b·q + r n'étant pas un terme disponible (cf. réserve générale)."""
    vb, vq, vr, va = _t(b), _t(q), _t(r), _t(a)
    bq_plus_r = app("plus_ent", app("prod_ent", vb, vq), vr)
    return et(egal(va, bq_plus_r), inf_strict_card(vr, vb))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5.1 — Corollaire 3 : puissance sur les entiers  a^b
# ═══════════════════════════════════════════════════════════════════════════════
def puissance_entiers(a, b):
    """a^b := exponentiation cardinale de a par b   (E.III.5.1, Cor. 3 ; E.III.3.5, Déf. 4).

    « Si a et b sont des entiers, a^b est un entier. »  La puissance sur les entiers
    EST l'exponentiation cardinale (a^b = Card(𝓕(b; a))), déjà construite ; on la
    nomme ici pour les entiers (sans la redéfinir).  Le fait que a^b soit un entier
    (Cor. 3) repose sur la Prop. 1 (récurrence) → REPORTÉ."""
    return exposant_cardinal_binaire(_t(a), _t(b))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5.7 — Développement de base b : chiffre, symbole numérique
# ═══════════════════════════════════════════════════════════════════════════════
def est_chiffre(r, b):
    """« r est un chiffre (en base b) » := 0 ≤ r ≤ b − 1   (E.III.5.7).

    « Chaque entier < b est représenté par un symbole distinctif appelé chiffre. »
    Un chiffre de base b est un entier r tel que 0 ≤ r ≤ b−1 (≡ r < b).  On l'exprime
    par : r entier et r < b."""
    vr, vb = _t(r), _t(b)
    return et(est_entier(vr), inf_strict_card(vr, vb))


def developpement_base_b(a, b):
    """développement de base b de a := la suite des chiffres (r_h)_{0≤h≤k−1}
       telle que a = Σ_{h=0}^{k−1} r_h b^{k−h−1}, 0 ≤ r_h ≤ b−1, r_0 ≠ 0  (E.III.5.7).

    « On dit que Σ_{h} r_h b^{k−h−1} est le développement de base b du nombre entier
    a. »  Existence/unicité (suite finie de chiffres) : récurrence par division
    euclidienne (th. 1) → REPORTÉE.  On RÉIFIE le développement (la famille des
    chiffres) par le terme abréviateur opaque app('dev_base', a, b)."""
    return app("dev_base", _t(a), _t(b))


def symbole_numerique(a, b):
    """symbole numérique de a en base b := la suite des chiffres r_0,r_1,…,r_{k−1}
       écrite de gauche à droite   (E.III.5.7, système de numération de base b).

    « la suite des chiffres r_0, r_1, …, r_{k−1} écrite de gauche à droite est le
    symbole numérique associé à a ».  Réifié par le terme app('sym_num', a, b)
    (la chaîne de chiffres) ; identique en contenu au développement, vu comme symbole."""
    return app("sym_num", _t(a), _t(b))


def chiffre_de_rang(a, b, h):
    """r_h := le chiffre de rang h du développement de base b de a   (E.III.5.7).

    Le h-ième chiffre (0 ≤ h ≤ k−1) de la suite (r_h).  Réifié par app('chiffre', a, b, h).
    0 ≤ r_h ≤ b−1 (est_chiffre) ; r_0 ≠ 0 (cf. énoncé) — propriétés REPORTÉES."""
    return app("chiffre", _t(a), _t(b), _t(h))


# ═══════════════════════════════════════════════════════════════════════════════
# THÉORÈMES DIRECTS (bonus) — synonymies définitionnelles, niveau abrégé pur
# ═══════════════════════════════════════════════════════════════════════════════
# Par la Déf. 1, « a multiple de b », « a divisible par b », « b diviseur de a » et
# « b divise a » sont LE MÊME prédicat divise(b, a) (synonymes verbatim).  La synonymie
# se certifie par l'identité logique ⊢ P ⇒ P (loi de déduction sur l'hypothèse P),
# entièrement au niveau abrégé (Formule), donc CLOSE et sans axiome.

def _identite_impl(P):
    """⊢ P ⇒ P   (loi de déduction : {P}⊢P  ⟹  ⊢ P⇒P).  Théorème CLOS abrégé."""
    return N.loi_deduction(P, N.assume(P))


def multiple_ssi_divise(a="a", b="b"):
    """⊢ (a est multiple de b) ⇒ (b divise a)   (E.III.5.6, Déf. 1 — synonymie).

    est_multiple(a,b) ≡ divise(b,a) par définition ; l'implication est l'identité."""
    return _identite_impl(est_multiple(_t(a), _t(b)))


def divise_ssi_multiple(a="a", b="b"):
    """⊢ (b divise a) ⇒ (a est multiple de b)   (E.III.5.6, Déf. 1 — synonymie)."""
    return _identite_impl(divise(_t(b), _t(a)))


def diviseur_ssi_divise(a="a", b="b"):
    """⊢ (b est un diviseur de a) ⇒ (b divise a)   (E.III.5.6, Déf. 1 — synonymie)."""
    return _identite_impl(est_diviseur(_t(b), _t(a)))


def divisible_ssi_multiple(a="a", b="b"):
    """⊢ (a est divisible par b) ⇒ (a est multiple de b)   (E.III.5.6, Déf. 1)."""
    return _identite_impl(est_divisible_par(_t(a), _t(b)))


__all__ = [
    # §III.5.6 Déf. 1 — multiple / divisible / diviseur / quotient a/b
    "est_multiple", "est_divisible_par", "est_diviseur",
    "quotient_a_sur_b", "notation_quotient_implique_divise", "partie_entiere_quotient",
    # §III.5.6 — division euclidienne (couple)
    "division_euclidienne", "condition_division_euclidienne",
    # §III.5.1 Cor. 3 — puissance sur les entiers
    "puissance_entiers",
    # §III.5.7 — développement de base b
    "est_chiffre", "developpement_base_b", "symbole_numerique", "chiffre_de_rang",
    # théorèmes directs (synonymies)
    "multiple_ssi_divise", "divise_ssi_multiple",
    "diviseur_ssi_divise", "divisible_ssi_multiple",
]
