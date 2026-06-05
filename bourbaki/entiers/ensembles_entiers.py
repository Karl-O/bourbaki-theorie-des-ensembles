"""§III.4 — Entiers naturels. Ensembles finis : DÉFINITIONS (abrégées).

Définitions VERBATIM de E.III.4 (énoncés lus dans le Texte.tex §III.4.1) :

  • Déf. 1 (cardinal fini / entier naturel / ensemble fini) :
        Fini(𝔞)  :⇔  (𝔞 est un cardinal) ∧ (𝔞 ≠ 𝔞 + 1).
    Un cardinal fini s'appelle aussi un ENTIER NATUREL (ou entier).  Un ensemble E
    est FINI si Card(E) est un cardinal fini ; Card(E) est alors le nombre
    d'éléments de E.  Une famille est finie si son ensemble d'indices est fini.

  • Successeur 𝔞 ↦ 𝔞 + 1 et premiers entiers (Implémentation §III.4.1) :
        0 = Card(∅),  1 = 0 + 1,  2 = 1 + 1,  3 = 2 + 1,  4 = 3 + 1, …
    Itération du successeur à partir de 0.

  • Déf. 2 (ensemble de caractère fini) : une partie 𝔖 ⊂ 𝔓(E) est de caractère
    fini ssi  X ∈ 𝔖 ⇔ (∀Y)((Y ⊂ X ∧ Y fini) ⇒ Y ∈ 𝔖)  (§III.4.5, Déf. 2).

────────────────────────────────────────────────────────────────────────────────
SUCCESSEUR — FIDÉLITÉ À BOURBAKI (corrigée, round 13) :

Bourbaki DÉFINIT le successeur 𝔞 ↦ 𝔞 + 1 comme la SOMME CARDINALE 𝔞 + 1, où
1 = Card({∅}) (E.III.3.1, Déf. 2, Exemple) et + est la somme cardinale binaire
(E.III.3.3, Déf. 3 : 𝔞 + 𝔟 = Card de la somme disjointe).  Le successeur N'EST
DONC PAS un primitif opaque : c'est, PAR DÉFINITION,

        successeur(𝔞)  :=  𝔞 + 1  =  somme_cardinale_binaire(𝔞, {∅})  =  Card(𝔞 ⊔ {∅}),

terme DÉRIVÉ de la somme cardinale binaire (ensembles_somme_disjointe), sans aucun
axiome nouveau (la somme disjointe 𝔞 ⊔ {∅} = (𝔞×{0}) ∪ ({∅}×{1}) découle des axiomes
existants réunion/produit/paire).  C'est la définition de 𝔞+1 de Bourbaki rendue
littérale — fidèle ET non postulée.  (Le marqueur ensembliste {∅} représente le
cardinal 1 = Card({∅}) ; voir le pont successeur(0)=Card({∅}) ci-dessous.)

[Historique : round 12 codait successeur par un terme OPAQUE app("succ", 𝔞) SANS
axiome le reliant à la somme — gap de FIDÉLITÉ corrigé ici.]

THÉORÈMES débloqués par cette définition fidèle (ensembles_zero_plus_un.py) :
  • successeur(0) = Card(∅ ⊔ {∅}) = Card({∅}) = 1   (« 0 + 1 = 1 », card_somme_zero_un) ;
  • 0 ≠ 0 + 1  (Card(∅) ≠ Card({∅}), via ¬Eq(∅,{∅}) + Proposition 1) ;
  • Fini(0) = (0 est un cardinal) ∧ (0 ≠ 0+1)  — 0 EST UN ENTIER NATUREL (1er entier
    concret certifié par le noyau).
Le théorème direct « Card(X) est un cardinal » (1er conjoint de Fini) reste dans
ensembles_entiers_theoremes.py ; les THÉORÈMES DE FINITUDE concrets sont dans
ensembles_zero_plus_un.py.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, egal, et, non, impl, existe, pourtout, equiv,
                     inclus, appartient)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (cardinal, est_cardinal, CARD_VIDE,
                                 inf_egal_card, inf_strict_card)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_cardinale_binaire


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ── Successeur 𝔞 ↦ 𝔞 + 1  (E.III.4.1, Implémentation FIDÈLE) ───────────────────
def successeur(a):
    """𝔞 + 1 := 𝔞 + Card({∅}) := somme_cardinale_binaire(𝔞, {∅}) = Card(𝔞 ⊔ {∅}).

    SUCCESSEUR D'UN CARDINAL (E.III.4.1, Déf. 1 / E.III.3.3, Déf. 3) : c'est la
    SOMME CARDINALE de 𝔞 et de 1 = Card({∅}) (E.III.3.1, Déf. 2, Exemple).  Terme
    DÉRIVÉ de la somme cardinale binaire (= Card de la somme disjointe), SANS axiome
    nouveau — la définition de 𝔞+1 de Bourbaki rendue littérale (et non postulée).
    Bourbaki itère ce successeur à partir de 0 = Card(∅) : 1 = 0+1, 2 = 1+1, …"""
    return somme_cardinale_binaire(_t(a), E.singleton(E.VIDE))


# ── Premiers entiers : 0, 1, 2, 3, 4  (E.III.4.1, Implémentation) ──────────────
ZERO = CARD_VIDE                 # 0 = Card(∅)
UN = successeur(ZERO)            # 1 = 0 + 1
DEUX = successeur(UN)            # 2 = 1 + 1
TROIS = successeur(DEUX)         # 3 = 2 + 1
QUATRE = successeur(TROIS)       # 4 = 3 + 1


# ── Déf. 1 : « 𝔞 est fini » / « 𝔞 est un entier naturel » ─────────────────────
def est_fini(a):
    """Fini(𝔞) := (𝔞 est un cardinal) ∧ (𝔞 ≠ 𝔞 + 1)   (E.III.4.1, Déf. 1).

    Un cardinal fini s'appelle aussi un entier naturel."""
    return et(est_cardinal(a), non(egal(a, successeur(a))))


def est_entier(a):
    """« 𝔞 est un entier (naturel) » := Fini(𝔞)   (E.III.4.1, Déf. 1).

    Par définition, un entier naturel EST un cardinal fini : c'est exactement
    le prédicat Fini.  (Synonyme fourni pour la lisibilité des énoncés.)"""
    return est_fini(a)


# ── Déf. 1 (suite) : « l'ensemble E est fini » ────────────────────────────────
def est_fini_ensemble(e):
    """« E est fini » := Fini(Card(E))   (E.III.4.1, Déf. 1).

    Card(E) est alors « le nombre d'éléments de E »."""
    return est_fini(cardinal(e))


def nombre_d_elements(e):
    """Card(E) = « le nombre d'éléments de E » (terme, défini quand E est fini)."""
    return cardinal(e)


# ── Déf. 1 (suite) : « la famille (X_ι) est finie » ───────────────────────────
def famille_finie(i):
    """« une famille est finie » := son ensemble d'indices I est fini (E.III.4.1).

    Paramètre i : l'ensemble d'indices I (terme)."""
    return est_fini_ensemble(i)


# ── Déf. 2 : ensemble de caractère fini  (§III.4.5, Déf. 2) ────────────────────
def de_caractere_fini(S, e, x="X", y="Y"):
    """« 𝔖 (⊂ 𝔓(E)) est de caractère fini »   (E.III.4.5, Déf. 2) :=
       (∀X)((X∈𝔖) ⇔ (∀Y)((Y⊂X ∧ Y fini) ⇒ Y∈𝔖)).

    X∈𝔖 équivaut à : toute partie finie de X appartient à 𝔖.  Liants X, Y."""
    vX, vY = var(x), var(y)
    droite = pourtout(y, impl(et(inclus(vY, vX), est_fini_ensemble(vY)),
                              appartient(vY, S)))
    from bourbaki.logique.formule import equiv
    return pourtout(x, equiv(appartient(vX, S), droite))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5 — CALCUL SUR LES ENTIERS : DÉFINITIONS (termes / prédicats, abrégés)
# ═══════════════════════════════════════════════════════════════════════════════
# Énoncés lus verbatim V7 §III.5 (Texte.tex de chaque sous-section).  Ce sont des
# DÉFINITIONS fidèles ; les PROPOSITIONS/THÉORÈMES de la section reposent toutes sur
# la RÉCURRENCE (C61, NON disponible) et/ou l'arithmétique cardinale binaire (+, ·,
# différence, NON implémentée) → elles sont REPORTÉES honnêtement (voir le rapport).
# Seuls les théorèmes DIRECTS (instances de l'axiome d'intervalle + projections
# logiques immédiates) sont prouvés, dans ensembles_entiers_theoremes.py.


# ── §III.5.2 — Inégalité stricte ; différence b − a (Cor. 4) ──────────────────
def inf_strict_entiers(a, b):
    """a < b   (inégalité stricte entre entiers, E.III.5.2).

    C'est l'ordre strict des cardinaux (E.III.3.2) : a < b :⇔ (a≤b et a≠b).
    Prop. 2 (a<b ⇔ (∃c>0)(b=a+c)) repose sur l'arithmétique cardinale → REPORTÉE."""
    return inf_strict_card(a, b)


def difference_entiers(b, a, c="c"):
    """b − a := μ c. (b = a + c)   (différence des entiers b et a, a ≤ b ; E.III.5.2, Cor. 4).

    Notation Bourbaki : l'unique entier c tel que b = a + c (existe et est unique
    quand a ≤ b, par Cor. 4).  Codée par le terme app("diff_ent", b, a) abréviant
    μc.(b = a + c).

    ⚠ RÉSERVE D'HONNÊTETÉ : la somme cardinale BINAIRE a + c n'est pas disponible
    comme terme (ensembles_cardinaux n'expose que la somme d'une FAMILLE), et le
    plus-petit-élément μ exige le bon ordre de ℕ ; on code donc b − a par un terme
    abréviateur opaque, sans axiome caractérisant (aucun théorème direct ne peut en
    être tiré sans l'arithmétique cardinale)."""
    return app("diff_ent", _t(b), _t(a))


# ── §III.5.3 — Intervalle d'entiers [a, b] ────────────────────────────────────
def intervalle_entiers(a, b):
    """[a, b] := { x | x cardinal et a ≤ x et x ≤ b }   (E.III.5.3).

    Ré-exporté depuis ensembles_abrege (terme collectivisant, Remarque III.25).
    Le corps caractérisant et l'axiome AXIOME_INTERV_ENT sont dans
    ensembles_entiers_theoremes.py (qui peut importer l'ordre des cardinaux)."""
    return E.intervalle_entiers(_t(a), _t(b))


def corps_intervalle_entiers(a, b, x):
    """Corps caractérisant x ∈ [a, b] : (x cardinal et a ≤ x et x ≤ b)  (E.III.5.3)."""
    return et(et(est_cardinal(_t(x)), inf_egal_card(_t(a), _t(x))),
              inf_egal_card(_t(x), _t(b)))


# ── §III.5.4 — Suite finie ; longueur ────────────────────────────────────────
def est_suite_finie(t, i):
    """« (t_i)_{i∈I} est une suite finie » := I est un ensemble fini d'entiers (E.III.5.4).

    Une suite finie est une famille (t = fonction Python ou graphe) dont l'ensemble
    d'indices I est un ensemble fini dont les éléments sont des entiers.  Codé :
    I fini et (∀i)(i∈I ⇒ i entier)."""
    vI, vi = _t(i), var("i")
    return et(est_fini_ensemble(vI),
              pourtout("i", impl(appartient(vi, vI), est_entier(vi))))


def longueur_suite(i):
    """longueur de la suite (t_i)_{i∈I} := Card(I) = nombre d'éléments de I (E.III.5.4)."""
    return cardinal(_t(i))


# ── §III.5.5 — Fonction caractéristique φ_A ───────────────────────────────────
def fonction_caracteristique(A, E_, x="x"):
    """φ_A : E → {0,1},  φ_A(x) = 1 si x∈A, 0 si x∈E−A   (E.III.5.5).

    Codée par le terme app("carac", A, E) (graphe de l'application caractéristique
    de la partie A de E).  La valeur φ_A(x) = E.valeur(φ_A, x).
    Prop. 7 (φ_{E−A}=1−φ_A, φ_{A∩B}=φ_A·φ_B, …) repose sur l'arithmétique sur {0,1}
    (1−·, ·, +) → REPORTÉE."""
    return app("carac", _t(A), _t(E_))


# ── §III.5.6 — Division euclidienne : pair / impair, divisibilité ─────────────
def est_pair(a):
    """« a est pair » := a est multiple de 2   (E.III.5.6).

    a pair :⇔ (∃n)(a = 2·n) ; codé via le successeur (2 = UN+1) et le terme
    abréviateur de produit.  ⚠ Le produit binaire 2·n n'étant pas disponible comme
    terme, on encode « a pair » par divise(2, a) (b divise a, Déf. 1)."""
    return divise(DEUX, a)


def est_impair(a):
    """« a est impair » := a n'est pas pair (a non multiple de 2)   (E.III.5.6).

    Les entiers impairs sont de la forme 2n+1 (d'après le th. 1)."""
    return non(est_pair(a))


def divise(b, a, q="q"):
    """« b divise a » (b | a) := (∃q)(a = b·q)   (E.III.5.6, Déf. 1).

    a est multiple de b ⇔ b divise a ⇔ le reste de la division de a par b est 0.
    ⚠ RÉSERVE : le produit cardinal BINAIRE b·q n'est pas un terme disponible ; on
    code b | a par le terme-prédicat opaque app-relation « divise(b,a) » sans axiome
    (aucun théorème direct sans l'arithmétique cardinale)."""
    vb, va, vq = _t(b), _t(a), var(q)
    return existe(q, egal(va, app("prod_ent", vb, vq)))


def reste_division(a, b):
    """reste de la division de a par b (E.III.5.6, th. 1) : terme r tel que
       a = b·q + r et r < b.  Codé app("reste", a, b) (= a − b·⌊a/b⌋).

    ⚠ REPORTÉ : l'existence/unicité (th. 1) exige le bon ordre de ℕ + prop. 3."""
    return app("reste", _t(a), _t(b))


def quotient_division(a, b):
    """quotient de la division de a par b (E.III.5.6, th. 1 / Déf. 1) : terme q tel
       que a = b·q + r, r < b.  Codé app("quot_ent", a, b)."""
    return app("quot_ent", _t(a), _t(b))


# ── §III.5.8 — Factorielle ; coefficient binomial ────────────────────────────
def factorielle(n):
    """n! := ∏_{1≤i≤n} (i+1)   (E.III.5.8, Déf. 2).

    0! = 1, 1! = 1, (n+1)! = n!·(n+1).  Codé par le terme app("factorielle", n).
    ⚠ La caractérisation récursive (récurrence sur n) n'est PAS dérivable (C61
    absent) → REPORTÉ ; on ne fournit que le terme."""
    return app("factorielle", _t(n))


def coefficient_binomial(n, p):
    """C(n, p) := n! / (p!·(n−p)!)  si p ≤ n,  0 si p > n   (E.III.5.8).

    Nombre des parties à p éléments d'un ensemble à n éléments.  Codé par le terme
    app("binom", n, p).  ⚠ REPORTÉ : toutes ses propriétés (Prop. 12-15, symétrie
    C(n,p)=C(n,n−p), récurrence de Pascal) reposent sur l'arithmétique + récurrence."""
    return app("binom", _t(n), _t(p))


__all__ = ["successeur", "ZERO", "UN", "DEUX", "TROIS", "QUATRE",
           "est_fini", "est_entier", "est_fini_ensemble", "nombre_d_elements",
           "famille_finie", "de_caractere_fini",
           # §III.5 — Calcul sur les entiers
           "inf_strict_entiers", "difference_entiers",
           "intervalle_entiers", "corps_intervalle_entiers",
           "est_suite_finie", "longueur_suite",
           "fonction_caracteristique",
           "est_pair", "est_impair", "divise", "reste_division", "quotient_division",
           "factorielle", "coefficient_binomial"]
