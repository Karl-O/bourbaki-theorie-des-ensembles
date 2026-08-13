"""§III.5.8 — Analyse combinatoire (E III.42-44) : les ÉNONCÉS, forme multiplicative.

Prop. 10 (fin), Corollaires, Prop. 11-15 : le décompte des injections,
permutations, recouvrements, parties (coefficient binomial), couples et
applications à somme bornée.

DEUX PARTIS PRIS (honnêtes, documentés) :

1. FORME MULTIPLICATIVE.  Le livre écrit des QUOTIENTS (n!/(n−m)!,
   n!/(p!(n−p)!), n(n+1)/2…).  Or la division n'est PAS un terme du dépôt
   (le quotient euclidien n'est pas formalisé — cf. §5.6, CAMPAGNE_TROUS).
   Chaque énoncé est donc transposé sous sa forme multiplicative ÉQUIVALENTE
   (celle que Bourbaki lui-même utilise dans les démonstrations, via le
   principe des bergers) :  X = a/b  devient  X·b = a.

2. STATUT : ÉNONCÉS FORMALISÉS, DÉMONSTRATIONS NON DÉRIVÉES (PARTIEL).
   Ce module construit les RELATIONS-énoncés au niveau formule (couche
   outil_formule), sur des termes de décompte OPAQUES fournis par l'appelant
   (même discipline que la caractérisation de la factorielle, fichier voisin
   ensembles_factorielle_iii5 : rien n'est postulé, aucun `Theoreme` n'est
   forgé).  Les démonstrations du livre (principe des bergers, récurrences)
   restent à dériver — listées dans outils_ia/corpus/CAMPAGNE_TROUS.md.

Conventions d'arguments : n, p, … sont des Termes (ou noms de variables) ;
`fact` est un callable Terme→Terme (le terme-fonction factorielle, mêmes
conventions que ensembles_factorielle_iii5) ; les décomptes (nb d'injections,
coefficient binomial C, …) sont des Termes ou callables opaques.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur, DEUX)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire as PCB)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SCB)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Prop. 10 (énoncé E III.41, fin de démo E III.42 L.1-4 : NON dérivée) ─────
def enonce_prop10_injections(nb_inj, fact, n, n_moins_m) -> Terme:
    """Prop. 10, forme multiplicative :  I(n,m) · (n−m)! = n!.

    Livre : « le nombre des applications injectives d'un ensemble à m éléments
    dans un ensemble à n éléments (m≤n) est n!/(n−m)! ».  L'appelant fournit
    le terme opaque nb_inj = I(n,m) et le terme n_moins_m = n−m."""
    return egal(PCB(_t(nb_inj), fact(_t(n_moins_m))), fact(_t(n)))


# @livre Ch.III §5.8 Cor.- | E III.42 L.5-7 | PDF p.145  (permutations d'un ensemble à n éléments : n! ; démo L.6-7 non dérivée)
def enonce_permutations(nb_perm, fact, n) -> Terme:
    """Corollaire (E III.42 L.5) :  le nombre de permutations = n!  (pas de
    quotient ici : l'énoncé du livre est déjà multiplicatif)."""
    return egal(_t(nb_perm), fact(_t(n)))


# @livre Ch.III §5.8 Prop.11 | E III.42 L.8-11 | PDF p.145  (recouvrements disjoints à cardinaux imposés ; démo L.12-21 [bergers] non dérivée)
def enonce_prop11_multinomial(nb_rec, produit_des_pi_fact, fact, n) -> Terme:
    """Prop. 11, forme multiplicative :  R · ∏ᵢ pᵢ! = n!.

    Livre : « le nombre des recouvrements (Xᵢ) de E par des ensembles
    mutuellement disjoints tels que Card(Xᵢ)=pᵢ (Σpᵢ=n) est n!/∏pᵢ! ».
    L'appelant fournit nb_rec = R et le terme produit_des_pi_fact = ∏ᵢ pᵢ!
    (le produit-famille n'étant pas requis ici, il reste un terme opaque)."""
    return egal(PCB(_t(nb_rec), _t(produit_des_pi_fact)), fact(_t(n)))


# @livre Ch.III §5.8 Cor.1 | E III.42 L.22-23 | PDF p.145  (parties à p éléments ; démo L.24 = Prop.11 avec h=2, non dérivée)
# @livre Ch.III §5.8 Def.- | E III.42 L.25-28 | PDF p.145  (coefficient binomial (n p) ; symétrie (n p) = (n n−p))
def enonce_cor1_binomial(C_np, fact, n, p, n_moins_p) -> Terme:
    """Cor. 1 / définition du coefficient binomial, forme multiplicative :

        C(n,p) · p! · (n−p)! = n!

    (au lieu de C(n,p) = n!/(p!(n−p)!)).  C_np est le terme opaque (n p)."""
    return egal(PCB(_t(C_np), PCB(fact(_t(p)), fact(_t(n_moins_p)))),
                fact(_t(n)))


def enonce_symetrie_binomiale(C, n, p, n_moins_p) -> Terme:
    """(n p) = (n n−p)  (E III.42 L.27-28).  C est un callable (n,p) ↦ Terme."""
    return egal(C(_t(n), _t(p)), C(_t(n), _t(n_moins_p)))


def enonce_convention_binomiale_nulle(C, n, p) -> Terme:
    """CONVENTION (E III.43 L.4-6) :  p > n  ⇒  (n p) = 0.

    « On pose (n p) = 0 pour tout couple d'entiers naturels tels que p > n.
    Avec cette convention, le nombre des parties à p éléments d'un ensemble à
    n éléments est (n p) pour tout entier naturel p. »  Garde d'ordre au sens
    cardinal strict (n < p) ; 0 = ZERO du dépôt."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_strict_card)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        ZERO)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    vn, vp = _t(n), _t(p)
    return impl(inf_strict_card(vn, vp), egal(C(vn, vp), ZERO))


# @livre Ch.III §5.8 Rem.- | E III.43 L.1-6 | PDF p.146
#   (petits textes : X↦E−X bijection parties-p ↔ parties-(n−p) [autre preuve de
#    la symétrie] ; CONVENTION (n p)=0 si p>n — documentées, la garde d'ordre
#    p>n n'est pas câblée ici)

# @livre Ch.III §5.8 Cor.2 | E III.43 L.7-9 | PDF p.146  (applications strictement croissantes E→F : (n p) ; démo L.10-13 non dérivée)
def enonce_cor2_croissantes(nb_croissantes, C, n, p) -> Terme:
    """Cor. 2 :  le nombre des applications strictement croissantes d'un
    ensemble totalement ordonné à p éléments dans un à n éléments est (n p)."""
    return egal(_t(nb_croissantes), C(_t(n), _t(p)))


# @livre Ch.III §5.8 Prop.12 | E III.43 L.14 | PDF p.146  (Σ_p (n p) = 2^n ; démo L.15-16 [Card 𝔓(E), III p.29 Prop.12] non dérivée)
def enonce_prop12_somme_binomiaux(somme_des_C, deux_puissance_n) -> Terme:
    """Prop. 12 :  Σ_p (n p) = 2ⁿ.  Les deux membres restent des termes
    opaques (somme-famille et exponentiation cardinale fournies par l'appelant ;
    2^n = exposant(2, n) du dépôt convient)."""
    return egal(_t(somme_des_C), _t(deux_puissance_n))


# @livre Ch.III §5.8 Prop.13 | E III.43 L.17-18 | PDF p.146  (triangle de Pascal ; démo ensembliste L.19-25 et « calcul facile » L.26-27 non dérivées)
def enonce_prop13_pascal(C, n, p) -> Terme:
    """Prop. 13 (Pascal) :  (n+1 p+1) = (n p+1) + (n p).

    Aucun quotient : l'énoncé du livre passe tel quel, la somme étant la
    somme cardinale binaire du dépôt."""
    vn, vp = _t(n), _t(p)
    return egal(C(successeur(vn), successeur(vp)),
                SCB(C(vn, successeur(vp)), C(vn, vp)))


# @livre Ch.III §5.8 Rem.- | E III.43 L.26-27 | PDF p.146
#   (petit texte : Prop.13 par « un calcul facile » depuis (n p)=n!/(p!(n−p)!) — prose)

# @livre Ch.III §5.8 Prop.14 | E III.43 L.28-30 | PDF p.146  (couples i≤j / i<j ; démo E III.44 L.1-5 non dérivée)
def enonce_prop14_couples_larges(a_n, n) -> Terme:
    """Prop. 14, couples 1≤i≤j≤n, forme multiplicative :  2·aₙ = n·(n+1)."""
    vn = _t(n)
    return egal(PCB(DEUX, _t(a_n)), PCB(vn, successeur(vn)))


def enonce_prop14_couples_stricts(b_n, n, n_moins_1) -> Terme:
    """Prop. 14, couples 1≤i<j≤n, forme multiplicative :  2·bₙ = n·(n−1)."""
    return egal(PCB(DEUX, _t(b_n)), PCB(_t(n), _t(n_moins_1)))


def enonce_prop14_lien(a_n, b_n, n) -> Terme:
    """Charnière de la démo (E III.44 L.5) :  aₙ = n + bₙ."""
    return egal(_t(a_n), SCB(_t(n), _t(b_n)))


# @livre Ch.III §5.8 Cor.- | E III.44 L.6 | PDF p.147  (Σᵢ₌₁ⁿ i = n(n+1)/2 ; démo L.7-10 [partition (A_k)] non dérivée)
def enonce_somme_premiers_entiers(somme_i, n) -> Terme:
    """Corollaire, forme multiplicative :  2·(Σᵢ₌₁ⁿ i) = n·(n+1).

    somme_i = le terme-somme Σᵢ₌₁ⁿ i (somme-famille, opaque ici)."""
    vn = _t(n)
    return egal(PCB(DEUX, _t(somme_i)), PCB(vn, successeur(vn)))


# @livre Ch.III §5.8 Prop.15 | E III.44 L.11-13 | PDF p.147  (applications à somme ≤n [resp. =n] : (n+h n) [resp. (n+h−1 h−1)] ; démo L.14-27 non dérivée)
def enonce_prop15_somme_bornee(A_hn, C, n_plus_h, n) -> Terme:
    """Prop. 15 (cas Σu(x) ≤ n) :  A(h,n) = (n+h n).

    A_hn = le décompte opaque des applications u : E → (0,n) avec Σu(x) ≤ n ;
    n_plus_h = le terme n+h."""
    return egal(_t(A_hn), C(_t(n_plus_h), _t(n)))


def enonce_prop15_recurrence(A, h, n, h_moins_1, n_moins_1) -> Terme:
    """Charnière de la démo (E III.44 L.25) :  A(h,n) = A(h,n−1) + A(h−1,n).

    C'est la récurrence qui, jointe à A(0,0)=1 et à Pascal (Prop.13), donne
    la Prop. 15 « par récurrence sur n+h »."""
    vh, vn = _t(h), _t(n)
    return egal(A(vh, vn), SCB(A(vh, _t(n_moins_1)), A(_t(h_moins_1), vn)))


# @livre Ch.III §5.8 Rem.- | E III.44 L.28-31 | PDF p.147
#   (petit texte étoilé : nombre des monômes de degré total ≤n [resp. n] à h
#    [resp. h+1] indéterminées = (n+h h) — prose, renvoie à A IV §1)

__all__ = [
    "enonce_prop10_injections", "enonce_permutations",
    "enonce_prop11_multinomial", "enonce_cor1_binomial",
    "enonce_symetrie_binomiale", "enonce_cor2_croissantes",
    "enonce_prop12_somme_binomiaux", "enonce_prop13_pascal",
    "enonce_prop14_couples_larges", "enonce_prop14_couples_stricts",
    "enonce_prop14_lien", "enonce_somme_premiers_entiers",
    "enonce_prop15_somme_bornee", "enonce_prop15_recurrence",
]
