"""§III.3.5 — EXPONENTIATION ET PRODUIT  a^(b·c) = (a^b)^c  (CURRYING).

Énoncé VERBATIM (Bourbaki, E.III.3.5) :
    • Proposition 10 (§III.3.5) : « Soient a et b des cardinaux, et I un ensemble
      tel que Card(I) = b ; si a_ι = a pour tout ι ∈ I, on a a^b = ∏_{ι∈I} a_ι. »
    • Corollaire 3 (de la Proposition 10) : « Soient a, b, c des cardinaux ; on a
      a^(bc) = (a^b)^c. »

C'est le Corollaire 3 (le CURRYING) qui est l'objet de ce module.  En termes
d'ensembles : si a = Card(A), b = Card(B), c = Card(C), alors
        a^(b·c) = Card(𝓕(B×C ; A))      (applications du produit B×C dans A)
        (a^b)^c = Card(𝓕(C ; 𝓕(B;A)))   (applications de C dans 𝓕(B;A))
et le but est
        ⊢ Card(𝓕(B×C ; A)) = Card(𝓕(C ; 𝓕(B;A))).

CRUX (NON RÉSOLU — voir REPORT en bas) : la bijection de CURRYING
        Φ : 𝓕(B×C ; A) → 𝓕(C ; 𝓕(B;A)),   f ↦ ( c ↦ ( b ↦ f(b,c) ) ).
C'est la PLUS DURE des trois propositions exponentielles : DOUBLE niveau de
fonctions (les VALEURS de l'image sont elles-mêmes des triples ((G,B),A)∈𝓕(B;A),
et l'image globale est un triple ((H,C),𝓕(B;A))).  Construire Φ via graphe_terme
exige un terme-valeur lui-même bâti sur un graphe_terme paramétré par c, puis la
fonctionnalité / le domaine / l'injectivité / la SURJECTIVITÉ à deux étages.

PALIERS LIVRÉS (tous CLOS, rien postulé) :
  (1) exposant_produit_gauche / exposant_produit_droit : les deux cardinaux
        a^(b·c) et (a^b)^c comme TERMES sur leurs supports 𝓕 fidèles ;
  (2) membre_curry_source  : caractérisation membership de 𝓕(B×C;A) (gauche) ;
  (3) membre_curry_but     : caractérisation membership de 𝓕(C;𝓕(B;A)) (droit,
        ensemble de fonctions à valeurs-fonctions) ;
  (4) eq_source_son_cardinal / eq_but_son_cardinal : Eq(support, Card support)
        — chaque support est équipotent à son propre cardinal (socle Prop. 1) ;
  (5) curry_but_egale_via_eq : SI l'on dispose de Eq(𝓕(B×C;A), 𝓕(C;𝓕(B;A))),
        ALORS Card(gauche)=Card(droit) (réduction du Corollaire 3 à l'équipotence
        des deux supports, via la Proposition 1 sens direct _prop1_direct_t).
        => le Corollaire 3 est RAMENÉ à l'unique lemme manquant `eq_curry`.

REPORT (honnête) : `eq_curry` = Eq(𝓕(B×C;A), 𝓕(C;𝓕(B;A))) — la bijection de
currying — n'est PAS construite (effort borné, salvage attendu).  Voir le module
ensembles_exposant_un comme MODÈLE de la machinerie graphe_terme/axiome_exposant/
axiome_applications à reproduire, ici DOUBLÉE.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl, appartient,
                     existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 1 : les deux cardinaux du Corollaire 3 (currying), supports fidèles
# ═══════════════════════════════════════════════════════════════════════════════
def support_source(a="A", b="B", c="C"):
    """Support de a^(b·c) : 𝓕(B×C ; A)  (applications du produit B×C dans A)."""
    return E.applications(E.produit(_t(b), _t(c)), _t(a))


def support_but(a="A", b="B", c="C"):
    """Support de (a^b)^c : 𝓕(C ; 𝓕(B;A))  (applications de C dans 𝓕(B;A))."""
    return E.applications(_t(c), E.applications(_t(b), _t(a)))


def exposant_produit_gauche(a="A", b="B", c="C"):
    """a^(b·c) := Card(𝓕(B×C ; A)).   (membre gauche du Corollaire 3.)

    Par définition de l'exponentiation cardinale (exposant_cardinal_binaire) avec
    pour exposant le produit cardinal b·c (support ensembliste B×C) et pour base a
    (support A) : a^(b·c) = Card(𝓕(b·c ; a)) avec b·c codé par B×C."""
    return cardinal(support_source(a, b, c))


def exposant_produit_droit(a="A", b="B", c="C"):
    """(a^b)^c := Card(𝓕(C ; 𝓕(B;A))).   (membre droit du Corollaire 3.)

    a^b = Card(𝓕(B;A)) (support 𝓕(B;A)) ; (a^b)^c = Card(𝓕(c ; a^b)) avec
    exposant c (support C) et base a^b (support 𝓕(B;A))."""
    return cardinal(support_but(a, b, c))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 2 : caractérisation membership de 𝓕(B×C ; A)  (la source du currying)
# ═══════════════════════════════════════════════════════════════════════════════
def membre_curry_source(a="A", b="B", c="C", t="t", g="G"):
    """⊢ (t ∈ 𝓕(B×C;A)) ⇔ (∃G)(t = ((G, B×C), A) et G ∈ A^(B×C)).

    Caractérisation FIDÈLE de l'appartenance à la source 𝓕(B×C;A) du currying :
    une application de B×C dans A est le triple ((G,B×C),A) d'un graphe fonctionnel
    G ∈ A^(B×C).  Instance directe de l'AXIOME_APPLICATIONS (E={B×C}, F=A)."""
    BC = E.produit(_t(b), _t(c))
    vA = _t(a)
    ax = N.axiome(E.theorie_applications(BC, vA, t, g),
                  E.axiome_applications(BC, vA, t, g))      # (∀t)(t∈𝓕(B×C;A) ⇔ (∃G)…)
    return instancie(ax, var(t))                           # t∈𝓕(B×C;A) ⇔ (∃G)(t=((G,B×C),A) et G∈A^(B×C))


def membre_curry_source_graphe(a="A", b="B", c="C", g="G"):
    """⊢ (G ∈ A^(B×C)) ⇔ (G ⊂ (B×C)×A et G fonctionnel et dom G = B×C).

    Caractérisation FIDÈLE des GRAPHES de la source : G est un graphe fonctionnel
    de domaine B×C inclus dans (B×C)×A.  Instance de l'AXIOME_EXPOSANT (E={B×C}, F=A)."""
    BC = E.produit(_t(b), _t(c))
    vA = _t(a)
    ax = N.axiome(E.theorie_exposant(BC, vA, g), E.axiome_exposant(BC, vA, g))
    return instancie(ax, var(g))                           # G∈A^(B×C) ⇔ (G⊂(B×C)×A et G fonct et dom G=B×C)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 3 : caractérisation membership de 𝓕(C ; 𝓕(B;A))  (le but du currying)
#   — ENSEMBLE DE FONCTIONS À VALEURS-FONCTIONS (le double étage)
# ═══════════════════════════════════════════════════════════════════════════════
def membre_curry_but(a="A", b="B", c="C", t="t", h="H"):
    """⊢ (t ∈ 𝓕(C ; 𝓕(B;A))) ⇔ (∃H)(t = ((H, C), 𝓕(B;A)) et H ∈ 𝓕(B;A)^C).

    Caractérisation FIDÈLE de l'appartenance au but du currying : une application
    de C dans 𝓕(B;A) est le triple ((H,C),𝓕(B;A)) d'un graphe fonctionnel
    H ∈ 𝓕(B;A)^C.  Le BUT de l'application est lui-même un ESPACE DE FONCTIONS
    𝓕(B;A) — c'est le double étage qui rend le Corollaire 3 difficile.
    Instance de l'AXIOME_APPLICATIONS (E={C}, F={𝓕(B;A)})."""
    vC = _t(c)
    FBA = E.applications(_t(b), _t(a))                     # 𝓕(B;A)
    ax = N.axiome(E.theorie_applications(vC, FBA, t, h),
                  E.axiome_applications(vC, FBA, t, h))    # (∀t)(t∈𝓕(C;𝓕(B;A)) ⇔ (∃H)…)
    return instancie(ax, var(t))                          # t∈𝓕(C;𝓕(B;A)) ⇔ (∃H)(t=((H,C),𝓕(B;A)) et H∈𝓕(B;A)^C)


def membre_curry_but_graphe(a="A", b="B", c="C", h="H"):
    """⊢ (H ∈ 𝓕(B;A)^C) ⇔ (H ⊂ C×𝓕(B;A) et H fonctionnel et dom H = C).

    Caractérisation des GRAPHES du but : H est un graphe fonctionnel de domaine C
    à valeurs DANS L'ESPACE DE FONCTIONS 𝓕(B;A) (chaque H(γ) est une application
    B→A).  Instance de l'AXIOME_EXPOSANT (E={C}, F={𝓕(B;A)})."""
    vC = _t(c)
    FBA = E.applications(_t(b), _t(a))                     # 𝓕(B;A)
    ax = N.axiome(E.theorie_exposant(vC, FBA, h), E.axiome_exposant(vC, FBA, h))
    return instancie(ax, var(h))                          # H∈𝓕(B;A)^C ⇔ (H⊂C×𝓕(B;A) et H fonct et dom H=C)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 4 : chaque support est équipotent à son propre cardinal (socle Prop. 1)
# ═══════════════════════════════════════════════════════════════════════════════
def _eq_son_cardinal_terme(vX):
    """⊢ Eq(T, Card T) pour un TERME T  (généralise equipotent_son_cardinal)."""
    refl_all = N.generalisation("X", equipotent_son_cardinal("X"))   # (∀X) Eq(X, Card X)
    return instancie(refl_all, vX)


def eq_source_son_cardinal(a="A", b="B", c="C"):
    """⊢ Eq(𝓕(B×C;A), Card(𝓕(B×C;A))).   (= Eq(support gauche, a^(b·c)).)

    Le support de a^(b·c) est équipotent à son cardinal — brique du transfert
    d'équipotence vers l'égalité cardinale (Proposition 1)."""
    return _eq_son_cardinal_terme(support_source(a, b, c))


def eq_but_son_cardinal(a="A", b="B", c="C"):
    """⊢ Eq(𝓕(C;𝓕(B;A)), Card(𝓕(C;𝓕(B;A)))).   (= Eq(support droit, (a^b)^c).)"""
    return _eq_son_cardinal_terme(support_but(a, b, c))


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 5 : RÉDUCTION du Corollaire 3 à l'équipotence des deux supports
#   (la bijection de currying reste le seul maillon manquant — REPORTÉ)
# ═══════════════════════════════════════════════════════════════════════════════
def curry_but_egale_via_eq(a="A", b="B", c="C"):
    """⊢ Eq(𝓕(B×C;A), 𝓕(C;𝓕(B;A))) ⇒ (Card(𝓕(B×C;A)) = Card(𝓕(C;𝓕(B;A)))).

    RÉDUCTION du Corollaire 3 (a^(b·c) = (a^b)^c) à l'unique lemme manquant
    `eq_curry` = l'équipotence des deux supports (la bijection de currying) : par
    la Proposition 1 (sens direct, version TERME), Eq(U,V) ⇒ Card U = Card V.

    DONC : dès que la bijection de currying Φ : 𝓕(B×C;A) → 𝓕(C;𝓕(B;A)) sera
    construite (REPORTÉE), le Corollaire 3 s'obtiendra par un seul modus ponens
    sur cette implication.  C'est le socle propre du Corollaire 3."""
    src = support_source(a, b, c)                          # 𝓕(B×C;A)
    but = support_but(a, b, c)                             # 𝓕(C;𝓕(B;A))
    return _prop1_direct_t(src, but)                       # Eq(src,but) ⇒ Card src = Card but


__all__ = [
    "support_source", "support_but",
    "exposant_produit_gauche", "exposant_produit_droit",
    "membre_curry_source", "membre_curry_source_graphe",
    "membre_curry_but", "membre_curry_but_graphe",
    "eq_source_son_cardinal", "eq_but_son_cardinal",
    "curry_but_egale_via_eq",
]
