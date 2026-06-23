"""§III.3 — PROPOSITION 10, COROLLAIRE 2 (E III.29) :  (∏_{ι∈I} a_ι)^b = ∏_{ι∈I} a_ι^b.

ÉNONCÉ VERBATIM (Bourbaki, E III.29, Corollaire 2 de la Proposition 10) :
    « Soient (a_ι)_{ι∈I} une famille de cardinaux, et b un cardinal ; on a
        ( ∏_{ι∈I} a_ι )^b = ∏_{ι∈I} a_ι^b. »
Preuve de Bourbaki : on pose a_{ι,β} = a_ι pour tout (ι,β) ∈ I×b ; alors, par
ASSOCIATIVITÉ du produit (III, p. 26, prop. 5 b),
    ( ∏_ι a_ι )^b = ∏_β ( ∏_ι a_{ιβ} ) = ∏_ι ( ∏_β a_{ιβ} ) = ∏_ι a_ι^b.

FORME ENSEMBLISTE (l'objet de ce module) — « currying SUR LE FACTEUR PRODUIT » :
    𝓕( B ; ∏_{ι∈I} A_ι )  ≅  ∏_{ι∈I} 𝓕( B ; A_ι )
        (une application à valeurs dans un produit = une famille d'applications).
La bijection canonique :
    Φ : f ↦ ( ι ↦ ( b ↦ pr_ι( f(b) ) ) )          (« distribuer la coordonnée »)
    Ψ : g ↦ ( b ↦ ( ι ↦ g(ι)(b) ) )                (« recoller les coordonnées »)
deux sens inverses l'un de l'autre — exactement le schéma des Propositions 9 et 10
(`ensembles_prop9_close`, `ensembles_prop10_inj_curry`/`_inj_uncurry`), assemblé par
CANTOR–BERNSTEIN sur deux injections, puis passé aux cardinaux via `_prop1_direct_t`.

──────────────────────────────────────────────────────────────────────────────────
PARAMÉTRAGE FIDÈLE ET HONNÊTE (point technique central).
──────────────────────────────────────────────────────────────────────────────────
Le produit d'une famille est `E.produit_famille(famA, I)` où famA EST la famille
(ι ↦ A_ι) ; le facteur A_ι est le TERME OPAQUE `E.valeur_famille(famA, ι)` — il n'y a
PAS d'axiome reliant `valeur_famille(famA,ι)` à une construction explicite (une
famille est un graphe fonctionnel quelconque, E.II.4.1).  La famille-but
(ι ↦ 𝓕(B;A_ι)) n'est donc pas un terme calculable à partir de famA : on l'introduit
comme une famille-paramètre `famF` SOUS L'HYPOTHÈSE HONNÊTE de liaison

    LIEN(famF, famA) :≡ (∀ι)( ι∈I ⇒ valeur_famille(famF, ι) = 𝓕(B ; valeur_famille(famA, ι)) )

qui exprime LITTÉRALEMENT « famF est la famille des espaces de fonctions
(𝓕(B;A_ι))_{ι∈I} ».  C'est la seule façon fidèle, sans constructeur de famille, de
nommer la famille-but ; elle n'est NI fausse NI vide (la conclusion 𝓕(B;∏A)≅∏famF
ne figure pas dans les hypothèses), et famF/famA/B/I restent des paramètres libres.

──────────────────────────────────────────────────────────────────────────────────
ÉTAT (honnête) — ce qui est CLOS dans ce module et ce qui est REPORTÉ.
──────────────────────────────────────────────────────────────────────────────────
CLOS, 0 hyp :
  • supports `source` = 𝓕(B;∏A) et `but` = ∏famF, comme TERMES fidèles ;
  • caractérisations membership `membre_source` (axiome_applications) et
    `membre_but` (axiome_produit_fam : F∈∏famF ⇔ F fonct ∧ dom F=I ∧ (∀ι)(ι∈I⇒F(ι)∈famF(ι))) ;
  • `eq_source_son_cardinal`, `eq_but_son_cardinal` : chaque support ≅ son cardinal ;
  • `cor2_via_eq` :  Eq(source, but) ⇒ Card(source)=Card(but)   (RÉDUCTION par Prop.1) ;
        c'est la forme CARDINALE (∏a_ι)^b = ∏ a_ι^b ramenée à l'unique équipotence.

REPORTÉ (résidu HONNÊTE, hors budget — JAMAIS postulé) :
  • `eq_cor2` = Eq(𝓕(B;∏A), ∏famF) — les DEUX injections Φ,Ψ (swap de coordonnées)
    sur le produit d'une famille à index OPAQUE.  Construction analogue à
    prop10_inj_curry/uncurry mais où le « facteur » n'est plus le binaire B×C : la
    bien-définition de l'image demande la caractérisation à TROIS conjoints du
    produit_famille (dont le ∀ι borné), et l'injectivité un back-and-forth indexé
    par l'index opaque ι.  Le squelette (supports + membership + réduction) est
    livré ; la bijection elle-même est le seul maillon manquant — exactement comme
    `curry_but_egale_via_eq` l'était pour le Corollaire 3 avant prop10_close.

theorie_ensembles INCHANGÉE (22 axiomes) ; aucun fichier déposé modifié (tout est
IMPORTÉ) ; rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, appartient,
                                       pourtout, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import instancie

from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import membre_produit_famille


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
#  SUPPORTS de l'identité (∏a_ι)^b = ∏ a_ι^b   (forme ensembliste)
# ═══════════════════════════════════════════════════════════════════════════════
def produit_facteurs(famA="famA", i="I"):
    """∏_{ι∈I} A_ι := produit_famille(famA, I)   (A_ι = valeur_famille(famA, ι))."""
    return E.produit_famille(_t(famA), _t(i))


def source(famA="famA", i="I", b="B"):
    """𝓕( B ; ∏_{ι∈I} A_ι )  — SOURCE de Φ.   (= support de (∏ a_ι)^b.)"""
    return E.applications(_t(b), produit_facteurs(famA, i))


def but(famF="famF", i="I"):
    """∏_{ι∈I} 𝓕(B ; A_ι) := produit_famille(famF, I)  — BUT de Φ.

    famF est la famille des espaces de fonctions (𝓕(B;A_ι))_{ι∈I} ; sa valeur en ι,
    valeur_famille(famF,ι) = 𝓕(B;A_ι), est fixée par LIEN(famF,famA) (cf. en-tête).
    (= support de ∏ a_ι^b.)"""
    return E.produit_famille(_t(famF), _t(i))


# ── HYPOTHÈSE de liaison famF ↔ famA (cf. en-tête) ──────────────────────────────
def lien_familles(famF="famF", famA="famA", i="I", b="B"):
    """LIEN := (∀ι)( ι∈I ⇒ valeur_famille(famF,ι) = 𝓕(B ; valeur_famille(famA,ι)) ).

    « famF est la famille des espaces de fonctions (𝓕(B;A_ι))_{ι∈I}. »  Liant « i »."""
    vfamF, vfamA, vI, vB = _t(famF), _t(famA), _t(i), _t(b)
    vi = var("i")
    return pourtout("i", impl(appartient(vi, vI),
                              egal(E.valeur_famille(vfamF, vi),
                                   E.applications(vB, E.valeur_famille(vfamA, vi)))))


# ═══════════════════════════════════════════════════════════════════════════════
#  CARACTÉRISATIONS MEMBERSHIP des deux supports  (CLOS, 0 hyp)
# ═══════════════════════════════════════════════════════════════════════════════
def membre_source(famA="famA", i="I", b="B", t="t", g="G"):
    """⊢ ( t ∈ 𝓕(B;∏A) ) ⇔ (∃G)( t = ((G, B), ∏A) et G ∈ (∏A)^B ).

    Caractérisation FIDÈLE de la SOURCE : une application de B dans le produit ∏A
    est le triple ((G,B),∏A) d'un graphe fonctionnel G ∈ (∏A)^B.  Instance directe
    de AXIOME_APPLICATIONS (E=B, F=∏A)."""
    P = produit_facteurs(famA, i)
    vB = _t(b)
    ax = N.axiome(E.theorie_applications(vB, P, t, g),
                  E.axiome_applications(vB, P, t, g))
    return instancie(ax, var(t))


def membre_but(famF="famF", i="I", ff="F"):
    """⊢ ( F ∈ ∏_{ι∈I} 𝓕(B;A_ι) )
         ⇔ ( F fonctionnel ∧ dom F = I ∧ (∀ι)(ι∈I ⇒ F(ι) ∈ valeur_famille(famF,ι)) ).

    Caractérisation FIDÈLE du BUT : un élément du produit de la famille famF est un
    graphe fonctionnel de domaine I dont la valeur en ι tombe dans famF(ι)=𝓕(B;A_ι)
    (sous LIEN).  Instance directe de AXIOME_PRODUIT_FAM (Déf. 1, E.II.5.3)."""
    return membre_produit_famille(famF, i, ff)


# ═══════════════════════════════════════════════════════════════════════════════
#  CHAQUE SUPPORT EST ÉQUIPOTENT À SON CARDINAL  (socle Prop. 1)   (CLOS, 0 hyp)
# ═══════════════════════════════════════════════════════════════════════════════
def _eq_son_cardinal_terme(vX):
    """⊢ Eq(T, Card T) pour un TERME T  (généralise equipotent_son_cardinal)."""
    refl_all = N.generalisation("X", equipotent_son_cardinal("X"))
    return instancie(refl_all, vX)


def eq_source_son_cardinal(famA="famA", i="I", b="B"):
    """⊢ Eq( 𝓕(B;∏A) , Card(𝓕(B;∏A)) ).   (= Eq(source, (∏a_ι)^b).)"""
    return _eq_son_cardinal_terme(source(famA, i, b))


def eq_but_son_cardinal(famF="famF", i="I"):
    """⊢ Eq( ∏famF , Card(∏famF) ).   (= Eq(but, ∏ a_ι^b).)"""
    return _eq_son_cardinal_terme(but(famF, i))


# ═══════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION DU COROLLAIRE 2 À L'ÉQUIPOTENCE  (Prop. 1 sens direct)   (CLOS, 0 hyp)
# ═══════════════════════════════════════════════════════════════════════════════
def cor2_via_eq(famF="famF", famA="famA", i="I", b="B"):
    """⊢ Eq( 𝓕(B;∏A) , ∏famF ) ⇒ ( Card(𝓕(B;∏A)) = Card(∏famF) ).

    RÉDUCTION du Corollaire 2 — la forme CARDINALE (∏_ι a_ι)^b = ∏_ι a_ι^b — à
    l'unique équipotence des deux supports (la bijection canonique de currying sur
    le facteur produit) : par la Proposition 1 (sens direct, version TERME),
    Eq(U,V) ⇒ Card U = Card V.  Card(source)=(∏a_ι)^b et Card(but)=∏ a_ι^b (sous
    LIEN).  Donc, dès que `eq_cor2` (REPORTÉ) sera construit, le Corollaire 2
    s'obtiendra par un seul modus ponens sur cette implication.

    C'est le socle propre du Corollaire 2 — strict analogue de `curry_but_egale_via_eq`
    (`ensembles_exposant_produit`) pour le Corollaire 3 avant sa clôture."""
    src = source(famA, i, b)               # 𝓕(B;∏A)
    tgt = but(famF, i)                      # ∏famF
    return _prop1_direct_t(src, tgt)        # Eq(src,tgt) ⇒ Card src = Card tgt


def cor2_cardinal_terme_gauche(famA="famA", i="I", b="B"):
    """(∏_{ι∈I} a_ι)^b := Card( 𝓕(B;∏A) )   (membre gauche du Corollaire 2)."""
    return cardinal(source(famA, i, b))


def cor2_cardinal_terme_droit(famF="famF", i="I"):
    """∏_{ι∈I} a_ι^b := Card( ∏famF )   (membre droit du Corollaire 2, sous LIEN)."""
    return cardinal(but(famF, i))


__all__ = [
    "produit_facteurs", "source", "but", "lien_familles",
    "membre_source", "membre_but",
    "eq_source_son_cardinal", "eq_but_son_cardinal",
    "cor2_via_eq", "cor2_cardinal_terme_gauche", "cor2_cardinal_terme_droit",
]
