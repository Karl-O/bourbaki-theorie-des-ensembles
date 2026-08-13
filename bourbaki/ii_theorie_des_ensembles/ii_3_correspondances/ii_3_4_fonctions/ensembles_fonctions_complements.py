"""§II.3 — Micro-notions complémentaires (INTRODUCTION fidèle, module NEUF).

Trous « micro » du chapitre II repérés par le cross-check PDF (E.II.3) : quelques
notions de Bourbaki étaient utilisables IMPLICITEMENT (via image directe, bijection,
graphe réciproque/composé déjà présents) mais n'étaient pas EXPOSÉES sous leur nom.
Ce module les INTRODUIT comme TERMES / PRÉDICATS réutilisables, sans dupliquer
l'existant et sans toucher à aucun fichier déjà écrit.

theorie_ensembles() RESTE à 22 axiomes — ce module n'écrit AUCUN axiome (il se
contente de composer des termes/prédicats déjà caractérisés : image, reciproque,
composee, est_bijective, est_un_couple…). Aucun théorème n'est postulé.

Notions introduites
-------------------
  • coupe(G, x)                  E.II.3.2 — coupe de G suivant x : G{x} = G⟨{x}⟩
                                 = {y | (x,y)∈G}.
  • est_permutation(F, A)        E.II.3.4 — permutation de A : bijection de A sur A.
  • est_fonction_deux_arguments(F, A, B)
                                 E.II.3.x — fonction de deux arguments : application
                                 dont l'ensemble de définition est ⊂ A×B
                                 (le domaine est un ensemble de couples).
  • application_partielle_seconde(F, y0)   /   _premiere(F, x0)
                                 E.II.3.x — applications partielles x↦f(x,y₀) (resp.
                                 y↦f(x₀,y)) déduites d'une fonction de deux arguments
                                 en fixant un argument.
  • correspondance_reciproque(Gamma)        E.II.3.2 — correspondance réciproque
                                 (G,A,B)⁻¹ := (G⁻¹, B, A).
  • correspondance_composee(Gamma2, Gamma)  E.II.3.3 — composée de correspondances
                                 (H,B,C)∘(G,A,B) := (H∘G, A, C).

Lemmes DIRECTS (sans nouvel axiome)
-----------------------------------
  • coupe_caracterisation : ⊢ (y ∈ G{x}) ⇔ ((x,y) ∈ G)  (réutilise coupe_membre).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, et, impl, appartient, existe, pourtout, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import (
    correspondance, est_une_correspondance, est_application,
)


def _t(v):
    """Coercion nom→terme : accepte un Terme ou un nom de variable."""
    return v if isinstance(v, Terme) else var(v)


# ── E.II.3.2 — Coupe de G suivant x ──────────────────────────────────────────
# @livre Ch.II §3.2 Def.4 | E II.11 L.2-3 | PDF p.62
# @livre Ch.R §3 Def.- | E.R.14 item 7 (coupe K(x) de K suivant x) | PDF p.317
def coupe(g, x):
    """G{x} := G⟨{x}⟩ = {y | (x,y)∈G}   (coupe de G suivant x, E.II.3.2).

    Bourbaki : pour un graphe G et un objet x, la « coupe de G suivant x » est
    l'ensemble des y tels que (x,y)∈G ; c'est exactement l'image directe par G du
    singleton {x}.  On la code donc comme image(G, {x}) — terme déjà caractérisé
    par AXIOME_IMAGE + la coupe sur singleton `coupe_membre` (théorie inchangée).
    Notation Bourbaki : G{x} (parfois G(x) pour les graphes fonctionnels)."""
    return E.image(_t(g), E.singleton(_t(x)))


# @livre Ch.II §3.2 Def.4 | E II.11 L.4-5 | PDF p.62
def coupe_caracterisation(g="G", a="a"):
    """⊢ (y ∈ G{a}) ⇔ ((a,y) ∈ G).   (caractérisation de la coupe suivant a, E.II.3.2.)

    Lemme DIRECT : G{a} = G⟨{a}⟩, et l'appartenance à l'image directe d'un singleton
    est donnée par `coupe_membre` (déjà prouvé, sans nouvel axiome).  L'élément est
    nommé « a » (et non « x ») pour ne pas entrer en collision avec la variable liée
    interne « x » de l'existentielle de `coupe_membre` (capture)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances import coupe_membre
    return coupe_membre(g, a)


# ── E.II.3.4 — Permutation : bijection de A sur lui-même ──────────────────────
# @livre Ch.II §3.4 Def.- | E II.17 L.8-9 | PDF p.68
def est_permutation(f, a):
    """« F (graphe) est une permutation de A » := F bijection de A sur A   (E.II.3.4).

    Une permutation d'un ensemble A est une application bijective de A sur A
    lui-même.  On la code par son graphe F, via est_bijective(F, A, A) (déjà défini :
    injective sur A et image F⟨A⟩ = A).  C'est le cas particulier B = A de
    « bijection de A sur B »."""
    return E.est_bijective(_t(f), _t(a), _t(a))


# @livre Ch.II §3.4 Def.- | E II.17 L.8-9 | PDF p.68
def est_permutation_triple(f, a):
    """« (F, A, A) est une permutation de A » : variante exposant aussi
    l'appartenance applicative (F application de A dans A) + bijectivité   (E.II.3.4).

    Forme « application » totale : F est une application de A dans A (domaine = A,
    graphe ⊂ A×A) ET F est bijective de A sur A.  Plus complète que est_permutation
    (qui ne porte que sur la bijectivité du graphe)."""
    vF, vA = _t(f), _t(a)
    return et(est_application(vF, vA, vA), E.est_bijective(vF, vA, vA))


# ── E.II.3 — Fonction de deux arguments ──────────────────────────────────────
# @livre Ch.II §3.9 Def.- | E II.21 L.4-5 | PDF p.72
# @livre Ch.R §3 Def.- | E.R.16 item 13 (fonction de plusieurs arguments — cas de deux arguments formalisé) | PDF p.319
def est_fonction_deux_arguments(f, a, b):
    """« F est une fonction de deux arguments (dans A×B) » :=
        F est une application dont le domaine est contenu dans A×B   (E.II.3).

    Bourbaki : une fonction de deux arguments est une fonction dont l'ensemble de
    définition est un ensemble de couples (ici ⊂ A×B) ; on écrit alors f(x,y) pour
    f((x,y)).  On expose : F graphe fonctionnel ET dom F ⊂ A×B.  (Le but n'est pas
    contraint ici ; pour une APPLICATION de A×B, voir est_application(F, A×B, C).)"""
    vF, vA, vB = _t(f), _t(a), _t(b)
    return et(E.est_fonctionnel(vF), inclus(E.dom(vF), E.produit(vA, vB)))


# @livre Ch.II §3.9 Def.- | E II.21 L.6-7 | PDF p.72
def valeur_deux_arguments(f, x, y):
    """f(x, y) := f((x, y)) = valeur(F, (x,y))   (valeur d'une fonction de deux args).

    Application de la fonction-de-deux-arguments F au couple (x,y) ; simple synonyme
    exposé de la valeur de F en le couple (x,y)."""
    return E.valeur(_t(f), E.couple(_t(x), _t(y)))


# ── E.II.3 — Applications partielles ──────────────────────────────────────────
# @livre Ch.II §3.9 Def.- | E II.21 L.10-13 | PDF p.72
# @livre Ch.R §3 Def.- | E.R.16 item 13 (application partielle engendrée par f) | PDF p.319
def application_partielle_seconde(f, a, c, y0, x="x"):
    """x ↦ f(x, y₀) (x∈A, y₀ fixé) := fonction-terme (graphe {(x, f(x,y₀)) | x∈A}, A, C)
    (application partielle relative à y₀, E.II.3).

    Bourbaki : étant donnée une fonction de deux arguments f et un élément y₀ fixé,
    l'application partielle (relative à y₀) est x ↦ f(x, y₀) ; c'est une application
    de A (l'ensemble des premiers arguments) dans C (le but de f).  On la code par la
    fonction-terme (mécanisme C54 `fonction_terme`) du terme T = f((x, y₀)) à x libre,
    de source A et but C.  Son graphe est {(x, f(x,y₀)) | x∈A}."""
    vx = var(x)
    T = E.valeur(_t(f), E.couple(vx, _t(y0)))
    return E.fonction_terme(_t(a), T, _t(c), x)


# @livre Ch.II §3.9 Def.- | E II.21 L.10-13 | PDF p.72
def application_partielle_seconde_terme(f, y0, x="x"):
    """Le TERME-valeur partiel x ↦ f(x, y₀) (sans contrainte de source/but) :
    renvoie simplement le terme f((x, y₀)) à x libre   (application partielle, forme terme).

    Utile quand on veut le terme f(x,y₀) lui-même (à brancher dans graphe_terme /
    fonction_terme avec la source et le but voulus)."""
    return E.valeur(_t(f), E.couple(var(x), _t(y0)))


# @livre Ch.II §3.9 Def.- | E II.21 L.13-16 | PDF p.72
def application_partielle_premiere_terme(f, x0, y="y"):
    """Le TERME-valeur partiel y ↦ f(x₀, y) (à x₀ fixé) : terme f((x₀, y)) à y libre
    (application partielle relative à x₀, E.II.3)."""
    return E.valeur(_t(f), E.couple(_t(x0), var(y)))


# ── E.R.16 item 13 — Fonctions de TROIS arguments (E×F×G) ─────────────────────
#   DÉFINITIONS pures (terminologie du livre, aucun théorème à dériver) : produit
#   de trois ensembles associé à GAUCHE, (E×F)×G ; un triple est ((x,y),z) et l'on
#   écrit f(x,y,z) pour f(((x,y),z)).  Analogues des fonctions de deux arguments.
# @livre Ch.R §3 Def.- | E.R.16 item 13 (fonction de trois arguments f(x,y,z) sur E×F×G) | PDF p.319
def est_fonction_trois_arguments(f, a, b, c):
    """« F est une fonction de trois arguments (dans E×F×G) » := F graphe fonctionnel
    dont le domaine est contenu dans (E×F)×G   (E.R.16 item 13).

    On écrit alors f(x,y,z) pour f(((x,y),z)).  Extension directe de
    est_fonction_deux_arguments (produit associé à gauche : E×F×G = (E×F)×G)."""
    vF = _t(f)
    return et(E.est_fonctionnel(vF), inclus(E.dom(vF), E.produit(E.produit(_t(a), _t(b)), _t(c))))


# @livre Ch.R §3 Def.- | E.R.16 item 13 (valeur f(x,y,z) = f(((x,y),z))) | PDF p.319
def valeur_trois_arguments(f, x, y, z):
    """f(x, y, z) := f(((x,y),z)) = valeur(F, ((x,y),z))   (E.R.16 item 13)."""
    return E.valeur(_t(f), E.couple(E.couple(_t(x), _t(y)), _t(z)))


# @livre Ch.R §3 Def.- | E.R.16 item 13 (application partielle f(a,·,·) : (y,z)↦f(a,y,z)) | PDF p.319
def application_partielle_trois_premiere_terme(f, a, y="y", z="z"):
    """Terme (y,z) ↦ f(a,y,z) = f(((a,y),z)) à y,z libres — application partielle
    « engendrée par f » relative au 1er argument a  (E.R.16 item 13, notée f(a,·,·))."""
    return E.valeur(_t(f), E.couple(E.couple(_t(a), var(y)), var(z)))


# @livre Ch.R §3 Def.- | E.R.16 item 13 (application partielle f(a,b,·) : z↦f(a,b,z)) | PDF p.319
def application_partielle_trois_deux_terme(f, a, b, z="z"):
    """Terme z ↦ f(a,b,z) = f(((a,b),z)) à z libre — application partielle relative
    aux 1er et 2e arguments a,b  (E.R.16 item 13, notée f(a,b,·))."""
    return E.valeur(_t(f), E.couple(E.couple(_t(a), _t(b)), var(z)))


# ── E.II.3.2 / II.3.3 — Réciproque et composée de CORRESPONDANCES (triples) ───
# @livre Ch.II §3.2 Def.- | E II.11 L.19-24 | PDF p.62
def correspondance_reciproque(gamma_graphe, a, b):
    """Γ⁻¹ := (G⁻¹, B, A)   pour Γ = (G, A, B)   (correspondance réciproque, E.II.3.2).

    La correspondance réciproque d'une correspondance Γ = (G, A, B) entre A et B est
    la correspondance (G⁻¹, B, A) entre B et A, de graphe le graphe réciproque G⁻¹
    (déjà défini).  On échange ensemble de départ et d'arrivée et on prend G⁻¹.
    Arguments : le GRAPHE G de Γ, puis A et B (comme `correspondance(G, A, B)`)."""
    return correspondance(E.reciproque(_t(gamma_graphe)), _t(b), _t(a))


# @livre Ch.II §3.3 Def.7 | E II.13 L.10-13 | PDF p.64
def correspondance_composee(h, gamma2_dep, c, g, a, gamma1_dep):
    """(H, B, C) ∘ (G, A, B) := (H∘G, A, C)   (composée de correspondances, E.II.3.3).

    Soient Γ = (G, A, B) entre A et B et Γ' = (H, B, C) entre B et C (l'arrivée B de
    Γ = le départ de Γ').  La correspondance composée Γ'∘Γ entre A et C est
    (H∘G, A, C), de graphe le graphe composé H∘G (déjà défini).  On garde la source A
    de Γ et le but C de Γ'.  (gamma2_dep / gamma1_dep = B en commun, ici inutilisés
    dans le triple résultat mais explicités pour la lisibilité de l'appariement.)"""
    return correspondance(E.composee(_t(h), _t(g)), _t(a), _t(c))


# @livre Ch.II §3.3 Def.7 | E II.13 L.10-13 | PDF p.64
def correspondance_composee_simple(h, g, a, c):
    """(H∘G, A, C) — composée de correspondances, signature allégée   (E.II.3.3).

    Variante : on ne passe que le graphe H de Γ', le graphe G de Γ, la source A de Γ
    et le but C de Γ'.  Résultat : la correspondance (H∘G, A, C)."""
    return correspondance(E.composee(_t(h), _t(g)), _t(a), _t(c))


# @livre Ch.R §2 Def.- | E.R.11 item 14 | PDF p.314
#   (« représentation paramétrique de F au moyen de E » = application de E SUR F ;
#    E = ensemble des paramètres, ses éléments = paramètres. Terminologie : SYNONYME
#    de la surjection — aucun théorème à dériver, simple définition/renommage.)
def representation_parametrique(f, e, f_set):
    """« f est une représentation paramétrique de F au moyen de E » := f application
    de E SUR F (surjective)   (E.R.11 item 14).

    E est appelé l'« ensemble des paramètres » et ses éléments les « paramètres ».
    C'est un pur SYNONYME terminologique de la surjectivité : la définition coïncide
    avec `est_surjective(f, E, F)` (= image(f,E) = F).  Aucune propriété nouvelle,
    donc aucun `Theoreme` — définition seule (cf. E.R.11 item 14, texte du livre)."""
    return E.est_surjective(_t(f), _t(e), _t(f_set))


__all__ = [
    "coupe", "coupe_caracterisation", "representation_parametrique",
    "est_permutation", "est_permutation_triple",
    "est_fonction_deux_arguments", "valeur_deux_arguments",
    "application_partielle_seconde", "application_partielle_seconde_terme",
    "application_partielle_premiere_terme",
    "est_fonction_trois_arguments", "valeur_trois_arguments",
    "application_partielle_trois_premiere_terme", "application_partielle_trois_deux_terme",
    "correspondance_reciproque",
    "correspondance_composee", "correspondance_composee_simple",
]
