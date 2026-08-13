"""Chap. I §1.3 — Constructions formatives (E I.18--19).

Le livre :
  * à chaque signe spécifique est associé un entier, son POIDS (pratiquement
    toujours 2) ;
  * un assemblage est de PREMIÈRE ESPÈCE s'il commence par un τ ou s'il se
    réduit à une lettre, de DEUXIÈME ESPÈCE dans les autres cas ;
  * une CONSTRUCTION FORMATIVE d'une théorie 𝒯 est une suite d'assemblages
    telle que, pour chaque assemblage A de la suite, l'une des conditions :
      a) A est une lettre ;
      b) il y a, dans la suite, un assemblage de deuxième espèce B précédant A,
         tel que A soit ¬B ;
      c) il y a deux assemblages de deuxième espèce B et C précédant A
         (distincts ou non) tels que A soit ∨BC ;
      d) il y a un assemblage de deuxième espèce B précédant A et une lettre x
         tels que A soit τ_x(B) ;
      e) il y a un signe spécifique s de poids n de 𝒯, et n assemblages de
         première espèce A₁, ..., Aₙ précédant A, tels que A soit sA₁A₂...Aₙ ;
  * les TERMES (resp. RELATIONS) de 𝒯 sont les assemblages de première espèce
    (resp. de deuxième espèce) figurant dans les constructions formatives de 𝒯.

Une théorie est ici donnée par sa SIGNATURE : dict {signe spécifique: poids},
p. ex. {"∈": 2} pour la théorie des ensembles, {"=": 2, "∈": 2} en égalitaire.
"""
from __future__ import annotations

from itertools import product

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, est_lettre, concat, negation, disjonction, tau_x, lettres)


# @livre Ch.I §1.3 Def.- | E I.17 L.30-32 | PDF p.17  (titre §3 + poids d'un signe spécifique)
# @livre Ch.I §1.3 Def.- | E I.17 L.33-34 | PDF p.17  (première / deuxième espèce)
def est_premiere_espece(a: Assemblage) -> bool:
    """Première espèce : commence par un τ, ou se réduit à une lettre (E I.17 L.33-34)."""
    if a.n == 0:
        raise ValueError("assemblage vide : d'aucune espèce")
    return a.signes[0] == "TAU" or (a.n == 1 and est_lettre(a.signes[0]))


def est_deuxieme_espece(a: Assemblage) -> bool:
    """Deuxième espèce : tous les autres cas (E I.17 L.33-34)."""
    return not est_premiere_espece(a)


# @livre Ch.I §1.3 Def.- | E I.17 L.35 ; E I.18 L.1-11 | PDF p.18  (construction formative, conditions a-e)
def _justifie(a: Assemblage, anterieurs: list[Assemblage],
              signature: dict[str, int]) -> bool:
    """L'une des conditions a)--e) de E I.18 L.3-11 pour A, sachant les assemblages antérieurs."""
    # a) A est une lettre.
    if a.n == 1 and est_lettre(a.signes[0]):
        return True
    secondes = [b for b in anterieurs if est_deuxieme_espece(b)]
    # b) A = ¬B, B de deuxième espèce antérieur.
    if any(a == negation(b) for b in secondes):
        return True
    # c) A = ∨BC, B et C de deuxième espèce antérieurs (distincts ou non).
    if any(a == disjonction(b, c) for b in secondes for c in secondes):
        return True
    # d) A = τ_x(B), B de deuxième espèce antérieur, x une lettre.
    #    Si x ne figure pas dans B, τ_x(B) = TAU ++ B (aucun lien ajouté).
    for b in secondes:
        if any(a == tau_x(b, x) for x in lettres(b)):
            return True
        if a == concat(Assemblage(("TAU",)), b):
            return True
    # e) A = sA₁...Aₙ, s spécifique de poids n, les Aᵢ de première espèce antérieurs.
    premieres = [b for b in anterieurs if est_premiere_espece(b)]
    for s, n in signature.items():
        if a.signes and a.signes[0] == s:
            for morceaux in product(premieres, repeat=n):
                cand = Assemblage((s,))
                for m in morceaux:
                    cand = concat(cand, m)
                if a == cand:
                    return True
    return False


def premiere_faute_formative(suite, signature) -> int | None:
    """Indice 0-based du premier assemblage injustifiable ; None si construction formative."""
    for i, a in enumerate(suite):
        if not _justifie(a, list(suite[:i]), signature):
            return i
    return None


def est_construction_formative(suite, signature) -> bool:
    """True ssi la suite est une construction formative de la théorie (E I.18)."""
    return len(suite) > 0 and premiere_faute_formative(suite, signature) is None


# @livre Ch.I §1.3 Def.- | E I.18 L.12-13 | PDF p.18  (termes et relations de 𝒯)
def termes_de(suite, signature) -> tuple[Assemblage, ...]:
    """Les TERMES figurant dans la construction formative (première espèce, E I.18 L.12-13)."""
    if not est_construction_formative(suite, signature):
        raise ValueError("la suite n'est pas une construction formative")
    return tuple(a for a in suite if est_premiere_espece(a))


def relations_de(suite, signature) -> tuple[Assemblage, ...]:
    """Les RELATIONS figurant dans la construction formative (deuxième espèce, E I.18 L.12-13)."""
    if not est_construction_formative(suite, signature):
        raise ValueError("la suite n'est pas une construction formative")
    return tuple(a for a in suite if est_deuxieme_espece(a))


# @livre Ch.I §1.3 Ex.- | E I.18 L.14-25 | PDF p.18
#   (l'Exemple du livre — A, A', A'', ∈AA', ∈AA'', ¬∈AA', ∨¬∈AA'∈AA'', τ_A(…) —
#    est rejoué signe pour signe dans
#    tests/…/test_i_1_3_constructions_formatives.py::test_exemple_du_livre)
# @livre Ch.I §1.3 Rem.- | E I.18 L.26-38 | PDF p.18
#   (remarque intuitive : termes = objets, relations = assertions — prose, rien à formaliser)
# @livre Ch.I §1.3 Ex.- | E I.18 L.39-43 | PDF p.18
#   (exemples de symboles : ∅, N, π = √2+√3… — prose, rien à formaliser)

# ── MÉTATHÉORÈME des signes initiaux (E I.19) — pas un théorème du noyau ──────
# @livre Ch.I §1.3 Meta.- | E I.19 L.1-8 | PDF p.19  (énoncé L.1-2, démonstration L.2-8)
#
# ÉNONCÉ. « Le signe initial d'une relation est ∨, ¬ ou un signe spécifique ;
# le signe initial d'un terme est τ, à moins que le terme ne se réduise à une
# lettre. »
#
# STATUT. C'est le premier résultat DÉMONTRÉ du livre — mais démontré dans la
# théorie générale (métamathématique), PAS dans une théorie formelle : ce n'est
# donc pas un théorème d'une théorie (aucun objet `Theoreme`, rien à faire
# passer par le solveur). On le consigne avec sa démonstration, c'est tout.
#
# DÉMONSTRATION (livre). L'assertion relative aux termes résulte de ce qu'un
# terme est un assemblage de première espèce. Si A est une relation, A figure
# dans une construction formative, n'est pas une lettre et ne commence pas par
# un τ ; donc trois cas sont possibles : 1) A est précédé d'un assemblage B tel
# que A soit ¬B ; 2) A est précédé par deux assemblages B et C tels que A soit
# ∨BC ; 3) A est précédé par des assemblages A₁, A₂, ..., Aₙ tels que A soit
# sA₁A₂...Aₙ, s étant un signe spécifique.  ∎
#
# On NE le démontre PAS dans le solveur (ce n'est pas un théorème d'une théorie,
# donc aucun objet `Theoreme`, aucune fonction exécutable qui prétende l'établir) :
# sa démonstration est consignée ci-dessus, en commentaire, et c'est tout.


__all__ = [
    "est_premiere_espece", "est_deuxieme_espece",
    "premiere_faute_formative", "est_construction_formative",
    "termes_de", "relations_de",
]
