"""§IV.1.3 — Typification des lettres et relation transportable.   REPRÉSENTATIONNEL.

⚠️ MÉTAMATHÉMATIQUE.  Une typification (IV.1.3) est une conjonction d'appartenances
« s_j ∈ S_j(x₁,…,xₙ,A₁,…,A_m) » à des ÉCHELONS ; la transportabilité d'une relation
R{x,s} est une propriété MÉTA portant sur TOUTES les bijections f₁,…,fₙ (et l'égalité
des structures transportées (3) s_j' = ⟨f₁,…,fₙ,Id,…⟩^{S_j}(s_j)).

Représentation fidèle au niveau objet :
  • `typification([s₁,…,s_p], [S₁,…,S_p], [x₁,…,xₙ], [A₁,…,A_m])` RENVOIE la Formule
    T{x,s} : « s₁∈S₁(…) et … et s_p∈S_p(…) » (conjonction d'appartenances à des
    échelons interprétés par `echelon` — IV.1.3, relation T) ;
  • `structures_transportees(...)` RENVOIE la liste des Termes s_j' de la relation (3)
    de IV.1.3 : s_j' = ⟨f₁,…,fₙ,Id₁,…,Id_m⟩^{S_j}(s_j) (Id_h = diagonale de A_h) ;
  • `relation_transportable_instance(R, ...)` RENVOIE la Formule (1)⇒(2) de IV.1.3
    POUR UN SYSTÈME DONNÉ de bijections f₁,…,fₙ et d'images y₁,…,yₙ (instance objet
    de la définition de transportabilité ; le « pour toute bijection » universel
    reste MÉTA et est documenté comme tel — on fournit l'instance qui en est le cœur).

Aucun axiome ajouté à theorie_ensembles() (reste à 22)."""
from __future__ import annotations

from typing import Sequence

from bourbaki.logique.formule import var, et, impl, equiv, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import Schema, echelon, extension_canonique


def _conj(formules):
    """Conjonction itérée « f₁ et f₂ et … et f_p » (renvoie f₁ si p=1)."""
    formules = list(formules)
    if not formules:
        raise ValueError("conjonction vide")
    out = formules[0]
    for f in formules[1:]:
        out = et(out, f)
    return out


def typification(s_lettres: Sequence, schemas: Sequence[Schema],
                 x_bases: Sequence, A_aux: Sequence = ()):
    """Typification T{x₁,…,xₙ, s₁,…,s_p} (IV.1.3).

    « La relation T{x₁,…,xₙ,s₁,…,s_p} : "s_1∈S_1(x₁,…,xₙ,A₁,…,A_m) et … et
    s_p∈S_p(x₁,…,xₙ,A₁,…,A_m)" est une typification des lettres s_1,…,s_p. »

    `s_lettres`=[s₁,…,s_p] (Termes), `schemas`=[S₁,…,S_p] (Schema sur n+m termes),
    `x_bases`=[x₁,…,xₙ], `A_aux`=[A₁,…,A_m].  Chaque échelon S_j est interprété par
    `echelon(S_j, [x₁,…,xₙ,A₁,…,A_m])`.  Renvoie la Formule T (conjonction)."""
    s_lettres = list(s_lettres)
    schemas = list(schemas)
    if len(s_lettres) != len(schemas):
        raise ValueError("nombre de lettres ≠ nombre de schémas")
    socle = list(x_bases) + list(A_aux)             # x₁,…,xₙ,A₁,…,A_m
    clauses = [appartient(sj, echelon(Sj, socle)) for sj, Sj in zip(s_lettres, schemas)]
    return _conj(clauses)


def structures_transportees(s_lettres: Sequence, schemas: Sequence[Schema],
                            f_bij: Sequence, A_aux: Sequence = ()):
    """Liste des structures transportées s_j' (relation (3) de IV.1.3).

    « s_j' = ⟨f_1,…,f_n, Id_1,…,Id_m⟩^{S_j}(s_j) (1≤j≤p) », Id_h = application
    identique de A_h sur lui-même.  Représentée par `valeur(⟨…⟩^{S_j}, s_j)`
    (l'extension canonique appliquée à s_j).  Id_h = diagonale(A_h)."""
    f_bij = list(f_bij)
    ids = [E.diagonale(A) for A in A_aux]           # Id_h = Δ_{A_h}
    applis = f_bij + ids                            # f₁,…,fₙ,Id₁,…,Id_m
    out = []
    for sj, Sj in zip(s_lettres, schemas):
        ext = extension_canonique(Sj, applis)       # ⟨f₁,…,fₙ,Id,…⟩^{S_j}
        out.append(E.valeur(ext, sj))               # …(s_j)
    return out


def relation_transportable_instance(R, s_lettres, schemas, x_bases, y_bases,
                                    f_bij, A_aux=()):
    """Instance objet de la transportabilité de R pour la typification T (IV.1.3).

    Renvoie la Formule (1)⇒(2) de IV.1.3, POUR le système donné (f₁,…,fₙ) et
    (y₁,…,yₙ) :
      (1) « T{x,s} et (f₁ bijection de x₁ sur y₁) et … et (fₙ bijection de xₙ sur yₙ) »
      ⇒ (2) « R{x₁,…,xₙ,s₁,…,s_p} ⇔ R{y₁,…,yₙ,s₁',…,s_p'} »,
    où s_j' = ⟨f₁,…,fₙ,Id,…⟩^{S_j}(s_j) (cf. structures_transportees).

    R est un PRÉDICAT abstrait : R(bases, structures) -> Formule (R{x₁,…,xₙ,s₁,…,s_p}).
    Dire que R est transportable, c'est dire que CETTE implication est un théorème
    pour TOUS f,y (quantification MÉTA, non exprimable d'un coup — documentée) ; on
    fournit ici l'instance, cœur de la définition (énoncé VERBATIM de IV.1.3)."""
    x_bases, y_bases, f_bij = list(x_bases), list(y_bases), list(f_bij)
    T = typification(s_lettres, schemas, x_bases, A_aux)            # T{x,s}
    bij_clauses = [est_bijection_de(f, x, y)
                   for f, x, y in zip(f_bij, x_bases, y_bases)]     # f_i bij de x_i sur y_i
    hyp = _conj([T] + bij_clauses)                                 # (1)
    s_prime = structures_transportees(s_lettres, schemas, f_bij, A_aux)
    concl = equiv(R(x_bases, list(s_lettres)), R(y_bases, s_prime)) # (2)
    return impl(hyp, concl)


__all__ = [
    "typification", "structures_transportees", "relation_transportable_instance",
]
