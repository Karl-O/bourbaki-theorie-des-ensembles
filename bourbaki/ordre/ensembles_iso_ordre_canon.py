"""§III.1-2 — FORMES CANONIQUES (anti-capture) des notions d'ISOMORPHISME D'ORDRE.

────────────────────────────────────────────────────────────────────────────────
POURQUOI CE MODULE EXISTE — le BUG de collision de liants.

`compatible_ordre(f,E,R,R', x, y)` (ensembles_ordre_vocab.py:150) construit la valeur
f(y) par `E.valeur(f, var(y))`, et `E.valeur(·,·)` utilise par DÉFAUT le liant interne
`b="y"` :   valeur(f, z) := τ_y( (z, y) ∈ f ).

Quand le 2ᵉ quantificateur d'ordre est lui-même nommé « y » (le DÉFAUT), on obtient

    f(y) = valeur(f, var("y")) = τ_y( (y, y) ∈ f )          ← CAPTURE

c.-à-d. « le y tel que (y,y)∈f » (un point fixe), PAS la valeur de f en y.  La condition
d'isomorphisme dégénère.  ⇒ `est_isomorphisme_ordre(...)`, `sont_isomorphes_ordre(...)`,
`ordinal_inferieur_ou_egal(...)`, `trichotomie_ordinaux(...)` en FORME DÉFAUT (x="x",
y="y") sont DÉFECTUEUX.  (Vérifié : repr(valeur(f,var("y"))) contient (y,y).)

La forme SAINE n'exige AUCUN changement des définitions : il suffit que le 2ᵉ binder
d'ordre soit ≠ "y" (le τ de valeur).  Alors f(yo)=τ_y((yo,y)∈f) est CORRECT.

────────────────────────────────────────────────────────────────────────────────
CONVENTION CANONIQUE (à adopter partout dans l'arc trichotomie/ordinaux) :

    binders d'ordre = ISO_X="xo", ISO_Y="yo".

`xo`,`yo` évitent À LA FOIS « y » (τ interne de valeur) ET « w » (slot interne de
composition_valeur, qui casse la composée).  Toute notion iso-ordre réutilisée dans
l'assemblage de la trichotomie DOIT passer par ces wrappers (ou ces binders), pour que
les formules COÏNCIDENT structurellement et CHAÎNENT.

Ce module n'ajoute AUCUN axiome (theorie=22) et ne modifie AUCUNE définition : il fournit
les INSTANCES canoniques (anti-capture) des notions existantes, + la CIBLE SAINE
`trichotomie_ordinaux_canon` que l'assemblage doit viser.
"""
from __future__ import annotations

from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.ordre import ensembles_ordinaux as O

# Binders d'ordre canoniques : ≠ "y" (τ de valeur), ≠ "w" (slot de composition_valeur).
ISO_X = "xo"
ISO_Y = "yo"


def compatible_ordre_canon(f, e, R, Rp):
    """compatible_ordre en binders SAINS (xo,yo) — f(yo)=τ_y((yo,y)∈f), pas de capture."""
    return V.compatible_ordre(f, e, R, Rp, ISO_X, ISO_Y)


def est_isomorphisme_ordre_canon(f, e, ep, R, Rp):
    """est_isomorphisme_ordre en binders SAINS (xo,yo)."""
    return V.est_isomorphisme_ordre(f, e, ep, R, Rp, ISO_X, ISO_Y)


def sont_isomorphes_ordre_canon(e, ep, R, Rp, f="f"):
    """sont_isomorphes_ordre en binders SAINS (xo,yo)."""
    return V.sont_isomorphes_ordre(e, ep, R, Rp, f, ISO_X, ISO_Y)


def ordinal_inferieur_ou_egal_canon(e, R, ep, Rp, S="S", f="f"):
    """ordinal_inferieur_ou_egal en binders SAINS (xo,yo)."""
    return O.ordinal_inferieur_ou_egal(e, R, ep, Rp, S, f, ISO_X, ISO_Y)


def trichotomie_ordinaux_canon(e, R, ep, Rp, S="S", f="f"):
    """🎯 CIBLE SAINE de la trichotomie (Th3 §III.2) — binders SAINS (xo,yo).

        ordinal_inferieur_ou_egal_canon(E,R,E',R')  OU  ordinal_inferieur_ou_egal_canon(E',R',E,R)

    C'est CETTE formule (et non la forme défaut défectueuse) que l'assemblage doit clore."""
    return O.trichotomie_ordinaux(e, R, ep, Rp, S, f, ISO_X, ISO_Y)


__all__ = [
    "ISO_X", "ISO_Y",
    "compatible_ordre_canon", "est_isomorphisme_ordre_canon",
    "sont_isomorphes_ordre_canon", "ordinal_inferieur_ou_egal_canon",
    "trichotomie_ordinaux_canon",
]
