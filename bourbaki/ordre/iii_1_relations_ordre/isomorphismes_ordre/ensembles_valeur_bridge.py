"""§III — PONT entre conventions de liant-valeur :  f(x)[τ_j]  =  f(x)[τ_y].

`compatible_ordre` (ensembles_ordre_vocab) construit f(x) avec le liant-valeur DÉFAUT
« y » (E.valeur défaut b="y").  `est_strictement_croissante` / `_val` (ordre_monotone,
lemme_4) utilisent « j » (lettre simple fraîche, jamais quantifiée, choisie pour rester
alpha_tau-compatible).  Pour CHAÎNER les deux (ex. iso_donne_strict_croissant →
coincidence_sur_chevauchement → Lemme 1), il faut prouver que les deux écritures de f(x)
sont ÉGALES.

C'est un α-renommage du liant τ : `valeur(f,x,b="j") = τ_j((x,j)∈f)` et
`valeur(f,x,b="y") = τ_y((x,y)∈f)` sont α-équivalents.  `alpha_tau` (CS1) le certifie —
ET « j », « y » sont des LETTRES SIMPLES, donc `tau()` les accepte (contrairement à « yv »
multi-caractères que `tau()` refusait, ce qui bloquait ce pont).

INVARIANT : theorie_ensembles() = 22 (alpha_tau est une primitive justifiée, pas un axiome).
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, appartient, egal
from bourbaki.logique.noyau_abrege import alpha_tau
from bourbaki.ensembles import ensembles_abrege as E

J = "j"   # liant-valeur de est_strictement_croissante / _val
Y = "y"   # liant-valeur défaut de E.valeur (compatible_ordre)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def valeur_j_egal_y(f, x):
    """⊢ valeur(f, x, b="j") = valeur(f, x, b="y").   (α-renommage τ_j → τ_y, CS1.)

    Pré-condition implicite : « y » n'est pas libre dans x (sinon capture — refusée par
    le garde-fou d'alpha_tau).  Vrai pour x une variable de quantification usuelle ≠ y."""
    vx, vf = _t(x), _t(f)
    body = appartient(E.couple(vx, var(J)), vf)          # corps de τ_j : (x, j) ∈ f
    return alpha_tau(body, J, Y)                          # ⊢ τ_j(body) = τ_y(body[j:=y])


def valeur_y_egal_j(f, x):
    """⊢ valeur(f, x, b="y") = valeur(f, x, b="j").   (sens inverse, par symétrie.)"""
    vx, vf = _t(x), _t(f)
    body = appartient(E.couple(vx, var(Y)), vf)          # corps de τ_y : (x, y) ∈ f
    return alpha_tau(body, Y, J)                          # ⊢ τ_y(body) = τ_j(body[y:=j])


def valeur_j_egal_y_cible(f, x):
    """ÉNONCÉ-cible (test miroir) : valeur(f,x,b="j") = valeur(f,x,b="y")."""
    return egal(E.valeur(_t(f), _t(x), b=J), E.valeur(_t(f), _t(x), b=Y))


__all__ = ["valeur_j_egal_y", "valeur_y_egal_j", "valeur_j_egal_y_cible", "J", "Y"]
