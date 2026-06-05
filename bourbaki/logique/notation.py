"""Couche 5 — notation lisible ⇄ assemblage (pour dialoguer avec une IA).

Un LLM ne connaît pas les assemblages τ de Bourbaki, mais manie très bien la
logique infixe. Ce module traduit :
  * `afficher`     : assemblage → texte lisible (¬ ∨ ⇒ et ⇔ = ∀ ∃ τ) ;
  * `lire_formule` : texte → assemblage (via les constructeurs vérifiés).

Grammaire d'entrée (entièrement parenthésée, robuste et facile pour un LLM) :

    F := lettre                       (un terme : a, b, x, …)
       | ( F = F )                    égalité
       | ( non F )
       | ( F ou F )                   disjonction
       | ( F => F )                   implication
       | ( F et F )                   conjonction
       | ( F <=> F )                  équivalence
       | ( forall lettre F )          (∀)
       | ( exists lettre F )          (∃)
       | ( tau lettre F )             terme τ
"""
from __future__ import annotations
import re

from bourbaki.assemblage.assemblage import (
    Assemblage, negation, disjonction, implication, conjonction, equivalence,
    egalite, existe, pour_tout, tau_x,
)
from bourbaki.logique.lecture import Signature, DEFAUT, depuis_assemblage

_TOKEN = re.compile(r"<=>|=>|=|\(|\)|[A-Za-z][A-Za-z0-9]*'*")
_LETTRE = re.compile(r"[A-Za-z]'*$")  # un terme-lettre : une seule lettre (+ primes)


# ── Affichage : assemblage → texte lisible ────────────────────────────────────

def afficher(asm: Assemblage, sig: Signature = DEFAUT) -> str:
    """Rend un assemblage en notation infixe lisible."""
    return _aff(depuis_assemblage(asm, sig))


def _aff(a) -> str:
    if a.tete == "LETTRE":
        return a.etiquette
    if a.tete == "CARRE":
        return "□"
    if a.tete == "TAU":
        return f"τ({_aff(a.enfants[0])})"
    if a.tete == "SIGNE":
        if not a.enfants:          # signe de poids 0 (atome propositionnel)
            return a.etiquette
        return "(" + f" {a.etiquette} ".join(_aff(c) for c in a.enfants) + ")"
    if a.tete == "NON":
        return f"¬{_aff(a.enfants[0])}"
    if a.tete == "OU":
        g, d = a.enfants
        if g.tete == "NON":  # ∨ ¬G D  ≡  G ⇒ D
            return f"({_aff(g.enfants[0])} ⇒ {_aff(d)})"
        return f"({_aff(g)} ∨ {_aff(d)})"
    raise ValueError(f"tête inconnue : {a.tete!r}")


# ── Lecture : texte → assemblage ──────────────────────────────────────────────

class ErreurNotation(ValueError):
    """Texte de formule mal formé."""


def lire_formule(texte: str, sig: Signature = DEFAUT) -> Assemblage:
    """Parse une formule infixe parenthésée en assemblage."""
    toks = _TOKEN.findall(texte)
    if not toks:
        raise ErreurNotation(f"formule vide : {texte!r}")
    asm, i = _parse(toks, 0)
    if i != len(toks):
        raise ErreurNotation(f"tokens résiduels dans {texte!r}")
    return asm


_BINAIRE = {
    "=": egalite,
    "ou": disjonction,
    "=>": implication,
    "et": conjonction,
    "<=>": equivalence,
}


def _attendre(toks: list, i: int, t: str) -> int:
    if i >= len(toks) or toks[i] != t:
        raise ErreurNotation(f"attendu {t!r} en position {i}")
    return i + 1


def _parse(toks: list, i: int):
    if i >= len(toks):
        raise ErreurNotation("fin de formule inattendue")
    t = toks[i]
    if t == "(":
        i += 1
        tete = toks[i] if i < len(toks) else ""
        if tete == "non":
            r, i = _parse(toks, i + 1)
            return negation(r), _attendre(toks, i, ")")
        if tete in ("forall", "exists", "tau"):
            x = toks[i + 1]
            r, i = _parse(toks, i + 2)
            i = _attendre(toks, i, ")")
            if tete == "tau":
                return tau_x(r, x), i
            return (pour_tout if tete == "forall" else existe)(x, r), i
        gauche, i = _parse(toks, i)
        if i >= len(toks) or toks[i] not in _BINAIRE:
            raise ErreurNotation(f"opérateur binaire attendu en position {i}")
        op = toks[i]
        droite, i = _parse(toks, i + 1)
        i = _attendre(toks, i, ")")
        return _BINAIRE[op](gauche, droite), i
    if _LETTRE.match(t):
        return Assemblage((t,)), i + 1
    raise ErreurNotation(f"jeton inattendu : {t!r}")


__all__ = ["afficher", "lire_formule", "ErreurNotation"]
