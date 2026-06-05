"""Couche 1 — Lecture : assemblage ⇄ arbre de syntaxe.

PDF p.~33--35, Bourbaki, Chap. I, Appendice (« critères de formation »,
caractérisation des mots significatifs).

C'est LA pièce que la V8 n'avait jamais implémentée (`est_significatif`
y valait littéralement ``len(M) <= 50``). Ici on réalise la *lecture unique*
des mots significatifs : un assemblage en notation préfixe se décompose de
manière unique grâce aux poids (arités) des signes. C'est l'unicité de
lecture à la Łukasiewicz, qui est précisément ce que démontre l'Appendice.

Grammaire (notation préfixe) :

    Relation ::= OU  Relation Relation
               | NON Relation
               | s   Terme … Terme        (s signe spécifique *relationnel*, arité n)

    Terme    ::= lettre
               | CARRE                    (▢, lié à un τ englobant — De Bruijn)
               | TAU Relation             (τ ; le corps contient les ▢ qu'il lie)
               | f   Terme … Terme        (f signe spécifique *fonctionnel*, arité n)

Les ▢ sont représentés par leur **indice de De Bruijn** (nombre de τ qui les
séparent de leur lieur), ce qui rend l'arbre indépendant des positions et
garantit le round-trip exact avec les liens de l'assemblage.
"""
from __future__ import annotations
from dataclasses import dataclass

from assemblage import Assemblage, est_lettre

# Signature : nom du signe spécifique -> (arité, sorte∈{'relation','terme'}).
Signature = dict[str, tuple[int, str]]

# Signature par défaut de la théorie des ensembles : = et ∈, relationnels, arité 2.
DEFAUT: Signature = {"=": (2, "relation"), "in": (2, "relation")}


class NonSignificatif(ValueError):
    """L'assemblage n'est ni un terme ni une relation bien formé."""


@dataclass(frozen=True)
class Arbre:
    """Arbre de syntaxe. ``sorte`` ∈ {'terme','relation'}.

    tete ∈ {'OU','NON','TAU','CARRE','LETTRE','SIGNE'}.
    etiquette : nom de lettre ou de signe spécifique (sinon '').
    db : indice de De Bruijn (uniquement pour 'CARRE').
    """
    tete: str
    sorte: str
    enfants: tuple["Arbre", ...] = ()
    etiquette: str = ""
    db: int = -1


# ── depuis_assemblage : lecture (parse) ───────────────────────────────────────

def depuis_assemblage(a: Assemblage, sig: Signature = DEFAUT) -> Arbre:
    """Lit l'assemblage en arbre. Lève NonSignificatif si mal formé.

    Vérifie que TOUT l'assemblage est consommé (un mot significatif n'a pas
    de « reste »), ce qui est exactement le critère de l'Appendice.
    """
    arbre, i = _lire(a, 0, [], sig)
    if i != a.n:
        raise NonSignificatif(f"signes résiduels après lecture (i={i}, n={a.n})")
    return arbre


def _binder_de(a: Assemblage, pos_carre: int) -> int:
    """Position 1-based du τ liant le ▢ situé à ``pos_carre`` (1-based)."""
    binders = [u for (u, v) in a.liens if v == pos_carre]
    if len(binders) != 1:
        raise NonSignificatif(f"▢ en {pos_carre} doit avoir exactement un lieur")
    return binders[0]


def _lire(a: Assemblage, i: int, taus: list[int], sig: Signature) -> tuple[Arbre, int]:
    """Lit un mot significatif à partir de l'indice ``i`` (0-based).

    ``taus`` = pile des positions 1-based des τ ouverts (du plus externe au
    plus interne). Retourne (arbre, indice suivant).
    """
    if i >= a.n:
        raise NonSignificatif("lecture au-delà de la fin")
    s = a.signes[i]

    if s == "OU":
        g, i = _lire(a, i + 1, taus, sig)
        d, i = _lire(a, i, taus, sig)
        _exiger(g.sorte == "relation" and d.sorte == "relation", "OU attend deux relations")
        return Arbre("OU", "relation", (g, d)), i

    if s == "NON":
        r, i = _lire(a, i + 1, taus, sig)
        _exiger(r.sorte == "relation", "NON attend une relation")
        return Arbre("NON", "relation", (r,)), i

    if s == "TAU":
        pos_tau = i + 1  # 1-based
        corps, i = _lire(a, i + 1, taus + [pos_tau], sig)
        _exiger(corps.sorte == "relation", "TAU attend une relation")
        return Arbre("TAU", "terme", (corps,)), i

    if s == "CARRE":
        pos = i + 1
        binder = _binder_de(a, pos)
        _exiger(binder in taus, f"▢ en {pos} non lié à un τ englobant")
        db = (len(taus) - 1) - taus.index(binder)  # 0 = τ le plus interne
        return Arbre("CARRE", "terme", db=db), i + 1

    # La signature est consultée AVANT est_lettre : un signe déclaré (ex. un
    # atome propositionnel « A » de poids 0) prime sur son statut de lettre.
    if s in sig:
        arite, sorte = sig[s]
        enfants: list[Arbre] = []
        i += 1  # consommer le signe spécifique avant de lire ses arguments
        for _ in range(arite):
            c, i = _lire(a, i, taus, sig)
            _exiger(c.sorte == "terme", f"signe {s!r} attend des termes")
            enfants.append(c)
        return Arbre("SIGNE", sorte, tuple(enfants), etiquette=s), i

    if est_lettre(s):
        return Arbre("LETTRE", "terme", etiquette=s), i + 1

    raise NonSignificatif(f"signe inconnu ou hors-place : {s!r}")


def _exiger(cond: bool, msg: str) -> None:
    if not cond:
        raise NonSignificatif(msg)


# ── vers_assemblage : écriture (unparse) ──────────────────────────────────────

def vers_assemblage(arbre: Arbre) -> Assemblage:
    """Reconstruit l'assemblage à partir de l'arbre (inverse de depuis_assemblage)."""
    signes: list[str] = []
    liens: list[tuple[int, int]] = []
    _ecrire(arbre, [], signes, liens)
    return Assemblage(tuple(signes), tuple(liens))


def _ecrire(arbre: Arbre, taus: list[int], signes: list[str],
            liens: list[tuple[int, int]]) -> None:
    if arbre.tete == "OU":
        signes.append("OU")
        _ecrire(arbre.enfants[0], taus, signes, liens)
        _ecrire(arbre.enfants[1], taus, signes, liens)
    elif arbre.tete == "NON":
        signes.append("NON")
        _ecrire(arbre.enfants[0], taus, signes, liens)
    elif arbre.tete == "TAU":
        pos_tau = len(signes) + 1
        signes.append("TAU")
        _ecrire(arbre.enfants[0], taus + [pos_tau], signes, liens)
    elif arbre.tete == "CARRE":
        pos = len(signes) + 1
        signes.append("CARRE")
        liens.append((taus[-1 - arbre.db], pos))  # De Bruijn -> position du τ lieur
    elif arbre.tete == "LETTRE":
        signes.append(arbre.etiquette)
    elif arbre.tete == "SIGNE":
        signes.append(arbre.etiquette)
        for c in arbre.enfants:
            _ecrire(c, taus, signes, liens)
    else:
        raise ValueError(f"tête d'arbre inconnue : {arbre.tete!r}")


# ── Prédicats de l'Appendice (enfin réels) ────────────────────────────────────

def est_significatif(a: Assemblage, sig: Signature = DEFAUT) -> bool:
    """True ssi A est un terme OU une relation bien formé. PDF p.~33."""
    try:
        depuis_assemblage(a, sig)
        return True
    except NonSignificatif:
        return False


def est_relation(a: Assemblage, sig: Signature = DEFAUT) -> bool:
    """True ssi A est une relation. PDF p.~34."""
    try:
        return depuis_assemblage(a, sig).sorte == "relation"
    except NonSignificatif:
        return False


def est_terme(a: Assemblage, sig: Signature = DEFAUT) -> bool:
    """True ssi A est un terme. PDF p.~33."""
    try:
        return depuis_assemblage(a, sig).sorte == "terme"
    except NonSignificatif:
        return False


__all__ = [
    "Signature", "DEFAUT", "NonSignificatif", "Arbre",
    "depuis_assemblage", "vers_assemblage",
    "est_significatif", "est_relation", "est_terme",
]
