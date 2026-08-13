"""Couche 0 — Assemblages de Bourbaki (matrice signes × liens).

Bourbaki, *Théorie des Ensembles*, Chap. I §1 (E I.14--E I.21).

Un assemblage est un couple ``(signes, liens)`` :
  * ``signes`` : suite de signes (logiques ▢ τ ∨ ¬, lettres, signes spécifiques) ;
  * ``liens``  : couples (u, v) 1-based, u < v, reliant un τ à un ▢ qu'il lie ;
    les signes liés ne sont jamais des lettres.

"""
from __future__ import annotations
from dataclasses import dataclass

# E I.14 — les quatre signes logiques fixes.
# @livre Ch.I §1.1 Def.- | E I.14 L.1-2 | PDF p.14  (les signes d'une théorie : 1° signes logiques ▢ τ ∨ ¬)
SIGNES_LOGIQUES: tuple[str, ...] = ("CARRE", "TAU", "OU", "NON")

_LETTRES_BASE: frozenset[str] = (
    frozenset(chr(c) for c in range(ord("a"), ord("z") + 1))
    | frozenset(chr(c) for c in range(ord("A"), ord("Z") + 1))
)


# @livre Ch.I §1.1 Def.- | E I.14 L.3-7 | PDF p.14  (2° les lettres : majuscules/minuscules latines + accents ; réserve illimitée)
def est_lettre(s: str) -> bool:
    """True ssi ``s`` est une lettre au sens Bourbaki (a..z A..Z + primes).

    E I.14 — « lettres latines, affectées éventuellement d'accents ».
    Les primes (``'``) servent à fabriquer une réserve infinie de lettres.
    """
    if not isinstance(s, str) or not s:
        return False
    base = s.rstrip("'")
    return len(base) == 1 and base in _LETTRES_BASE


# @livre Ch.I §1.1 Def.- | E I.14 L.11-16 | PDF p.14  (assemblage = succession de signes, certains joints par des liens ; exemple τ∨¬∈▢A′∈▢A″)
@dataclass(frozen=True)
class Assemblage:
    """Assemblage = (signes, liens). Liens canonicalisés (triés) à la construction.

    Invariants vérifiés :
      - 1 ≤ u < v ≤ n pour chaque lien ;
      - liens distincts ;
      - les deux extrémités d'un lien ne sont pas des lettres.
    """
    signes: tuple[str, ...] = ()
    liens: tuple[tuple[int, int], ...] = ()

    def __post_init__(self) -> None:
        n = len(self.signes)
        vus: set[tuple[int, int]] = set()
        for u, v in self.liens:
            if not (1 <= u < v <= n):
                raise ValueError(f"lien invalide ({u},{v}) pour n={n}")
            if (u, v) in vus:
                raise ValueError(f"lien dupliqué ({u},{v})")
            vus.add((u, v))
            if est_lettre(self.signes[u - 1]) or est_lettre(self.signes[v - 1]):
                raise ValueError(f"lien ({u},{v}) touche une lettre")
        # canonicalisation : ordre indépendant de l'insertion
        object.__setattr__(self, "liens", tuple(sorted(self.liens)))

    @property
    def n(self) -> int:
        return len(self.signes)

    def __repr__(self) -> str:
        return f"A({list(self.signes)}, {list(self.liens)})"


# ── Constructeurs élémentaires ────────────────────────────────────────────────

# @livre Ch.I §1.1 Rem.- | E I.15 L.28-41 | PDF p.15  (conventions métamathématiques : symboles gras désignent des assemblages — prose, rien à formaliser)
# @livre Ch.I §1.1 Def.- | E I.15 L.42-45 | PDF p.15  (AB = B écrit à la droite de A ; ∨ A ¬ B etc.)
def concat(a: Assemblage, b: Assemblage) -> Assemblage:
    """Concatène AB ; les liens de B sont décalés de n = |A|."""
    n = a.n
    return Assemblage(
        signes=a.signes + b.signes,
        liens=a.liens + tuple((u + n, v + n) for (u, v) in b.liens),
    )


# @livre Ch.I §1.1 Def.- | E I.15 L.42-45 | PDF p.15  (¬P : cas particulier de la juxtaposition « signe ¬, l'assemblage B »)
def negation(p: Assemblage) -> Assemblage:
    """¬P est identique à l'assemblage ``NON`` ++ P."""
    return concat(Assemblage(("NON",)), p)


# @livre Ch.I §1.1 Def.- | E I.15 L.42-45 | PDF p.15  (∨ A B : juxtaposition « ∨, l'assemblage A, … »)
def disjonction(p: Assemblage, q: Assemblage) -> Assemblage:
    """P ∨ Q est identique à l'assemblage ``OU`` ++ P ++ Q."""
    return concat(concat(Assemblage(("OU",)), p), q)


# @livre Ch.I §1.1 Rem.- | E I.14 L.17-19 | PDF p.14  (symboles abréviateurs, début du petit texte — prose)
# @livre Ch.I §1.1 Rem.- | E I.15 L.1-3 | PDF p.15  (symboles abréviateurs, fin : « l'objet des définitions » — prose)
# @livre Ch.I §1.1 Ex.- | E I.15 L.4-4 | PDF p.15  (Exemple 1 : l'assemblage ∨ ¬ se représente par ⇒)
def implication(p: Assemblage, q: Assemblage) -> Assemblage:
    """P ⇒ Q est identique à ∨ ¬P Q, c.-à-d. l'assemblage ``OU NON`` ++ P ++ Q (⇒ abréviateur)."""
    return concat(concat(Assemblage(("OU", "NON")), p), q)


# ── τ et substitution 

def positions_de(a: Assemblage, x: str) -> tuple[int, ...]:
    """Positions 1-based où la lettre x apparaît dans A."""
    return tuple(k + 1 for k, s in enumerate(a.signes) if s == x)


# @livre Ch.I §1.1 Def.- | E I.15 L.46-46 | PDF p.15  (τx(A) — début de la définition)
# @livre Ch.I §1.1 Def.- | E I.16 L.1-4 | PDF p.16  (τx(A), fin : lien de chaque x au τ, remplacement par ▢ ; τx(A) ne contient pas x)
# @livre Ch.I §1.1 Ex.- | E I.16 L.5-5 | PDF p.16  (exemple : τx(∈ x y) = τ ∈ ▢ y)
def tau_x(a: Assemblage, x: str) -> Assemblage:
    """τ_x(A) : préfixe τ, lie chaque occurrence de x au τ, remplace x par ▢.

    Le résultat est un *terme* sans la lettre x (forme « sans nom »).
    """
    if not est_lettre(x):
        raise ValueError(f"τ_x : x doit être une lettre, reçu {x!r}")
    pos_x = positions_de(a, x)
    signes = ("TAU",) + tuple("CARRE" if s == x else s for s in a.signes)
    liens = tuple((u + 1, v + 1) for (u, v) in a.liens) + tuple((1, k + 1) for k in pos_x)
    return Assemblage(signes=signes, liens=liens)


# @livre Ch.I §1.1 Ex.- | E I.15 L.5-16 | PDF p.15  (Exemple 2 : symboles « 3 et 4 », ∅, N, Z, π=√2+√3… — prose, rien à formaliser)
# @livre Ch.I §1.1 Rem.- | E I.15 L.17-23 | PDF p.15  (le symbole d'un assemblage contient en général ses lettres — prose, petit texte)
def lettres(a: Assemblage) -> set[str]:
    """Ensemble des lettres figurant dans A."""
    return {s for s in a.signes if est_lettre(s)}


# @livre Ch.I §1.1 Def.- | E I.16 L.6-9 | PDF p.16  ((B|x)A : remplacer x par B ; (B|x)τx(A) identique à τx(A))
# @livre Ch.I §1.1 Ex.- | E I.16 L.10-13 | PDF p.16  (exemple : x remplacé par ▢ dans ∨ ∈ x y = x x)
# @livre Ch.I §1.1 Rem.- | E I.16 L.21-34 | PDF p.16  (substitution dans les symboles abréviateurs, exemples E⊗F, M∩(P∪Q) — prose, petit texte)
def substitution_b_x_a(b: Assemblage, x: str, a: Assemblage) -> Assemblage:
    """(B|x)A : remplace chaque occurrence de la lettre x dans A par B.

    Décalage f(k) = k + (p-1)·|{kᵢ < k}| ; liens de A réindexés via f ;
    copie locale des liens de B à chaque occurrence de x. 
    """
    if not est_lettre(x):
        raise ValueError("(B|x) : x doit être une lettre")
    n, p = a.n, b.n
    pos_x = positions_de(a, x)

    def f(k: int) -> int:
        return k + (p - 1) * sum(1 for ki in pos_x if ki < k)

    nouv: list[str] = []
    for k in range(1, n + 1):
        s = a.signes[k - 1]
        if s == x:
            nouv.extend(b.signes)
        else:
            nouv.append(s)
    liens = [(f(u), f(v)) for (u, v) in a.liens]
    for k_i in pos_x:
        debut = f(k_i)
        liens += [(debut + u - 1, debut + v - 1) for (u, v) in b.liens]
    return Assemblage(tuple(nouv), tuple(liens))


# @livre Ch.I §1.1 Def.- | E I.16 L.14-20 | PDF p.16  (« lettres ne figurant ni dans A, ni dans B, ni dans C » — clause de fraîcheur du passage A{B,C})
def lettre_hors_de(assemblages, exclues=()):
    """Une lettre ne figurant dans aucun des assemblages donnés ni dans ``exclues``.

    Le livre exige des lettres « ne figurant ni dans A, ni dans B, ni dans C » :
    on prime une base jusqu'à sortir de l'ensemble interdit (les primes donnent
    une réserve infinie de lettres, cf. est_lettre).
    """
    interdites = set(exclues)
    for a in assemblages:
        interdites |= lettres(a)
    cand = "x"
    while cand in interdites:
        cand += "'"
    return cand


# @livre Ch.I §1.1 Def.- | E I.16 L.14-20 | PDF p.16  (notations A{x}, A{B} et A{B,C} : substitution simultanée = (B|x')(C|y')(x'|x)(y'|y)A)
def substitution_simultanee(b, x, c, y, a):
    """A{B, C} : remplace SIMULTANÉMENT x par B et y par C dans A.

    Livre (passage « Lorsque, étant donné un assemblage A… », après (B|x)A) :
    « On désigne par A{B, C} l'assemblage obtenu en remplaçant simultanément
    x par B et y par C en toutes leurs occurrences dans A (on notera que x et y
    peuvent figurer dans B et dans C) ; si x' et y' sont des lettres distinctes
    de x et de y et distinctes entre elles, ne figurant ni dans A, ni dans B,
    ni dans C, A{B, C} n'est autre que (B | x')(C | y')(x' | x)(y' | y)A. »

    On suit cette définition mot à mot ; les lettres fraîches garantissent la
    simultanéité (deux substitutions successives directes seraient fausses dès
    que x figure dans C ou y dans B). Notation associée : A{B} = (B|x)A, c'est
    ``substitution_b_x_a`` tel quel.
    """
    if not est_lettre(x) or not est_lettre(y) or x == y:
        raise ValueError("A{B, C} : x et y doivent être des lettres distinctes")
    xp = lettre_hors_de((a, b, c), exclues={x, y})
    yp = lettre_hors_de((a, b, c), exclues={x, y, xp})
    etape = substitution_b_x_a(Assemblage((yp,)), y, a)        # (y' | y) A
    etape = substitution_b_x_a(Assemblage((xp,)), x, etape)    # (x' | x) ...
    etape = substitution_b_x_a(c, yp, etape)                   # (C  | y') ...
    return substitution_b_x_a(b, xp, etape)                    # (B  | x') ...


__all__ = [
    "Assemblage", "SIGNES_LOGIQUES", "est_lettre", "lettres",
    "concat", "negation", "disjonction", "implication",
    "positions_de", "tau_x", "substitution_b_x_a",
    "lettre_hors_de", "substitution_simultanee",
]
