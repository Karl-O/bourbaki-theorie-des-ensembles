"""Couche 0 — Assemblages de Bourbaki (matrice signes × liens).

PDF p.~15--17, Bourbaki, *Théorie des Ensembles*, Chap. I §1.

Un assemblage est un couple ``(signes, liens)`` :
  * ``signes`` : suite de signes (logiques ▢ τ ∨ ¬, lettres, signes spécifiques) ;
  * ``liens``  : couples (u, v) 1-based, u < v, reliant un τ à un ▢ qu'il lie ;
    les signes liés ne sont jamais des lettres.

Différence avec V8 : les ``liens`` sont **canonicalisés** (triés) à la
construction, de sorte que l'égalité d'assemblages soit indépendante de
l'ordre d'insertion. C'est indispensable pour le round-trip de la couche
de lecture (`lecture.py`).

Ce module est repris quasi verbatim de la V8 (couche jugée fidèle) ; il
constitue la *vérité de terrain* sur laquelle s'appuie tout le reste.
"""
from __future__ import annotations
from dataclasses import dataclass

# PDF p.~15 — les quatre signes logiques fixes.
SIGNES_LOGIQUES: tuple[str, ...] = ("CARRE", "TAU", "OU", "NON")

_LETTRES_BASE: frozenset[str] = (
    frozenset(chr(c) for c in range(ord("a"), ord("z") + 1))
    | frozenset(chr(c) for c in range(ord("A"), ord("Z") + 1))
)


def est_lettre(s: str) -> bool:
    """True ssi ``s`` est une lettre au sens Bourbaki (a..z A..Z + primes).

    PDF p.~15 — « lettres latines, affectées éventuellement d'accents ».
    Les primes (``'``) servent à fabriquer une réserve infinie de lettres.
    """
    if not isinstance(s, str) or not s:
        return False
    base = s.rstrip("'")
    return len(base) == 1 and base in _LETTRES_BASE


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

def concat(a: Assemblage, b: Assemblage) -> Assemblage:
    """Concatène AB ; les liens de B sont décalés de n = |A|. PDF p.~16."""
    n = a.n
    return Assemblage(
        signes=a.signes + b.signes,
        liens=a.liens + tuple((u + n, v + n) for (u, v) in b.liens),
    )


def negation(p: Assemblage) -> Assemblage:
    """¬P  ≡  l'assemblage ``NON`` ++ P."""
    return concat(Assemblage(("NON",)), p)


def disjonction(p: Assemblage, q: Assemblage) -> Assemblage:
    """P ∨ Q  ≡  ``OU`` ++ P ++ Q."""
    return concat(concat(Assemblage(("OU",)), p), q)


def implication(p: Assemblage, q: Assemblage) -> Assemblage:
    """P ⇒ Q  ≡  ∨ ¬P Q  ≡  ``OU NON`` ++ P ++ Q. PDF p.~16 (⇒ abréviateur)."""
    return concat(concat(Assemblage(("OU", "NON")), p), q)


# ── τ et substitution (repris de V8, fidèles ; utiles aux tests et à la suite) ──

def positions_de(a: Assemblage, x: str) -> tuple[int, ...]:
    """Positions 1-based où la lettre x apparaît dans A. PDF p.~16."""
    return tuple(k + 1 for k, s in enumerate(a.signes) if s == x)


def tau_x(a: Assemblage, x: str) -> Assemblage:
    """τ_x(A) : préfixe τ, lie chaque occurrence de x au τ, remplace x par ▢.

    PDF p.~16. Le résultat est un *terme* sans la lettre x (forme « sans nom »).
    """
    if not est_lettre(x):
        raise ValueError(f"τ_x : x doit être une lettre, reçu {x!r}")
    pos_x = positions_de(a, x)
    signes = ("TAU",) + tuple("CARRE" if s == x else s for s in a.signes)
    liens = tuple((u + 1, v + 1) for (u, v) in a.liens) + tuple((1, k + 1) for k in pos_x)
    return Assemblage(signes=signes, liens=liens)


def lettres(a: Assemblage) -> set[str]:
    """Ensemble des lettres figurant dans A."""
    return {s for s in a.signes if est_lettre(s)}


def substitution_b_x_a(b: Assemblage, x: str, a: Assemblage) -> Assemblage:
    """(B|x)A : remplace chaque occurrence de la lettre x dans A par B. PDF p.~17.

    Décalage f(k) = k + (p-1)·|{kᵢ < k}| ; liens de A réindexés via f ;
    copie locale des liens de B à chaque occurrence de x. (Repris de V8, fidèle.)
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


# ── Abréviations dérivées (définitions Bourbaki, vérifiées sur le PDF) ─────────

def conjonction(p: Assemblage, q: Assemblage) -> Assemblage:
    """A et B := ¬((¬A) ∨ (¬B)). PDF p.~29 (§I.3.4)."""
    return negation(disjonction(negation(p), negation(q)))


def equivalence(p: Assemblage, q: Assemblage) -> Assemblage:
    """A ⇔ B := (A ⇒ B) et (B ⇒ A). PDF p.~30 (§I.3.5)."""
    return conjonction(implication(p, q), implication(q, p))


def egalite(t: Assemblage, u: Assemblage) -> Assemblage:
    """T = U := l'assemblage « = » ++ T ++ U (= signe relationnel, poids 2). PDF p.~38."""
    return concat(concat(Assemblage(("=",)), t), u)


def existe(x: str, r: Assemblage) -> Assemblage:
    """(∃x)R := (τ_x(R) | x) R. PDF p.~32 (§I.4.1)."""
    return substitution_b_x_a(tau_x(r, x), x, r)


def pour_tout(x: str, r: Assemblage) -> Assemblage:
    """(∀x)R := ¬(∃x)(¬R). PDF p.~32 (§I.4.1)."""
    return negation(existe(x, negation(r)))


__all__ = [
    "Assemblage", "SIGNES_LOGIQUES", "est_lettre", "lettres",
    "concat", "negation", "disjonction", "implication",
    "positions_de", "tau_x", "substitution_b_x_a",
    "conjonction", "equivalence", "egalite", "existe", "pour_tout",
]
