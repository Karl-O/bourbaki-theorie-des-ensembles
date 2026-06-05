"""Couche 5 (bis) — « ta propre IA » : modèle numérique from-scratch (Python pur).

Régression logistique entraînée par descente de gradient, sans aucune dépendance
externe (ni numpy ni torch). Elle consomme les vecteurs de traits issus des
VALEURS PURES (cf. encodeur.py) — pas de notation, pas de LLM.

C'est volontairement un modèle simple et transparent : on veut comprendre ce
qu'il apprend, et il sert d'abord d'heuristique de valeur (« cet assemblage
ressemble-t-il à un théorème ? ») pour guider la recherche. Le noyau reste le
garde-fou : le modèle ne fait que scorer, jamais certifier.
"""
from __future__ import annotations
import math


def _sigmoide(z: float) -> float:
    z = max(-30.0, min(30.0, z))
    return 1.0 / (1.0 + math.exp(-z))


class RegressionLogistique:
    """Classifieur linéaire binaire, entraîné par SGD, avec normalisation."""

    def __init__(self, dim: int):
        self.dim = dim
        self.w = [0.0] * dim
        self.b = 0.0
        self.mu = [0.0] * dim
        self.sd = [1.0] * dim

    # ── normalisation des traits (centrage / réduction) ───────────────────────
    def _calibrer(self, X: list) -> None:
        n = len(X)
        for j in range(self.dim):
            col = [x[j] for x in X]
            m = sum(col) / n
            var = sum((c - m) ** 2 for c in col) / n
            self.mu[j] = m
            self.sd[j] = math.sqrt(var) if var > 1e-12 else 1.0

    def _norm(self, x: list) -> list:
        return [(x[j] - self.mu[j]) / self.sd[j] for j in range(self.dim)]

    # ── entraînement ──────────────────────────────────────────────────────────
    def entrainer(self, X: list, y: list, epochs: int = 300, lr: float = 0.2) -> None:
        self._calibrer(X)
        Xn = [self._norm(x) for x in X]
        for _ in range(epochs):
            for xi, cible in zip(Xn, y):
                p = _sigmoide(self.b + sum(self.w[j] * xi[j] for j in range(self.dim)))
                err = p - cible
                self.b -= lr * err
                for j in range(self.dim):
                    self.w[j] -= lr * err * xi[j]

    # ── inférence ───────────────────────────────────────────────────────────
    def proba(self, x: list) -> float:
        xn = self._norm(x)
        return _sigmoide(self.b + sum(self.w[j] * xn[j] for j in range(self.dim)))

    def predire(self, x: list) -> int:
        return 1 if self.proba(x) >= 0.5 else 0

    def precision(self, X: list, y: list) -> float:
        if not X:
            return 0.0
        bons = sum(1 for x, c in zip(X, y) if self.predire(x) == c)
        return bons / len(X)

    def poids_tries(self, noms: tuple) -> list:
        """(trait, poids) triés par |poids| décroissant — pour interpréter le modèle."""
        return sorted(zip(noms, self.w), key=lambda t: -abs(t[1]))


__all__ = ["RegressionLogistique"]
