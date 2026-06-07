"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (Proposition 12) : CLÔTURE FINALE (package).

Re-exporte le CRUX (χ∘ρ = id au niveau des graphes, `_crux`) et la BIJECTION +
l'égalité de cardinaux + Cantor (`_bijection`).
"""
from ._crux import (
    round_trip_rho_chi, chi_eq_graphe,
    # ré-exposé pour les tests/usagers (mêmes termes que les rounds 25/27) :
    chi,
)
from ._bijection import (
    W_fonctionnel, W_domaine, W_valeur, W_injective,
    W_image_egale_applications, chi_bijection,
    powerset_equipotent_applications,
    card_parties_egale_deux_exp, cantor_deux_exp,
)

__all__ = [
    "round_trip_rho_chi", "chi_eq_graphe", "chi",
    "W_fonctionnel", "W_domaine", "W_valeur", "W_injective",
    "W_image_egale_applications", "chi_bijection",
    "powerset_equipotent_applications",
    "card_parties_egale_deux_exp", "cantor_deux_exp",
]
