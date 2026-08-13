"""Tests §II.5.3 — la diagonale vit dans le produit E^I.

Vérifie, pour chaque énoncé :
  • conclusion EXACTE (== cible reconstruite indépendamment) ;
  • hypothèses honnêtes : (a) hypothèses == {x∈E} (antécédent honnête, jamais la
    conclusion) ; (b) théorème CLOS (Δ⊂E^I, 0 hypothèse) ;
  • invariant theorie_ensembles() == 22 (la caractérisation de E^I vit dans la
    théorie SÉPARÉE theorie_exposant ; aucun axiome neuf dans les 22).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl, appartient, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_1_extension_canonique import ensembles_extension_canonique as X
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_diagonale import ensembles_diagonale_dans_exposant as D


# ── (a)  x̃ ∈ E^I ─────────────────────────────────────────────────────────────
def test_cible_terme_dans_exposant_forme():
    """La cible (a) est (x∈E) ⇒ ( x̃ ∈ E^I ),  x̃ = famille_constante(I, x, ι)."""
    vE, vI, vx = var("E"), var("I"), var("x")
    xt = X.famille_constante(vI, vx, "iota")
    cible = impl(appartient(vx, vE), appartient(xt, E.exposant(vI, vE)))
    assert D.cible_diagonale_terme_dans_exposant("E", "I", "x", "iota") == cible


def test_terme_dans_exposant_conclusion_et_hyps():
    """⊢ (x∈E) ⇒ x̃∈E^I : conclusion == cible et théorème clos (antécédent porté)."""
    thm = D.diagonale_terme_dans_exposant("E", "I", "x", "iota")
    cible = D.cible_diagonale_terme_dans_exposant("E", "I", "x", "iota")
    assert thm.conclusion == cible
    # l'antécédent x∈E est INTERNE à l'implication (déchargé) → théorème clos
    assert thm.est_clos


# ── (b)  Δ ⊂ E^I ─────────────────────────────────────────────────────────────
def test_cible_incluse_exposant_forme():
    """La cible (b) est Δ ⊂ E^I,  Δ = diagonale_produit(E, I, xa, ι)."""
    vE, vI = var("E"), var("I")
    Delta = X.diagonale_produit(vE, vI, "xa", "iota")
    cible = inclus(Delta, E.exposant(vI, vE))
    assert D.cible_diagonale_incluse_exposant("E", "I", "xa", "iota") == cible


def test_incluse_exposant_conclusion_et_close():
    """⊢ Δ ⊂ E^I : conclusion == cible et théorème CLOS (0 hypothèse non déchargée)."""
    thm = D.diagonale_incluse_exposant("E", "I", "xa", "iota")
    cible = D.cible_diagonale_incluse_exposant("E", "I", "xa", "iota")
    assert thm.conclusion == cible
    assert thm.est_clos


# ── invariant ────────────────────────────────────────────────────────────────
def test_theorie_ensembles_inchangee_22():
    """Preuve set/fonction-théorique : la caractérisation de E^I est dans
    theorie_exposant (séparée) ; theorie_ensembles() reste à 22 axiomes."""
    assert len(E.theorie_ensembles().axiomes) == 22
