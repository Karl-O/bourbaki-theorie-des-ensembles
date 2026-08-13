"""Tests §III.3.5 — Card(𝔓(X)) = 2^Card X  (E.III.3.5, Proposition 12) : SENS FACILE.

Ce module verrouille le SENS FACILE 𝓕(X; {0,1}) → 𝔓(X) de la Proposition 12,
f ↦ Pre(f) = f⁻¹(1) = { z∈X | (z,1)∈f }, entièrement CERTIFIÉ par le noyau (rien
postulé : seul un axiome de DÉFINITION général fidèle, S8+A1, comme diagonale_cantor).
Le CRUX (bijection caractéristique complète χ : 𝔓(X) ⇄ 𝓕(X;{0,1})) reste REPORTÉ
(sélecteur conditionnel χ_Y + extensionnalité fonctionnelle absents).

  • membre_parties_t          : (Y ∈ P(X)) ⇔ (Y ⊂ X)              [A3, TERMES] ;
  • partie_dans_parties       : {Y ⊂ X} ⊢ Y ∈ P(X) ;
  • preimage_membre           : (z ∈ Pre(f)) ⇔ (z∈X et (z,1)∈f) ;
  • preimage_inclus           : Pre(f) ⊂ X ;
  • preimage_dans_parties     : Pre(f) ∈ P(X)  (sens facile bien défini) ;
  • rho_fonctionnel/domaine   : ρ = f↦f⁻¹(1) est une fonction 𝓕(X;2)→𝔓(X) ;
  • cible_powerset_deux       : l'énoncé exact Card(𝔓(X)) = 2^Card X.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, non, ou, equiv, appartient, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset import ensembles_powerset_deux as P


def _deux():
    return E.paire(E.VIDE, E.singleton(E.VIDE))


def _un():
    return E.singleton(E.VIDE)


# ── Palier A : A3 tolérant aux TERMES ─────────────────────────────────────────
def test_membre_parties_t():
    """⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X), CLOS  (axiome A3 instancié, version TERMES)."""
    vY, vX = var("Y"), var("X")
    t = P.membre_parties_t(vY, vX)
    assert t.conclusion == equiv(appartient(vY, E.parties(vX)), inclus(vY, vX))
    assert t.est_clos


def test_membre_parties_t_terme_compose():
    """Robustesse : A3 tient quand X, Y sont des TERMES composés."""
    vY = E.intersection(var("A"), var("B"))
    vX = E.reunion(var("A"), var("B"))
    t = P.membre_parties_t(vY, vX)
    assert t.conclusion == equiv(appartient(vY, E.parties(vX)), inclus(vY, vX))
    assert t.est_clos


def test_partie_dans_parties():
    """{Y ⊂ X} ⊢ Y ∈ P(X)  (toute partie est un élément de P(X) ; hypothèse Y⊂X)."""
    vY, vX = var("Y"), var("X")
    t = P.partie_dans_parties(vY, vX)
    assert t.conclusion == appartient(vY, E.parties(vX))
    # théorème CONDITIONNEL : l'hypothèse Y⊂X figure dans le contexte
    assert inclus(vY, vX) in t.hypotheses


# ── Le sens facile : Pre(f) = f⁻¹(1) = { z∈X | (z,1)∈f } ───────────────────────
def test_preimage_un_terme():
    """Pre(f) est bien le terme de sélection app(\"preimage_un\", f, X)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import app
    assert P.preimage_un(var("f"), var("X")) == app("preimage_un", var("f"), var("X"))


def test_preimage_membre():
    """⊢ (z ∈ Pre(f)) ⇔ (z∈X et (z,1)∈f), CLOS  (caractérisation de f⁻¹(1))."""
    vf, vX, vz = var("f"), var("X"), var("z")
    t = P.preimage_membre("f", "X", "z")
    attendu = equiv(appartient(vz, P.preimage_un(vf, vX)),
                    et(appartient(vz, vX), appartient(E.couple(vz, _un()), vf)))
    assert t.conclusion == attendu
    assert t.est_clos


def test_preimage_inclus():
    """⊢ Pre(f) ⊂ X, CLOS  (la préimage de 1 est une PARTIE de X)."""
    vf, vX = var("f"), var("X")
    t = P.preimage_inclus("f", "X")
    assert t.conclusion == inclus(P.preimage_un(vf, vX), vX)
    assert t.est_clos


def test_preimage_dans_parties():
    """⊢ Pre(f) ∈ P(X), CLOS  (le sens facile 𝓕(X;2)→𝔓(X) est BIEN DÉFINI)."""
    vf, vX = var("f"), var("X")
    t = P.preimage_dans_parties("f", "X")
    assert t.conclusion == appartient(P.preimage_un(vf, vX), E.parties(vX))
    assert t.est_clos


def test_preimage_dans_parties_terme_compose():
    """Robustesse : Pre(f) ∈ P(X) tient quand X est un TERME composé."""
    vf = var("f")
    vX = E.produit(var("U"), var("V"))
    t = P.preimage_dans_parties(vf, vX)
    assert t.conclusion == appartient(P.preimage_un(vf, vX), E.parties(vX))
    assert t.est_clos


# ── Le graphe ρ : 𝓕(X;2) → 𝔓(X), f ↦ f⁻¹(1) est une FONCTION ──────────────────
def test_rho_fonctionnel():
    """⊢ est_fonctionnel(ρ), CLOS  (le sens facile f↦f⁻¹(1) est une vraie fonction)."""
    vX = var("X")
    rho = E.graphe_terme(E.applications(vX, _deux()), P.preimage_un(var("f"), vX), "f")
    t = P.rho_fonctionnel("X")
    assert t.conclusion == E.est_fonctionnel(rho)
    assert t.est_clos


def test_rho_domaine():
    """⊢ dom(ρ) = 𝓕(X; {0,1}), CLOS  (ρ est défini sur tout 𝓕(X;2))."""
    vX = var("X")
    rho = E.graphe_terme(E.applications(vX, _deux()), P.preimage_un(var("f"), vX), "f")
    t = P.rho_domaine("X")
    assert t.conclusion == egal(E.dom(rho), E.applications(vX, _deux()))
    assert t.est_clos


def test_rho_valeur():
    """{g ∈ 𝓕(X;2)} ⊢ ρ(g) = Pre(g) = g⁻¹(1)  (valeur du sens facile en g ≠ liant f)."""
    vX, vg = var("X"), var("g")
    rho = E.graphe_terme(E.applications(vX, _deux()), P.preimage_un(var("f"), vX), "f")
    t = P.rho_valeur("X", "g")
    assert t.conclusion == egal(E.valeur(rho, vg), P.preimage_un(vg, vX))
    assert appartient(vg, E.applications(vX, _deux())) in t.hypotheses


# ── Cible + report ────────────────────────────────────────────────────────────
def test_cible_powerset_deux_signature():
    """L'énoncé-cible (Proposition 12) : Card(𝔓(X)) = exposant_cardinal_binaire(2, X)."""
    vX = var("X")
    f = P.cible_powerset_deux("X")
    assert f == egal(cardinal(E.parties(vX)), exposant_cardinal_binaire(_deux(), vX))


def test_exposant_deux_base_reexpose():
    """⊢ exposant_cardinal_binaire(2, X) = Card(𝓕(X; 2)), CLOS  (pivot, réexposé du socle)."""
    vX = var("X")
    t = P.exposant_deux_base("X")
    assert t.conclusion == egal(exposant_cardinal_binaire(_deux(), vX),
                                cardinal(E.applications(vX, _deux())))
    assert t.est_clos


def test_bijection_complete_reporte():
    """Le CRUX (bijection χ complète) est explicitement REPORTÉ (NotImplementedError)."""
    import pytest
    with pytest.raises(NotImplementedError):
        P.bijection_complete_REPORTE()
