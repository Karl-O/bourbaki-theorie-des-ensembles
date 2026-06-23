"""Tests des QUATRE briques de restriction (ensembles_restriction_iso_pieces).

Chaque pièce : conclusion == cible (test miroir), non-vacuité (concl ∉ hyps), et
les hypothèses EXACTES attendues.  Invariant permanent : theorie_ensembles() = 22.
"""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.formule import var, egal, inclus, appartient
import bourbaki.cardinaux.ensembles_restriction_iso_pieces as P


def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
    # AXIOME_RESTRICTION est bien l'un des 22 (utilisé, pas ajouté)
    assert E.AXIOME_RESTRICTION in E.theorie_ensembles().axiomes


# ── PIÈCE (1) : { est_fonctionnel(φ) } ⊢ est_fonctionnel(φ|S1) ────────────────
def test_piece1_fonctionnelle():
    thm = P.restriction_fonctionnelle_piece()
    assert thm.conclusion == P.restriction_fonctionnelle_piece_cible()
    assert thm.conclusion not in thm.hypotheses
    vphi = var("phi")
    assert thm.hypotheses == frozenset({E.est_fonctionnel(vphi)})


# ── PIÈCE (2) : { inclus(S1, dom φ) } ⊢ egal(dom(φ|S1), S1) ───────────────────
def test_piece2_domaine():
    thm = P.restriction_domaine_piece()
    assert thm.conclusion == P.restriction_domaine_piece_cible()
    assert thm.conclusion not in thm.hypotheses
    vphi, vS1 = var("phi"), var("S1")
    assert thm.hypotheses == frozenset({inclus(vS1, E.dom(vphi))})


# ── PIÈCE (3) : injectivité transférée à φ|S1 sur S1 ──────────────────────────
def test_piece3_injective():
    thm = P.restriction_injective_piece()
    assert thm.conclusion == P.restriction_injective_piece_cible()
    assert thm.conclusion not in thm.hypotheses
    vphi, vS1, vS2 = var("phi"), var("S1"), var("S2")
    attendues = frozenset({
        E.injective_dans(vphi, vS2, "c", "d"),     # φ injective sur S2
        inclus(vS1, vS2),                          # S1 ⊆ S2
        E.est_fonctionnel(vphi),                   # (additionnelle, requise par le pont)
        inclus(vS1, E.dom(vphi)),                  # (additionnelle, requise par le pont)
    })
    assert thm.hypotheses == attendues


# ── PIÈCE (4) : compatibilité d'ordre transférée à φ|S1 sur S1 ────────────────
def test_piece4_compatible_ordre():
    thm = P.restriction_compatible_ordre_piece()
    assert thm.conclusion == P.restriction_compatible_ordre_piece_cible()
    assert thm.conclusion not in thm.hypotheses
    from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
    vphi, vS1, vS2 = var("phi"), var("S1"), var("S2")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    attendues = frozenset({
        V.compatible_ordre(vphi, vS2, Rf, Rpf, "a", "b"),   # compatible_ordre(φ, S2, R, R')
        inclus(vS1, vS2),                                   # S1 ⊆ S2
        E.est_fonctionnel(vphi),                            # (additionnelle, requise par le pont)
        inclus(vS1, E.dom(vphi)),                           # (additionnelle, requise par le pont)
    })
    assert thm.hypotheses == attendues


def test_theorie_22_apres():
    # rien postulé : la théorie reste à 22 axiomes après construction des pièces
    P.restriction_fonctionnelle_piece()
    P.restriction_domaine_piece()
    P.restriction_injective_piece()
    P.restriction_compatible_ordre_piece()
    assert len(E.theorie_ensembles().axiomes) == 22
