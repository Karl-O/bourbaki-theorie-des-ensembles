"""Tests §III.6.1 — seg(≤_G, ℕ, 0) = ∅  (« rien avant 0 » dans le VRAI ℕ).

L'énoncé est RECONSTRUIT À LA MAIN ici (hors du module testé) et comparé par
égalité EXACTE ; la clôture est assertée par frozenset() vide ; theorie_ensembles()
vaut 22 avant ET après.  On vérifie AUSSI que le terme conclu est bien celui que
consomme la Déf. 2 de la factorielle (_seg_NN(0)), sans quoi le théorème serait
vrai mais inutilisable.

⚠️ slow : premier contact avec ensemble_NN() ⇒ N_existe (~3 min, mémoïsé/session).
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_segment_zero_NN import (
    graphe_ordre_NN, segment_zero_NN, plus_petit_element_zero_NN,
    segment_zero_NN_est_vide_enonce, segment_zero_NN_est_vide,
)

pytestmark = pytest.mark.slow


def test_invariant_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_terme_segment_reconstruit_a_la_main():
    """Le terme conclu est EXACTEMENT seg(≤_G, ℕ, 0), reconstruit hors du module.

    NB : `_graphe_R` rend un CONSTRUCTEUR de relation (lambda), jamais comparable
    par == ; on compare donc les TERMES qu'il produit, pas le constructeur."""
    attendu = E.segment_extremite(G_ordre_NN(), ensemble_NN(), ZERO)
    assert segment_zero_NN() == attendu
    assert E.segment_extremite(G_ordre_NN(), ensemble_NN(), ZERO) == attendu


def test_terme_est_celui_de_la_factorielle_def2():
    """Le segment conclu est CELUI que consomme la Déf. 2 (_seg_NN(0)) — sinon le
    théorème serait vrai mais inutilisable en aval."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (
        _seg_NN,
    )
    assert segment_zero_NN() == _seg_NN(ZERO)


def test_plus_petit_element_zero_NN_est_clos():
    """⊢ est_plus_petit_element(≤_G, ℕ, 0) — énoncé reconstruit à la main."""
    thm = plus_petit_element_zero_NN()
    attendu = E.est_plus_petit_element(_graphe_R(G_ordre_NN()), ensemble_NN(), ZERO)
    assert thm.conclusion == attendu
    assert thm.est_clos
    assert thm.hypotheses == frozenset(), "aucune hypothèse résiduelle attendue"


def test_segment_zero_NN_est_vide():
    """🎯 ⊢ seg(≤_G, ℕ, 0) = ∅ — CLOS, 0 hypothèse.

    Corrige l'annotation périmée « rien avant 0 n'est pas dérivable » : c'est vrai
    sur des VARIABLES, faux sur les TERMES ℕ / G_ordre_NN."""
    thm = segment_zero_NN_est_vide()
    attendu = egal(E.segment_extremite(G_ordre_NN(), ensemble_NN(), ZERO),
                   E.VIDE)                                  # reconstruit à la main
    assert thm.conclusion == attendu
    assert thm.conclusion == segment_zero_NN_est_vide_enonce()
    assert thm.est_clos, "le théorème DOIT être clos"
    assert thm.hypotheses == frozenset(), "hypothèses ≠ frozenset() : résidu caché"
    assert thm.conclusion not in thm.hypotheses


def test_non_vacuite_le_zero_est_dans_NN():
    """Garde-fou : 0 ∈ ℕ est bien le 1ᵉʳ conjoint (le théorème n'est pas creux)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
        zero_dans_NN,
    )
    z0 = zero_dans_NN()
    assert z0.conclusion == appartient(ZERO, ensemble_NN())
    assert z0.est_clos


def test_invariant_22_axiomes_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
