"""Tests MIROIR de `ensembles_pont_segment_iii5` — cibles RECONSTRUITES à la main.

Aucune cible n'est empruntée au module testé : `seg(ℕ,k+1)` et `[0,k]` sont
réassemblés ICI depuis les définitions primitives.  Les hypothèses sont assertées
par ÉGALITÉ EXACTE de frozenset — jamais par un `len(...)`, qui ne dit PAS
lesquelles et laisserait passer un résidu de complaisance.

⚠️ slow, MESURÉ le 2026-07-27 (fichier seul, machine chargée) : 9 passed en 590 s,
dont 485 s pour le PREMIER `segment_succ_est_intervalle` (`fini_downward_garde_thm`
+ `N_existe`) ; les suivants ~20 s grâce à la mémoïsation.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import G_ordre_NN

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_pont_segment_iii5 import (
    segment_succ_est_intervalle, segment_succ_NN,
)

pytestmark = pytest.mark.slow

K = "kpd"


# ── cibles RECONSTRUITES à la main, hors du module ───────────────────────────
def _G_main():
    """Le GRAPHE de l'ordre ≤ de ℕ, réassemblé : G_ordre_NN() (TERME).

    Depuis la migration seg_ext, c'est LUI que porte le terme de segment
    (auparavant le terme ignorait l'ordre : cf. la faiblesse levee ci-dessous)."""
    return G_ordre_NN()


def _seg_main(k):
    """seg(ℕ, k+1) réassemblé : segment_extremite(≤_G, ℕ, successeur(k))."""
    return E.segment_extremite(_G_main(), ensemble_NN(), successeur(k))


def _interv_main(k):
    """[0,k] réassemblé : intervalle_entiers(ZERO, k)."""
    return E.intervalle_entiers(ZERO, k)


def _hyp_k(k):
    return appartient(k, ensemble_NN())


# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_segment_succ_est_intervalle():
    """{ k ∈ ℕ } ⊢ seg(ℕ, k+1) = [0, k]  — cible et hypothèses reconstruites."""
    vk = var(K)
    th = segment_succ_est_intervalle()
    assert th.conclusion == egal(_seg_main(vk), _interv_main(vk))
    assert th.hypotheses == frozenset({_hyp_k(vk)})
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_segment_succ_terme_est_le_meme():
    """Le TERME exporté coïncide avec le segment reconstruit (pas d'α-dérive).

    ✅ FAIBLESSE LEVÉE (migration seg_ext, 2026-07-31) : `segment_extremite(G, e, x)`
    PORTE désormais le graphe (= `app("seg_ext", G, e, x)`), donc cette assertion est
    SENSIBLE au choix de l'ordre — le contre-cas ci-dessous le mesure."""
    vk = var(K)
    assert segment_succ_NN(vk) == _seg_main(vk)
    # un AUTRE graphe donne un AUTRE terme : le segment n'oublie plus son ordre.
    assert segment_succ_NN(vk) != E.segment_extremite(var("Gautre"), ensemble_NN(),
                                                      successeur(vk))


def test_segment_est_celui_de_la_chaine_c62():
    """Le segment du pont est LITTÉRALEMENT `_seg_NN(k+1)` (iii_3_6_familles) — donc le
    MÊME terme que celui de `segment_succ_decomposition` et de la chaîne C62."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import _seg_NN
    vk = var(K)
    assert segment_succ_NN(vk) == _seg_NN(successeur(vk))


def test_pont_est_l_hypothese_honnete_de_factorielle_succ():
    """🎯 Le pont conclut EXACTEMENT l'hypothèse HONNÊTE `seg(m)=[0,n]` que
    `factorielle_succ_fallback` assume — À CONDITION que la chaîne soit instanciée à
    e := ℕ (terme concret) / G := G_ordre_NN().  Aux DÉFAUTS (variables « Enat »/« Gle »)
    ce n'est PAS la même formule : le contre-cas est asserté, pour que le test ne puisse
    pas passer par accident."""
    vn = var("nfsc")
    concl = segment_succ_est_intervalle(vn).conclusion
    h_seg_NN = egal(E.segment_extremite(_G_main(), ensemble_NN(), successeur(vn)),
                    E.intervalle_entiers(ZERO, vn))
    h_seg_var = egal(E.segment_extremite(_G_main(), var("Enat"), successeur(vn)),
                     E.intervalle_entiers(ZERO, vn))
    assert concl == h_seg_NN
    assert concl != h_seg_var


# ══════════════════════════════════════════════════════════════════════════════
#  MUTANTS — chaque cible FAUSSE doit être REJETÉE par les mêmes assertions.
#  (Un mutant qui « meurt » sur TypeError ne prouverait rien : ils meurent tous
#   ici sur une INÉGALITÉ de formule, donc sur le contenu mathématique.)
# ══════════════════════════════════════════════════════════════════════════════
def test_mutant_voisin_vrai_point_k():
    """VOISIN VRAI : le pont au point k (et non k+1) — seg(ℕ,k) ≠ [0,k]."""
    vk = var(K)
    th = segment_succ_est_intervalle()
    faux = egal(E.segment_extremite(_G_main(), ensemble_NN(), vk), _interv_main(vk))
    assert th.conclusion != faux


def test_mutant_voisin_vrai_semi_ouvert():
    """VOISIN VRAI : le membre droit SEMI-OUVERT seg(ℕ,k) au lieu du fermé [0,k]."""
    vk = var(K)
    th = segment_succ_est_intervalle()
    seg_k = E.segment_extremite(_G_main(), ensemble_NN(), vk)
    assert th.conclusion != egal(_seg_main(vk), seg_k)


def test_mutant_substitution_borne():
    """SUBSTITUTION : [0, k+1] au lieu de [0, k] doit être rejeté."""
    vk = var(K)
    th = segment_succ_est_intervalle()
    assert th.conclusion != egal(_seg_main(vk), _interv_main(successeur(vk)))


def test_mutant_pollution_hypothese():
    """POLLUTION : une hypothèse en trop casse l'égalité EXACTE de frozenset."""
    vk = var(K)
    th = segment_succ_est_intervalle()
    pollue = frozenset({_hyp_k(vk), appartient(successeur(vk), ensemble_NN())})
    assert th.hypotheses != pollue
    assert th.hypotheses == frozenset({_hyp_k(vk)})
