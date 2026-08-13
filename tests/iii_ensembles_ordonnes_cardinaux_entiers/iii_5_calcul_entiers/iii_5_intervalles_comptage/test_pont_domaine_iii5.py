"""Tests MIROIR de `ensembles_pont_domaine_iii5` — cibles RECONSTRUITES à la main.

Aucune cible n'est empruntée au module testé : `seg(ℕ,k+1)`, `[0,k]`, `dom(f|·)`,
le τ de M et les résidus C62 sont réassemblés ICI depuis les définitions primitives.
Les hypothèses sont assertées par ÉGALITÉ EXACTE de frozenset — y compris celles du
`domaine_restriction_est_intervalle`, où un `len(th.hypotheses) == 4` laissait jadis
les trois résidus C62 NON épinglés par identité.

🎯 F1 — LE BON ORDRE N'EST PAS UN RÉSIDU.  `dom_restriction_seg` sort sous
{ bo, essais_bien_formes, rule_codomain } ; `bo = est_bien_ordonne(R_G≤, ℕ)` est un
THÉORÈME sur le VRAI ℕ (`bo_graphe_NN`, CLOS).  Le test le montre DES DEUX CÔTÉS :
bo EST une hypothèse de la brique amont, et bo N'EST PLUS une hypothèse ici — sinon
le module ferait un affaiblissement gratuit.

⚠️ slow, MESURÉ le 2026-07-27 (fichier seul, machine chargée) : 9 passed en 581 s,
dont 545 s pour le setup du PREMIER théorème (`bo_graphe_NN` + `fini_downward_garde_thm`
+ `N_existe`) ; le capstone qui suit ne coûte plus que 33 s.  Les théorèmes lourds sont
construits UNE FOIS (fixtures de portée module) : les rebâtir par test coûterait des
minutes sans rien prouver de plus.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, tau, appartient,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import G_ordre_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import dom_restriction_seg

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_pont_domaine_iii5 import (
    domaine_restriction_est_intervalle, max_domaine_restriction_succ,
)

pytestmark = pytest.mark.slow

K, V, ZCARD = "kpd", "Vfac62", "Z"


# ── cibles RECONSTRUITES à la main, hors du module ───────────────────────────
def _R_main():
    """La RELATION ≤ portée par G_≤, réassemblée : (a,b) ↦ ((a,b) ∈ G_≤).

    Toujours nécessaire là où une relation CALLABLE est attendue (`est_bien_ordonne`) ;
    le TERME de segment, lui, prend désormais le GRAPHE (`_G_main`)."""
    return lambda a, b: appartient(E.couple(a, b), G_ordre_NN())


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


def _dom_main(k):
    """dom( f | seg(ℕ,k+1) ) réassemblé."""
    return E.dom(E.restriction(fonction_globale(ensemble_NN(), V), _seg_main(k)))


def _max_main(A):
    """M(A) réassemblé : τ_m( est_plus_grand_element(≤_card, A, m) ), liants « m »/« x »."""
    return tau("m", E.est_plus_grand_element(inf_egal_card, A, var("m"), "x"))


def _bo_main():
    """bo = est_bien_ordonne(R_G≤, ℕ) réassemblé — le résidu C62 qui N'EN EST PAS un."""
    return E.est_bien_ordonne(_R_main(), ensemble_NN())


def _hyp_k(k):
    return appartient(k, ensemble_NN())


def _residus_regle():
    """Les DEUX résidus HONNÊTES restants, reconstruits à la main : les DONNÉES de T.

    `zcard=ZCARD` est ÉPINGLÉ (pas laissé au défaut) : il fixe le liant du `cardinal`
    interne de la règle, donc l'identité `==` des hypothèses règle-dépendantes — deux
    valeurs donnent des α-variants que le noyau n'identifie PAS.  Une règle FRAÎCHE est
    reconstruite ici : le test ne se contente pas de comparer le module à lui-même."""
    T = regle_factorielle(zcard=ZCARD)
    NN, Gle = ensemble_NN(), G_ordre_NN()
    return frozenset({
        essais_bien_formes(T, NN, Gle, V, "qwf", "wwf", "zess"),
        rule_codomain(T, V, "zess"),
    })


def _hypotheses_attendues(k):
    """Le frozenset EXACT attendu : 2 résidus de règle + { k ∈ ℕ }.  PAS de `bo`."""
    return _residus_regle() | frozenset({_hyp_k(k)})


# ══════════════════════════════════════════════════════════════════════════════
@pytest.fixture(scope="module")
def _regle():
    return regle_factorielle(zcard=ZCARD)


@pytest.fixture(scope="module")
def _amont(_regle):
    """`dom_restriction_seg` BRUT (3 résidus C62) — la brique AVANT décharge du bo."""
    return dom_restriction_seg(_regle, ensemble_NN(), G_ordre_NN(), V,
                               successeur(var(K)))


@pytest.fixture(scope="module")
def _domaine(_regle):
    return domaine_restriction_est_intervalle(_regle, V)


@pytest.fixture(scope="module")
def _capstone(_regle):
    return max_domaine_restriction_succ(_regle, V)


# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_amont_a_bien_trois_residus_dont_le_bon_ordre(_amont):
    """🎯 F1 (côté AMONT) : la brique `dom_restriction_seg` A bien `bo` en hypothèse.

    Sans ceci, « bo est absent en aval » serait vide de sens : il faut d'abord
    établir qu'il y ÉTAIT, et que la formule déchargée est LITTÉRALEMENT celle-ci."""
    vk = var(K)
    assert _amont.conclusion == egal(_dom_main(vk), _seg_main(vk))
    assert len(_amont.hypotheses) == 3
    assert _bo_main() in _amont.hypotheses
    assert _amont.hypotheses == _residus_regle() | frozenset({_bo_main()})


def test_domaine_restriction_est_intervalle(_domaine):
    """{ 2 résidus C62, k ∈ ℕ } ⊢ dom(f|seg(ℕ,k+1)) = [0,k]  — frozenset EXACT.

    ⚠️ C'est ICI que l'ancien test se contentait de `len(th.hypotheses) == 4` : les
    résidus n'étaient épinglés par IDENTITÉ nulle part."""
    vk = var(K)
    assert _domaine.conclusion == egal(_dom_main(vk), _interv_main(vk))
    assert _domaine.hypotheses == _hypotheses_attendues(vk)
    assert len(_domaine.hypotheses) == 3
    assert _domaine.conclusion not in _domaine.hypotheses


def test_domaine_ne_porte_plus_le_bon_ordre(_domaine):
    """🎯 F1 (côté AVAL) : `bo` est DÉCHARGÉ — sinon, affaiblissement gratuit."""
    assert _bo_main() not in _domaine.hypotheses


def test_max_domaine_restriction_succ(_capstone, _domaine):
    """🎯 { 2 résidus C62, k ∈ ℕ } ⊢ M( dom(f|seg(ℕ,k+1)) ) = k  — frozenset EXACT."""
    vk = var(K)
    assert _capstone.conclusion == egal(_max_main(_dom_main(vk)), vk)
    assert _capstone.hypotheses == _hypotheses_attendues(vk)   # égalité EXACTE
    assert _capstone.hypotheses == _domaine.hypotheses         # rien d'ajouté par (2)
    assert _bo_main() not in _capstone.hypotheses
    assert _capstone.conclusion not in _capstone.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


# ══════════════════════════════════════════════════════════════════════════════
#  MUTANTS — chaque cible FAUSSE doit être REJETÉE par les mêmes assertions.
#  (Un mutant qui « meurt » sur TypeError ne prouverait rien : ils meurent tous
#   ici sur une INÉGALITÉ de formule, donc sur le contenu mathématique.)
# ══════════════════════════════════════════════════════════════════════════════
def test_mutant_voisin_vrai_plus_petit(_capstone):
    """VOISIN VRAI : M du PLUS PETIT élément (τ sur est_plus_petit_element) ≠ M."""
    vk = var(K)
    petit = tau("m", E.est_plus_petit_element(inf_egal_card, _dom_main(vk), var("m"), "x"))
    assert _capstone.conclusion != egal(petit, vk)


def test_mutant_alpha_variante_liant_tau(_capstone):
    """ALPHA-VARIANTE : le τ de M sur un AUTRE liant n'est PAS identifié par le noyau."""
    vk = var(K)
    alpha = tau("m2", E.est_plus_grand_element(inf_egal_card, _dom_main(vk),
                                               var("m2"), "x"))
    assert _capstone.conclusion != egal(alpha, vk)


def test_mutant_pollution_par_le_bon_ordre(_capstone):
    """POLLUTION : remettre `bo` dans le frozenset attendu doit FAIRE ÉCHOUER l'égalité.

    C'est le mutant qui garde F1 honnête : si un jour la décharge disparaissait, le
    frozenset du capstone redeviendrait `_hypotheses_attendues ∪ {bo}` et ce test
    (comme `test_max_domaine_restriction_succ`) tomberait."""
    vk = var(K)
    pollue = _hypotheses_attendues(vk) | frozenset({_bo_main()})
    assert _capstone.hypotheses != pollue
    assert len(pollue) == 4


def test_mutant_residu_de_complaisance(_capstone):
    """SUBSTITUTION : un résidu bâti sur une AUTRE règle (zcard ≠) n'est pas identifié."""
    vk = var(K)
    autre = regle_factorielle(zcard="Zautre")
    faux = frozenset({
        essais_bien_formes(autre, ensemble_NN(), G_ordre_NN(), V, "qwf", "wwf", "zess"),
        rule_codomain(autre, V, "zess"),
        _hyp_k(vk),
    })
    assert _capstone.hypotheses != faux
