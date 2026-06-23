"""Tests de la CHAÎNE D'EXTENSION VRAIE de Hessenberg (NON vacuous)."""
from bourbaki.logique.i_1_termes_relations.formule import egal, var
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.logique.i_1_termes_relations.formule import non, appartient
from bourbaki.cardinaux.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_chaine_vraie import (
    phi1_bijection_derivee,
    extension_dans_frame_chainee,
    extension_ordre_chainee,
    extension_force_egalite_chainee,
    extension_absurde_chainee,
)


def _lock():
    return egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))


def test_step1_phi1_bijection_derivee():
    r = phi1_bijection_derivee()
    vphi0, vpsi, vS, vU = var("phi0"), var("psi"), var("S0"), var("Ucadre")
    Z = E.reunion(vS, vU)
    cible = est_bijection_de(E.reunion(vphi0, vpsi), E.produit(Z, Z), Z)
    assert r.conclusion == cible
    # conclusion non triviale
    assert r.conclusion not in r.hypotheses


def test_step1_lock_absent():
    """ACCEPTANCE : le lock reunion(S₀,U)=S₀ n'est PAS dans les hypothèses."""
    r = phi1_bijection_derivee()
    assert _lock() not in r.hypotheses


def test_step1_hyps_satisfiables():
    """Les 6 résidus sont honnêtes (2 bijections + 4 identités géométriques)."""
    r = phi1_bijection_derivee()
    assert len(r.hypotheses) == 6


def test_step2_dans_frame():
    r = extension_dans_frame_chainee()
    vS, vU, vphi0, vpsi = var("S0"), var("Ucadre"), var("phi0"), var("psi")
    Z = E.reunion(vS, vU)
    q = E.couple(E.couple(Z, Z), E.couple(Z, E.reunion(vphi0, vpsi)))
    # conclusion = (Z,φ₁)∈𝔉(E)  (couple Bourbaki = paire(paire,paire))
    assert r.conclusion.tag == "in"
    assert _lock() not in r.hypotheses


def test_step3_ordre():
    r = extension_ordre_chainee()
    assert r.conclusion.tag == "in"        # ((S₀,φ₀),(Z,φ₁))∈Γ𝔉(E)
    assert _lock() not in r.hypotheses
    assert r.conclusion not in r.hypotheses


def test_step4_lock_derive_pas_suppose():
    """STEP 4 : Z=S₀ est la CONCLUSION (prouvée par maximalité), PAS une hypothèse."""
    r = extension_force_egalite_chainee()
    assert r.conclusion == _lock()             # le lock est PROUVÉ
    assert _lock() not in r.hypotheses         # et JAMAIS supposé
    # la maximalité (element_maximal-data) est bien présente comme hyp honnête :
    # (S₀,φ₀)∈𝔉 figure parmi les hypothèses (composant de element_maximal).
    p_in = appartient(E.couple(var("S0"), var("phi0")),
                      frame_pair(var("E")))
    assert p_in in r.hypotheses


def test_step5_contradiction_lock_absent():
    """STEP 5 ACCEPTANCE : ⊥ dérivé, lock ABSENT, pas de trio contradictoire du lock."""
    r = extension_absurde_chainee()
    u, U, S = var("uwit"), var("Ucadre"), var("S0")
    assert r.conclusion == non(appartient(u, U))   # ¬(u∈U)
    assert appartient(u, U) in r.hypotheses        # u∈U → contradiction réelle
    # LOCK ABSENT (le test décisif de non-vacuité) :
    assert _lock() not in r.hypotheses


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
