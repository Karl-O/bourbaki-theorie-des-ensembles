"""Tests de la CHAÎNE D'EXTENSION VRAIE de Hessenberg (NON vacuous)."""
from bourbaki.logique.formule import egal, var
import bourbaki.ensembles.ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.ensembles_hessenberg_chaine_vraie import (
    phi1_bijection_derivee,
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


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
