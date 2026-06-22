"""Tests du CADRE PLAT (déverrouillage hyp[2] de Hessenberg a²=a)."""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.formule import var, egal
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.entiers.ensembles_infinis import est_infini
import bourbaki.cardinaux.ensembles_cadre_plat as m


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_P1_blocs_disjoints():
    """P1 : les 3 blocs plats deux à deux disjoints + bloc-tête, sous U∩S₀=∅."""
    t = m.cadre_plat_blocs_disjoints()
    cible = m.cadre_plat_blocs_disjoints_cible()
    # conclusion == conséquent de la cible
    assert t.conclusion == cible.sous[1]
    # une seule hypothèse honnête : U∩S₀=∅
    assert len(t.hypotheses) == 1
    assert E.sont_disjoints(var("Ucadre"), var("S0")) in t.hypotheses
    # non vacueux
    assert t.conclusion not in t.hypotheses


def test_P2_cardinal():
    """P2 : Card(F_plain) = Card S₀ sous les 5 hyps honnêtes (3𝔟=𝔟)."""
    t = m.cadre_plat_cardinal()
    assert t.conclusion == m.cadre_plat_cardinal_cible()
    vS, vU = var("S0"), var("Ucadre")
    b = cardinal(vS)
    bb = produit_cardinal_binaire(b, b)
    expected = {
        egal(b, cardinal(vU)),
        egal(bb, b),
        est_cardinal(b),
        est_infini(b),
        E.sont_disjoints(vU, vS),
    }
    assert set(t.hypotheses) == expected
    assert t.conclusion not in t.hypotheses


def test_P3_bijection():
    """P3 : (∃ψ) bij(ψ, F_plain, U) sous les 5 hyps honnêtes."""
    t = m.cadre_plat_bijection()
    assert t.conclusion == m.cadre_plat_bijection_cible()
    assert t.conclusion not in t.hypotheses
    # mêmes 5 gardes honnêtes que P2 (Card S0=Card U notamment).
    assert len(t.hypotheses) == 5
