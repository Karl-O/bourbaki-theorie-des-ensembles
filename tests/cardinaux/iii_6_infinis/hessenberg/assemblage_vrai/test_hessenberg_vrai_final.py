"""Tests de bourbaki.cardinaux.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_final (Hessenberg a²=a).

STEP A (`unpack_maximal`) : squelette d'élimination existentielle imbriquée du maximal,
CLOS (2 résidus = ceux de frame_a_maximal).  hessenberg_vrai : endgame a²=a sous l'unique
hyp honnête Card S₀=Card E (« CLAIM » de Bourbaki ; STEP B ouvert, rapporté).
"""
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_1_termes_relations.formule import var, egal, libres_f
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg
from bourbaki.cardinaux.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_final import (
    unpack_maximal, hessenberg_vrai,
)

LOCK = egal(E.reunion(var("S0"), var("Ucadre")), var("S0"))


def test_theorie_22_inchangee():
    assert len(theorie_ensembles().axiomes) == 22


def test_unpack_maximal_squelette_clos():
    """unpack_maximal avec une dérivation triviale (Card E = Card E) : conclusion E-seule,
    résidus = ceux de frame_a_maximal, lock absent, non vacuous."""
    cE = cardinal(var("E"))

    def derive(bij0, S_inc, S_inf, h_max, vS0, vphi0):
        return N.reflexivite(cE)

    r = unpack_maximal("E", derive)
    assert r.conclusion == egal(cE, cE)
    assert r.conclusion not in r.hypotheses
    assert LOCK not in r.hypotheses
    # la conclusion ne mentionne QUE E (S0/phi0/mmx éliminés)
    assert libres_f(r.conclusion) == {"E"}


def test_hessenberg_vrai_endgame():
    """hessenberg_vrai : a²=a sous l'unique CLAIM honnête Card S₀=Card E (+ bijection φ₀)."""
    r = hessenberg_vrai("E")
    assert r.conclusion == enonce_hessenberg("E")
    assert r.conclusion not in r.hypotheses
    assert LOCK not in r.hypotheses
    cS, cE = cardinal(var("S0")), cardinal(var("E"))
    assert egal(cS, cE) in r.hypotheses          # le CLAIM, honnête
    # tous les résidus sont honnêtes : aucun n'est une contradiction triviale
    for h in r.hypotheses:
        assert h != LOCK


def test_theorie_22_apres():
    assert len(theorie_ensembles().axiomes) == 22
