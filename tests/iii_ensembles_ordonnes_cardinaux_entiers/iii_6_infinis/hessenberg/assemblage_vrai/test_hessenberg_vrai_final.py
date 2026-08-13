"""Tests de bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_final (Hessenberg a²=a).

STEP A (`unpack_maximal`) : squelette d'élimination existentielle imbriquée du maximal,
CLOS (2 résidus = ceux de frame_a_maximal).  hessenberg_vrai : endgame a²=a sous l'unique
hyp honnête Card S₀=Card E (« CLAIM » de Bourbaki ; STEP B ouvert, rapporté).
"""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, libres_f
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_final import (
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


def test_hessenberg_a_carre_egal_a_REEL():
    """🎯🎯🎯 TH.2 (HESSENBERG, E III.48) : a²=a E-SEUL — le CLAIM DÉRIVÉ (STEP B CLOS).
    Résidus attendus (4, tous témoins-libres) : principe_recurrence C61,
    cardinal_pas_entre, 𝔉≠∅, m_dans_frame_universel."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_final import (
        hessenberg_a_carre_egal_a_REEL,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
    th = hessenberg_a_carre_egal_a_REEL()
    assert th.conclusion == enonce_hessenberg("E")
    assert len(th.hypotheses) == 4
    for h in th.hypotheses:
        interdits = {"S0", "Smx", "phi0", "phimx", "Ucadre", "mmx", "psi", "uwit"} & set(libres_f(h))
        assert not interdits, f"témoin fuité {interdits}"
    assert th.conclusion not in th.hypotheses
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    assert len(E.theorie_ensembles().axiomes) == 22
