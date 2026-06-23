"""Tests §III.2 — Lemme 1 (témoins communs) depuis DEUX couples de h.

Salvage de l'effort recollement : le cas DIAGONAL (un seul couple ⇒ son iso le couvre)
et le cas GÉNÉRAL (deux couples, conditionnel à l'hypothèse géométrique d'emboîtement/
coïncidence) sont CONSTRUITS via h_membre_donne_temoin (CLOS, iso px,pw) + temoin_commun_
depuis_iso.  Conclusions == cibles COH ; non tautologiques ; theorie=22.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.temoins_comparabilite import ensembles_temoin_deux_couples as T2


def test_temoin_diagonal_depuis_h():
    """{ (u,v)∈h } ⊢ temoin_commun_h(u,v,u,v)  (cas diagonal, via h_membre_donne_temoin)."""
    t = T2.temoin_commun_diagonal_depuis_h()
    assert not t.est_clos
    assert len(t.hypotheses) == 1
    assert t.conclusion == T2.temoin_commun_diagonal_depuis_h_cible()
    assert t.conclusion not in t.hypotheses


def test_temoin_general_deux_couples():
    """{ (u,v)∈h, (u',v')∈h, hyp_géométrique } ⊢ temoin_commun_h(u,v,u',v')  (cas général)."""
    t = T2.temoin_commun_depuis_deux_h_couples()
    assert not t.est_clos
    assert len(t.hypotheses) == 3            # 2 couples + 1 hyp géométrique (emboîtement)
    assert t.conclusion == T2.temoin_commun_depuis_deux_h_couples_cible()
    assert t.conclusion not in t.hypotheses
    # 2 hypothèses = les couples (u,v)∈h, (u',v')∈h
    incoups = [h for h in t.hypotheses if h.tag == "in"]
    assert len(incoups) == 2


def test_inv_et_fonc_general():
    ti = T2.temoin_inv_depuis_deux_h_couples()
    tf = T2.temoin_fonc_depuis_deux_h_couples()
    assert not ti.est_clos and not tf.est_clos
    assert ti.conclusion == T2.temoin_inv_depuis_deux_h_couples_cible()
    assert tf.conclusion == T2.temoin_fonc_depuis_deux_h_couples_cible()


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
