"""Test §III.2 — construction couvrante (cœur de l'assemblage de fusion_hyp, Lemme 1)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.temoins_comparabilite import ensembles_temoin_couvrant as TCV


def test_temoin_commun_couvrant():
    """{ seg S₂, seg T₂, iso(φ₂,S₂,T₂), u∈S₁, S₁⊂S₂, v=φ₁(u), φ₁(u)=φ₂(u),
         u'∈S₂, v'=φ₂(u') } ⊢ temoin_commun_h(u,v,u',v')."""
    t = TCV.temoin_commun_couvrant()
    assert not t.est_clos
    assert len(t.hypotheses) == 9
    assert t.conclusion == TCV.temoin_commun_couvrant_cible()
    assert t.conclusion not in t.hypotheses


def test_parametrable():
    t = TCV.temoin_commun_couvrant("Ep", "Rp", "Fp", "Rq")
    assert len(t.hypotheses) == 9


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
