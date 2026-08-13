"""Test §III.2 — ASSEMBLAGE de fusion_hyp (Lemme 1) MODULO la SEULE coïncidence.

`fusion_depuis_coincidence` RÉDUIT l'hypothèse de FUSION du Lemme 1 §III.2
(`ensembles_temoin_deux_couples.fusion_hyp`) aux DEUX SEULES hypothèses :
  • est_bien_ordonne(R,E)  (arrière-plan structurel) ;
  • coincidence_univ       (la SEULE coïncidence géométrique reportée, Lemme 1).
Conclusion == T2.fusion_hyp LITTÉRALEMENT ; non tautologique ; theorie=22.
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.coincidence_fusion import ensembles_fusion_assemblage as FA
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.temoins_comparabilite import ensembles_temoin_deux_couples as T2


def test_fusion_depuis_coincidence():
    """{ est_bien_ordonne(R,E), coincidence_univ } ⊢ fusion_hyp(u,v,u',v')."""
    t = FA.fusion_depuis_coincidence()
    assert not t.est_clos
    # conclusion == ensembles_temoin_deux_couples.fusion_hyp (LITTÉRALEMENT)
    assert t.conclusion == FA.fusion_depuis_coincidence_cible()
    # NON vacueux : fusion_hyp n'est aucune hypothèse
    assert t.conclusion not in t.hypotheses


def test_exactement_deux_hypotheses():
    """Les hypothèses sont EXACTEMENT { est_bien_ordonne(R,E), coincidence_univ }."""
    t = FA.fusion_depuis_coincidence()
    assert len(t.hypotheses) == 2
    assert set(t.hypotheses) == set(FA.fusion_depuis_coincidence_hypotheses())


def test_coincidence_est_load_bearing():
    """coincidence_univ est une VRAIE hypothèse (load-bearing), ≠ conclusion."""
    t = FA.fusion_depuis_coincidence()
    cu = FA.coincidence_univ()
    assert cu in set(t.hypotheses)        # consommée
    assert cu != t.conclusion             # non tautologique


def test_conclusion_est_bien_fusion_hyp():
    """La conclusion est EXACTEMENT T2.fusion_hyp aux points schématiques ua,va,ub,vb."""
    t = FA.fusion_depuis_coincidence()
    fh = T2.fusion_hyp("E", "R", "F", "Rp", "ua", "va", "ub", "vb", "S", "T", "phi")
    assert t.conclusion == fh


def test_swap_temoin_commun_clos():
    """Le SWAP des antécédents est CLOS et inconditionnel."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences import ensembles_trichotomie_coherences as COH
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    sw = FA._swap_temoin_commun("E", "R", "F", "Rp", "u", "v", "up", "vp")
    assert sw.est_clos
    src = COH.temoin_commun_h("E", "R", "F", "Rp", "up", "vp", "u", "v")
    tgt = COH.temoin_commun_h("E", "R", "F", "Rp", "u", "v", "up", "vp")
    assert sw.conclusion == impl(src, tgt)


def test_parametrable():
    t = FA.fusion_depuis_coincidence("Ep", "Rp", "Fp", "Rq")
    assert not t.est_clos
    assert len(t.hypotheses) == 2


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
