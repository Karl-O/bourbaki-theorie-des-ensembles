"""Tests TASK B-finish / C — assemblage HAUT Hessenberg « vrai » (non vacuous)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_vrai_haut import phi1_bijection_moins


def test_phi1_bijection_moins_conclusion_et_lock_absent():
    t = phi1_bijection_moins()
    vS, vU, vphi0, vpsi = var("S0"), var("Ucadre"), var("phi0"), var("psi")
    Z = E.reunion(vS, vU)
    cible = est_bijection_de(E.reunion(vphi0, vpsi), E.produit(Z, Z), Z)
    assert t.conclusion == cible
    # ACCEPTANCE : le lock reunion(S₀,U)=S₀ n'est JAMAIS une hypothèse.
    assert egal(Z, vS) not in t.hypotheses
    # non vacuous
    assert t.conclusion not in t.hypotheses


def test_phi1_bijection_moins_hyp_count_reduit():
    t = phi1_bijection_moins()
    # passe de 6 (phi1_bijection_derivee) à 5 (hyp imgφ₀∪imgψ=Z déchargée).
    assert len(t.hypotheses) == 5
    vS, vU, vphi0, vpsi = var("S0"), var("Ucadre"), var("phi0"), var("psi")
    imgG = E.image(vphi0, E.dom(vphi0))
    imgH = E.image(vpsi, E.dom(vpsi))
    assert egal(E.reunion(imgG, imgH), E.reunion(vS, vU)) not in t.hypotheses


def test_theorie_intacte():
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
    assert len(theorie_ensembles().axiomes) == 22
