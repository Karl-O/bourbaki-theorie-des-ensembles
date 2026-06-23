"""Tests — recollement le long de la somme disjointe (ensembles_restriction_somme).

Chaque test vérifie la CONCLUSION EXACTE du théorème via le noyau abrégé.
"""
from bourbaki.logique.formule import (var, egal, et, ou, non, impl, appartient,
                                       pourtout)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    recollement, membre_reunion_graphes, antecedent_dans_domaine,
    reunion_graphes_fonctionnelle, dom_reunion_graphes,
    domaines_disjoints_si_marques)


def test_membre_reunion_graphes():
    th = membre_reunion_graphes("G", "H", "z")
    vG, vH, vz = var("G"), var("H"), var("z")
    attendu = E.equiv(appartient(vz, E.reunion(vG, vH)),
                      ou(appartient(vz, vG), appartient(vz, vH)))
    assert th.conclusion == attendu
    assert th.hypotheses == frozenset()


def test_antecedent_dans_domaine():
    th = antecedent_dans_domaine("u", "v", "F")
    vu, vv, vF = var("u"), var("v"), var("F")
    attendu = impl(appartient(E.couple(vu, vv), vF), appartient(vu, E.dom(vF)))
    assert th.conclusion == attendu
    assert th.hypotheses == frozenset()


def test_reunion_graphes_fonctionnelle_pivot():
    """LEMME PIVOT : G,H fonctionnels à domaines disjoints ⇒ G∪H fonctionnel."""
    th = reunion_graphes_fonctionnelle("G", "H")
    vG, vH = var("G"), var("H")
    # conclusion exacte = est_fonctionnel(G∪H)
    assert th.conclusion == E.est_fonctionnel(E.reunion(vG, vH))
    # hypothèses : G fonctionnel, H fonctionnel, disjonction des domaines
    disj = pourtout("u", non(et(appartient(var("u"), E.dom(vG)),
                                appartient(var("u"), E.dom(vH)))))
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vG), E.est_fonctionnel(vH), disj})


def test_antecedent_dans_domaine_liant_frais():
    """Liant ∃ FRAIS (y≠"y") : même CONCLUSION que le défaut (α-pont vers AXIOME_DOM)."""
    th_def = antecedent_dans_domaine("u", "v", "F")
    th_fr = antecedent_dans_domaine("u", "v", "F", y="yfrais")
    assert th_fr.conclusion == th_def.conclusion
    assert th_fr.hypotheses == frozenset()


def test_reunion_graphes_fonctionnelle_temoins_frais():
    """Pivot avec témoins FRAIS : conclusion α-équivalente (binders frais), 3 hyps."""
    vG, vH = var("G"), var("H")
    th = reunion_graphes_fonctionnelle("G", "H",
                                       u="uu", v="vv", z="zz", y="yy")
    # conclusion : est_fonctionnel-forme mais liée sur uu/vv/zz (α-équiv. de u/v/z)
    attendu = pourtout("uu", pourtout("vv", pourtout("zz", impl(
        et(appartient(E.couple(var("uu"), var("vv")), E.reunion(vG, vH)),
           appartient(E.couple(var("uu"), var("zz")), E.reunion(vG, vH))),
        egal(var("vv"), var("zz"))))))
    assert th.conclusion == attendu
    disj = pourtout("uu", non(et(appartient(var("uu"), E.dom(vG)),
                                 appartient(var("uu"), E.dom(vH)))))
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vG), E.est_fonctionnel(vH), disj})


def test_dom_reunion_graphes():
    th = dom_reunion_graphes("G", "H")
    vG, vH = var("G"), var("H")
    attendu = egal(E.dom(E.reunion(vG, vH)),
                   E.reunion(E.dom(vG), E.dom(vH)))
    assert th.conclusion == attendu
    assert th.hypotheses == frozenset()


def test_domaines_disjoints_si_marques():
    """Disjonction des domaines déduite de la structure marquée (0≠1)."""
    th = domaines_disjoints_si_marques("G", "H", "B", "C", "u")
    vG, vH, vB, vC, vu = (var("G"), var("H"), var("B"), var("C"), var("u"))
    attendu = non(et(appartient(vu, E.dom(vG)), appartient(vu, E.dom(vH))))
    assert th.conclusion == attendu
    # hypothèses : dom G ⊂ B×{0}, dom H ⊂ C×{1}
    B0 = E.produit(vB, E.singleton(ZERO))
    C1 = E.produit(vC, E.singleton(UN))
    assert th.hypotheses == frozenset({
        E.inclus(E.dom(vG), B0), E.inclus(E.dom(vH), C1)})


def test_recollement_terme():
    """Le recollement est littéralement la réunion des deux graphes."""
    assert recollement("G", "H") == E.reunion(var("G"), var("H"))
