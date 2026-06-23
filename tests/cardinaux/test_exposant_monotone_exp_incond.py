"""Tests — monotonie de l'exponentiation cardinale en l'EXPOSANT, inconditionnelle.

    support_monotone_exposant   ⊢ (C≤D et A≠∅) ⇒ 𝓕(C;A)≤𝓕(D;A)   [0 hyp]
    exposant_monotone_exposant  ⊢ (c≤d et a≠0) ⇒ (a^c ≤ a^d)       [0 hyp, CLEAN]

theorie_ensembles INCHANGÉE (22 axiomes).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, et, non, egal, impl
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.cardinaux.arithmetique.ensembles_exposant_monotone_exp_incond import (
    support_monotone_exposant, exposant_monotone_exposant,
    support_extension_domaine, support_le_image)


def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_support_le_image_palier1():
    """Palier 1 : {inj(κ,C,D)} ⊢ 𝓕(C;A) ≤ 𝓕(κ⟨C⟩;A)."""
    t = support_le_image()
    vk, vc = var("kappa"), var("C")
    imgC = E.image(vk, vc)
    assert t.conclusion == inf_egal_card(E.applications(vc, var("A")),
                                         E.applications(imgC, var("A")))


def test_support_extension_domaine_palier2():
    """Palier 2 : {S⊆D, a₀∈A} ⊢ 𝓕(S;A) ≤ 𝓕(D;A)  (recollement-prolongement)."""
    t = support_extension_domaine()
    vs, vd, va = var("S"), var("D"), var("A")
    assert t.conclusion == inf_egal_card(E.applications(vs, va), E.applications(vd, va))
    # hypothèses honnêtes : exactement S⊆D et a₀∈A
    assert len(t.hypotheses) == 2


def test_support_monotone_exposant_close():
    """(C≤D et A≠∅) ⇒ 𝓕(C;A)≤𝓕(D;A)  CLOS, 0 hyp."""
    t = support_monotone_exposant()
    assert t.est_clos
    assert len(t.hypotheses) == 0
    vc, vd, va = var("C"), var("D"), var("A")
    cible = impl(et(inf_egal_card(vc, vd), non(egal(va, E.VIDE))),
                 inf_egal_card(E.applications(vc, va), E.applications(vd, va)))
    assert t.conclusion == cible


def test_exposant_monotone_exposant_clean():
    """(c≤d et a≠0) ⇒ (a^c ≤ a^d)  CLOS, 0 hyp, CLEAN (aucun antécédent de support)."""
    t = exposant_monotone_exposant()
    assert t.est_clos
    assert len(t.hypotheses) == 0
    va, vc, vd = var("a"), var("c"), var("d")
    cible = impl(et(inf_egal_card(vc, vd), non(egal(va, E.VIDE))),
                 inf_egal_card(exposant_cardinal_binaire(va, vc),
                               exposant_cardinal_binaire(va, vd)))
    assert t.conclusion == cible
    assert len(E.theorie_ensembles().axiomes) == 22
