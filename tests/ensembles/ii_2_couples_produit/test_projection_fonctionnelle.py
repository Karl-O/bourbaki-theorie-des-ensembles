"""Tests §II.2 — CARACTÉRISATION FONCTIONNELLE DES PROJECTIONS (Bourbaki E II.7).

On APPELLE les théorèmes (impératif), puis on vérifie : conditionnel HONNÊTE
(est_clos == False, exactement 2 hypothèses), conclusion == cible reconstruite
À LA MAIN (mêmes constructeurs/liants : ⇔, ∃, couple, pr₁/pr₂), hypothèses ==
{ univoque, est_couple } reconstruites elles aussi à la main, et theorie == 22.

  pr1 : { univoque_x((∃y)(z=(x,y))), est_couple(z) } ⊢ (∃y)(z=(x,y)) ⇔ x = pr₁z
  pr2 : { univoque_y((∃x)(z=(x,y))), est_couple(z) } ⊢ (∃x)(z=(x,y)) ⇔ y = pr₂z
"""
from bourbaki.logique.i_1_termes_relations.formule import (
    var, egal, existe, equiv, et, impl, pourtout)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
import bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle as M

x, y, z, u, v = var("x"), var("y"), var("z"), var("u"), var("v")


def _est_couple_raw():
    """est_couple(z) = (∃x)(∃y)(z=(x,y)) — reconstruit à la main."""
    return existe("x", existe("y", egal(z, E.couple(x, y))))


def test_pr1_cible_litterale_et_hyps_honnetes():
    t = M.pr1_caracterisation()
    assert not t.est_clos                                  # conditionnel honnête
    # cible : (∃y)(z=(x,y)) ⇔ x = pr₁z   (constructeurs de l'énoncé)
    R1 = existe("y", egal(z, E.couple(x, y)))
    attendu = equiv(R1, egal(x, E.pr1(z)))
    assert t.conclusion == attendu == M.pr1_caracterisation_cible()
    # hypothèses == { univoque_x(R1), est_couple(z) } reconstruites à la main
    uni_x = pourtout("u", pourtout("v", impl(
        et(existe("y", egal(z, E.couple(u, y))),
           existe("y", egal(z, E.couple(v, y)))),
        egal(u, v))))
    assert set(t.hypotheses) == {uni_x, _est_couple_raw()}


def test_pr2_cible_litterale_et_hyps_honnetes():
    t = M.pr2_caracterisation()
    assert not t.est_clos
    # cible : (∃x)(z=(x,y)) ⇔ y = pr₂z
    R2 = existe("x", egal(z, E.couple(x, y)))
    attendu = equiv(R2, egal(y, E.pr2(z)))
    assert t.conclusion == attendu == M.pr2_caracterisation_cible()
    # hypothèses == { univoque_y(R2), est_couple(z) }
    uni_y = pourtout("u", pourtout("v", impl(
        et(existe("x", egal(z, E.couple(x, u))),
           existe("x", egal(z, E.couple(x, v)))),
        egal(u, v))))
    assert set(t.hypotheses) == {uni_y, _est_couple_raw()}


def test_theorie_inchangee_22():
    M.pr1_caracterisation()
    M.pr2_caracterisation()
    assert len(theorie_ensembles().axiomes) == 22
