"""Tests §II.4 — propositions restantes (famille constante, reparamétrage surjectif).

Vérifie la conclusion EXACTE (== cible verbatim) et .est_clos de chaque théorème.
theorie_ensembles() reste à 22 axiomes (aucun axiome neuf en théorie principale).
"""
from bourbaki.logique.formule import (var, egal, et, impl, appartient, existe,
                                       pourtout, inclus)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles import ensembles_chap2_props_restantes as P


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reunion_constante():
    vf, vI, va = var("X"), var("I"), var("a")
    vi = var("i")
    cst = pourtout("i", pourtout("k",
        egal(E.valeur_famille(vf, vi), E.valeur_famille(vf, var("k")))))
    hyp = et(cst, appartient(va, vI))
    cible = impl(hyp, egal(E.reunion_famille(vf, vI), E.valeur_famille(vf, va)))
    t = P.reunion_constante()
    assert t.est_clos
    assert t.conclusion == cible


def test_inter_constante():
    vf, vI, va = var("X"), var("I"), var("a")
    vi = var("i")
    cst = pourtout("i", pourtout("k",
        egal(E.valeur_famille(vf, vi), E.valeur_famille(vf, var("k")))))
    hyp = et(cst, appartient(va, vI))
    cible = impl(hyp, egal(E.inter_famille(vf, vI), E.valeur_famille(vf, va)))
    t = P.inter_constante()
    assert t.est_clos
    assert t.conclusion == cible


def test_reparam_reunion_incluse():
    vf, vphi, vI, vK = var("X"), var("phi"), var("I"), var("K")
    vk = var("k")
    phik = E.valeur(vphi, vk)
    fam_r = P.famille_reparam(vf, vphi)
    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    cible = impl(dom_hyp,
                 inclus(E.reunion_famille(fam_r, vK), E.reunion_famille(vf, vI)))
    t = P.reparam_reunion_incluse()
    assert t.est_clos
    assert t.conclusion == cible


def test_reparam_reunion_egal_si_surjectif():
    vf, vphi, vI, vK = var("X"), var("phi"), var("I"), var("K")
    vk, vi = var("k"), var("i")
    phik = E.valeur(vphi, vk)
    fam_r = P.famille_reparam(vf, vphi)
    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    surj_hyp = pourtout("i", impl(appartient(vi, vI),
                                  existe("k", et(appartient(vk, vK), egal(phik, vi)))))
    hyp = et(dom_hyp, surj_hyp)
    cible = impl(hyp,
                 egal(E.reunion_famille(fam_r, vK), E.reunion_famille(vf, vI)))
    t = P.reparam_reunion_egal_si_surjectif()
    assert t.est_clos
    assert t.conclusion == cible
