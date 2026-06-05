"""Tests V9 — §II.3.4 Fonctions : graphe fonctionnel, valeur f(x), C46."""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, equiv, appartient, existe, pourtout, impl
from bourbaki.ensembles.ensembles_abrege import est_fonctionnel, valeur, couple
from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_dans_graphe, valeur_caracterisation


def test_est_fonctionnel():
    f, u, v, z = var("F"), var("u"), var("v"), var("z")
    assert est_fonctionnel(f) == pourtout("u", pourtout("v", pourtout("z",
        impl(et(appartient(couple(u, v), f), appartient(couple(u, z), f)), egal(v, z)))))


def test_composee_fonctionnelle():
    from bourbaki.ensembles.ensembles_abrege import composee
    from bourbaki.ensembles.fonctions.ensembles_fonctions_composee import composee_fonctionnelle
    vG, vF = var("G"), var("F")
    t = composee_fonctionnelle("G", "F")
    cible = impl(et(est_fonctionnel(vF), est_fonctionnel(vG)),
                 est_fonctionnel(composee(vG, vF)))
    assert t.conclusion == cible and t.est_clos


def test_composition_valeur():
    from bourbaki.logique.formule import existe, appartient
    from bourbaki.ensembles.ensembles_abrege import composee, valeur, couple
    from bourbaki.ensembles.fonctions.ensembles_fonctions_composee import composition_valeur
    vG, vF, vx, vy = var("G"), var("F"), var("x"), var("y")
    t = composition_valeur("G", "F", "x")
    fx = valeur(vF, vx)
    assert t.conclusion == egal(valeur(composee(vG, vF), vx), valeur(vG, fx))
    # hypothèses = exactement {F fonctionnel, G fonctionnel, x∈dom F, f(x)∈dom G}
    assert t.hypotheses == {est_fonctionnel(vF), est_fonctionnel(vG),
                            existe("y", appartient(couple(vx, vy), vF)),
                            existe("y", appartient(couple(fx, vy), vG))}


def test_valeur_dans_graphe():
    vF, vx, vy = var("F"), var("x"), var("y")
    t = valeur_dans_graphe("F", "x")
    assert t.conclusion == appartient(couple(vx, valeur(vF, vx)), vF)
    assert t.hypotheses == {existe("y", appartient(couple(vx, vy), vF))}


def test_valeur_caracterisation():
    vF, vx, vy = var("F"), var("x"), var("y")
    t = valeur_caracterisation("F", "x")
    assert t.conclusion == equiv(appartient(couple(vx, vy), vF), egal(vy, valeur(vF, vx)))
    # hypothèses : F fonctionnel + x dans le domaine
    assert est_fonctionnel(vF) in t.hypotheses
    assert existe("y", appartient(couple(vx, vy), vF)) in t.hypotheses
