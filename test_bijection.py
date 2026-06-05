"""Test §II.3.7/§III.3 — F⁻¹ fonctionnel quand F est une application injective (Prop. 7)."""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_bijection import reciproque_fonctionnelle


def test_reciproque_fonctionnelle():
    vF, vX = var("F"), var("X")
    t = reciproque_fonctionnelle("F", "X")
    assert t.conclusion == E.est_fonctionnel(E.reciproque(vF))
    # hypothèses = exactement {F fonctionnel, dom F = X, F injective sur X}
    assert t.hypotheses == {E.est_fonctionnel(vF), egal(E.dom(vF), vX),
                            E.injective_dans(vF, vX)}


def test_reciproque_domaine():
    from bourbaki.logique.formule import egal
    from bourbaki.cardinaux.ensembles_bijection import reciproque_domaine
    vF, vX, vY = var("F"), var("X"), var("Y")
    t = reciproque_domaine("F", "X", "Y")
    assert t.conclusion == egal(E.dom(E.reciproque(vF)), vY)
    assert t.hypotheses == {egal(E.dom(vF), vX), egal(E.image(vF, vX), vY)}


def test_image_reciproque():
    from bourbaki.logique.formule import egal
    from bourbaki.cardinaux.ensembles_bijection import image_reciproque
    vF, vX, vY = var("F"), var("X"), var("Y")
    t = image_reciproque("F", "X", "Y")
    assert t.conclusion == egal(E.image(E.reciproque(vF), vY), vX)
    assert t.hypotheses == {egal(E.dom(vF), vX), egal(E.image(vF, vX), vY)}


def test_reciproque_injective():
    from bourbaki.cardinaux.ensembles_bijection import reciproque_injective
    vF, vX, vY = var("F"), var("X"), var("Y")
    t = reciproque_injective("F", "X", "Y")
    assert t.conclusion == E.injective_dans(E.reciproque(vF), vY)
    assert t.hypotheses == {E.est_fonctionnel(vF), egal(E.dom(vF), vX),
                            egal(E.image(vF, vX), vY)}


def test_equipotence_symetrique():
    from bourbaki.logique.formule import impl
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    from bourbaki.cardinaux.ensembles_bijection import equipotence_symetrique
    vX, vY = var("X"), var("Y")
    t = equipotence_symetrique("F", "X", "Y")
    assert t.conclusion == impl(equipotent(vX, vY), equipotent(vY, vX)) and t.est_clos


def test_reciproque_est_application():
    from bourbaki.logique.formule import impl, et
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    from bourbaki.cardinaux.ensembles_bijection import reciproque_est_application
    vF, vX, vY = var("F"), var("X"), var("Y")
    t = reciproque_est_application("F", "X", "Y")
    Frec = E.reciproque(vF)
    cible = impl(est_bijection_de(vF, vX, vY),
                 et(E.est_fonctionnel(Frec), egal(E.dom(Frec), vY)))
    assert t.conclusion == cible and t.est_clos


def test_reciproque_est_bijection():
    from bourbaki.logique.formule import impl
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    from bourbaki.cardinaux.ensembles_bijection import reciproque_est_bijection
    vF, vX, vY = var("F"), var("X"), var("Y")
    t = reciproque_est_bijection("F", "X", "Y")
    Frec = E.reciproque(vF)
    cible = impl(est_bijection_de(vF, vX, vY), est_bijection_de(Frec, vY, vX))
    assert t.conclusion == cible and t.est_clos


def test_composee_image():
    from bourbaki.cardinaux.ensembles_bijection import composee_image
    vG, vF, vX, vY, vZ = var("G"), var("F"), var("X"), var("Y"), var("Z")
    t = composee_image("G", "F", "X", "Y", "Z")
    assert t.conclusion == egal(E.image(E.composee(vG, vF), vX), vZ)
    assert t.hypotheses == {egal(E.image(vF, vX), vY), egal(E.image(vG, vY), vZ)}


def test_composee_domaine():
    from bourbaki.cardinaux.ensembles_bijection import composee_domaine
    vG, vF, vX, vY = var("G"), var("F"), var("X"), var("Y")
    t = composee_domaine("G", "F", "X", "Y")
    assert t.conclusion == egal(E.dom(E.composee(vG, vF)), vX)
    assert t.hypotheses == {egal(E.dom(vF), vX), egal(E.dom(vG), vY),
                            egal(E.image(vF, vX), vY)}


def test_composee_injective():
    from bourbaki.cardinaux.ensembles_bijection import composee_injective
    vG, vF, vX, vY = var("G"), var("F"), var("X"), var("Y")
    t = composee_injective("G", "F", "X", "Y")
    assert t.conclusion == E.injective_dans(E.composee(vG, vF), vX) and not t.est_clos


def test_equipotence_transitive():
    from bourbaki.logique.formule import et, impl
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    from bourbaki.cardinaux.ensembles_bijection import equipotence_transitive
    vX, vY, vZ = var("X"), var("Y"), var("Z")
    t = equipotence_transitive("F", "G", "X", "Y", "Z")
    cible = impl(et(equipotent(vX, vY), equipotent(vY, vZ)), equipotent(vX, vZ))
    assert t.conclusion == cible and t.est_clos
