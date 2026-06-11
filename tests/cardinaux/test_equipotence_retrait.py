"""Tests — GEN « retrait d'un point de deux ensembles équipotents » (E.III.4) et
décharge inconditionnelle du LEMME N (cardinal_pas_entre).

Vérifie :
  • image_diff      : {bij(F,X,Y), a∈X} ⊢ image(F, X∖{a}) = Y∖{F(a)}  (2 hyps, clos sous hyps) ;
  • eq_retrait_via_bijection (CORE) : ⊢ bij(F,X,Y) ⇒ (a∈X ⇒ Eq(X∖{a}, Y∖{F(a)}))  (clos) ;
  • eq_retrait_meme_ensemble : ⊢ (p∈Y et q∈Y) ⇒ Eq(Y∖{p}, Y∖{q})  (clos, via transposition) ;
  • gen_corps       : ⊢ (Eq(X,Y) et x∈X et y∈Y) ⇒ Eq(X∖{x}, Y∖{y})  (corps de GEN, clos) ;
  • equipotence_retrait_un_point_general : ⊢ GEN  (universel, clos) ;
  • cardinal_pas_entre_inconditionnel : ⊢ est_cardinal(b) ⇒ cardinal_pas_entre(b,c)  (clos) ;
  • theorie_ensembles() = 22  (intangible).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, et, appartient, impl
from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent, est_cardinal
from bourbaki.cardinaux.ensembles_equipotence_retrait import (
    image_diff, eq_retrait_via_bijection, eq_retrait_meme_ensemble,
    gen_corps, equipotence_retrait_un_point_general,
    cardinal_pas_entre_inconditionnel)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_image_diff():
    """{bij(F,X,Y), a∈X} ⊢ image(F, X∖{a}) = Y∖{F(a)}."""
    t = image_diff()
    vF, vX, vY, va = var("F"), var("X"), var("Y"), var("a")
    hyps = set(t.hypotheses)
    assert len(hyps) == 2
    assert est_bijection_de(vF, vX, vY) in hyps
    assert appartient(va, vX) in hyps
    Fa = E.valeur(vF, va)
    cible = E.egal(E.image(vF, E.difference(vX, E.singleton(va))),
                   E.difference(vY, E.singleton(Fa)))
    assert t.conclusion == cible


def test_eq_retrait_via_bijection_clos():
    """⊢ bij(F,X,Y) ⇒ (a∈X ⇒ Eq(X∖{a}, Y∖{F(a)}))  (CORE, clos)."""
    t = eq_retrait_via_bijection()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    vB, vX, vY, va = var("Bij"), var("X"), var("Y"), var("a")
    ante, cons = antecedent_consequent(t.conclusion)
    assert ante == est_bijection_de(vB, vX, vY)
    inner_a, inner_eq = antecedent_consequent(cons)
    assert inner_a == appartient(va, vX)
    Ba = E.valeur(vB, va)
    assert inner_eq == equipotent(E.difference(vX, E.singleton(va)),
                                  E.difference(vY, E.singleton(Ba)))


def test_eq_retrait_meme_ensemble_clos():
    """⊢ (p∈Y et q∈Y) ⇒ Eq(Y∖{p}, Y∖{q})  (clos)."""
    t = eq_retrait_meme_ensemble()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    vY, vp, vq = var("Y"), var("p"), var("yy")
    cible = impl(et(appartient(vp, vY), appartient(vq, vY)),
                 equipotent(E.difference(vY, E.singleton(vp)),
                            E.difference(vY, E.singleton(vq))))
    assert t.conclusion == cible


def test_gen_corps_clos():
    """⊢ (Eq(X,Y) et xpt∈X et ypt∈Y) ⇒ Eq(X∖{xpt}, Y∖{ypt})  (corps de GEN, clos)."""
    t = gen_corps()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    vX, vY, vxp, vyp = var("X"), var("Y"), var("xpt"), var("ypt")
    cible = impl(et(et(equipotent(vX, vY), appartient(vxp, vX)), appartient(vyp, vY)),
                 equipotent(E.difference(vX, E.singleton(vxp)),
                            E.difference(vY, E.singleton(vyp))))
    assert t.conclusion == cible


def test_gen_universel_clos():
    """⊢ GEN := (∀X)(∀Y)(∀x)(∀ypt)(…)  (universel, clos, forme canonique τ_y)."""
    t = equipotence_retrait_un_point_general()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    # forme canonique : pas de « @0 », τ_y préservé
    assert "@0" not in repr(t.conclusion)


def test_gen_interchangeable_avec_surgery():
    """La GEN canonique, instanciée aux termes de la surgery (c+1, C⊔{∅}, q, *), donne
    EXACTEMENT la même instance que la GEN-littéral de ensembles_retrait_surgery."""
    from bourbaki.entiers.ensembles_retrait_surgery import (
        equipotence_retrait_un_point_general as SURG_GEN)
    from bourbaki.entiers.ensembles_retrait_point import _S, _STAR
    from bourbaki.entiers.ensembles_entiers import successeur
    from bourbaki.logique import noyau_abrege as N
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
    vc, vq = var("c"), var("q")
    succ_c, S = successeur(vc), _S(vc)

    def inst4(formula):
        h = N.assume(formula)
        return instancie(instancie(instancie(instancie(h, succ_c), S), vq), _STAR)

    mine = inst4(equipotence_retrait_un_point_general().conclusion)
    surg = inst4(SURG_GEN())
    assert mine.conclusion == surg.conclusion


def test_cardinal_pas_entre_inconditionnel():
    """⊢ est_cardinal(b) ⇒ cardinal_pas_entre(b,c)  (LEMME N, GEN DÉCHARGÉE, clos)."""
    from bourbaki.entiers.ensembles_retrait_surgery import cardinal_pas_entre_mod_general
    t = cardinal_pas_entre_inconditionnel()
    assert t.est_clos
    assert len(set(t.hypotheses)) == 0
    ante, cons = antecedent_consequent(t.conclusion)
    assert ante == est_cardinal(var("b"))
    # le conséquent EST cardinal_pas_entre(b,c) (= conséquent du conditionnel surgery)
    _, surg_cons = antecedent_consequent(cardinal_pas_entre_mod_general().conclusion)
    assert cons == surg_cons
