"""Tests — CANTOR–BERNSTEIN, CLÔTURE (Corollaire 2 du Théorème 1, E.III.3.2).

Vérifie la CONCLUSION EXACTE et la CLÔTURE de chacune des quatre étapes via le
noyau (PROUVE == certifie) :
  • image_reciproque_image (ÉTAPE 1) — rétraction g⁻¹⟨g⟨S⟩⟩=S.
  • morceau_gI             (ÉTAPE 2) — g⁻¹|(A∖D) bijection A∖D → B∖f⟨D⟩.
  • recollement_h          (ÉTAPE 3) — h=(f|D)∪(g⁻¹|(A∖D)) bijection a → b.
  • cantor_bernstein       (ÉTAPE 4) — (a≤b et b≤a) ⇒ Eq(a,b).  GRAND PRIX.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein as CB
from bourbaki.cardinaux import ensembles_cantor_bernstein_final as CBF
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (est_injection_de,
                                                    est_bijection_de, equipotent,
                                                    inf_egal_card)


def test_image_reciproque_image():
    """⊢ est_injection_de(g,b,a) ⇒ ((S⊂b) ⇒ image(g⁻¹, g⟨S⟩) = S), clos.

    RÉTRACTION g⁻¹∘g = id sur b : c'est LE verrou de Cantor–Bernstein."""
    th = CBF.image_reciproque_image("g", "A", "B", "S")
    vg, vA, vB, vS = var("g"), var("A"), var("B"), var("S")
    exp = impl(est_injection_de(vg, vB, vA),
               impl(inclus(vS, vB),
                    egal(E.image(E.reciproque(vg), E.image(vg, vS)), vS)))
    assert th.est_clos
    assert th.conclusion == exp


def test_morceau_gI():
    """{est_injection_de(g,b,a)} ⊢ est_bijection_de(g⁻¹|(A∖D), A∖D, B∖f⟨D⟩), clos.

    SECOND MORCEAU de la bijection : sur A∖D, g⁻¹ est une bijection sur B∖f⟨D⟩."""
    th = CBF.morceau_gI("A", "B", "f", "g")
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    AmD = E.difference(vA, dterm)
    BmfD = E.difference(vB, E.image(vf, dterm))
    gI = E.restriction(E.reciproque(vg), AmD)
    assert th.est_clos
    assert th.conclusion == impl(est_injection_de(vg, vB, vA),
                                 est_bijection_de(gI, AmD, BmfD))


def test_recollement_h():
    """⊢ (inj(f,a,b) et inj(g,b,a)) ⇒ est_bijection_de((f|D)∪(g⁻¹|(A∖D)), a, b), clos.

    RECOLLEMENT des deux morceaux : la réunion des deux bijections partielles est
    la bijection complète a → b."""
    th = CBF.recollement_h("A", "B", "f", "g")
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    fD = E.restriction(vf, dterm)
    AmD = E.difference(vA, dterm)
    gI = E.restriction(E.reciproque(vg), AmD)
    h = E.reunion(fD, gI)
    assert th.est_clos
    assert th.conclusion == impl(et(est_injection_de(vf, vA, vB),
                                    est_injection_de(vg, vB, vA)),
                                 est_bijection_de(h, vA, vB))


def test_cantor_bernstein():
    """⊢ (inf_egal_card(a,b) et inf_egal_card(b,a)) ⇒ equipotent(a,b), clos.

    🎯 GRAND PRIX — Théorème de Cantor–Bernstein–Schröder = ANTISYMÉTRIE de ≤ :
    « Deux ensembles tels que chacun soit équipotent à une partie de l'autre sont
    équipotents. » (E.III.3.2, Cor. 2 du Théorème 1.)"""
    th = CBF.cantor_bernstein("A", "B", "f", "g")
    vA, vB = var("A"), var("B")
    exp = impl(et(inf_egal_card(vA, vB), inf_egal_card(vB, vA)),
               equipotent(vA, vB))
    assert th.est_clos
    assert th.conclusion == exp
