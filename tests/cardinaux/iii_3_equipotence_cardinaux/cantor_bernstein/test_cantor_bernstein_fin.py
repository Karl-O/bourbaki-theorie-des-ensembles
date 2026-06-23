"""Tests — CANTOR–BERNSTEIN, suite (du point fixe φ(D)=D vers la bijection).

Vérifie les PALIERS additifs : double complément, image dans le codomaine,
et LE PIVOT  A∖D = g⟨B∖f⟨D⟩⟩.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, et, non, impl, appartient, inclus, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein as CB
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein_fin as CBF
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_injection_de


# ── brique : double complément ────────────────────────────────────────────────
def test_double_complement():
    """⊢ (Y⊂A) ⇒ (A∖(A∖Y)=Y), clos."""
    thm = CBF.double_complement()
    vA, vY = var("A"), var("Y")
    AmY = E.difference(vA, vY)
    cible = impl(inclus(vY, vA), egal(E.difference(vA, AmY), vY))
    assert thm.est_clos
    assert thm.conclusion == cible


# ── image d'une partie de B reste dans A (sous g injection) ───────────────────
def test_image_dans_codomaine_diff():
    """{g injection B→A} ⊢ g⟨B∖f⟨D⟩⟩ ⊂ A  (hyp = est_injection_de(g,B,A))."""
    thm = CBF.image_dans_codomaine_diff()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    gBfD = E.image(vg, E.difference(vB, E.image(vf, dterm)))
    assert thm.conclusion == inclus(gBfD, vA)
    assert thm.hypotheses == frozenset({est_injection_de(vg, vB, vA)})


# ── ÉTAPE 1 — LE PIVOT  A∖D = g⟨B∖f⟨D⟩⟩ ───────────────────────────────────────
def test_pivot_AmoinsD():
    """{g injection B→A} ⊢ A∖D = g⟨B∖f⟨D⟩⟩  (LE PIVOT)."""
    thm = CBF.pivot_AmoinsD()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    AmD = E.difference(vA, dterm)
    gBfD = E.image(vg, E.difference(vB, E.image(vf, dterm)))
    assert thm.conclusion == egal(AmD, gBfD)
    assert thm.hypotheses == frozenset({est_injection_de(vg, vB, vA)})


# ── PARTITION : disjonction + recouvrement ────────────────────────────────────
def test_partie_disjoint_complement():
    """⊢ X ∩ (A∖X) = ∅, clos."""
    thm = CBF.partie_disjoint_complement()
    vA, vX = var("A"), var("X")
    inter = E.intersection(vX, E.difference(vA, vX))
    assert thm.est_clos
    assert thm.conclusion == egal(inter, E.VIDE)


def test_partie_reunion_complement():
    """⊢ (X⊂A) ⇒ (X ∪ (A∖X) = A), clos."""
    thm = CBF.partie_reunion_complement()
    vA, vX = var("A"), var("X")
    reun = E.reunion(vX, E.difference(vA, vX))
    cible = impl(inclus(vX, vA), egal(reun, vA))
    assert thm.est_clos
    assert thm.conclusion == cible


# ── ÉTAPE 2 (i) — restriction fonctionnelle ───────────────────────────────────
def test_sous_graphe_fonctionnel():
    """⊢ (est_fonctionnel(F) et G⊂F) ⇒ est_fonctionnel(G), clos."""
    thm = CBF.sous_graphe_fonctionnel()
    vF, vG = var("F"), var("G")
    cible = impl(et(E.est_fonctionnel(vF), inclus(vG, vF)), E.est_fonctionnel(vG))
    assert thm.est_clos
    assert thm.conclusion == cible


def test_restriction_fonctionnelle():
    """⊢ est_fonctionnel(F) ⇒ est_fonctionnel(f|X), clos."""
    thm = CBF.restriction_fonctionnelle()
    vF, vX = var("F"), var("X")
    cible = impl(E.est_fonctionnel(vF), E.est_fonctionnel(E.restriction(vF, vX)))
    assert thm.est_clos
    assert thm.conclusion == cible
