"""Tests V9 — §II.6 : R_f (égalité des valeurs), décomposition canonique, R/S.

Vérifient les FORMULES verbatim des définitions et la conclusion EXACTE (== cible)
+ clôture (.est_clos / hypothèses) des théorèmes directs.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, app, egal, et, impl, equiv,
                                       appartient, existe, pourtout)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition import ensembles_decomposition_quotient as D


# ════════════════════════════════════════════════════════════════════════════
# 1.  R_f — relation d'égalité des valeurs
# ════════════════════════════════════════════════════════════════════════════
def test_relation_egalite_valeurs_def():
    """R_f{x,y} = (x∈dom f et y∈dom f et f(x)=f(y))  (E.II.6.2, verbatim)."""
    vf, vx, vy = var("f"), var("x"), var("y")
    R = D.relation_egalite_valeurs(vf)
    attendu = et(et(appartient(vx, E.dom(vf)), appartient(vy, E.dom(vf))),
                 egal(E.valeur(vf, vx), E.valeur(vf, vy)))
    assert R(vx, vy) == attendu
    # alias fidèle de relation_associee_fonction
    assert R(vx, vy) == E.relation_associee_fonction(vf)(vx, vy)


def test_rf_symetrique():
    vf = var("f")
    R = D.relation_egalite_valeurs(vf)
    t = D.rf_symetrique("f")
    vx, vy = var("x"), var("y")
    assert t.conclusion == pourtout("x", pourtout("y", impl(R(vx, vy), R(vy, vx))))
    assert t.est_clos
    # = forme E.est_symetrique appliquée à R_f
    assert t.conclusion == E.est_symetrique(R)


def test_rf_transitive():
    vf = var("f")
    R = D.relation_egalite_valeurs(vf)
    t = D.rf_transitive("f")
    vx, vy, vz = var("x"), var("y"), var("z")
    assert t.conclusion == pourtout("x", pourtout("y", pourtout("z",
        impl(et(R(vx, vy), R(vy, vz)), R(vx, vz)))))
    assert t.est_clos
    assert t.conclusion == E.est_transitive(R)


def test_rf_reflexive_dans_dom():
    vf, vx = var("f"), var("x")
    R = D.relation_egalite_valeurs(vf)
    t = D.rf_reflexive_dans_dom("f")
    assert t.conclusion == pourtout("x", equiv(R(vx, vx), appartient(vx, E.dom(vf))))
    assert t.est_clos
    assert t.conclusion == E.est_reflexive_dans(R, E.dom(vf))


def test_rf_relation_equivalence_dans():
    vf = var("f")
    R = D.relation_egalite_valeurs(vf)
    t = D.rf_relation_equivalence_dans("f")
    assert t.conclusion == E.est_relation_equivalence_dans(R, E.dom(vf))
    assert t.est_clos


# ════════════════════════════════════════════════════════════════════════════
# 2.  Décomposition canonique f = i ∘ b ∘ p
# ════════════════════════════════════════════════════════════════════════════
def test_surjection_canonique_def():
    """p = application canonique de E sur E/R  (E.II.6.2)."""
    vG, vE = var("G"), var("E")
    assert D.surjection_canonique(vG, vE) == E.application_canonique(vG, vE)


def test_injection_canonique_def():
    """i = identité de B ⊂ F, graphe = diagonale Δ_B  (E.II.6.5 / E.III.3.1)."""
    vB = var("B")
    assert D.injection_canonique(vB) == E.diagonale(vB)


def test_bijection_induite_def():
    vG, vE, vf = var("G"), var("E"), var("f")
    assert D.bijection_induite(vG, vE, vf) == app("bij_induite", vG, vE, vf)


def test_axiome_bijection_induite_def():
    """(∀w)(w∈b ⇔ (∃x)(x∈E et w=(Cl_R(x), f(x))))  (membership verbatim)."""
    vG, vE, vf, vw, vx = var("G"), var("E"), var("f"), var("w"), var("x")
    corps = existe("x", et(appartient(vx, vE),
                           egal(vw, E.couple(E.classe(vG, vx), E.valeur(vf, vx)))))
    attendu = pourtout("w", equiv(appartient(vw, D.bijection_induite(vG, vE, vf)), corps))
    assert D.axiome_bijection_induite("G", "E", "f") == attendu


def test_membre_bijection_induite_clos():
    """Théorème de membership de b : sort clos de sa théorie dédiée."""
    vG, vE, vf, vw, vx = var("G"), var("E"), var("f"), var("w"), var("x")
    t = D.membre_bijection_induite("G", "E", "f")
    corps = existe("x", et(appartient(vx, vE),
                           egal(vw, E.couple(E.classe(vG, vx), E.valeur(vf, vx)))))
    cible = equiv(appartient(vw, D.bijection_induite(vG, vE, vf)), corps)
    assert t.conclusion == cible and t.est_clos


def test_decomposition_canonique_def():
    """f = i ∘ (b ∘ p) : égalité de graphes F = composee(i, composee(b, p))  (E.II.6.5)."""
    vF, vG, vE, vBut = var("F"), var("G"), var("E"), var("F2")
    p = D.surjection_canonique(vG, vE)
    b = D.bijection_induite(vG, vE, vF)
    i = D.injection_canonique(E.image(vF, vE))
    attendu = egal(vF, E.composee(i, E.composee(b, p)))
    assert D.decomposition_canonique(vF, vG, vE, vBut) == attendu


# ════════════════════════════════════════════════════════════════════════════
# 3.  Quotient R/S
# ════════════════════════════════════════════════════════════════════════════
def test_relation_quotient_RS_graphe_def():
    """(R/S){t,t'} = (∃x)(∃y)(t=Cl_S(x) et t'=Cl_S(y) et R{x,y})  (E.II.6.7, verbatim)."""
    R = E.rel_graphe("GR")
    vgS = var("GS")
    vt, vtp, vx, vy = var("t"), var("tp"), var("x"), var("y")
    rel = D.relation_quotient_RS_graphe(R, vgS)
    attendu = existe("x", existe("y",
        et(et(egal(vt, E.classe(vgS, vx)), egal(vtp, E.classe(vgS, vy))),
           R(vx, vy))))
    assert rel(vt, vtp) == attendu


def test_quotient_bien_pose():
    """{S plus fine que R} ⊢ (∀x)(∀y)(S{x,y} ⇒ R{x,y})  (E.II.6.7)."""
    R = E.rel_graphe("GR")
    S = E.rel_graphe("GS")
    t = D.quotient_bien_pose(R, S)
    assert t.conclusion == E.plus_fine(S, R)
    assert t.hypotheses == frozenset({E.plus_fine(S, R)})


def test_quotient_bien_pose_instance():
    """{S plus fine que R} ⊢ S{a,b} ⇒ R{a,b}  (E.II.6.7, instance ponctuelle)."""
    R = E.rel_graphe("GR")
    S = E.rel_graphe("GS")
    va, vb = var("a"), var("b")
    t = D.quotient_bien_pose_instance(R, S, "a", "b")
    assert t.conclusion == impl(S(va, vb), R(va, vb))
    assert t.hypotheses == frozenset({E.plus_fine(S, R)})
