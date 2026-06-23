"""Tests V9 — §II.6 compléments : système de représentants, compatible R/S,
relation induite R_A, image réciproque d'une relation, ensemble des classes
d'objets équivalents.

Vérifient les FORMULES verbatim des définitions et la conclusion EXACTE (== cible)
+ clôture (.est_clos / hypothèses) des lemmes directs.  theorie_ensembles = 22.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, app, egal, et, impl, equiv,
                                       appartient, existe, pourtout, tau)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_6_equivalence import ensembles_quotient_complements as Q


# ════════════════════════════════════════════════════════════════════════════
# theorie_ensembles reste à 22 axiomes (axiomes de membership en théories DÉDIÉES)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
# 1.  Système de représentants des classes suivant R  (E.II.6.2)
# ════════════════════════════════════════════════════════════════════════════
def test_est_systeme_representants_def():
    """S système de représentants := S⊂E et p|S bijective de S sur E/R  (E.II.6.2)."""
    vS, vG, vE = var("S"), var("G"), var("E")
    p = E.application_canonique(vG, vE)
    p_S = E.restriction(p, vS)
    attendu = et(E.inclus(vS, vE),
                 E.est_bijective(p_S, vS, E.quotient(vG, vE)))
    assert Q.est_systeme_representants(vS, vG, vE) == attendu


def test_injection_representants_def():
    """r système de représentants (injection) := r injective et r⟨E/R⟩ syst. repr.  (E.II.6.2)."""
    vr, vG, vE = var("r"), var("G"), var("E")
    quot = E.quotient(vG, vE)
    attendu = et(E.injective_dans(vr, quot),
                 Q.est_systeme_representants(E.image(vr, quot), vG, vE))
    assert Q.injection_representants(vr, vG, vE) == attendu


# ════════════════════════════════════════════════════════════════════════════
# 2.  Application compatible avec R et S ; applications déduites  (E.II.6.5)
# ════════════════════════════════════════════════════════════════════════════
def test_est_compatible_RS_def():
    """f compat. R,S := (∀x)(∀x')(R{x,x'} ⇒ S{f(x),f(x')})  (E.II.6.5, verbatim)."""
    vf = var("f")
    R = E.rel_graphe("GR")
    S = E.rel_graphe("GS")
    vx, vxp = var("x"), var("xp")
    attendu = pourtout("x", pourtout("xp",
        impl(R(vx, vxp), S(E.valeur(vf, vx), E.valeur(vf, vxp)))))
    assert Q.est_compatible_RS(vf, R, S) == attendu


def test_application_deduite_quotient_def():
    """h déduite de f par passage au quotient := f = h ∘ p  (E.II.6.5)."""
    vF, vP, vH = var("F"), var("P"), var("H")
    assert Q.application_deduite_quotient(vF, vP, vH) == egal(vF, E.composee(vH, vP))


def test_application_deduite_quotients_def():
    """h déduite par passage aux quotients R,S := v∘f = h∘u  (E.II.6.5)."""
    vF, vU, vV, vH = var("F"), var("U"), var("V"), var("H")
    attendu = egal(E.composee(vV, vF), E.composee(vH, vU))
    assert Q.application_deduite_quotients(vF, vU, vV, vH) == attendu


def test_compatible_RS_via_v_clos_mod_hyp():
    """{f compat. R,S} ⊢ R{x,x'} ⇒ S{f(x),f(x')}  (cœur de « v∘f compatible avec R »)."""
    vf = var("f")
    R = E.rel_graphe("GR")
    S = E.rel_graphe("GS")
    vx, vxp = var("x"), var("xp")
    t = Q.compatible_RS_via_v(vf, R, S)
    assert t.conclusion == impl(R(vx, vxp), S(E.valeur(vf, vx), E.valeur(vf, vxp)))
    assert t.hypotheses == frozenset({Q.est_compatible_RS(vf, R, S)})


# ════════════════════════════════════════════════════════════════════════════
# 3.  Relation induite R_A  (E.II.6.6)
# ════════════════════════════════════════════════════════════════════════════
def test_relation_induite_def():
    """R_A{x,y} := (x∈A et y∈A et R{x,y})  (E.II.6.6, verbatim)."""
    R = E.rel_graphe("GR")
    vA, vx, vy = var("A"), var("x"), var("y")
    RA = Q.relation_induite(R, vA)
    attendu = et(et(appartient(vx, vA), appartient(vy, vA)), R(vx, vy))
    assert RA(vx, vy) == attendu


def test_relation_induite_implique():
    """⊢ (∀x)(∀y)(R_A{x,y} ⇒ R{x,y})  (R_A plus fine que R ; clos)."""
    R = E.rel_graphe("GR")
    vA, vx, vy = var("A"), var("x"), var("y")
    RA = Q.relation_induite(R, vA)
    t = Q.relation_induite_implique(R, vA)
    assert t.conclusion == pourtout("x", pourtout("y", impl(RA(vx, vy), R(vx, vy))))
    assert t.est_clos


def test_relation_induite_symetrique():
    """{R symétrique} ⊢ (∀x)(∀y)(R_A{x,y} ⇒ R_A{y,x})  (R_A symétrique ; clos mod. hyp.)."""
    R = E.rel_graphe("GR")
    vA, vx, vy = var("A"), var("x"), var("y")
    RA = Q.relation_induite(R, vA)
    t = Q.relation_induite_symetrique(R, vA)
    assert t.conclusion == pourtout("x", pourtout("y", impl(RA(vx, vy), RA(vy, vx))))
    assert t.hypotheses == frozenset({E.est_symetrique(R, "x", "y")})


# ════════════════════════════════════════════════════════════════════════════
# 4.  Image réciproque d'une relation par une application  (E.II.6.6)
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_relation_def():
    """(S∘φ){x,y} := S{φ(x),φ(y)}  (E.II.6.6, verbatim)."""
    S = E.rel_graphe("GS")
    vphi, vx, vy = var("phi"), var("x"), var("y")
    SP = Q.image_reciproque_relation(S, vphi)
    assert SP(vx, vy) == S(E.valeur(vphi, vx), E.valeur(vphi, vy))


def test_image_reciproque_relation_dans_def():
    """forme gardée : (x∈E et y∈E et S{φ(x),φ(y)})  (E.II.6.6)."""
    S = E.rel_graphe("GS")
    vphi, vE, vx, vy = var("phi"), var("E"), var("x"), var("y")
    SP = Q.image_reciproque_relation_dans(S, vphi, vE)
    attendu = et(et(appartient(vx, vE), appartient(vy, vE)),
                 S(E.valeur(vphi, vx), E.valeur(vphi, vy)))
    assert SP(vx, vy) == attendu


def test_graphe_image_reciproque_relation_def():
    vgS, vphi, vE = var("GS"), var("phi"), var("E")
    assert (Q.graphe_image_reciproque_relation(vgS, vphi, vE)
            == app("img_recip_rel", vgS, vphi, vE))


def test_axiome_graphe_image_reciproque_def():
    """membership verbatim de S∘φ  (S8+A1)."""
    vgS, vphi, vE = var("GS"), var("phi"), var("E")
    vw, vx, vy = var("w"), var("x"), var("y")
    corps = existe("x", existe("y",
        et(et(et(appartient(vx, vE), appartient(vy, vE)),
               egal(vw, E.couple(vx, vy))),
           appartient(E.couple(E.valeur(vphi, vx), E.valeur(vphi, vy)), vgS))))
    attendu = pourtout("w", equiv(
        appartient(vw, Q.graphe_image_reciproque_relation(vgS, vphi, vE)), corps))
    assert Q.axiome_graphe_image_reciproque("GS", "phi", "E") == attendu


def test_membre_graphe_image_reciproque_clos():
    """Théorème de membership de S∘φ : sort clos de sa théorie dédiée."""
    vgS, vphi, vE = var("GS"), var("phi"), var("E")
    vw, vx, vy = var("w"), var("x"), var("y")
    t = Q.membre_graphe_image_reciproque("GS", "phi", "E")
    corps = existe("x", existe("y",
        et(et(et(appartient(vx, vE), appartient(vy, vE)),
               egal(vw, E.couple(vx, vy))),
           appartient(E.couple(E.valeur(vphi, vx), E.valeur(vphi, vy)), vgS))))
    cible = equiv(appartient(vw, Q.graphe_image_reciproque_relation(vgS, vphi, vE)), corps)
    assert t.conclusion == cible and t.est_clos


def test_image_reciproque_symetrique():
    """{S symétrique} ⊢ (S∘φ) symétrique (clos mod. hyp.)."""
    S = E.rel_graphe("GS")
    vphi, vx, vy = var("phi"), var("x"), var("y")
    SP = Q.image_reciproque_relation(S, vphi)
    t = Q.image_reciproque_symetrique(S, vphi)
    assert t.conclusion == pourtout("x", pourtout("y", impl(SP(vx, vy), SP(vy, vx))))
    assert t.hypotheses == frozenset({E.est_symetrique(S, "a", "b")})


def test_image_reciproque_transitive():
    """{S transitive} ⊢ (S∘φ) transitive (clos mod. hyp.)."""
    S = E.rel_graphe("GS")
    vphi, vx, vy, vz = var("phi"), var("x"), var("y"), var("z")
    SP = Q.image_reciproque_relation(S, vphi)
    t = Q.image_reciproque_transitive(S, vphi)
    assert t.conclusion == pourtout("x", pourtout("y", pourtout("z",
        impl(et(SP(vx, vy), SP(vy, vz)), SP(vx, vz)))))
    assert t.hypotheses == frozenset({E.est_transitive(S, "a", "b", "c")})


# ════════════════════════════════════════════════════════════════════════════
# 5.  Ensemble des classes d'objets équivalents  E_R  (E.II.6.9)
# ════════════════════════════════════════════════════════════════════════════
def test_classe_objets_alias():
    """θ{x} = τ_y(R{x,y}) — alias fidèle de E.classe_objets."""
    R = E.rel_graphe("GR")
    vx = var("x")
    assert Q.classe_objets(R, vx) == E.classe_objets(R, vx)


def test_ensemble_classes_objets_def():
    vT = var("T")
    R = E.rel_graphe("GR")
    assert Q.ensemble_classes_objets(R, vT) == app("ens_classes_obj", vT)


def test_axiome_ensemble_classes_objets_def():
    """(∀z)(z∈E_R ⇔ ∃x(x∈T et R{x,x} et z=θ{x}))  (membership verbatim)."""
    R = E.rel_graphe("GR")
    vT, vz, vx = var("T"), var("z"), var("x")
    corps = existe("x", et(et(appartient(vx, vT), R(vx, vx)),
                           egal(vz, Q.classe_objets(R, vx, y="_yθ"))))
    attendu = pourtout("z", equiv(
        appartient(vz, Q.ensemble_classes_objets(R, vT)), corps))
    assert Q.axiome_ensemble_classes_objets(R, "T") == attendu


def test_membre_ensemble_classes_objets_clos():
    """Théorème de membership de E_R : sort clos de sa théorie dédiée."""
    R = E.rel_graphe("GR")
    vT, vz, vx = var("T"), var("z"), var("x")
    t = Q.membre_ensemble_classes_objets(R, "T")
    corps = existe("x", et(et(appartient(vx, vT), R(vx, vx)),
                           egal(vz, Q.classe_objets(R, vx, y="_yθ"))))
    cible = equiv(appartient(vz, Q.ensemble_classes_objets(R, vT)), corps)
    assert t.conclusion == cible and t.est_clos


def test_classe_objets_unicite():
    """{R sym., R trans.} ⊢ R{x,x'} ⇒ θ{x}=θ{x'}  (E.II.6.9 ; clos mod. hyp.)."""
    R = E.rel_graphe("GR")
    vx, vxp = var("x"), var("xp")
    t = Q.classe_objets_unicite(R)
    assert t.conclusion == impl(R(vx, vxp),
                                egal(Q.classe_objets(R, vx), Q.classe_objets(R, vxp)))
    # R{x,x'} déchargé dans l'implication ; restent symétrie + transitivité
    assert t.hypotheses == frozenset({
        E.est_symetrique(R, "a", "b"),
        E.est_transitive(R, "a", "b", "c"),
    })
