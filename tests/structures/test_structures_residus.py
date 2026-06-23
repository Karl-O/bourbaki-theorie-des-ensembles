"""Tests §IV.2.5 (résidu) — Décomposition canonique d'un MORPHISME.

Vérifient la FIDÉLITÉ des définitions (réutilisation exacte des graphes II.6.5 et des
structures dérivées IV.2), la forme de l'énoncé IV.2.5 (hypothèses ⇒ g morphisme), la
clôture des lemmes logiques directs, et l'invariance theorie_ensembles() = 22 axiomes.
"""
from bourbaki.logique.formule import (var, et, impl, appartient, app, alpha_egal)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.structures.iv_2_morphismes_structures_derivees import ensembles_structures_residus as R
from bourbaki.structures.iv_2_morphismes_structures_derivees import ensembles_universel_morphismes as M
from bourbaki.ensembles.relations import ensembles_decomposition_quotient as D


# ════════════════════════════════════════════════════════════════════════════
# 1.  Données dérivées — réutilisation FIDÈLE des graphes II.6.5
# ════════════════════════════════════════════════════════════════════════════
def test_relation_du_morphisme_est_Rf():
    """R{x,y} = R_f{x,y} = (x∈dom f et y∈dom f et f(x)=f(y))  (alias II.6.2)."""
    vf, vx, vy = var("f"), var("x"), var("y")
    rel = R.relation_du_morphisme(vf)
    assert rel(vx, vy) == D.relation_egalite_valeurs(vf)(vx, vy)
    assert rel(vx, vy) == E.relation_associee_fonction(vf)(vx, vy)


def test_application_canonique_phi_reutilise_surjection():
    """φ = surjection canonique de A sur A/R (graphe application_canonique, II.6.2)."""
    vf, va = var("f"), var("A")
    gR = app("graphe_Rf", vf, va)
    assert R.application_canonique_phi(vf, va) == D.surjection_canonique(gR, va)
    assert R.application_canonique_phi(vf, va) == E.application_canonique(gR, va)


def test_injection_canonique_j_est_diagonale_fA():
    """j = injection canonique f(A) ↪ B = Δ_{f(A)}  (II.6.5)."""
    vf, va, vb = var("f"), var("A"), var("B")
    fA = E.image(vf, va)
    assert R.injection_canonique_j(vf, va, vb) == D.injection_canonique(fA)
    assert R.injection_canonique_j(vf, va, vb) == E.diagonale(fA)


def test_bijection_g_reutilise_bijection_induite():
    """g = bijection induite A/R → f(A), g(Cl_R(x)) = f(x)  (II.6.5)."""
    vf, va = var("f"), var("A")
    gR = app("graphe_Rf", vf, va)
    assert R.bijection_g(vf, va) == D.bijection_induite(gR, va, vf)


# ════════════════════════════════════════════════════════════════════════════
# 2.  Structures dérivées 𝒮₀ (quotient) / 𝒮'₀ (induite) — IV.2
# ════════════════════════════════════════════════════════════════════════════
def test_structure_quotient_S0_terme():
    """𝒮₀ = app('structure_quotient', A, 𝒮, graphe_R) (structure quotient, IV.2)."""
    vf, va, vs = var("f"), var("A"), var("Sa")
    gR = app("graphe_Rf", vf, va)
    assert R.structure_quotient_S0(va, vs, vf) == app("structure_quotient", va, vs, gR)


def test_structure_induite_S0prime_terme():
    """𝒮'₀ = app('structure_induite', B, 𝒮', f(A)) (structure induite, IV.2)."""
    vf, va, vb, vsp = var("f"), var("A"), var("B"), var("Sb")
    fA = E.image(vf, va)
    assert R.structure_induite_S0prime(vb, vsp, vf, va) == \
        app("structure_induite", vb, vsp, fA)


# ════════════════════════════════════════════════════════════════════════════
# 3.  IV.2.5 — g est un σ-morphisme (contenu structurel)
# ════════════════════════════════════════════════════════════════════════════
def test_g_est_morphisme_forme():
    """g morphisme de (A/R, 𝒮₀) dans (f(A), 𝒮'₀) — est_morphisme aux bons arguments."""
    mor = M._morph_defaut()
    vf, va, vs, vb, vsp = var("f"), var("A"), var("Sa"), var("B"), var("Sb")
    gm = R.g_est_morphisme(va, vs, vb, vsp, vf, morph=mor)
    gR = app("graphe_Rf", vf, va)
    cible = M.est_morphisme(
        E.quotient(gR, va),                              # A/R
        app("structure_quotient", va, vs, gR),           # 𝒮₀
        E.image(vf, va),                                 # f(A)
        app("structure_induite", vb, vsp, E.image(vf, va)),  # 𝒮'₀
        D.bijection_induite(gR, va, vf),                 # g
        mor)
    assert alpha_egal(gm, cible)


def test_hypothese_f_morphisme_forme():
    """Hypothèse « f morphisme de (A,𝒮) dans (B,𝒮') » = est_morphisme(A,𝒮,B,𝒮',f)."""
    mor = M._morph_defaut()
    vf, va, vs, vb, vsp = var("f"), var("A"), var("Sa"), var("B"), var("Sb")
    h = R.hypothese_f_morphisme(va, vs, vb, vsp, vf, morph=mor)
    assert alpha_egal(h, M.est_morphisme(va, vs, vb, vsp, vf, mor))


def test_hypothese_structures_derivees_conjonction():
    """Hypothèse structures dérivées = (𝒮₀ ∈ Struct_Σ(A/R)) ET (𝒮'₀ ∈ Struct_Σ(f(A)))."""
    vf, va, vs, vb, vsp = var("f"), var("A"), var("Sa"), var("B"), var("Sb")
    h = R.hypothese_structures_derivees(va, vs, vb, vsp, vf)
    assert h.tag == "non"             # et = ¬(¬a ∨ ¬b) → tag 'non' (encodage noyau)
    gR = app("graphe_Rf", vf, va)
    s0 = app("structure_quotient", va, vs, gR)
    s0p = app("structure_induite", vb, vsp, E.image(vf, va))
    ex_q = appartient(s0, app("Struct_Sigma", E.quotient(gR, va)))
    ex_i = appartient(s0p, app("Struct_Sigma", E.image(vf, va)))
    assert alpha_egal(h, et(ex_q, ex_i))


# ════════════════════════════════════════════════════════════════════════════
# 4.  Énoncé COMPLET IV.2.5 et décomposition ensembliste (rappel II.6.5)
# ════════════════════════════════════════════════════════════════════════════
def test_decomposition_canonique_morphisme_enonce():
    """IV.2.5 : (hypothèses) ⇒ (g morphisme).  Implication aux bons membres."""
    mor = M._morph_defaut()
    vf, va, vs, vb, vsp = var("f"), var("A"), var("Sa"), var("B"), var("Sb")
    enonce = R.decomposition_canonique_morphisme(va, vs, vb, vsp, vf, morph=mor)
    hyp = R.hypotheses_decomposition(va, vs, vb, vsp, vf, mor)
    ccl = R.g_est_morphisme(va, vs, vb, vsp, vf, mor)
    assert alpha_egal(enonce, impl(hyp, ccl))


def test_decomposition_ensembliste_reutilise_II65():
    """f = j∘g∘φ (décomposition ensembliste) = decomposition_canonique de II.6.5."""
    vf, va, vb = var("f"), var("A"), var("B")
    gR = app("graphe_Rf", vf, va)
    assert R.decomposition_ensembliste(vf, va, vb) == \
        D.decomposition_canonique(vf, gR, va, vb)


# ════════════════════════════════════════════════════════════════════════════
# 5.  Lemmes logiques DIRECTS — clos, conclusions exactes
# ════════════════════════════════════════════════════════════════════════════
def test_decomp_extrait_f_morphisme_clos():
    """{hyp} ⊢ hyp ⇒ (f morphisme) — clos, conclusion = implication vers f morphisme."""
    t = R.decomp_extrait_f_morphisme()
    assert t.est_clos
    assert t.conclusion.tag == "ou"   # impl(hyp, f morphisme) = ¬hyp ∨ (f morph)


def test_decomp_extrait_structures_derivees_clos():
    t = R.decomp_extrait_structures_derivees()
    assert t.est_clos


def test_decomp_extrait_existence_quotient_clos():
    t = R.decomp_extrait_existence_quotient()
    assert t.est_clos


# ════════════════════════════════════════════════════════════════════════════
# 6.  Invariance theorie_ensembles() = 22 axiomes
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22
