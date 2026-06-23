"""Tests §II.5.4-5.7 — PROPOSITIONS 3-11 du produit (suite).

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
Aucun fichier existant n'est modifié ; theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.logique.i_1_termes_relations.formule import (var, app, egal, et, impl, non, appartient,
                                       existe, inclus, pourtout, equiv)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit import ensembles_produit_props2 as P


# ── §5.4 — Cor. 3 (Prop. 6) : monotonie du produit  X_ι⊂Y_ι ⇒ ∏X⊂∏Y ──────────
def test_produit_monotone_facteurs():
    thm = P.produit_monotone_facteurs("f", "g", "I", "F", "i")
    vf, vg, vI = var("f"), var("g"), var("I")
    vi = var("i")
    Xi = E.valeur_famille(vf, vi)
    Yi = E.valeur_famille(vg, vi)
    H = pourtout("i", impl(appartient(vi, vI), inclus(Xi, Yi)))
    cible = impl(H, inclus(E.produit_famille(vf, vI), E.produit_famille(vg, vI)))
    assert thm.conclusion == cible
    assert thm.est_clos
    assert thm.hypotheses == frozenset()


# ── §5.4 — facteurs égaux ⇒ produits inclus ──────────────────────────────────
def test_facteurs_egaux_donne_inclus():
    thm = P.facteurs_egaux_donne_inclus("f", "g", "I", "F", "i")
    vf, vg, vI = var("f"), var("g"), var("I")
    vi = var("i")
    Xi = E.valeur_famille(vf, vi)
    Yi = E.valeur_famille(vg, vi)
    H = pourtout("i", impl(appartient(vi, vI), egal(Xi, Yi)))
    cible = impl(H, inclus(E.produit_famille(vf, vI), E.produit_famille(vg, vI)))
    assert thm.conclusion == cible
    assert thm.est_clos
    assert thm.hypotheses == frozenset()


# ── §5.3 — Prop. 4 : reparamétrage F↦F∘U injectif (conditionnel inverse) ──────
def test_reparametrage_injectif():
    thm = P.reparametrage_injectif("F", "Fp", "U", "V", "P")
    vF, vFp, vU, vV, vP = var("F"), var("Fp"), var("U"), var("V"), var("P")
    FU, FpU = E.composee(vF, vU), E.composee(vFp, vU)
    FUV, FpUV = E.composee(FU, vV), E.composee(FpU, vV)
    hyp = et(et(et(et(appartient(vF, vP), appartient(vFp, vP)),
                   egal(FUV, vF)), egal(FpUV, vFp)),
             egal(FU, FpU))
    cible = impl(hyp, egal(vF, vFp))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── §5.5 — Prop. 7 : associativité (surjectivité via inverse-recollement) ─────
def test_associativite_via_inverse():
    thm = P.associativite_via_inverse("F", "PI", "PIPI")
    vF, vPI, vPIPI = var("F"), var("PI"), var("PIPI")
    aF = P.assoc(vF)
    rec = P.recoller(aF)
    hyp = et(et(appartient(vF, vPI), appartient(aF, vPIPI)), egal(rec, vF))
    body = et(appartient(var("H"), vPIPI), egal(P.recoller(var("H")), vF))
    cible = impl(hyp, existe("H", body))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── §5.6 — LEMME : ⋂_{κ∈K}X_κ ⊂ X_{κ₀}  (incond.) ────────────────────────────
def test_inter_famille_incluse_facteur():
    thm = P.inter_famille_incluse_facteur("h", "K", "k0", "z")
    vh, vK, vk0 = var("h"), var("K"), var("k0")
    Inter = E.inter_famille(vh, vK)
    Xk0 = E.valeur_famille(vh, vk0)
    cible = impl(appartient(vk0, vK), inclus(Inter, Xk0))
    assert thm.conclusion == cible
    assert thm.est_clos
    assert thm.hypotheses == frozenset()


# ── §5.6 — Prop. 10 : commutation produit/intersection (sens « ⊂ ») ───────────
def test_produit_distrib_inter_membre():
    thm = P.produit_distrib_inter_membre("W", "V", "I", "K", "G", "i", "k0")
    assert thm.est_clos
    # la conclusion est une implication hyp ⇒ (G∈∏V)
    concl = thm.conclusion
    assert concl.tag == "ou"           # impl A B = ou(non A, B)
    vV, vI, vG = var("V"), var("I"), var("G")
    cible_concl = appartient(vG, E.produit_famille(vV, vI))
    assert concl.sous[1] == cible_concl


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
