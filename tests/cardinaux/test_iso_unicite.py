"""Tests §III.2 — UNICITÉ de l'iso d'ordre / Cor 1 (cœur algébrique).

On certifie le CŒUR de l'unicité (le « un et un seul » du Théorème 3, E.III.2.6) :
un automorphisme d'ordre d'un bon ordre est l'identité (point_fixe_automorphisme,
dérivé de lemme_4 + antisymétrie, hypothèses STRUCTURELLES explicites, conclusion
fidèle, non tautologique) ; et le pas final extensionnel f=g (iso_unicite_extensionnel,
RÉUTILISE application_egale_par_valeurs).  theorie_ensembles() reste = 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl, appartient, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_iso_unicite as U
from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de, _val, _f_dans_E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante


def test_point_fixe_automorphisme():
    """{ bo, h:E→E, h scr, k:E→E, k scr, k∘h=id } ⊢ (∀x)(x∈E ⇒ h(x)=x)."""
    pf = U.point_fixe_automorphisme()
    assert not pf.est_clos
    assert len(pf.hypotheses) == 6
    assert pf.conclusion == U.point_fixe_automorphisme_cible()
    assert pf.conclusion not in pf.hypotheses           # non tautologique


def test_point_fixe_hypotheses_structurelles():
    """Les 6 hypothèses sont EXACTEMENT les attendues (rien en trop, rien postulé)."""
    pf = U.point_fixe_automorphisme()
    hyps = set(pf.hypotheses)
    vR, vE, vh, vk = var("R"), var("E"), var("h"), var("k")
    Rf = _R_de("R")
    vx = var("x")
    hx = _val(vh, vx)
    expected = {
        E.est_bien_ordonne(Rf, vE),                                     # bon ordre CANONIQUE
        _f_dans_E(vh, vE),                                              # h : E→E
        est_strictement_croissante(vR, vR, vh, vE, vE),                # h strict croissante
        _f_dans_E(vk, vE),                                              # k : E→E
        est_strictement_croissante(vR, vR, vk, vE, vE),                # k strict croissante
        pourtout("x", impl(appartient(vx, vE), egal(_val(vk, hx), vx))),  # k∘h = id_E
    }
    assert hyps == expected
    # bon ordre CANONIQUE présent (chainable == est_bien_ordonne standard)
    assert E.est_bien_ordonne(Rf, vE) in hyps
    # la stricte croissance des DEUX applications est réellement requise
    assert est_strictement_croissante(vR, vR, vh, vE, vE) in hyps
    assert est_strictement_croissante(vR, vR, vk, vE, vE) in hyps


def test_point_fixe_parametrable():
    pf = U.point_fixe_automorphisme("Rp", "F", "phi", "psi")
    assert len(pf.hypotheses) == 6
    assert pf.conclusion == U.point_fixe_automorphisme_cible("Rp", "F", "phi", "psi")


def test_iso_unicite_extensionnel():
    """{ f,g∈𝓕(E',E), mêmes valeurs sur E' } ⊢ f=g  (pas final extensionnel)."""
    ue = U.iso_unicite_extensionnel()
    assert not ue.est_clos
    assert len(ue.hypotheses) == 3
    assert ue.conclusion == U.iso_unicite_extensionnel_cible()
    assert ue.conclusion not in ue.hypotheses


def test_reciproque_bijection_role():
    """⊢ bij(g,E,E') ⇒ bij(g⁻¹,E',E)  (g⁻¹ joue le rôle d'inverse — Prop. 7)."""
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    rr = U.reciproque_bijection_role()
    assert rr.est_clos
    vg = var("g")
    grec = E.reciproque(vg)
    # implication bij(g,E,Ep) ⇒ bij(g⁻¹,Ep,E)
    concl = rr.conclusion
    assert concl.tag == "ou"                            # une implication ¬A ∨ B
    assert est_bijection_de(grec, var("Ep"), var("E")) == concl.sous[1]


def test_compose_bijection_automorphisme():
    """{ bij(k,E',E), bij(f,E,E') } ⊢ bij(f∘k, E', E')  (pièce d'assemblage)."""
    cb = U.compose_bijection_automorphisme()
    assert not cb.est_clos
    assert len(cb.hypotheses) == 2
    assert cb.conclusion == U.compose_bijection_automorphisme_cible()
    assert cb.conclusion not in cb.hypotheses
    # les 2 hypothèses sont bien les bijectivités de k et f
    from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
    hyps = set(cb.hypotheses)
    assert est_bijection_de(var("k"), var("Ep"), var("E")) in hyps
    assert est_bijection_de(var("f"), var("E"), var("Ep")) in hyps


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
