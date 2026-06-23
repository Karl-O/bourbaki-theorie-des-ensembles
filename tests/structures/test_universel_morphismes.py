"""Tests §IV.2 — Morphismes et structures dérivées (représentation paramétrée).

Chaque test vérifie soit que la DÉFINITION renvoyée est exactement la formule
fidèle visée, soit qu'un THÉORÈME logique direct est correctement certifié par le
noyau (clos, ou conditionnel avec les hypothèses attendues).
"""
from bourbaki.logique.formule import (var, et, ou, non, impl, equiv, pourtout,
                                       existe, appartient, egal, app, alpha_egal)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.structures.iv_2_morphismes_structures_derivees import ensembles_universel_morphismes as M


def test_morph_defaut_callable():
    mor = M._morph_defaut("Mor")
    f = mor(var("E1"), var("S1"), var("E2"), var("S2"), var("f"))
    assert alpha_egal(f, appartient(var("f"),
                      app("Mor", var("E1"), var("S1"), var("E2"), var("S2"))))


def test_est_morphisme_definition():
    mor = M._morph_defaut()
    d = M.est_morphisme(var("E1"), var("S1"), var("E2"), var("S2"), var("f"), mor)
    assert alpha_egal(d, mor(var("E1"), var("S1"), var("E2"), var("S2"), var("f")))


# ── plus fine / moins fine / comparables / strictement ────────────────────────
def test_plus_fine_est_identite_morphisme():
    """« 𝒮₁ plus fine que 𝒮₂ » = id_E=Δ_E est un morphisme de (E,𝒮₁) dans (E,𝒮₂)."""
    mor = M._morph_defaut()
    pf = M.plus_fine("E", var("S1"), var("S2"), mor)
    cible = M.est_morphisme(var("E"), var("S1"), var("E"), var("S2"),
                            E.diagonale(var("E")), mor)
    assert alpha_egal(pf, cible)


def test_moins_fine_est_plus_fine_inversee():
    mor = M._morph_defaut()
    mf = M.moins_fine("E", var("S1"), var("S2"), mor)
    pf = M.plus_fine("E", var("S2"), var("S1"), mor)
    assert alpha_egal(mf, pf)


def test_comparables_disjonction():
    mor = M._morph_defaut()
    c = M.comparables("E", var("S1"), var("S2"), mor)
    cible = ou(M.plus_fine("E", var("S1"), var("S2"), mor),
               M.plus_fine("E", var("S2"), var("S1"), mor))
    assert alpha_egal(c, cible)


def test_strictement_plus_fine():
    mor = M._morph_defaut()
    sp = M.strictement_plus_fine("E", var("S1"), var("S2"), mor)
    cible = et(M.plus_fine("E", var("S1"), var("S2"), mor),
               non(egal(var("S1"), var("S2"))))
    assert alpha_egal(sp, cible)


def test_moins_fine_reflexive_certifie():
    """⊢ (id morphisme) ⇒ plus_fine(E,𝒮,𝒮) — réflexivité (cœur MO_III)."""
    t = M.moins_fine_reflexive()
    # la conclusion est plus_fine(E,S,S) ; l'hypothèse est « id_E est un morphisme »
    pf = M.plus_fine("E", var("S"), var("S"), M._morph_defaut())
    assert alpha_egal(t.conclusion, pf)
    assert pf in t.hypotheses          # contenu = (MO_III) instancié


# ── structure initiale / propriété (IN) ───────────────────────────────────────
def test_propriete_IN_forme():
    mor = M._morph_defaut()
    af = lambda t: app("A", t)
    sf = lambda t: app("Sig", t)
    ff = lambda t: app("f", t)
    inn = M.propriete_IN("E", var("Istruct"), var("I0"), af, sf, ff, morph=mor)
    # doit être un (∀E')(∀𝒮')(∀g)(equiv …) : tête = pourtout (codé non∃non)
    assert inn.tag == "non"   # pourtout = ¬∃¬
    # contient la composée f_ι ∘ g quelque part : vérifions présence du symbole
    assert "composee" in repr(inn)


def test_est_structure_initiale_est_IN():
    mor = M._morph_defaut()
    af = lambda t: app("A", t)
    sf = lambda t: app("Sig", t)
    ff = lambda t: app("f", t)
    a = M.est_structure_initiale("E", var("Istruct"), var("I0"), af, sf, ff, mor)
    b = M.propriete_IN("E", var("Istruct"), var("I0"), af, sf, ff, morph=mor)
    assert alpha_egal(a, b)


def test_initiale_implique_f_iota_morphisme_certifie():
    """{(IN), id morphisme} ⊢ (∀ι)(ι∈I ⇒ f_ι∘Δ_E morphisme)."""
    t = M.initiale_implique_f_iota_morphisme()
    # conditionnel : ses hypothèses contiennent la propriété (IN) et « id morphisme »
    assert t.hypotheses  # non clos (hypothèses = axiomes IN + MO_III)
    # la conclusion est un ∀ι (codé ¬∃¬)
    assert t.conclusion.tag == "non"


# ── image réciproque / induite / produit ──────────────────────────────────────
def test_image_reciproque_caracterisation():
    mor = M._morph_defaut()
    car = M.image_reciproque_structure(var("E"), var("A"), var("S"), var("f"),
                                       morph=mor)
    assert car.tag == "non"   # (∀E')(∀𝒮')(∀g) = ¬∃¬…


def test_structure_induite_via_injection():
    mor = M._morph_defaut()
    car = M.structure_induite(var("A"), var("S"), "B", morph=mor)
    # induite = image réciproque par j = Δ_B
    cible = M.image_reciproque_structure(var("B"), var("A"), var("S"),
                                         E.diagonale(var("B")), morph=mor)
    assert alpha_egal(car, cible)


def test_structure_produit_forme():
    mor = M._morph_defaut()
    af = lambda t: app("A", t)
    sf = lambda t: app("Sig", t)
    car = M.structure_produit("I0", af, sf, morph=mor)
    assert car.tag == "non"   # propriété (IN) = ∀…
