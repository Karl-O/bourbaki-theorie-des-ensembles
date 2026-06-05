"""Tests §IV.2.1 — Morphismes (fragment objet relationnel).

Chaque test vérifie que la CONCLUSION du théorème renvoyé par le noyau est
EXACTEMENT la cible visée (et qu'il est clos pour les théorèmes inconditionnels,
ou que ses hypothèses sont les conditions attendues pour les conditionnels).
"""
from bourbaki.logique.formule import var, et, impl, appartient, alpha_egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.fonctions import ensembles_morphismes as M


def test_identite_preserve_clos_et_cible():
    """⊢ preserve_relation(Δ_E, E, R, R)  (clos)."""
    t = M.identite_preserve()
    assert t.est_clos
    cible = M.preserve_relation(E.diagonale(var("E")), var("E"),
                                M._rel_defaut("G"), M._rel_defaut("G"))
    assert alpha_egal(t.conclusion, cible)


def test_identite_est_morphisme_clos_et_cible():
    """⊢ est_morphisme(Δ_E, E, E, R, R)  (clos) — « id est un morphisme »."""
    t = M.identite_est_morphisme()
    assert t.est_clos
    cible = M.est_morphisme(E.diagonale(var("E")), var("E"), var("E"),
                            M._rel_defaut("G"), M._rel_defaut("G"))
    assert alpha_egal(t.conclusion, cible)


def test_composee_preserve_cible():
    """⊢ (u∈E et v∈E et R{u,v}) ⇒ R''{(G∘F)u,(G∘F)v}  (MO_II, pointwise)."""
    t = M.composee_preserve()
    vu, vv, vE = var("u"), var("v"), var("E")
    comp = E.composee(var("G"), var("F"))
    r, rpp = M._rel_defaut("G_R"), M._rel_defaut("G_Rpp")
    gofu, gofv = E.valeur(comp, vu), E.valeur(comp, vv)
    cible = impl(et(et(appartient(vu, vE), appartient(vv, vE)), r(vu, vv)),
                 rpp(gofu, gofv))
    assert t.conclusion == cible


def test_composee_preserve_hypotheses_contiennent_les_preservations():
    """Les hypothèses (MO_II conditionnel) contiennent bien les deux clauses de
    préservation de f et de g — c'est le contenu axiomatique de MO_II."""
    t = M.composee_preserve()
    pres_f = M.preserve_relation(var("F"), var("E"),
                                 M._rel_defaut("G_R"), M._rel_defaut("G_Rp"))
    pres_g = M.preserve_relation(var("G"), var("Ep"),
                                 M._rel_defaut("G_Rp"), M._rel_defaut("G_Rpp"))
    assert pres_f in t.hypotheses
    assert pres_g in t.hypotheses


def test_plus_fine_est_preservation_identite():
    """« 𝒮₁ plus fine que 𝒮₂ » (IV.2.2) = Δ_E préserve R₁ vers R₂ (définition)."""
    r1, r2 = M._rel_defaut("G1"), M._rel_defaut("G2")
    pf = M.plus_fine_morphisme("E", r1, r2)
    cible = M.est_morphisme(E.diagonale(var("E")), var("E"), var("E"), r1, r2)
    assert pf == cible
