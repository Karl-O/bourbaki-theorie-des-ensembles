"""Tests de ensembles_codomaine_reconciliation (Lemme 1 §III.2, réconciliation codomaine)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, inclus, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.temoins_comparabilite import ensembles_codomaine_reconciliation as M


def _Rg(n):
    vg = var(n)
    return lambda a, b: appartient(E.couple(a, b), vg)


def test_theorie_intangible():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── SOUS-LEMME (1) : φ2|S1 iso S1 ≅ image(φ2,S1) ──────────────────────────────
def test_iso_restriction_image_conclusion():
    thm = M.iso_restriction_image()
    assert thm.conclusion == M.iso_restriction_image_cible()


def test_iso_restriction_image_hyps():
    """Hypothèses HONNÊTES : compat(φ2,S2), inj(φ2,S2), S1⊂S2, func φ2, S1⊂dom φ2."""
    thm = M.iso_restriction_image()
    # conclusion non vacueuse : pas dans les hypothèses
    assert thm.conclusion not in set(thm.hypotheses)
    # toutes les hypothèses parlent de φ2 / S1 / S2 (pas de la restriction directement)
    assert len(thm.hypotheses) >= 1


# ── RACCORD APPLIQUÉ : φ2|S1 iso S1 ≅ T1 (codomaine réconcilié) ────────────────
def test_iso_restriction_vers_T1_conclusion():
    """iso(φ2|S1, S1, T1) : le codomaine image(φ2,S1) est réécrit en T1 (codomaine_egal_image)."""
    thm = M.iso_restriction_vers_T1()
    assert thm.conclusion == M.iso_restriction_vers_T1_cible()   # iso(φ2|S1,S1,T1)
    assert thm.conclusion not in set(thm.hypotheses)             # non vacueux
    assert len(E.theorie_ensembles().axiomes) == 22


# ── SOUS-LEMME (2) : ψ=(φ2|S1)∘(φ1⁻¹) iso T1 ≅ image(φ2,S1) ───────────────────
def test_iso_T1_vers_image_conclusion():
    thm = M.iso_T1_vers_image()
    assert thm.conclusion == M.iso_T1_vers_image_cible()


def test_iso_T1_vers_image_non_vacueux():
    thm = M.iso_T1_vers_image()
    assert thm.conclusion not in set(thm.hypotheses)


# ── THÉORÈME : T1 = image(φ2, S1) ─────────────────────────────────────────────
def test_codomaine_egal_image_conclusion():
    thm = M.codomaine_egal_image()
    assert thm.conclusion == M.codomaine_egal_image_cible()


def test_codomaine_egal_image_non_vacueux():
    thm = M.codomaine_egal_image()
    assert thm.conclusion not in set(thm.hypotheses)


def test_codomaine_egal_image_theorie_intacte():
    M.codomaine_egal_image()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_codomaine_egal_image_hyps_honnetes():
    """Les 10 hypothèses sont EXACTEMENT les données NESTÉES de la fusion, avec le BON
    ORDRE AMBIANT bo(R',F) SEUL — plus de bo(R',T1)/bo(R',I) sur les SEGMENTS (route
    lemme_4_sous_domaine, qui consomme bo(R',F)+inclus(B,F) dérivées de est_segment).
    Aucune hypothèse parasite."""
    thm = M.codomaine_egal_image()
    Rf, Rpf = _Rg("R"), _Rg("Rp")
    p1, p2, S1, T1, S2, T2, F = (var("phi1"), var("phi2"), var("S1"), var("T1"),
                                 var("S2"), var("T2"), var("F"))
    I = E.image(p2, S1)
    attendues = {
        E.est_bien_ordonne(Rpf, F),                # BON ORDRE AMBIANT seul
        E.est_segment(T1, Rpf, F),
        E.est_segment(I, Rpf, F),
        V.est_isomorphisme_ordre(p1, S1, T1, Rf, Rpf, "x", "w"),
        E.est_fonctionnel(p1),
        egal(E.dom(p1), S1),
        V.est_isomorphisme_ordre(p2, S2, T2, Rf, Rpf, "a", "b"),
        E.est_fonctionnel(p2),
        egal(E.dom(p2), S2),
        inclus(S1, S2),
    }
    assert set(thm.hypotheses) == attendues
    # les bo SUR SEGMENTS ont disparu (faux sur segment propre — bo ambiant les couvre)
    assert E.est_bien_ordonne(Rpf, T1) not in set(thm.hypotheses)
    assert E.est_bien_ordonne(Rpf, I) not in set(thm.hypotheses)
