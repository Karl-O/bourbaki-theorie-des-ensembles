"""Tests §III.2 — UNICITÉ FINALE de l'iso d'ordre (le « un et un seul » du Th. 3).

On certifie l'ASSEMBLAGE de bout en bout (étape (c) du blueprint
DESIGN_trichotomie_III2.md) :

  • iso_donne_strict_croissant : GLUE « iso d'ordre ⇒ strictement croissant » (pont
    yv↔y), CONDITIONNEL sous (compatible_ordre + injectivité), conclusion = la
    stricte croissance attendue par lemme_4 / point_fixe_automorphisme ;
  • auto_iso_est_identite : COROLLAIRE 1 verbatim (le seul automorphisme d'ordre d'un
    bon ordre est l'identité) = point fixe h(x)=x sous les 6 hyps structurelles ;
  • iso_unicite_finale : f=g chaîné de bout en bout (point fixe + extensionnalité),
    hypothèses géométriques explicites, conclusion f=g non tautologique.

theorie_ensembles() reste = 22 (rien postulé : RÉUTILISE point_fixe_automorphisme,
iso_unicite_extensionnel, lemme_4 et l'axiome de la paire/vide pour la glue).
"""
from bourbaki.logique.formule import var, egal, et, non, impl, appartient, pourtout, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_iso_unicite_finale as F
from bourbaki.cardinaux.ensembles_lemme4_croissante import _R_de, _val, _f_dans_E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import compatible_ordre


# ════════════════════════════════════════════════════════════════════════════
#  GLUE — iso d'ordre ⇒ strictement croissant (pont yv↔y)
# ════════════════════════════════════════════════════════════════════════════
def test_iso_donne_strict_croissant():
    """{ compatible_ordre(h,E,R,R), h injective sur E } ⊢ est_strictement_croissante(R,R,h,E,E)."""
    s = F.iso_donne_strict_croissant()
    assert not s.est_clos
    assert len(s.hypotheses) == 2
    assert s.conclusion == F.iso_donne_strict_croissant_cible()
    assert s.conclusion not in s.hypotheses               # non tautologique


def test_iso_donne_strict_croissant_hypotheses():
    """Les 2 hypothèses sont EXACTEMENT compatibilité d'ordre (binder yv) + injectivité."""
    s = F.iso_donne_strict_croissant()
    vR, vE, vh = var("R"), var("E"), var("h")
    Rf = _R_de("R")
    expected = {
        F._compat_yv(vh, vE, Rf, "x", "y"),               # compatible_ordre (binder yv)
        F._inj_hyp(vh, vE, "x", "y"),                     # h injective sur E
    }
    assert set(s.hypotheses) == expected


def test_iso_donne_strict_croissant_conclusion_exacte():
    """La conclusion est la stricte croissance au format consommé par lemme_4."""
    s = F.iso_donne_strict_croissant()
    vR, vh, vE = var("R"), var("h"), var("E")
    assert s.conclusion == est_strictement_croissante(vR, vR, vh, vE, vE, "x", "y")


def test_iso_donne_strict_croissant_parametrable():
    s = F.iso_donne_strict_croissant("Rp", "F", "phi")
    assert len(s.hypotheses) == 2
    assert s.conclusion == F.iso_donne_strict_croissant_cible("Rp", "F", "phi")


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 verbatim — le seul automorphisme d'ordre d'un bon ordre est l'identité.
# ════════════════════════════════════════════════════════════════════════════
def test_auto_iso_est_identite():
    """{ bo, h:E→E, h scr, k:E→E, k scr, k∘h=id } ⊢ (∀x)(x∈E ⇒ h(x)=x)."""
    a = F.auto_iso_est_identite()
    assert not a.est_clos
    assert len(a.hypotheses) == 6
    assert a.conclusion == F.auto_iso_est_identite_cible()
    assert a.conclusion not in a.hypotheses               # non tautologique


def test_auto_iso_hypotheses_structurelles():
    """Les 6 hypothèses sont EXACTEMENT les attendues (rien en trop, rien postulé)."""
    a = F.auto_iso_est_identite()
    hyps = set(a.hypotheses)
    vR, vE, vh, vk = var("R"), var("E"), var("h"), var("k")
    Rf = _R_de("R")
    vx = var("x")
    hx = _val(vh, vx)
    expected = {
        E.est_bien_ordonne(Rf, vE),
        _f_dans_E(vh, vE),
        est_strictement_croissante(vR, vR, vh, vE, vE),
        _f_dans_E(vk, vE),
        est_strictement_croissante(vR, vR, vk, vE, vE),
        pourtout("x", impl(appartient(vx, vE), egal(_val(vk, hx), vx))),
    }
    assert hyps == expected
    # le bon ordre est réellement consommé, la stricte croissance des deux applications aussi
    assert E.est_bien_ordonne(Rf, vE) in hyps
    assert est_strictement_croissante(vR, vR, vh, vE, vE) in hyps
    assert est_strictement_croissante(vR, vR, vk, vE, vE) in hyps


def test_auto_iso_parametrable():
    a = F.auto_iso_est_identite("Rp", "F", "phi", "psi")
    assert len(a.hypotheses) == 6
    assert a.conclusion == F.auto_iso_est_identite_cible("Rp", "F", "phi", "psi")


# ════════════════════════════════════════════════════════════════════════════
#  UNICITÉ FINALE chaînée — f = g de bout en bout.
# ════════════════════════════════════════════════════════════════════════════
def test_iso_unicite_finale():
    """{ f,g∈𝓕(E',E), bo(R,E'), h,k strict crois. E'→E', k∘h=id, mêmes valeurs } ⊢ f=g."""
    u = F.iso_unicite_finale()
    assert not u.est_clos
    assert len(u.hypotheses) == 9                         # 3 (extensionnel) + 6 (point fixe)
    assert u.conclusion == F.iso_unicite_finale_cible()
    assert u.conclusion not in u.hypotheses               # non tautologique : f=g n'est pas une hyp


def test_iso_unicite_finale_conclusion_est_fg():
    """La conclusion est bien l'égalité f=g (le « un et un seul »)."""
    u = F.iso_unicite_finale()
    assert u.conclusion == egal(var("f"), var("g"))


def test_iso_unicite_finale_porte_les_hyps_geometriques():
    """Le séquent porte BIEN les hypothèses géométriques du point fixe (chaînage réel)."""
    u = F.iso_unicite_finale()
    hyps = set(u.hypotheses)
    vR, vEp, vh, vk = var("R"), var("Ep"), var("h"), var("k")
    Rf = _R_de("R")
    # les hypothèses GÉOMÉTRIQUES du cœur point fixe sont présentes
    assert E.est_bien_ordonne(Rf, vEp) in hyps
    assert _f_dans_E(vh, vEp) in hyps
    assert est_strictement_croissante(vR, vR, vh, vEp, vEp) in hyps
    assert est_strictement_croissante(vR, vR, vk, vEp, vEp) in hyps
    # ET les hypothèses d'extensionnalité (f,g applications + mêmes valeurs)
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
        application_egale_par_valeurs,
    )
    ext = application_egale_par_valeurs("f", "g", "Ep", "E")
    for h in ext.hypotheses:
        assert h in hyps


def test_iso_unicite_finale_parametrable():
    u = F.iso_unicite_finale("ff", "gg", "Fp", "F", "Rr", "hh", "kk")
    assert len(u.hypotheses) == 9
    assert u.conclusion == egal(var("ff"), var("gg"))


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT — theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    # exercer tous les théorèmes du module avant de mesurer la théorie
    F.iso_donne_strict_croissant()
    F.auto_iso_est_identite()
    F.iso_unicite_finale()
    assert len(E.theorie_ensembles().axiomes) == 22
