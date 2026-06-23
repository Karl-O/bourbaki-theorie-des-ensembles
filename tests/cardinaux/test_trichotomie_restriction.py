"""Tests §III.2 — BRIQUES de cohérence de l'iso maximal h (trichotomie, Th3) :
RESTRICTION / COMPARABILITÉ des segments témoins / COÏNCIDENCE par unicité.

Certifie que `ensembles_trichotomie_restriction` livre RÉELLEMENT les trois briques
qui alimentent (A) compatibilite_inverse_h et (B) compatibilite_ordre_h :

  (2) comparabilite_segments_temoins : {bo, t∈E, s∈E} ⊢ seg(t)⊂seg(s) ou seg(s)⊂seg(t)
      — INCONDITIONNELLE (forme conditionnelle + close).
  (1) restriction_compatible_ordre   : {compatible_ordre(φ,S,R,R'), S0⊂S}
                                          ⊢ compatible_ordre(φ,S0,R,R')
      — INCONDITIONNELLE (forme conditionnelle + close).
  (3) coincidence_sur_chevauchement  : {géométrie auto-iso + rétraction φ'∘φ'⁻¹=id}
                                          ⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))
      — CONDITIONNELLE (6 hyps géométriques d'auto_iso_est_identite + 1 rétraction).

Aucune conclusion n'est tautologie / postulée ; theorie=22 ; rien de modifié ailleurs.
"""
from bourbaki.logique.formule import appartient, var, inclus, ou, egal, impl, et
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.cardinaux import ensembles_trichotomie_restriction as Rstr
from bourbaki.cardinaux.ensembles_iso_unicite_finale import auto_iso_est_identite
from bourbaki.cardinaux.ensembles_iso_unicite_sous_domaine import (
    auto_iso_est_identite_sous_domaine,
)


def _R_de(R="R"):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE (2) — comparabilité des segments témoins
# ════════════════════════════════════════════════════════════════════════════
def test_comparabilite_segments_conditionnelle():
    """{ bo, t∈E, s∈E } ⊢ ( seg(t)⊂seg(s) ou seg(s)⊂seg(t) )."""
    thm = Rstr.comparabilite_segments_temoins()
    assert not thm.est_clos
    assert thm.conclusion == Rstr.comparabilite_segments_temoins_cible()
    assert thm.conclusion not in thm.hypotheses


def test_comparabilite_segments_trois_hypotheses():
    """Exactement les 3 hypothèses canoniques { bo, t∈E, s∈E }, rien d'autre."""
    thm = Rstr.comparabilite_segments_temoins()
    Rf = _R_de("R")
    vE, vt, vs = var("E"), var("t"), var("s")
    bo = E.est_bien_ordonne(Rf, vE)
    tin = appartient(vt, vE)
    sin = appartient(vs, vE)
    assert set(thm.hypotheses) == {bo, tin, sin}


def test_comparabilite_segments_close():
    """Forme CLOSE : 0 hypothèse, but = conséquent le plus interne."""
    clos = Rstr.comparabilite_segments_temoins_clos()
    assert clos.est_clos
    assert not clos.hypotheses
    c = clos.conclusion
    for _ in range(3):
        assert c.tag == "ou"   # impl encodé en ¬A ∨ B
        c = c.sous[1]
    assert c == Rstr.comparabilite_segments_temoins_cible()


def test_comparabilite_segments_parametrable():
    """Fonctionne sur d'autres noms (R',F,u,v)."""
    thm = Rstr.comparabilite_segments_temoins("Rp", "F", "u", "v")
    assert thm.conclusion == Rstr.comparabilite_segments_temoins_cible("Rp", "F", "u", "v")


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE (1) — restriction préserve la compatibilité d'ordre
# ════════════════════════════════════════════════════════════════════════════
def test_restriction_compatible_conditionnelle():
    """{ compatible_ordre(φ,S,R,R'), S0⊂S } ⊢ compatible_ordre(φ,S0,R,R')."""
    thm = Rstr.restriction_compatible_ordre()
    assert not thm.est_clos
    assert thm.conclusion == Rstr.restriction_compatible_ordre_cible()
    assert thm.conclusion not in thm.hypotheses


def test_restriction_compatible_deux_hypotheses():
    """Exactement 2 hypothèses : compatible_ordre(φ,S,R,R') et S0⊂S."""
    thm = Rstr.restriction_compatible_ordre()
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    vphi, vS, vS0 = var("phi"), var("S"), var("S0")
    compat_S = V.compatible_ordre(vphi, vS, Rf, Rpf)
    incl = inclus(vS0, vS)
    assert set(thm.hypotheses) == {compat_S, incl}


def test_restriction_compatible_close():
    """Forme CLOSE : 0 hypothèse, cible = conséquent le plus interne (2 impl)."""
    clos = Rstr.restriction_compatible_ordre_clos()
    assert clos.est_clos
    assert not clos.hypotheses
    c = clos.conclusion
    for _ in range(2):
        assert c.tag == "ou"
        c = c.sous[1]
    assert c == Rstr.restriction_compatible_ordre_cible()


def test_restriction_compatible_non_tautologique():
    """La conclusion compatible_ordre(φ,S0) n'est pas l'hypothèse compatible_ordre(φ,S)
    (S0 ≠ S) : pas une tautologie déguisée."""
    thm = Rstr.restriction_compatible_ordre()
    cible = Rstr.restriction_compatible_ordre_cible()
    for h in thm.hypotheses:
        assert cible != h


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE (3) — coïncidence sur le chevauchement par unicité (auto_iso=id)
# ════════════════════════════════════════════════════════════════════════════
def test_coincidence_conditionnelle():
    """{ géométrie auto-iso + rétraction } ⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))."""
    thm = Rstr.coincidence_sur_chevauchement()
    assert not thm.est_clos
    assert thm.conclusion == Rstr.coincidence_sur_chevauchement_cible()
    assert thm.conclusion not in thm.hypotheses


def test_coincidence_hypotheses_explicites():
    """Les 8 hypothèses = exactement les 7 d'auto_iso_est_identite_sous_domaine (sur
    R,E,S,c,k — BON ORDRE AMBIANT bo(R,E)+inclus(S,E), JAMAIS bo(R,S)) + la rétraction
    φ'(c(u))=φ(u) — toutes EXPLICITES, fidèles, non postulées."""
    thm = Rstr.coincidence_sur_chevauchement()
    auto = auto_iso_est_identite_sous_domaine("R", "E", "S", "c", "k", x="u")
    auto_hyps = set(auto.hypotheses)
    b3_hyps = set(thm.hypotheses)
    assert auto_hyps.issubset(b3_hyps), "les hyps d'auto_iso (sous-domaine) doivent figurer"
    retr = Rstr._retraction_phip("R", "S", "phi", "phip", "c", "u")
    assert b3_hyps == auto_hyps | {retr}, "exactement auto_iso sous-domaine + rétraction"
    assert len(b3_hyps) == 8
    # le bon ordre est AMBIANT : bo(R,E)+inclus(S,E), jamais bo(R,S) (faux sur segment propre)
    Rf = _R_de("R")
    assert E.est_bien_ordonne(Rf, var("E")) in b3_hyps
    assert inclus(var("S"), var("E")) in b3_hyps
    assert E.est_bien_ordonne(Rf, var("S")) not in b3_hyps


def test_coincidence_non_vacueux():
    """La conclusion (∀u)(u∈S ⇒ φ(u)=φ'(u)) n'est aucune des 7 hypothèses."""
    thm = Rstr.coincidence_sur_chevauchement()
    cible = Rstr.coincidence_sur_chevauchement_cible()
    for h in thm.hypotheses:
        assert cible != h


# ════════════════════════════════════════════════════════════════════════════
#  Invariant global
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    """theorie_ensembles() = 22 : aucun axiome ajouté."""
    assert len(E.theorie_ensembles().axiomes) == 22
