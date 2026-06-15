"""Tests §III.2 — PONT ADJOINT ↔ R au sommet (ensembles_maximalite_adjoint_bridge).

On certifie :

  🎯 TARGET 1 — adjoint_egale_R_au_sommet :
        { a R-majorant de S∪{a} } ⊢ (∀xq∀yq)( ≤'_a{xq,yq} ⇔ R{xq,yq} ) sur S∪{a}.
     Le PONT : l'ordre adjoint COÏNCIDE avec R sur le segment FERMÉ.  1 hyp HONNÊTE.

  🎯 TARGET 2 — iso_hplus_pour_R :
     RÉÉCRIT iso(h⁺, ≤'_a, ≤'_b) [extension_iso_depuis_iso_h] en iso(h⁺, R, Rp)
     = RÉSIDU (3) de maximalite_donne_trichotomie_prouve.  Le RÉSIDU (3) DÉRIVE
     ainsi de extension_iso_depuis_iso_h (lemme prouvé) + le pont.

  ⚙️ majorant_seg_ferme_depuis_bo : les 2 majorants de TARGET 2 sont DÉCHARGEABLES
     depuis {bo, sommet∈ensemble} (réflexivité + déf. segment).

  ⚠️ TARGET 3 — maximalite_donne_trichotomie_prouve_v2 : BLOQUÉ (binder-collision
     de la machinerie recollement EXISTANTE avec le τ imbriqué du témoin a*).

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Conclusions NON vacueuses.
"""
import pytest

from bourbaki.logique.formule import var, appartient, egal, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.cardinaux import ensembles_trichotomie_extension_iso as EXT
from bourbaki.cardinaux import ensembles_maximalite_adjoint_bridge as B


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 1 — adjoint_egale_R_au_sommet : ≤'_a ⇔ R sur S∪{a}.
# ════════════════════════════════════════════════════════════════════════════
def test_target1_conclusion():
    thm = B.adjoint_egale_R_au_sommet()
    assert thm.conclusion == B.adjoint_egale_R_au_sommet_cible()
    assert thm.conclusion not in thm.hypotheses        # NON vacueux


def test_target1_une_seule_hyp_honnete():
    thm = B.adjoint_egale_R_au_sommet()
    assert not thm.est_clos
    # UNIQUE hypothèse : « a est R-majorant de S∪{a} »
    assert len(thm.hypotheses) == 1
    assert B.majorant_de_adjoint("R", "S", "a") in thm.hypotheses


def test_target1_theorie_intacte():
    B.adjoint_egale_R_au_sommet()
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  ⚙️ majorant_seg_ferme_depuis_bo : le majorant DÉRIVE de bo + sommet∈ensemble.
# ════════════════════════════════════════════════════════════════════════════
def test_majorant_depuis_bo():
    thm = B.majorant_seg_ferme_depuis_bo()
    assert not thm.est_clos
    S = B._seg("R", "E", "a")
    assert thm.conclusion == B.majorant_de_adjoint("R", S, "a")
    # 2 hyps HONNÊTES : bo(R,E), a∈E
    Rf = _R_de("R")
    assert E.est_bien_ordonne(Rf, var("E")) in thm.hypotheses
    assert appartient(var("a"), var("E")) in thm.hypotheses
    assert len(thm.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 2 — iso_hplus_pour_R = RÉSIDU (3) DÉRIVÉ (binders px/pw, R/Rp).
# ════════════════════════════════════════════════════════════════════════════
def test_target2_conclusion_est_residu3():
    thm = B.iso_hplus_pour_R()
    assert thm.conclusion == B.iso_hplus_pour_R_cible()
    assert thm.conclusion.tag == "non"                 # = et(bijective, compat), encodé ¬(¬∨¬)
    assert thm.conclusion not in thm.hypotheses        # NON vacueux


def test_target2_hypotheses_classees():
    thm = B.iso_hplus_pour_R()
    assert not thm.est_clos
    hyps = set(thm.hypotheses)
    # 9 hyps de extension_iso_depuis_iso_h
    ext9 = set(EXT.extension_iso_depuis_iso_h_hypotheses())
    assert ext9 <= hyps and len(ext9) == 9
    # 2 majorants (source S∪{a}, but T∪{b})
    S = EXT._seg_S("R", "E", "a")
    T = EXT._seg_T("Rp", "F", "b")
    majS = B.majorant_de_adjoint("R", S, "a")
    majT = B.majorant_de_adjoint("Rp", T, "b")
    assert majS in hyps and majT in hyps
    # inclusion h⁺ ⊂ (S∪{a})×(T∪{b})  (= RÉSIDU (10))  + dom h⁺ = S∪{a}
    hplus = EXT._hplus("E", "R", "F", "Rp", "a", "b")
    SaA = V.ensemble_adjoint(S, var("a"))
    TbB = V.ensemble_adjoint(T, var("b"))
    incl = inclus(hplus, E.produit(SaA, TbB))
    dom_eq = egal(E.dom(hplus), SaA)
    assert incl in hyps and dom_eq in hyps
    # décompte EXACT : 9 + 2 + 1 + 1 = 13
    assert hyps == ext9 | {majS, majT, incl, dom_eq}
    assert len(hyps) == 13


def test_target2_bijection_invariante():
    """Le conjoint est_bijective(h⁺,S∪{a},T∪{b}) est INVARIANT (indép. de la relation)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche as cg)
    iso_adj = EXT.extension_iso_depuis_iso_h()
    bij_adj = cg(iso_adj)
    iso_R = B.iso_hplus_pour_R()
    bij_R = cg(iso_R)
    # même conjoint gauche (la bijection) dans les deux iso
    assert bij_adj.conclusion == bij_R.conclusion


def test_target2_majorants_discharges():
    thm = B.iso_hplus_pour_R_majorants_discharges()
    assert thm.conclusion == B.iso_hplus_pour_R_cible()
    hyps = set(thm.hypotheses)
    # les 2 majorants ne survivent plus
    S = EXT._seg_S("R", "E", "a")
    T = EXT._seg_T("Rp", "F", "b")
    assert B.majorant_de_adjoint("R", S, "a") not in hyps
    assert B.majorant_de_adjoint("Rp", T, "b") not in hyps
    # remplacés par bo(R,E), a∈E, bo(Rp,F), b∈F
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    assert E.est_bien_ordonne(Rf, var("E")) in hyps
    assert appartient(var("a"), var("E")) in hyps
    assert E.est_bien_ordonne(Rpf, var("F")) in hyps
    assert appartient(var("b"), var("F")) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22


def test_target2_theorie_intacte():
    B.iso_hplus_pour_R()
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ TARGET 3 — BLOQUÉ : binder-collision du recollement EXISTANT au témoin a*.
# ════════════════════════════════════════════════════════════════════════════
def test_target3_bloque_honnetement():
    """v2 LÈVE (NotImplementedError) : substituer TARGET 2 au témoin a*=τx(…) bute sur
    une collision de binders DANS LES MODULES EXISTANTS (non modifiables), pas sur un
    trou du pont (TARGET 1/2 clos).  La cible est exposée."""
    assert B.maximalite_donne_trichotomie_prouve_v2_cible().tag == "ou"
    with pytest.raises(NotImplementedError):
        B.maximalite_donne_trichotomie_prouve_v2()
