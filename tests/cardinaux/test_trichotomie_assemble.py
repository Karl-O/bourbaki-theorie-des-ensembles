"""Tests — §III.2 : ASSEMBLAGE FINAL de la trichotomie contre la CIBLE SAINE (canon).

Vérifie `ensembles_trichotomie_assemble` :

  • `trichotomie_ordinaux_canon_prouve` (assemblage MAXIMAL) ⊢ trichotomie_ordinaux_canon
    (== maillon_final_cible) avec la MAXIMALITÉ et les segments dom DÉCHARGÉS sur leurs
    PREUVES (maximalite_donne_trichotomie_close, dom_h_est_segment_sous_val).  Hypothèses
    HONNÊTES survivantes = RÉSIDU STRUCTUREL irréductible
    { bo(R,E), bo(Rp,F), val_dans_F, h_graphe_hyp, 2× segment pr₂ }  (6).

  • `trichotomie_ordinaux_canon_prouve_min` (assemblage MINIMAL en COMPTE) ⊢ idem, en
    GARDANT la maximalité intacte et en ne déchargeant que le segment dom du maillon
    (5 hypothèses ; pas de h_graphe).

  • `residu_univ_app` (#8/#13) ÉLIMINÉ partout (dérivé de residu_univ_app_renforce,
    CLOS) : il n'est PLUS hypothèse d'aucun assemblage.

theorie_ensembles() = 22 (rien postulé).  Conclusion == trichotomie_ordinaux_canon.
"""
import pytest

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre import ensembles_iso_ordre_canon as C
from bourbaki.logique.i_1_termes_relations.formule import var, appartient
from bourbaki.cardinaux import ensembles_trichotomie_assemble as TA
from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP
from bourbaki.cardinaux import ensembles_trichotomie_maillon_final as MF
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
import bourbaki.cardinaux.ensembles_trichotomie_dom_segment as DS
import bourbaki.cardinaux.ensembles_maximalite_close as MAX


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(
        E.couple(var(a) if isinstance(a, str) else a, var(b) if isinstance(b, str) else b), vR)


# ── INVARIANTS GLOBAUX ───────────────────────────────────────────────────────
def test_theorie_ensembles_inchangee():
    """INVARIANT : theorie_ensembles() = 22 (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_apres_les_assemblages():
    """theorie_ensembles() reste = 22 APRÈS construction des deux assemblages."""
    TA.trichotomie_ordinaux_canon_prouve()
    TA.trichotomie_ordinaux_canon_prouve_min()
    assert len(E.theorie_ensembles().axiomes) == 22


# ── ASSEMBLAGE MAXIMAL ───────────────────────────────────────────────────────
def test_prouve_conclusion_est_trichotomie_canon():
    """trichotomie_ordinaux_canon_prouve ⊢ EXACTEMENT trichotomie_ordinaux_canon(E,R,F,Rp)."""
    thm = TA.trichotomie_ordinaux_canon_prouve()
    assert thm.conclusion == TA.trichotomie_ordinaux_canon_prouve_cible()
    assert thm.conclusion == MF.maillon_final_cible()
    tri = C.trichotomie_ordinaux_canon(var("E"), _R_de("R"), var("F"), _R_de("Rp"))
    assert thm.conclusion == tri


def test_prouve_hypotheses_exactes():
    """Hypothèses == résidu structurel documenté (2 honnêtes + val_dans_F + h_graphe + 2 seg pr₂)."""
    thm = TA.trichotomie_ordinaux_canon_prouve()
    assert set(thm.hypotheses) == set(TA.trichotomie_ordinaux_canon_prouve_hypotheses())
    assert len(set(thm.hypotheses)) == 6


def test_prouve_maximalite_et_segment_dom_decharges():
    """La MAXIMALITÉ et les segments dom ne sont PLUS des hypothèses (déchargés)."""
    thm = TA.trichotomie_ordinaux_canon_prouve()
    hs = set(thm.hypotheses)
    h = TA.TS.h_iso_max("E", "R", "F", "Rp")
    from bourbaki.logique.i_1_termes_relations.formule import ou, egal
    maxim = ou(egal(E.dom(h), var("E")), egal(E.img(h), var("F")))
    assert maxim not in hs
    for (xb, yb) in (("x", "w"), ("x", "y")):
        assert E.est_segment(E.dom(h), _R_de("R"), var("E"), xb, yb) not in hs


def test_prouve_contient_les_deux_honnetes():
    """Les 2 hypothèses HONNÊTES {bo,bo} restent PRÉSENTES."""
    thm = TA.trichotomie_ordinaux_canon_prouve()
    hs = set(thm.hypotheses)
    for honnete in FDA.fusion_depuis_coincidence_app_hypotheses():
        assert honnete in hs


def test_prouve_residu_univ_app_elimine():
    """Le RÉSIDU géométrique residu_univ_app (#8/#13) est ÉLIMINÉ (dérivé de
    residu_univ_app_renforce, CLOS) — il N'EST PLUS une hypothèse."""
    thm = TA.trichotomie_ordinaux_canon_prouve()
    assert FDA.residu_univ_app("E", "R", "F", "Rp") not in set(thm.hypotheses)


def test_prouve_non_vacueux():
    """La conclusion (trichotomie) n'est AUCUNE de ses hypothèses."""
    thm = TA.trichotomie_ordinaux_canon_prouve()
    assert thm.conclusion not in set(thm.hypotheses)


# ── ASSEMBLAGE MINIMAL (en compte) ───────────────────────────────────────────
def test_min_conclusion_est_trichotomie_canon():
    """trichotomie_ordinaux_canon_prouve_min ⊢ EXACTEMENT trichotomie_ordinaux_canon."""
    thm = TA.trichotomie_ordinaux_canon_prouve_min()
    assert thm.conclusion == TA.trichotomie_ordinaux_canon_prouve_cible()
    assert thm.conclusion == MF.maillon_final_cible()


def test_min_hypotheses_exactes():
    """Hypothèses == { bo, bo, maximalité, segment pr₂[x,w], val_dans_F } (5).
    (residu_univ_app ÉLIMINÉ — dérivé de residu_univ_app_renforce, CLOS.)"""
    thm = TA.trichotomie_ordinaux_canon_prouve_min()
    assert set(thm.hypotheses) == set(TA.trichotomie_ordinaux_canon_prouve_min_hypotheses())
    assert len(set(thm.hypotheses)) == 5


def test_min_maximalite_intacte():
    """La MAXIMALITÉ (disjonction) RESTE (NON déchargée) ; pas de h_graphe introduit."""
    thm = TA.trichotomie_ordinaux_canon_prouve_min()
    hs = set(thm.hypotheses)
    disj = [x for x in hs if x.tag == "ou"]
    assert len(disj) == 1                                  # la maximalité demeure
    assert MAX.h_graphe_hyp("E", "R", "F", "Rp") not in hs  # PAS de h_graphe (opaque)


def test_min_segment_dom_decharge_pour_val_dans_F():
    """Le segment dom[x,w] est déchargé ⇒ val_dans_F apparaît, segment dom disparaît."""
    thm = TA.trichotomie_ordinaux_canon_prouve_min()
    hs = set(thm.hypotheses)
    h = TA.TS.h_iso_max("E", "R", "F", "Rp")
    assert E.est_segment(E.dom(h), _R_de("R"), var("E"), "x", "w") not in hs
    assert DS.val_dans_F("E", "R", "F", "Rp") in hs


def test_min_residu_univ_app_elimine():
    """Le RÉSIDU géométrique residu_univ_app (#8/#13) est ÉLIMINÉ (dérivé de
    residu_univ_app_renforce, CLOS) — il N'EST PLUS une hypothèse."""
    thm = TA.trichotomie_ordinaux_canon_prouve_min()
    assert FDA.residu_univ_app("E", "R", "F", "Rp") not in set(thm.hypotheses)


def test_min_non_vacueux():
    """La conclusion (trichotomie) n'est AUCUNE de ses hypothèses."""
    thm = TA.trichotomie_ordinaux_canon_prouve_min()
    assert thm.conclusion not in set(thm.hypotheses)
