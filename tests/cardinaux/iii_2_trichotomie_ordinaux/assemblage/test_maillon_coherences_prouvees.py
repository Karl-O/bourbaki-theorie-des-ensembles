"""Tests — §III.2 : le MAILLON FINAL de la trichotomie avec ses 3 COHÉRENCES PROUVÉES.

Vérifie `ensembles_maillon_coherences_prouvees` :

  • `fonctionnel_h_prouve` ⊢ EXACTEMENT est_fonctionnel(h) sous les SEULES hypothèses
    HONNÊTES { bo(R,E), bo(R',F) } (miroir de compatibilite_inverse_h_prouve, côté
    fonctionnalité).  ⚠️ `residu_univ_app` ÉLIMINÉ (dérivé de residu_univ_app_renforce).

  • `maillon_final_h_plus3` ⊢ trichotomie_ordinaux_canon(E,R,F,Rp) (== maillon_final_cible)
    avec les 3 cohérences (compatibilite_inverse_h, est_fonctionnel(h), compatibilite
    _ordre_h) REMPLACÉES par {bo,bo} : il ne reste QUE {bo,bo} + maximalité + 2 segments.
    Les 3 cohérences/témoins ont DISPARU.

theorie_ensembles() = 22 (rien postulé).
"""
import pytest

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.assemblage import ensembles_maillon_coherences_prouvees as M
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.coincidence_fusion import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences import ensembles_trichotomie_coherences as COH
import bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences.ensembles_trichotomie_h_iso as HI


def test_theorie_ensembles_inchangee():
    """INVARIANT : theorie_ensembles() = 22 (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


# ── TARGET 1 — fonctionnel_h_prouve : est_fonctionnel(h) PROUVÉE ─────────────
def test_fonctionnel_conclusion_est_la_cible():
    """fonctionnel_h_prouve ⊢ EXACTEMENT est_fonctionnel(h) (cible de fonctionnel_depuis_temoin)."""
    thm = M.fonctionnel_h_prouve()
    assert thm.conclusion == M.fonctionnel_h_prouve_cible()
    h = TS.h_iso_max("E", "R", "F", "Rp")
    assert thm.conclusion == E.est_fonctionnel(h)
    assert thm.conclusion == COH.fonctionnel_depuis_temoin_cible()


def test_fonctionnel_hypotheses_honnetes():
    """Hypothèses == exactement { bo(R,E), bo(R',F) } (2 carries) — residu_univ_app ÉLIMINÉ."""
    thm = M.fonctionnel_h_prouve()
    honnetes = set(FDA.fusion_depuis_coincidence_app_hypotheses())
    assert set(thm.hypotheses) == honnetes
    assert len(thm.hypotheses) == 2


def test_fonctionnel_non_vacueux():
    """est_fonctionnel(h) n'est AUCUNE de ses hypothèses (non tautologique)."""
    thm = M.fonctionnel_h_prouve()
    assert thm.conclusion not in thm.hypotheses


def test_fonctionnel_sans_artefact_alpha():
    """Renommage vers les liants par défaut u,v,z SANS artefact « @ »."""
    thm = M.fonctionnel_h_prouve()
    assert "@" not in repr(thm.conclusion)


# ── TARGET 2 — maillon_final_h_plus3 : 3 cohérences DÉCHARGÉES sur leurs preuves ─
def test_plus3_conclusion_est_maillon_final_cible():
    """maillon_final_h_plus3 ⊢ EXACTEMENT trichotomie_ordinaux_canon(E,R,F,Rp)."""
    mf3 = M.maillon_final_h_plus3()
    assert mf3.conclusion == M.maillon_final_h_plus3_cible()


def test_plus3_les_trois_coherences_disparues():
    """Les 3 cohérences (compat_inverse, est_fonctionnel, compat_ordre) NE sont PLUS hypothèses."""
    mf3 = M.maillon_final_h_plus3()
    hs = set(mf3.hypotheses)
    h = TS.h_iso_max("E", "R", "F", "Rp")
    assert HI.compatibilite_inverse_h("E", "R", "F", "Rp") not in hs
    assert HI.compatibilite_ordre_h("E", "R", "F", "Rp") not in hs
    assert E.est_fonctionnel(h) not in hs


def test_plus3_temoins_communs_absents():
    """Les TÉMOINS COMMUNS (que maillon_final_h_plus2 laissait) sont AUSSI absents."""
    mf3 = M.maillon_final_h_plus3()
    hs = set(mf3.hypotheses)
    assert COH.temoin_commun_universel("E", "R", "F", "Rp") not in hs
    assert COH.temoin_commun_inv_universel("E", "R", "F", "Rp") not in hs
    assert COH.temoin_commun_fonc_universel("E", "R", "F", "Rp") not in hs


def test_plus3_hypotheses_exactes():
    """Hypothèses == { bo(R,E), bo(R',F), maximalité, 2 segments } (residu ÉLIMINÉ)."""
    mf3 = M.maillon_final_h_plus3()
    assert set(mf3.hypotheses) == set(M.maillon_final_h_plus3_hypotheses())
    assert len(mf3.hypotheses) == 5


def test_plus3_contient_les_deux_honnetes():
    """Les 2 hypothèses HONNÊTES {bo,bo} sont bien PRÉSENTES (remplaçant les cohérences)."""
    mf3 = M.maillon_final_h_plus3()
    hs = set(mf3.hypotheses)
    for honnete in FDA.fusion_depuis_coincidence_app_hypotheses():
        assert honnete in hs


def test_plus3_maximalite_et_segments_restent():
    """La MAXIMALITÉ (dom h=E ∨ pr₂ h=F) et les 2 SEGMENTS demeurent."""
    mf3 = M.maillon_final_h_plus3()
    hs = set(mf3.hypotheses)
    # exactement 1 disjonction (maximalité) et 4 autres (2 honnêtes + 2 segments)
    disj = [x for x in hs if x.tag == "ou"]
    assert len(disj) == 1


def test_plus3_non_vacueux():
    """La conclusion (trichotomie) n'est AUCUNE de ses hypothèses."""
    mf3 = M.maillon_final_h_plus3()
    assert mf3.conclusion not in mf3.hypotheses


def test_theorie_apres_les_preuves():
    """theorie_ensembles() reste = 22 APRÈS construction des deux théorèmes."""
    M.fonctionnel_h_prouve()
    M.maillon_final_h_plus3()
    assert len(E.theorie_ensembles().axiomes) == 22
