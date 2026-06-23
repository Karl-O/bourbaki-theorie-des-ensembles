"""Tests — §III.2 : les deux COHÉRENCES de h (=h_iso_max) PROUVÉES comme THÉORÈMES.

Vérifie que `ensembles_h_bien_defini` DÉRIVE (sans postuler) les FORMULES de cohérence
`compatibilite_inverse_h` (A) et `compatibilite_ordre_h` (B) — POSÉES en hypothèses
explicites dans `ensembles_trichotomie_h_iso` — sous les SEULES hypothèses HONNÊTES
{ bo(R,E), bo(R',F) }.

Contrôles : conclusion == la FORMULE-builder (importée de ensembles_trichotomie_h_iso) ;
hypothèses == exactement les 2 carries honnêtes {bo,bo} (residu_univ_app ÉLIMINÉ) ;
NON vacuité ; theorie_ensembles=22.
"""
import pytest

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_h_bien_defini as HBD
# FORMULE-builders importés depuis le module d'origine (source de vérité des cibles)
from bourbaki.cardinaux.ensembles_trichotomie_h_iso import (
    compatibilite_inverse_h, compatibilite_ordre_h,
)


def test_theorie_ensembles_inchangee():
    """INVARIANT : theorie_ensembles() = 22 (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


# ── TARGET 1 — compatibilite_inverse_h (A) ───────────────────────────────────
def test_target1_conclusion_est_la_formule():
    """compatibilite_inverse_h_prouve ⊢ EXACTEMENT compatibilite_inverse_h (FORMULE)."""
    thm = HBD.compatibilite_inverse_h_prouve()
    assert thm.conclusion == compatibilite_inverse_h()        # FORMULE d'origine (défauts)
    assert thm.conclusion == HBD.compatibilite_inverse_h_prouve_cible()


def test_target1_hypotheses_honnetes():
    """Hypothèses == exactement { bo(R,E), bo(R',F) } (2 carries)."""
    thm = HBD.compatibilite_inverse_h_prouve()
    assert set(thm.hypotheses) == set(HBD.h_bien_defini_hypotheses())
    assert len(thm.hypotheses) == 2


def test_target1_non_vacueux():
    """La conclusion (A) n'est AUCUNE de ses hypothèses (non tautologique)."""
    thm = HBD.compatibilite_inverse_h_prouve()
    assert thm.conclusion not in thm.hypotheses


def test_target1_sans_artefact_alpha():
    """Renommage vers les liants par défaut u,v,u' SANS artefact « @ »."""
    thm = HBD.compatibilite_inverse_h_prouve()
    assert "@" not in repr(thm.conclusion)


# ── TARGET 2 — compatibilite_ordre_h (B) ─────────────────────────────────────
def test_target2_conclusion_est_la_formule():
    """compatibilite_ordre_h_prouve ⊢ EXACTEMENT compatibilite_ordre_h (FORMULE)."""
    thm = HBD.compatibilite_ordre_h_prouve()
    assert thm.conclusion == compatibilite_ordre_h()          # FORMULE d'origine (défauts)
    assert thm.conclusion == HBD.compatibilite_ordre_h_prouve_cible()


def test_target2_hypotheses_honnetes():
    """Hypothèses == exactement { bo(R,E), bo(R',F) } (2 carries)."""
    thm = HBD.compatibilite_ordre_h_prouve()
    assert set(thm.hypotheses) == set(HBD.h_bien_defini_hypotheses())
    assert len(thm.hypotheses) == 2


def test_target2_non_vacueux():
    """La conclusion (B) n'est AUCUNE de ses hypothèses (non tautologique)."""
    thm = HBD.compatibilite_ordre_h_prouve()
    assert thm.conclusion not in thm.hypotheses


def test_target2_sans_artefact_alpha():
    """Renommage vers les liants par défaut u,v,u',v' SANS artefact « @ »."""
    thm = HBD.compatibilite_ordre_h_prouve()
    assert "@" not in repr(thm.conclusion)


def test_theorie_apres_les_preuves():
    """theorie_ensembles() reste = 22 APRÈS construction des deux preuves."""
    HBD.compatibilite_inverse_h_prouve()
    HBD.compatibilite_ordre_h_prouve()
    assert len(E.theorie_ensembles().axiomes) == 22
