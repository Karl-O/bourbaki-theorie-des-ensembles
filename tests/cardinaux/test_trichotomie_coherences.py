"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : PREUVE des deux COHÉRENCES de h.

On certifie (ensembles_trichotomie_coherences) que les deux cohérences de h
(=h_iso_max) — verrou restant de la trichotomie — sont DÉRIVÉES d'hypothèses
géométriques EXPLICITES (les « témoins communs » = Lemme 1 §III.2), jamais postulées :

  ✅ compatibilite_ordre_depuis_temoin   : { (∀) temoin_commun_h } ⊢ compatibilite_ordre_h   (B)
  ✅ compatibilite_inverse_depuis_temoin : { (∀) temoin_commun_inv_h } ⊢ compatibilite_inverse_h (A)
  ✅ fonctionnel_depuis_temoin           : { (∀) temoin_commun_fonc_h } ⊢ est_fonctionnel(h)
  ✅ surjectivite_h_image                : ⊢ est_surjective(h, dom h, pr₂ h)   (C, INCONDITIONNEL)
  🎯🎯 h_iso_ordre_sous_temoins_communs  : { 3 témoins communs (Lemme 1) }
                                             ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques (≠ hyps).
"""
from bourbaki.logique.formule import var, egal, appartient, Formule
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_h_iso as H
from bourbaki.cardinaux import ensembles_trichotomie_coherences as C


_h = TS.h_iso_max("E", "R", "F", "Rp")


# ════════════════════════════════════════════════════════════════════════════
#  (B)  COHÉRENCE D'ORDRE  depuis le témoin commun.
# ════════════════════════════════════════════════════════════════════════════
def test_compatibilite_ordre_depuis_temoin():
    thm = C.compatibilite_ordre_depuis_temoin()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    assert C.temoin_commun_universel() in thm.hypotheses
    # conclusion = EXACTEMENT la FORMULE (B) déjà posée dans ensembles_trichotomie_h_iso
    assert thm.conclusion == H.compatibilite_ordre_h()
    assert thm.conclusion == C.compatibilite_ordre_depuis_temoin_cible()
    assert thm.conclusion not in thm.hypotheses  # non tautologique


def test_temoin_commun_est_formule_non_circulaire():
    f = C.temoin_commun_universel()
    assert isinstance(f, Formule)
    # hypothèse géométrique ≠ conclusion (B) : non circulaire
    assert f != H.compatibilite_ordre_h()


# ════════════════════════════════════════════════════════════════════════════
#  (A)  COHÉRENCE INVERSE  depuis le témoin commun.
# ════════════════════════════════════════════════════════════════════════════
def test_compatibilite_inverse_depuis_temoin():
    thm = C.compatibilite_inverse_depuis_temoin()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    assert C.temoin_commun_inv_universel() in thm.hypotheses
    assert thm.conclusion == H.compatibilite_inverse_h()
    assert thm.conclusion == C.compatibilite_inverse_depuis_temoin_cible()
    assert thm.conclusion not in thm.hypotheses


def test_temoin_inverse_non_circulaire():
    assert C.temoin_commun_inv_universel() != H.compatibilite_inverse_h()


# ════════════════════════════════════════════════════════════════════════════
#  FONCTIONNALITÉ  depuis le témoin commun (duale de A).
# ════════════════════════════════════════════════════════════════════════════
def test_fonctionnel_depuis_temoin():
    thm = C.fonctionnel_depuis_temoin()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    assert C.temoin_commun_fonc_universel() in thm.hypotheses
    assert thm.conclusion == E.est_fonctionnel(_h)
    assert thm.conclusion == C.fonctionnel_depuis_temoin_cible()
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  (C)  SURJECTIVITÉ — INCONDITIONNELLE (CLOS).
# ════════════════════════════════════════════════════════════════════════════
def test_surjectivite_h_image_close():
    thm = C.surjectivite_h_image()
    assert thm.est_clos                       # 🎯 INCONDITIONNEL
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == E.est_surjective(_h, E.dom(_h), E.img(_h))
    assert thm.conclusion == C.surjectivite_h_image_cible()


def test_surjectivite_parametrable():
    thm = C.surjectivite_h_image("Ea", "Ra", "Fa", "Rpa")
    assert thm.est_clos
    assert thm.conclusion == C.surjectivite_h_image_cible("Ea", "Ra", "Fa", "Rpa")


# ════════════════════════════════════════════════════════════════════════════
#  CASCADE — (A),(B) déchargées dans l'iso d'ordre.
# ════════════════════════════════════════════════════════════════════════════
def test_coherences_donnent_iso_sous_hyp():
    thm = C.coherences_donnent_iso_sous_hyp()
    assert not thm.est_clos
    assert thm.conclusion == C.coherences_donnent_iso_sous_hyp_cible()
    # (A),(B) ne sont PLUS hypothèses (déchargées) ; restent func/surj/2 témoins
    assert H.compatibilite_inverse_h() not in thm.hypotheses
    assert H.compatibilite_ordre_h() not in thm.hypotheses
    assert E.est_fonctionnel(_h) in thm.hypotheses
    assert E.est_surjective(_h, E.dom(_h), E.img(_h)) in thm.hypotheses
    assert C.temoin_commun_universel() in thm.hypotheses
    assert C.temoin_commun_inv_universel() in thm.hypotheses
    assert thm.conclusion not in thm.hypotheses
    assert len(thm.hypotheses) == 4


def test_coherences_et_surjectivite_donnent_iso():
    thm = C.coherences_et_surjectivite_donnent_iso()
    assert not thm.est_clos
    assert thm.conclusion == C.coherences_et_surjectivite_donnent_iso_cible()
    # surjectivité AUSSI déchargée : restent func h + 2 témoins
    assert E.est_surjective(_h, E.dom(_h), E.img(_h)) not in thm.hypotheses
    assert len(thm.hypotheses) == 3


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 CASCADE FINALE — iso d'ordre SOUS LES SEULS 3 témoins communs (Lemme 1).
# ════════════════════════════════════════════════════════════════════════════
def test_h_iso_ordre_sous_temoins_communs():
    thm = C.h_iso_ordre_sous_temoins_communs()
    assert not thm.est_clos
    assert thm.conclusion == C.h_iso_ordre_sous_temoins_communs_cible()
    declared = C.h_iso_ordre_temoins_communs_hypotheses()
    # EXACTEMENT les 3 témoins communs (Lemme 1 §III.2), rien d'autre
    assert len(thm.hypotheses) == 3
    for d in declared:
        assert d in thm.hypotheses, f"hypothèse manquante : {d}"
    for hyp in thm.hypotheses:
        assert hyp in declared, f"hypothèse étrangère : {hyp}"
    # func h, surj, (A), (B) TOUS déchargés
    assert E.est_fonctionnel(_h) not in thm.hypotheses
    assert E.est_surjective(_h, E.dom(_h), E.img(_h)) not in thm.hypotheses
    assert H.compatibilite_inverse_h() not in thm.hypotheses
    assert H.compatibilite_ordre_h() not in thm.hypotheses
    assert thm.conclusion not in thm.hypotheses


def test_temoins_communs_mutuellement_distincts():
    a = C.temoin_commun_universel()
    b = C.temoin_commun_inv_universel()
    c = C.temoin_commun_fonc_universel()
    assert a != b and a != c and b != c


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    C.compatibilite_ordre_depuis_temoin()
    C.compatibilite_inverse_depuis_temoin()
    C.fonctionnel_depuis_temoin()
    C.surjectivite_h_image()
    C.coherences_donnent_iso_sous_hyp()
    C.coherences_et_surjectivite_donnent_iso()
    C.h_iso_ordre_sous_temoins_communs()
    assert len(E.theorie_ensembles().axiomes) == 22
