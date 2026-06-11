"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : h (=h_iso_max) est un ISO D'ORDRE sur dom h.

On certifie (ensembles_trichotomie_h_iso) les conjoints de est_isomorphisme_ordre(h,
dom h, pr₂ h, R, Rp) atteignables (étape d.3-d.4 du blueprint) :

  ✅ INCONDITIONNEL (le PONT « couple ↦ valeur ») :
     • h_couple_de_valeur : { func h, u∈dom h } ⊢ (u, valeur(h,u))∈h.
       (func h + u∈dom h sont les hyps STRUCTURELLES minimales — pas de cohérence.)
  ⚠️ CONJOINTS, CONDITIONNELS à des cohérences EXPLICITES (verrou dur en hypothèse,
     jamais postulé — comme compatibilite_h ⊢ h_fonctionnel_sous_compatibilite) :
     • h_injectif_sous_compatibilite_inverse : { func h, compatibilite_inverse_h }
           ⊢ injective_dans(h, dom h).
     • h_compatible_ordre_sous_hyp : { func h, compatibilite_ordre_h }
           ⊢ compatible_ordre(h, dom h, R, Rp).
     • h_est_isomorphisme_ordre_sous_hyp : { func h, compatibilite_inverse_h,
           compatibilite_ordre_h, est_surjective(h, dom h, pr₂ h) }
           ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques.
"""
from bourbaki.logique.formule import var, egal, appartient, Formule
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_h_iso as H


_h = TS.h_iso_max("E", "R", "F", "Rp")
_func_h = E.est_fonctionnel(_h)
_u_in_domh = appartient(var("u"), E.dom(_h))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ PONT « couple ↦ valeur » — { func h, u∈dom h } ⊢ (u, valeur(h,u))∈h.
# ════════════════════════════════════════════════════════════════════════════
def test_h_couple_de_valeur():
    thm = H.h_couple_de_valeur()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 2
    assert _func_h in thm.hypotheses
    assert _u_in_domh in thm.hypotheses
    assert thm.conclusion == H.h_couple_de_valeur_cible()
    assert thm.conclusion not in thm.hypotheses


def test_h_couple_de_valeur_parametrable():
    thm = H.h_couple_de_valeur("Ea", "Ra", "Fa", "Rpa", "t")
    assert not thm.est_clos
    assert thm.conclusion == H.h_couple_de_valeur_cible("Ea", "Ra", "Fa", "Rpa", "t")


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ INJECTIVITÉ sous cohérence inverse — CONDITIONNEL (2 hyps).
# ════════════════════════════════════════════════════════════════════════════
def test_h_injectif_sous_compatibilite_inverse():
    thm = H.h_injectif_sous_compatibilite_inverse()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 2
    assert _func_h in thm.hypotheses
    assert H.compatibilite_inverse_h() in thm.hypotheses
    assert thm.conclusion == H.h_injectif_sous_compatibilite_inverse_cible()
    assert thm.conclusion not in thm.hypotheses


def test_compatibilite_inverse_est_formule():
    # c'est une FORMULE (hypothèse posée), PAS un théorème
    f = H.compatibilite_inverse_h()
    assert isinstance(f, Formule)
    # forme (∀u)(∀v)(∀u')(...) — ∀ encodé ¬∃¬
    assert f.tag == "non" and f.sous[0].tag == "exists"


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ COMPATIBILITÉ D'ORDRE sous cohérence d'ordre — CONDITIONNEL (2 hyps).
# ════════════════════════════════════════════════════════════════════════════
def test_h_compatible_ordre_sous_hyp():
    thm = H.h_compatible_ordre_sous_hyp()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 2
    assert _func_h in thm.hypotheses
    assert H.compatibilite_ordre_h() in thm.hypotheses
    assert thm.conclusion == H.h_compatible_ordre_sous_hyp_cible()
    assert thm.conclusion not in thm.hypotheses


def test_compatibilite_ordre_est_formule():
    f = H.compatibilite_ordre_h()
    assert isinstance(f, Formule)
    assert f.tag == "non" and f.sous[0].tag == "exists"


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE — h iso d'ordre de dom h sur pr₂ h, sous 4 hyps de cohérence.
# ════════════════════════════════════════════════════════════════════════════
def test_h_est_isomorphisme_ordre_sous_hyp():
    thm = H.h_est_isomorphisme_ordre_sous_hyp()
    assert not thm.est_clos
    hyps = thm.hypotheses
    for hyp in H.h_est_isomorphisme_ordre_hypotheses():
        assert hyp in hyps, f"hypothèse manquante : {hyp}"
    assert thm.conclusion == H.h_est_isomorphisme_ordre_sous_hyp_cible()
    assert thm.conclusion not in thm.hypotheses
    # la conclusion est bien la conjonction (bijective et compatible d'ordre) :
    # « et » est encodé ¬(¬a ∨ ¬b), donc tag 'non' enveloppant un 'ou'.
    assert thm.conclusion.tag == "non" and thm.conclusion.sous[0].tag == "ou"


def test_assemblage_n_introduit_pas_d_hyp_etrangere():
    # AUCUNE hypothèse hors des 4 déclarées (pas de fuite)
    thm = H.h_est_isomorphisme_ordre_sous_hyp()
    declarees = H.h_est_isomorphisme_ordre_hypotheses()
    for hyp in thm.hypotheses:
        assert hyp in declarees, f"hypothèse étrangère : {hyp}"
    assert len(thm.hypotheses) == len(declarees)


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    H.h_couple_de_valeur()
    H.h_injectif_sous_compatibilite_inverse()
    H.h_compatible_ordre_sous_hyp()
    H.h_est_isomorphisme_ordre_sous_hyp()
    assert len(E.theorie_ensembles().axiomes) == 22
