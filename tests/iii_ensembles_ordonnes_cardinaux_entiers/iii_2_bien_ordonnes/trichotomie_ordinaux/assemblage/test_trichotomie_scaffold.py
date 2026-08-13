"""Tests §III.2 — SCAFFOLDING du Théorème 3 (TRICHOTOMIE) : l'iso MAXIMAL h.

On certifie le scaffolding inconditionnel de l'étape (d) du blueprint :
  • l'axiome DÉDIÉ de h = union des graphes d'iso de segments isomorphes (theorie=22) ;
  • h ⊂ E×F (h_inclus_produit), témoin (h_membre_donne_temoin) ;
  • chaque couple (u,v=φ(u)) d'un iso de segments ∈ h (couple_iso_dans_h) ;
  • dom(h)⊂E, pr₂(h)⊂F (h_dom_inclus_E / h_img_inclus_F) ;
  • la fonctionnalité de h SOUS compatibilité (h_fonctionnel_sous_compatibilite) ;
  • le cœur dur (maximalité ⇒ trichotomie) POSÉ conditionnel/REPORTÉ (formule).
theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, appartient, egal, Formule
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.maximalite import ensembles_trichotomie_scaffold_maximalite as M


# ════════════════════════════════════════════════════════════════════════════
#  Axiome de h + caractérisation de membre  (theorie dédiée, theorie=22).
# ════════════════════════════════════════════════════════════════════════════
def test_h_membre_clos():
    """(u,v)∈h ⇔ corps_h — axiome définitionnel de h instancié, CLOS."""
    hm = TS.h_membre()
    assert hm.est_clos


def test_theorie_h_dediee_et_intacte():
    """h est introduit dans une théorie DÉDIÉE ; theorie_ensembles() reste = 22."""
    th = TS.theorie_h()
    assert len(th.axiomes) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  h ⊂ E×F  +  témoin  (INCONDITIONNELS).
# ════════════════════════════════════════════════════════════════════════════
def test_h_inclus_produit():
    """⊢ (∀u)(∀v)((u,v)∈h ⇒ (u∈E et v∈F))  — INCONDITIONNEL."""
    hip = TS.h_inclus_produit()
    assert hip.est_clos and not hip.hypotheses
    assert hip.conclusion == TS.h_inclus_produit_cible()


def test_h_membre_donne_temoin():
    """⊢ (∀u)(∀v)((u,v)∈h ⇒ témoin (S,T,φ))  — INCONDITIONNEL."""
    hdt = TS.h_membre_donne_temoin()
    assert hdt.est_clos and not hdt.hypotheses
    assert hdt.conclusion == TS.h_membre_donne_temoin_cible()


# ════════════════════════════════════════════════════════════════════════════
#  couple_iso_dans_h : chaque (u, v=φ(u)) d'un iso de segments ∈ h  (INCOND.).
# ════════════════════════════════════════════════════════════════════════════
def test_couple_iso_dans_h():
    """{ S seg E, T seg F, φ:S≅T iso, u∈S, u∈E, v∈F, v=φ(u),
        func φ, dom φ=S, φ⊂S×T } ⊢ (u,v)∈h.

    ⚠️ ARCHITECTURE func/dom : le témoin de h porte désormais 8 conjoints (5 originaux
    + func + dom + graphe), donc couple_iso_dans_h requiert 10 hypothèses (7 + 3)."""
    cid = TS.couple_iso_dans_h()
    assert not cid.est_clos
    assert len(cid.hypotheses) == 10           # 7 structurelles + 3 « φ application »
    assert cid.conclusion == TS.couple_iso_dans_h_cible()
    assert cid.conclusion not in cid.hypotheses    # NON vacueux
    # les hypothèses-clés (segments + iso + v=φ(u) + func/dom/graphe) sont présentes
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    Rf = TS._R_de("R")
    Rpf = TS._R_de("Rp")
    vS, vT, vphi, vu, vv = var("S"), var("T"), var("phi"), var("u"), var("v")
    assert E.est_segment(vS, Rf, var("E")) in cid.hypotheses
    assert E.est_segment(vT, Rpf, var("F")) in cid.hypotheses
    assert V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw") in cid.hypotheses
    assert egal(vv, E.valeur(vphi, vu)) in cid.hypotheses
    assert E.est_fonctionnel(vphi) in cid.hypotheses
    assert egal(E.dom(vphi), vS) in cid.hypotheses
    assert inclus(vphi, E.produit(vS, vT)) in cid.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  dom(h) ⊂ E  et  pr₂(h) ⊂ F  (INCONDITIONNELS).
# ════════════════════════════════════════════════════════════════════════════
def test_h_dom_inclus_E():
    """⊢ dom(h) ⊂ E  — INCONDITIONNEL."""
    de = M.h_dom_inclus_E()
    assert de.est_clos and not de.hypotheses
    assert de.conclusion == M.h_dom_inclus_E_cible()


def test_h_img_inclus_F():
    """⊢ pr₂(h) ⊂ F  — INCONDITIONNEL."""
    ie = M.h_img_inclus_F()
    assert ie.est_clos and not ie.hypotheses
    assert ie.conclusion == M.h_img_inclus_F_cible()


# ════════════════════════════════════════════════════════════════════════════
#  Fonctionnalité de h SOUS compatibilité  (CONDITIONNEL, hypothèse EXPLICITE).
# ════════════════════════════════════════════════════════════════════════════
def test_h_fonctionnel_sous_compatibilite():
    """{ compatibilite_h } ⊢ est_fonctionnel(h)  — CONDITIONNEL, NON vacueux."""
    hf = M.h_fonctionnel_sous_compatibilite()
    assert not hf.est_clos
    assert len(hf.hypotheses) == 1
    assert M.compatibilite_h() in hf.hypotheses        # hypothèse de cohérence explicite
    assert hf.conclusion == M.h_fonctionnel_sous_compatibilite_cible()
    assert hf.conclusion not in hf.hypotheses          # NON vacueux (binders distincts)


# ════════════════════════════════════════════════════════════════════════════
#  Cœur dur (maximalité ⇒ trichotomie) — POSÉ conditionnel/REPORTÉ (formules).
# ════════════════════════════════════════════════════════════════════════════
def test_maximalite_donne_trichotomie_est_enonce():
    """Le cœur dur est POSÉ comme FORMULE-énoncé conditionnel (REPORTÉ, jamais prouvé)."""
    f = M.maximalite_donne_trichotomie()
    assert isinstance(f, Formule)                      # formule, PAS un Theoreme
    hyps = M.maximalite_donne_trichotomie_hypotheses()
    assert len(hyps) == 5                              # 5 hypothèses EXPLICITES
    assert all(isinstance(h, Formule) for h in hyps)
    assert isinstance(M.h_maximal(), Formule)


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_parametrable():
    """Le scaffolding est paramétrable (autres ensembles/relations)."""
    hip = TS.h_inclus_produit("A", "Ra", "B", "Rb")
    assert hip.est_clos
    assert hip.conclusion == TS.h_inclus_produit_cible("A", "Ra", "B", "Rb")
    de = M.h_dom_inclus_E("A", "Ra", "B", "Rb")
    assert de.est_clos and not de.hypotheses
