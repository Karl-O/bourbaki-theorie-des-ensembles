"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : CONSTRUCTION des TÉMOINS COMMUNS.

On certifie (ensembles_temoin_commun) que les trois TÉMOINS COMMUNS de Lemme 1 §III.2
— hypothèses de compatibilite_*_depuis_temoin / fonctionnel_depuis_temoin dans
ensembles_trichotomie_coherences — se CONSTRUISENT :

  ✅ NOYAU INCONDITIONNEL : un iso de segments couvrant les deux antécédents PRODUIT
     le témoin commun (∃-introduction des 3 existentiels).
       • temoin_commun_depuis_iso  ⊢ temoin_commun_h(u,v,u',v')
       • temoin_inv_depuis_iso     ⊢ temoin_commun_inv_h(u,v,u')
       • temoin_fonc_depuis_iso    ⊢ temoin_commun_fonc_h(u,v,z)
  🎯 ASSEMBLAGE depuis DEUX couples de h + géométrie Lemme 1 EXPLICITE :
       • temoin_commun_depuis_couples / temoin_inv_depuis_couples / temoin_fonc_…

Les conclusions sont EXACTEMENT les formules-témoins de COH (mêmes binders px/pw) ;
theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques (≠ hyps).
"""
from bourbaki.logique.i_1_termes_relations.formule import Formule, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_coherences as COH
from bourbaki.cardinaux import ensembles_temoin_commun as TC


_h = TS.h_iso_max("E", "R", "F", "Rp")


# ════════════════════════════════════════════════════════════════════════════
#  NOYAU INCONDITIONNEL — un iso couvrant PRODUIT le témoin commun.
# ════════════════════════════════════════════════════════════════════════════
def test_temoin_commun_depuis_iso():
    thm = TC.temoin_commun_depuis_iso()
    # conclusion = EXACTEMENT la formule temoin_commun_h de COH
    assert thm.conclusion == COH.temoin_commun_h()
    assert thm.conclusion == TC.temoin_commun_depuis_iso_cible()
    # 7 hypothèses structurelles (la donnée d'un iso couvrant) ; aucune cohérence
    assert len(thm.hypotheses) == 7
    assert thm.conclusion not in thm.hypotheses  # non tautologique


def test_temoin_inv_depuis_iso():
    thm = TC.temoin_inv_depuis_iso()
    assert thm.conclusion == COH.temoin_commun_inv_h()
    assert thm.conclusion == TC.temoin_inv_depuis_iso_cible()
    assert len(thm.hypotheses) == 7
    assert thm.conclusion not in thm.hypotheses


def test_temoin_fonc_depuis_iso():
    thm = TC.temoin_fonc_depuis_iso()
    assert thm.conclusion == COH.temoin_commun_fonc_h()
    assert thm.conclusion == TC.temoin_fonc_depuis_iso_cible()
    # 6 hypothèses (un seul antécédent u, deux valeurs)
    assert len(thm.hypotheses) == 6
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  Les NOYAUX branchent les COHÉRENCES : conclusion-témoin = hypothèse de COH.
#  (preuve que l'on construit bien le maillon manquant de la cascade.)
# ════════════════════════════════════════════════════════════════════════════
def test_noyaux_branchent_coherences_par_couple():
    # le témoin commun PRODUIT (par couple) est exactement le corps quantifié par
    # COH.temoin_commun_universel (la forme universelle prise en hypothèse là-bas).
    tc = TC.temoin_commun_depuis_iso().conclusion
    inv = TC.temoin_inv_depuis_iso().conclusion
    fonc = TC.temoin_fonc_depuis_iso().conclusion
    assert tc == COH.temoin_commun_h()
    assert inv == COH.temoin_commun_inv_h()
    assert fonc == COH.temoin_commun_fonc_h()
    # mutuellement distincts (3 témoins différents)
    assert tc != inv and tc != fonc and inv != fonc


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE depuis DEUX couples de h + géométrie Lemme 1.
# ════════════════════════════════════════════════════════════════════════════
def test_temoin_commun_depuis_couples():
    thm = TC.temoin_commun_depuis_couples()
    assert thm.conclusion == COH.temoin_commun_h()
    assert thm.conclusion == TC.temoin_commun_depuis_couples_cible()
    # les deux ∈h sont portés comme contexte (présents dans le séquent)
    c1 = appartient(E.couple(__v("u"), __v("v")), _h)
    c2 = appartient(E.couple(__v("up"), __v("vp")), _h)
    assert c1 in thm.hypotheses
    assert c2 in thm.hypotheses
    # 7 géométriques + 2 ∈h = 9 hypothèses
    assert len(thm.hypotheses) == 9
    assert thm.conclusion not in thm.hypotheses


def test_temoin_inv_depuis_couples():
    thm = TC.temoin_inv_depuis_couples()
    assert thm.conclusion == COH.temoin_commun_inv_h()
    assert thm.conclusion == TC.temoin_inv_depuis_couples_cible()
    c1 = appartient(E.couple(__v("u"), __v("v")), _h)
    c2 = appartient(E.couple(__v("up"), __v("v")), _h)
    assert c1 in thm.hypotheses
    assert c2 in thm.hypotheses
    assert len(thm.hypotheses) == 9
    assert thm.conclusion not in thm.hypotheses


def test_temoin_fonc_depuis_couples():
    thm = TC.temoin_fonc_depuis_couples()
    assert thm.conclusion == COH.temoin_commun_fonc_h()
    assert thm.conclusion == TC.temoin_fonc_depuis_couples_cible()
    c1 = appartient(E.couple(__v("u"), __v("v")), _h)
    c2 = appartient(E.couple(__v("u"), __v("z")), _h)
    assert c1 in thm.hypotheses
    assert c2 in thm.hypotheses
    # 6 géométriques + 2 ∈h = 8 hypothèses
    assert len(thm.hypotheses) == 8
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  NON-CIRCULARITÉ : le témoin commun ≠ les cohérences (A)/(B)/func qu'il dérive.
# ════════════════════════════════════════════════════════════════════════════
def test_temoins_non_circulaires():
    import bourbaki.cardinaux.ensembles_trichotomie_h_iso as H
    assert COH.temoin_commun_h() != H.compatibilite_ordre_h()
    assert COH.temoin_commun_inv_h() != H.compatibilite_inverse_h()
    assert COH.temoin_commun_fonc_h() != E.est_fonctionnel(_h)


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    TC.temoin_commun_depuis_iso()
    TC.temoin_inv_depuis_iso()
    TC.temoin_fonc_depuis_iso()
    TC.temoin_commun_depuis_couples()
    TC.temoin_inv_depuis_couples()
    TC.temoin_fonc_depuis_couples()
    assert len(E.theorie_ensembles().axiomes) == 22


def __v(nom):
    from bourbaki.logique.i_1_termes_relations.formule import var
    return var(nom)
