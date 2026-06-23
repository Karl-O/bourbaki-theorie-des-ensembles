"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : PREUVE du cœur de la MAXIMALITÉ de h.

On certifie (ensembles_trichotomie_maximalite_preuve) :
  ✅ INCONDITIONNELS (theorie=22, 0 hyp) :
     • couple_dans_h_donne_antecedent : {(a,b)∈h} ⊢ a∈dom(h).
     • couple_dans_h_donne_valeur     : {(a,b)∈h} ⊢ b∈pr₂(h).
     • point_pas_dans_son_segment     : ⊢ ¬(a∈seg(R,E,a)).
     • 🎯 h_maximal_preuve            : ⊢ h_maximal(E,R,F,Rp)  (FERME la formule posée).
  ⚠️ CONDITIONNELS (10 hyps STRUCTURELLES explicites, REPORTÉ précis ; ARCHITECTURE
     func/dom : 7 originales + func/dom/graphe de l'iso-application φ) :
     • extension_iso_donne_antecedent : {10 hyps} ⊢ a∈dom(h).
     • adjonction_contredit_segment_propre : {10 hyps} ⊢ ¬(dom h = seg(R,E,a)).
theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient, non, Formule
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux import ensembles_trichotomie_maximalite_preuve as P


# ════════════════════════════════════════════════════════════════════════════
#  ✅ (a,b)∈h ⇒ a∈dom(h)  et  b∈pr₂(h)  —  INCONDITIONNELS (1 hyp = (a,b)∈h).
# ════════════════════════════════════════════════════════════════════════════
def test_couple_dans_h_donne_antecedent():
    thm = P.couple_dans_h_donne_antecedent()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1                       # la seule hyp = (a,b)∈h
    h = TS.h_iso_max("E", "R", "F", "Rp")
    assert appartient(E.couple(var("a"), var("b")), h) in thm.hypotheses
    assert thm.conclusion == P.couple_dans_h_donne_antecedent_cible()
    assert thm.conclusion not in thm.hypotheses           # NON vacueux


def test_couple_dans_h_donne_valeur():
    thm = P.couple_dans_h_donne_valeur()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    h = TS.h_iso_max("E", "R", "F", "Rp")
    assert appartient(E.couple(var("a"), var("b")), h) in thm.hypotheses
    assert thm.conclusion == P.couple_dans_h_donne_valeur_cible()
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ✅ ¬( a∈seg(R,E,a) )  —  INCONDITIONNEL (0 hyp).
# ════════════════════════════════════════════════════════════════════════════
def test_point_pas_dans_son_segment():
    thm = P.point_pas_dans_son_segment()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == P.point_pas_dans_son_segment_cible()
    # NON tautologie syntaxique évidente : c'est une négation d'appartenance dérivée
    assert thm.conclusion.tag == "non"


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ⊢ h_maximal(E,R,F,Rp)  —  FERME la FORMULE de maximalité posée.  INCOND.
# ════════════════════════════════════════════════════════════════════════════
def test_h_maximal_preuve_clos():
    thm = P.h_maximal_preuve()
    assert thm.est_clos and not thm.hypotheses
    # ferme EXACTEMENT la formule h_maximal du scaffold
    assert thm.conclusion == M.h_maximal()
    assert thm.conclusion == P.h_maximal_preuve_cible()


def test_h_maximal_preuve_parametrable():
    thm = P.h_maximal_preuve("A", "Ra", "B", "Rb")
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == M.h_maximal("A", "Ra", "B", "Rb")


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ extension_iso_donne_antecedent : {7 hyps} ⊢ a∈dom(h).  CONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def test_extension_iso_donne_antecedent():
    thm = P.extension_iso_donne_antecedent()
    assert not thm.est_clos
    # ARCHITECTURE func/dom : 10 hyps (7 originales + func/dom/graphe de φ application)
    assert len(thm.hypotheses) == 10                      # 10 hyps STRUCTURELLES
    assert thm.conclusion == P.extension_iso_donne_antecedent_cible()
    assert thm.conclusion not in thm.hypotheses           # NON vacueux
    # les 10 hyps coïncident avec celles posées
    hyps = P.extension_iso_hypotheses()
    assert len(hyps) == 10
    for h in hyps:
        assert h in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️🎯 adjonction_contredit_segment_propre : {7 hyps} ⊢ ¬(dom h = seg(R,E,a)).
# ════════════════════════════════════════════════════════════════════════════
def test_adjonction_contredit_segment_propre():
    thm = P.adjonction_contredit_segment_propre()
    assert not thm.est_clos
    # ARCHITECTURE func/dom : MÊMES 10 hyps structurelles (7 + func/dom/graphe)
    assert len(thm.hypotheses) == 10
    assert thm.conclusion == P.adjonction_contredit_segment_propre_cible()
    assert thm.conclusion not in thm.hypotheses           # NON vacueux
    hyps = P.extension_iso_hypotheses()
    for h in hyps:
        assert h in thm.hypotheses
    # la conclusion est bien la NÉGATION de l'égalité dom h = seg propre
    assert thm.conclusion.tag == "non"


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
