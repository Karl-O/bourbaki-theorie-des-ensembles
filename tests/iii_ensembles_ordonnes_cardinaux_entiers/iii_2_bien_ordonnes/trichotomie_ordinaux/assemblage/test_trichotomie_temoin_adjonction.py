"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : TÉMOIN ISO-DE-SEGMENTS par ADJONCTION.

On certifie (ensembles_trichotomie_temoin_adjonction) le maillon (i) du HARD RÉSIDU :
le prolongement h⁺ = h ∪ {(a,b)} de l'iso maximal h par le point adjoint (a,b), qui
réalise l'adjonction du plus grand élément (relation_adjoint, E.III.1.8) pour produire
le témoin iso de ]←,a] sur ]←,b] de l'argument de maximalité (blueprint d.5).

  ✅ INCONDITIONNELS (theorie=22, 0 hyp) :
     • a_est_plus_grand_dans_adjoint : ⊢ est_plus_grand_element(≤'_a, E∪{a}, a).
     • singleton_couple_fonctionnel  : ⊢ est_fonctionnel({(a,b)}).
     • couple_dans_temoin            : ⊢ (a,b)∈h⁺.
     • h_inclus_temoin               : ⊢ (∀z)(z∈h ⇒ z∈h⁺).
     • a_dans_dom_singleton_couple   : ⊢ a∈dom({(a,b)}).
     • dom_singleton_couple          : ⊢ dom({(a,b)})={a}.
  ⚠️ CONDITIONNELS (hypothèses EXPLICITES, REPORTÉ précis) :
     • disjonction_domaines_sous_a_hors : { a∉dom h } ⊢ domaines disjoints.
     • temoin_fonctionnel_sous_a_hors   : { a∉dom h, func h } ⊢ est_fonctionnel(h⁺).
     • valeur_temoin_en_a_sous_a_hors   : { a∉dom h, func h } ⊢ valeur(h⁺,a)=b.
     • valeur_temoin_sur_dom_h_sous     : { a∉dom h, func h, u∈dom h } ⊢ h⁺(u)=h(u).
  ⚠️ REPORTÉ (énoncé, NON prouvé) : temoin_est_iso_segments_report.

theorie_ensembles() reste = 22 ; rien postulé ; conclusions non tautologiques.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient, non, Formule
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_temoin_adjonction as A


_h = TS.h_iso_max("E", "R", "F", "Rp")
_a_hors = non(appartient(var("a"), E.dom(_h)))
_func_h = E.est_fonctionnel(_h)
_u_in_domh = appartient(var("u"), E.dom(_h))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ a EST le plus grand de l'adjonction E∪{a} — INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def test_a_est_plus_grand_dans_adjoint():
    thm = A.a_est_plus_grand_dans_adjoint()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.a_est_plus_grand_dans_adjoint_cible()


def test_a_est_plus_grand_parametrable():
    thm = A.a_est_plus_grand_dans_adjoint("Ra", "Ea", "p")
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.a_est_plus_grand_dans_adjoint_cible("Ra", "Ea", "p")


# ════════════════════════════════════════════════════════════════════════════
#  ✅ {(a,b)} fonctionnel — INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def test_singleton_couple_fonctionnel():
    thm = A.singleton_couple_fonctionnel()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.singleton_couple_fonctionnel_cible()
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ✅ (a,b)∈h⁺  et  h⊂h⁺ — INCONDITIONNELS.
# ════════════════════════════════════════════════════════════════════════════
def test_couple_dans_temoin():
    thm = A.couple_dans_temoin()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.couple_dans_temoin_cible()


def test_h_inclus_temoin():
    thm = A.h_inclus_temoin()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.h_inclus_temoin_cible()
    # forme (∀z)(z∈h ⇒ z∈h⁺) — ∀ encodé ¬∃¬, donc tag 'non' enveloppant un 'exists'
    assert thm.conclusion.tag == "non" and thm.conclusion.sous[0].tag == "exists"


# ════════════════════════════════════════════════════════════════════════════
#  ✅ a∈dom({(a,b)})  et  dom({(a,b)})={a} — INCONDITIONNELS.
# ════════════════════════════════════════════════════════════════════════════
def test_a_dans_dom_singleton_couple():
    thm = A.a_dans_dom_singleton_couple()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.a_dans_dom_singleton_couple_cible()


def test_dom_singleton_couple():
    thm = A.dom_singleton_couple()
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == A.dom_singleton_couple_cible()
    assert thm.conclusion.tag == "="


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ disjonction des domaines sous a∉dom h — CONDITIONNEL (1 hyp).
# ════════════════════════════════════════════════════════════════════════════
def test_disjonction_domaines_sous_a_hors():
    thm = A.disjonction_domaines_sous_a_hors()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 1
    assert _a_hors in thm.hypotheses                      # SEULE hyp = a∉dom h
    assert thm.conclusion == A.disjonction_domaines_cible()
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ h⁺ fonctionnel sous {a∉dom h, func h} — CONDITIONNEL (2 hyps).
# ════════════════════════════════════════════════════════════════════════════
def test_temoin_fonctionnel_sous_a_hors():
    thm = A.temoin_fonctionnel_sous_a_hors()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 2
    assert _a_hors in thm.hypotheses
    assert _func_h in thm.hypotheses
    assert thm.conclusion == A.temoin_fonctionnel_cible()
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ valeur(h⁺,a)=b  et  h⁺=h sur dom h — CONDITIONNELS.
# ════════════════════════════════════════════════════════════════════════════
def test_valeur_temoin_en_a_sous_a_hors():
    thm = A.valeur_temoin_en_a_sous_a_hors()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 2
    assert _a_hors in thm.hypotheses
    assert _func_h in thm.hypotheses
    assert thm.conclusion == A.valeur_temoin_en_a_cible()
    assert thm.conclusion not in thm.hypotheses
    assert thm.conclusion.tag == "="


def test_valeur_temoin_sur_dom_h_sous():
    thm = A.valeur_temoin_sur_dom_h_sous()
    assert not thm.est_clos
    assert len(thm.hypotheses) == 3
    assert _a_hors in thm.hypotheses
    assert _func_h in thm.hypotheses
    assert _u_in_domh in thm.hypotheses
    assert thm.conclusion == A.valeur_temoin_sur_dom_h_cible()
    assert thm.conclusion not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ REPORTÉ — l'énoncé du cœur d'ordre/surjection est une FORMULE, NON prouvée.
# ════════════════════════════════════════════════════════════════════════════
def test_report_est_un_enonce_non_prouve():
    enonce = A.temoin_est_iso_segments_report()
    assert isinstance(enonce, Formule)                    # un énoncé, PAS un théorème
    # c'est bien est_isomorphisme_ordre(h⁺, ]←,a], ]←,b], ≤'_a, ≤'_b)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg as _seg
    def Rf(x, y): return appartient(E.couple(x, y), var("R"))
    def Rpf(x, y): return appartient(E.couple(x, y), var("Rp"))
    Sa, Sb = _seg("R", "E", "a"), _seg("Rp", "F", "b")
    expected = V.est_isomorphisme_ordre(
        A.temoin_adjonction("E", "R", "F", "Rp", "a", "b"),
        V.ensemble_adjoint(Sa, var("a")), V.ensemble_adjoint(Sb, var("b")),
        V.relation_adjoint(Rf, Sa, var("a")), V.relation_adjoint(Rpf, Sb, var("b")))
    assert enonce == expected


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    # construire tous les théorèmes ne touche pas theorie_ensembles
    A.a_est_plus_grand_dans_adjoint()
    A.singleton_couple_fonctionnel()
    A.couple_dans_temoin()
    A.h_inclus_temoin()
    A.dom_singleton_couple()
    A.temoin_fonctionnel_sous_a_hors()
    A.valeur_temoin_en_a_sous_a_hors()
    A.valeur_temoin_sur_dom_h_sous()
    assert len(E.theorie_ensembles().axiomes) == 22
