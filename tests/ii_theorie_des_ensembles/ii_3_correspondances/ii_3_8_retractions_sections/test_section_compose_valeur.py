"""Test §II.3.8 Déf.11 — (f∘s)(u)=u sur B quand s section de f  (dual de retraction).

Conclusion == cible ; hypothèses honnêtes ; theorie==22 ; garde ANTI-TAUTOLOGIE :
(f∘s)(u) lu comme UN graphe est α-différent du double emboîtement f(s(u)).
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
    section_compose_valeur, cible_section_compose_valeur)


def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_section_compose_valeur():
    """{est_section(S,F,B), F∘S func, u∈domS, s(u)∈domF} ⊢ (u∈B) ⇒ (f∘s)(u)=u."""
    th = section_compose_valeur()
    assert th.conclusion == cible_section_compose_valeur()
    assert len(th.hypotheses) == 4                      # est_section + F∘S func + 2 existences
    assert len(E.theorie_ensembles().axiomes) == 22


def test_anti_tautologie():
    """(f∘s)(u) [un graphe] ≠ f(s(u)) [deux valeurs emboîtées] — sinon le lemme serait vide."""
    fos = E.valeur(E.composee(var("F"), var("S")), var("u"))
    fsu = E.valeur(var("F"), E.valeur(var("S"), var("u")))
    assert fos != fsu
