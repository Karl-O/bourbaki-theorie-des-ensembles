"""Tests §II.3.8 — Théorème 1 b) : composition des SECTIONS (niveau valeurs).

Module testé :
bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_theoreme1_b_section.

Jumeau dual de test_theoreme1_a_retraction_valeur_hypotheses : on contrôle
(a) la CONCLUSION EXACTE (== cible construite indépendamment) ;
(b) l'ENSEMBLE EXACT des hypothèses structurelles honnêtes (jamais postulées :
ce sont les données « f:A→B, f':B→C, s section de f, s' section de f' »).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient, impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections import ensembles_theoreme1_b_section as BS


# ── Théorème 1 b) — composition des sections (s∘s' section de f'') ─────────────
def test_theoreme1_b_section_valeur():
    th = BS.theoreme1_b_section_valeur()
    assert th.conclusion == BS.cible_theoreme1_b_section_valeur()


def test_theoreme1_b_section_valeur_hypotheses():
    # hyps : S section de F sur B, S' section de F' sur C, s'(z)∈B.
    # Liant frais « t » (≠ « y », liant interne de valeur) : forme correcte
    # (∀t∈B) f(s(t))=t, α-identique à est_retraction du dual a) (cf. docstring).
    th = BS.theoreme1_b_section_valeur()
    vS, vSp, vF, vFp, vB, vC = (var("S"), var("Sp"), var("F"),
                                var("Fp"), var("B"), var("C"))
    spz = E.valeur(vSp, var("z"))
    attendu = {
        E.est_section(vS, vF, vB, y="t"),
        E.est_section(vSp, vFp, vC, y="t"),
        appartient(spz, vB),
    }
    assert set(th.hypotheses) == attendu


def test_theoreme1_b_section_valeur_autres_lettres():
    th = BS.theoreme1_b_section_valeur("s0", "s1", "g", "h", "Y", "Z")
    assert th.conclusion == BS.cible_theoreme1_b_section_valeur("s0", "s1", "g", "h", "Z")


def test_theoreme1_b_section_valeur_forme():
    # forme attendue : (z∈C) ⇒ f'(f(s(s'(z)))) = z
    vS, vSp, vF, vFp, vC = var("S"), var("Sp"), var("F"), var("Fp"), var("C")
    vz = var("z")
    spz = E.valeur(vSp, vz)
    lhs = E.valeur(vFp, E.valeur(vF, E.valeur(vS, spz)))
    attendu = impl(appartient(vz, vC), egal(lhs, vz))
    assert BS.theoreme1_b_section_valeur().conclusion == attendu
