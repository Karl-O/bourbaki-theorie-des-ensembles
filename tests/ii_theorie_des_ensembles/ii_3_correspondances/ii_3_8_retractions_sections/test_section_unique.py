"""Tests §II.3.8 — Déf. 11 : UNICITÉ de la section au niveau des valeurs-images.

Module testé :
bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_section_unique.

On contrôle :
(a) la CONCLUSION EXACTE (== cible construite indépendamment) ;
(b) l'ENSEMBLE EXACT des hypothèses honnêtes (jamais postulées : les deux données
    « s, s' sections de f sur B » ; jamais la conclusion, jamais d'hyp parasite) ;
(c) la robustesse au renommage (« autres lettres ») ;
(d) l'invariant theorie_ensembles() == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, appartient,
                                       impl, pourtout, alpha_egal)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections import (
                               ensembles_section_unique as SU)


# ── Unicité de la section — forme valeurs-images ──────────────────────────────
# NB : on compare à RENOMMAGE PRÈS des variables liées (alpha_egal) — la
# conclusion contient des τ (valeurs f(·), s(·)) dont le liant interne est
# α-renommé par le noyau (« @0 ») pour éviter la capture du « y » du ∀ extérieur,
# tandis que la cible utilise un liant frais « u » (cf. cible_section_unique_par_image).
# L'écart « u »/« @0 » est un pur renommage de variable liée, sans portée sémantique.
def test_section_unique_par_image_conclusion():
    th = SU.section_unique_par_image()
    assert alpha_egal(th.conclusion, SU.cible_section_unique_par_image())


def test_section_unique_par_image_hypotheses():
    # hyps EXACTES : S section de F sur B, S' section de F sur B.
    # Liant frais « t » (≠ « y », liant interne de valeur) : forme correcte
    # (∀t∈B) f(s(t))=t (cf. docstring du module).  Jamais la conclusion en hyp,
    # jamais d'hyp parasite (le y∈B a été déchargé par loi_deduction).
    th = SU.section_unique_par_image()
    vS, vSp, vF, vB = var("S"), var("Sp"), var("F"), var("B")
    attendu = {
        E.est_section(vS, vF, vB, y="t"),
        E.est_section(vSp, vF, vB, y="t"),
    }
    assert set(th.hypotheses) == attendu


def test_section_unique_par_image_forme():
    # forme attendue : (∀y)(y∈B ⇒ f(s(y)) = f(s'(y)))  (à renommage près des τ)
    vS, vSp, vF, vB, vy = var("S"), var("Sp"), var("F"), var("B"), var("y")
    lhs = E.valeur(vF, E.valeur(vS, vy, b="u"), b="u")
    rhs = E.valeur(vF, E.valeur(vSp, vy, b="u"), b="u")
    attendu = pourtout("y", impl(appartient(vy, vB), egal(lhs, rhs)))
    assert alpha_egal(SU.section_unique_par_image().conclusion, attendu)


def test_section_unique_par_image_autres_lettres():
    th = SU.section_unique_par_image("s0", "s1", "g", "Y")
    assert alpha_egal(th.conclusion,
                      SU.cible_section_unique_par_image("s0", "s1", "g", "Y"))
    vs0, vs1, vg, vY = var("s0"), var("s1"), var("g"), var("Y")
    attendu = {
        E.est_section(vs0, vg, vY, y="t"),
        E.est_section(vs1, vg, vY, y="t"),
    }
    assert set(th.hypotheses) == attendu


def test_theorie_ensembles_invariant():
    assert len(E.theorie_ensembles().axiomes) == 22
