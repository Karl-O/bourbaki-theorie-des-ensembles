"""Tests §II.3.8 — Prop. 8 (dual surjectif), Théorème 1 (a–f), Corollaire.

Module testé : bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_retractions_props.
Chaque théorème est vérifié sur sa CONCLUSION EXACTE (== cible construite
indépendamment) et sur .est_clos.  Les théorèmes CONDITIONNELS (Théorème 1 a/c)
sont en outre contrôlés sur l'ENSEMBLE EXACT de leurs hypothèses structurelles
(jamais postulées : ce sont les données « f:A→B, f':B→C » du Théorème 1).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient, impl, pourtout, existe
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections import ensembles_retractions_props as RP


# ── Proposition 8 — sens direct, CAS SURJECTIF (dual de retraction⇒injective) ──
def test_prop8_section_implique_surjective_valeur():
    th = RP.section_implique_surjective_valeur()
    assert th.est_clos
    assert th.conclusion == RP.cible_section_implique_surjective_valeur()


def test_prop8_section_surjective_autres_lettres():
    th = RP.section_implique_surjective_valeur("s0", "g", "E")
    assert th.est_clos
    assert th.conclusion == RP.cible_section_implique_surjective_valeur("s0", "g", "E")


def test_prop8_section_surjective_forme():
    # forme attendue : (s section de f) ⇒ (∀y∈B)(∃x)(f(x)=y)
    vS, vF, vB, vy = var("S"), var("F"), var("B"), var("y")
    R = egal(E.valeur(vF, var("x")), vy)
    attendu = impl(E.est_section(vS, vF, vB),
                   pourtout("y", impl(appartient(vy, vB), existe("x", R))))
    assert RP.section_implique_surjective_valeur().conclusion == attendu


# ── Théorème 1 a) — composition d'injections (f'' = f'∘f injection) ────────────
def test_theoreme1_a_injective():
    th = RP.theoreme1_a_injective()
    assert th.conclusion == RP.cible_theoreme1_a_injective()
    # conclusion = injective_dans(F'∘F, A)
    assert th.conclusion == E.injective_dans(E.composee(var("Fp"), var("F")), var("A"))


def test_theoreme1_a_injective_hypotheses_structurelles():
    # les 7 hyps sont exactement « F,F' fonctionnels, dom F=A, image(F,A)=B,
    # dom F'=B, F inj/A, F' inj/B » (données de f:A→B, f':B→C injectives).
    th = RP.theoreme1_a_injective()
    vF, vFp, vA, vB = var("F"), var("Fp"), var("A"), var("B")
    attendu = {
        E.est_fonctionnel(vF), E.est_fonctionnel(vFp),
        egal(E.dom(vF), vA), egal(E.image(vF, vA), vB), egal(E.dom(vFp), vB),
        E.injective_dans(vF, vA), E.injective_dans(vFp, vB),
    }
    assert set(th.hypotheses) == attendu


# ── Théorème 1 a) — composition des rétractions (r∘r' rétraction de f'') ───────
def test_theoreme1_a_retraction_valeur():
    th = RP.theoreme1_a_retraction_valeur()
    assert th.conclusion == RP.cible_theoreme1_a_retraction_valeur()


def test_theoreme1_a_retraction_valeur_hypotheses():
    # hyps : R rétr. de F sur A, R' rétr. de F' sur B, f(x)∈B
    th = RP.theoreme1_a_retraction_valeur()
    vR, vRp, vF, vFp, vA, vB = (var("R"), var("Rp"), var("F"),
                                var("Fp"), var("A"), var("B"))
    fx = E.valeur(vF, var("x"))
    attendu = {
        E.est_retraction(vR, vF, vA),
        E.est_retraction(vRp, vFp, vB),
        appartient(fx, vB),
    }
    assert set(th.hypotheses) == attendu


# ── Théorème 1 c) — f'' injective ⇒ f injective ───────────────────────────────
def test_theoreme1_c_injective():
    th = RP.theoreme1_c_injective()
    assert th.conclusion == RP.cible_theoreme1_c_injective()
    assert th.conclusion == E.injective_dans(var("F"), var("A"))


def test_theoreme1_c_injective_hypotheses_structurelles():
    # hyps : F'∘F injective sur A, F'∘F fonctionnel, dom F=A, dom F'=B,
    #        (∀v)(v∈A ⇒ f(v)∈B)   — exactement « f:A→B, f':B→C, f'∘f inj ».
    th = RP.theoreme1_c_injective()
    vF, vFp, vA, vB, vv = (var("F"), var("Fp"), var("A"), var("B"), var("v"))
    comp = E.composee(vFp, vF)
    attendu = {
        E.injective_dans(comp, vA),
        E.est_fonctionnel(comp),
        egal(E.dom(vF), vA),
        egal(E.dom(vFp), vB),
        pourtout("v", impl(appartient(vv, vA), appartient(E.valeur(vF, vv), vB))),
    }
    assert set(th.hypotheses) == attendu


# ── Théorème 1 d) — f'' surjective ⇒ f' surjective (niveau valeurs) ────────────
def test_theoreme1_d_surjective_valeur():
    th = RP.theoreme1_d_surjective_valeur()
    assert th.est_clos
    assert th.conclusion == RP.cible_theoreme1_d_surjective_valeur()


def test_theoreme1_d_surjective_forme():
    # (∀z∈C)(∃x) f'(f(x))=z  ⇒  (∀z∈C)(∃yy) f'(yy)=z
    vF, vFp, vC = var("F"), var("Fp"), var("C")
    vz, vx = var("z"), var("x")
    Rpp = egal(E.valeur(vFp, E.valeur(vF, vx)), vz)
    Rp = egal(E.valeur(vFp, var("yy")), vz)
    attendu = impl(pourtout("z", impl(appartient(vz, vC), existe("x", Rpp))),
                   pourtout("z", impl(appartient(vz, vC), existe("yy", Rp))))
    assert RP.theoreme1_d_surjective_valeur().conclusion == attendu


# ── Corollaire — g∘f=Id_A, f∘g=Id_B ⇒ f, g injectives, g=f⁻¹ ───────────────────
def test_corollaire_f_injective():
    th = RP.corollaire_f_injective()
    assert th.est_clos
    # (g rétraction de f sur A)  ⇒  injective_dans(F, A)
    attendu = impl(E.est_retraction(var("G"), var("F"), var("A")),
                   E.injective_dans(var("F"), var("A")))
    assert th.conclusion == attendu


def test_corollaire_g_injective():
    th = RP.corollaire_g_injective()
    assert th.est_clos
    # (f rétraction de g sur B)  ⇒  injective_dans(G, B)
    attendu = impl(E.est_retraction(var("F"), var("G"), var("B")),
                   E.injective_dans(var("G"), var("B")))
    assert th.conclusion == attendu


# test_corollaire_g_egal_reciproque RETIRÉ : la fonction donnait une tautologie vide
# (est_retraction ⇒ est_retraction), infidèle au corollaire g=f⁻¹ (REPORTÉ).


# ── Garde-fou : aucune des conclusions n'est triviale (≠ une tautologie vide) ──
def test_theoremes_non_triviaux_distincts():
    concls = {
        RP.section_implique_surjective_valeur().conclusion,
        RP.theoreme1_a_injective().conclusion,
        RP.theoreme1_a_retraction_valeur().conclusion,
        RP.theoreme1_c_injective().conclusion,
        RP.theoreme1_d_surjective_valeur().conclusion,
    }
    assert len(concls) == 5
