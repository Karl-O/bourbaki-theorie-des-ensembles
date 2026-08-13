"""Tests §II.3.7 (suite Prop. 7) — identité de COMPOSITION F⁻¹∘F = Id_A (valeurs).

Module testé :
bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_reciproque_identite.

On contrôle :
(a) la CONCLUSION EXACTE (== cible construite indépendamment) : la forme COMPOSÉE
    (x∈A) ⇒ (F⁻¹∘F)(x) = x, et NON la clause de rétraction emboîtée ;
(b) l'ENSEMBLE EXACT des 4 hypothèses honnêtes exposées par retraction_compose_valeur
    (est_retraction(F⁻¹,F,A), F⁻¹∘F fonctionnel, x∈domF, f(x)∈domF⁻¹) — jamais la
    conclusion, jamais d'hypothèse parasite ;
(c) l'invariant primitives N.* (théorème non clos : 4 hyps honnêtes restent) ;
(d) ⚠ GARDE ANTI-TAUTOLOGIE : la conclusion n'est α-égale à AUCUNE hypothèse — en
    particulier elle DIFFÈRE de est_retraction(F⁻¹,F,A) (= valeur(F⁻¹,valeur(F,x))=x),
    car elle porte sur valeur(composee(F⁻¹,F),x) (forme composée) ;
(e) la robustesse au renommage (« autres lettres ») ;
(f) l'invariant theorie_ensembles() == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, appartient,
                                       impl, existe, alpha_egal)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions import (
                               ensembles_reciproque_identite as RI)


def _hypotheses_attendues(f="F", a="A", x="x"):
    """Les 4 hypothèses honnêtes exposées par retraction_compose_valeur(F⁻¹,F,A,x)."""
    vF, vA, vx, vy = var(f), var(a), var(x), var("y")
    vR = E.reciproque(vF)
    comp = E.composee(vR, vF)
    fx = E.valeur(vF, vx)
    return [
        E.est_retraction(vR, vF, vA),                       # F⁻¹ rétraction de F sur A
        E.est_fonctionnel(comp),                            # F⁻¹∘F fonctionnel
        existe("y", appartient(E.couple(vx, vy), vF)),      # x ∈ dom F
        existe("y", appartient(E.couple(fx, vy), vR)),      # f(x) ∈ dom F⁻¹
    ]


# ── (a) conclusion == cible (forme COMPOSÉE, pas la clause de rétraction) ──────
def test_reciproque_compose_identite_conclusion():
    th = RI.reciproque_compose_identite_valeur()
    cible = RI.cible_reciproque_compose_identite_valeur()
    assert th.conclusion == cible
    # cible explicite, reconstruite à la main : (x∈A) ⇒ (F⁻¹∘F)(x) = x
    vF, vA, vx = var("F"), var("A"), var("x")
    rof = E.valeur(E.composee(E.reciproque(vF), vF), vx)
    attendu = impl(appartient(vx, vA), egal(rof, vx))
    assert th.conclusion == attendu


# ── (b) hypothèses EXACTES (honnêtes ; jamais la conclusion) ──────────────────
def test_reciproque_compose_identite_hypotheses():
    th = RI.reciproque_compose_identite_valeur()
    attendu = _hypotheses_attendues()
    hyps = list(th.hypotheses)
    assert len(hyps) == 4
    # chaque hypothèse attendue est présente (à α-renommage des liants des τ près)
    for cand in attendu:
        assert any(alpha_egal(h, cand) for h in hyps), f"hyp manquante : {cand}"
    # aucune hypothèse parasite : chaque hyp effective correspond à une attendue
    for h in hyps:
        assert any(alpha_egal(h, cand) for cand in attendu), f"hyp parasite : {h}"


# ── (c) théorème NON clos (les 4 hyps honnêtes ne sont jamais déchargées) ─────
def test_reciproque_compose_identite_non_clos():
    th = RI.reciproque_compose_identite_valeur()
    assert th.est_clos is False
    assert len(th.hypotheses) == 4


# ── (d) ⚠ GARDE ANTI-TAUTOLOGIE : conclusion ≠ chaque hypothèse ───────────────
def test_reciproque_compose_identite_non_tautologie():
    th = RI.reciproque_compose_identite_valeur()
    concl = th.conclusion
    # la conclusion n'est α-égale (ni ==) à AUCUNE hypothèse → ce n'est pas un P⇒P.
    for h in th.hypotheses:
        assert not alpha_egal(concl, h)
        assert concl != h
    # en particulier elle diffère de la clause de rétraction emboîtée :
    # est_retraction(F⁻¹,F,A) = (∀x)(x∈A ⇒ valeur(F⁻¹,valeur(F,x))=x), tandis que la
    # conclusion porte sur valeur(composee(F⁻¹,F),x) (forme composée).
    vF, vA = var("F"), var("A")
    retr = E.est_retraction(E.reciproque(vF), vF, vA)
    assert not alpha_egal(concl, retr)


# ── (e) robustesse au renommage ───────────────────────────────────────────────
def test_reciproque_compose_identite_autres_lettres():
    th = RI.reciproque_compose_identite_valeur("g", "Y", "u")
    cible = RI.cible_reciproque_compose_identite_valeur("g", "Y", "u")
    assert th.conclusion == cible
    attendu = _hypotheses_attendues("g", "Y", "u")
    hyps = list(th.hypotheses)
    assert len(hyps) == 4
    for cand in attendu:
        assert any(alpha_egal(h, cand) for h in hyps), f"hyp manquante : {cand}"
    # anti-tautologie tient aussi sous renommage
    for h in hyps:
        assert not alpha_egal(th.conclusion, h)


# ── (f) invariant 22 axiomes ──────────────────────────────────────────────────
def test_theorie_ensembles_invariant():
    assert len(E.theorie_ensembles().axiomes) == 22
