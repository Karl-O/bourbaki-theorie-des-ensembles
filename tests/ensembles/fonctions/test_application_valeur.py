"""Tests §II.5.2 — PONT GÉNÉRAL au niveau APPLICATION : « f(x) au sens Bourbaki ».

Pour f = ((G,E),F) ∈ 𝓕(E;F), f(x) entendu comme G(x) se calcule sur le GRAPHE
graphe_de(f) = pr₁(pr₁ f), PAS sur le triple f.  Deux théorèmes CONDITIONNELS :

  (1) valeur_application_dans_but(f,E,F,x) : {f∈𝓕(E;F), x∈E}
        ⊢ valeur(graphe_de(f), x) ∈ F ;
  (2) application_egale_par_valeurs(f,g,E,F) :
        {f∈𝓕(E;F), g∈𝓕(E;F), (∀x)(x∈E ⇒ f(x)=g(x))} ⊢ f = g.

On vérifie la CONCLUSION littérale et le JEU D'HYPOTHÈSES exact (versions
conditionnelles : .hypotheses non vide, donc PAS .est_clos).
"""
from bourbaki.logique.formule import var, egal, et, impl, appartient, pourtout
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de
from bourbaki.ensembles.fonctions import ensembles_application_valeur as M


def _F(e, f):
    return E.applications(e, f)               # 𝓕(E;F)


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  valeur_application_dans_but :  f(x) = G(x) ∈ F
# ═══════════════════════════════════════════════════════════════════════════════
def test_valeur_application_dans_but_conclusion():
    """{f∈𝓕(E;F), x∈E} ⊢ valeur(graphe_de(f), x) ∈ F  (conclusion littérale)."""
    vf, vE, vF, vx = var("f"), var("E"), var("F"), var("x")
    t = M.valeur_application_dans_but("f", "E", "F", "x")
    assert t.conclusion == appartient(E.valeur(graphe_de(vf), vx), vF)


def test_valeur_application_dans_but_hypotheses():
    """Hypothèses EXACTES : {f∈𝓕(E;F), x∈E}  (rien postulé, conditionnel)."""
    vf, vE, vF, vx = var("f"), var("E"), var("F"), var("x")
    t = M.valeur_application_dans_but("f", "E", "F", "x")
    assert t.hypotheses == frozenset({appartient(vf, _F(vE, vF)),
                                      appartient(vx, vE)})
    assert not t.est_clos


def test_valeur_application_dans_but_terme():
    """Robustesse : tient quand E, F, x sont des TERMES composés."""
    vf = var("f")
    vE = E.produit(var("U"), var("V"))
    vF = E.singleton(var("W"))
    vx = E.couple(var("u"), var("v"))      # termes frais (≠ binders a,b de pr₁ / y de valeur)
    t = M.valeur_application_dans_but(vf, vE, vF, vx)
    assert t.conclusion == appartient(E.valeur(graphe_de(vf), vx), vF)
    assert t.hypotheses == frozenset({appartient(vf, _F(vE, vF)),
                                      appartient(vx, vE)})


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  application_egale_par_valeurs :  mêmes valeurs ⇒ f = g
# ═══════════════════════════════════════════════════════════════════════════════
def _hyp_valeurs(vf, vg, vE):
    vx = var("x")
    return pourtout("x", impl(appartient(vx, vE),
                              egal(E.valeur(graphe_de(vf), vx),
                                   E.valeur(graphe_de(vg), vx))))


def test_application_egale_par_valeurs_conclusion():
    """{f∈𝓕, g∈𝓕, mêmes valeurs} ⊢ f = g  (conclusion littérale)."""
    vf, vg = var("f"), var("g")
    t = M.application_egale_par_valeurs("f", "g", "E", "F")
    assert t.conclusion == egal(vf, vg)


def test_application_egale_par_valeurs_hypotheses():
    """Hypothèses EXACTES : {f∈𝓕(E;F), g∈𝓕(E;F), (∀x)(x∈E⇒f(x)=g(x))}."""
    vf, vg, vE, vF = var("f"), var("g"), var("E"), var("F")
    t = M.application_egale_par_valeurs("f", "g", "E", "F")
    assert t.hypotheses == frozenset({
        appartient(vf, _F(vE, vF)),
        appartient(vg, _F(vE, vF)),
        _hyp_valeurs(vf, vg, vE)})
    assert not t.est_clos


def test_egalite_valeurs_application_forme():
    """L'hypothèse « mêmes valeurs » a la forme attendue (au sens Bourbaki, via graphe)."""
    vf, vg, vE = var("f"), var("g"), var("E")
    h = M.egalite_valeurs_application("f", "g", "E")
    assert h == _hyp_valeurs(vf, vg, vE)


def test_application_egale_par_valeurs_terme():
    """Robustesse : tient quand E, F sont des TERMES composés."""
    vf, vg = var("f"), var("g")
    vE = E.produit(var("U"), var("V"))
    vF = E.singleton(var("W"))
    t = M.application_egale_par_valeurs(vf, vg, vE, vF)
    assert t.conclusion == egal(vf, vg)
    assert t.hypotheses == frozenset({
        appartient(vf, _F(vE, vF)),
        appartient(vg, _F(vE, vF)),
        _hyp_valeurs(vf, vg, vE)})
