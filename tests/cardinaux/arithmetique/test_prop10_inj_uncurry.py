"""Tests — DIRECTION B de la Proposition 10 (currying) : l'injection UNCURRY.

    ⊢ inf_egal_card( 𝓕(C; 𝓕(B;A)) ,  𝓕(B×C; A) )                  ((a^b)^c ≤ a^(b·c))

U : 𝓕(C; 𝓕(B;A)) ↪ 𝓕(B×C; A),  g ↦ ( (b,c) ↦ g(c)(b) ).  Bien-déf = DOUBLE
valeur_application_dans_but ; injectivité = back-and-forth REDOUBLÉ (deux niveaux).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card
from bourbaki.cardinaux.arithmetique import ensembles_prop10_inj_uncurry as U


def test_conjoints_faciles():
    """W_U fonctionnel + dom W_U = 𝓕(C;𝓕(B;A))  (C54, triviaux)."""
    fonc = U.W_U_fonctionnel()
    assert fonc.est_clos
    assert fonc.conclusion == E.est_fonctionnel(U.W_U())
    dom = U.W_U_domaine()
    assert dom.est_clos
    assert dom.conclusion == egal(E.dom(U.W_U()), U.domaine_U())


def test_bien_definition():
    """uncurry_appli(g) ∈ 𝓕(B×C;A)  sous  g∈𝓕(C;𝓕(B;A))  (DOUBLE valeur_application_dans_but)."""
    vg, va, vb, vc = var("g"), var("A"), var("B"), var("C")
    thm = U.uncurry_appli_dans_codomaine()
    assert thm.conclusion == appartient(U.uncurry_appli(vg, va, vb, vc),
                                        U.codomaine_U(va, vb, vc))
    assert set(thm.hypotheses) == {appartient(vg, U.domaine_U(va, vb, vc))}


def test_image_incluse():
    """image(W_U, 𝓕(C;𝓕(B;A))) ⊂ 𝓕(B×C;A)  (BIEN-DÉFINITION, CLOS)."""
    va, vb, vc = var("A"), var("B"), var("C")
    thm = U.W_U_image_incluse()
    assert thm.est_clos
    assert thm.conclusion == inclus(E.image(U.W_U(va, vb, vc), U.domaine_U(va, vb, vc)),
                                    U.codomaine_U(va, vb, vc))


def test_injective():
    """injective_dans(W_U, 𝓕(C;𝓕(B;A))) (CLOS, back-and-forth redoublé)."""
    thm = U.W_U_injective()
    assert thm.est_clos
    assert thm.conclusion == E.injective_dans(U.W_U(), U.domaine_U())


def test_est_injection():
    """est_injection_de(W_U, 𝓕(C;𝓕(B;A)), 𝓕(B×C;A))  (les QUATRE conjoints, CLOS)."""
    va, vb, vc = var("A"), var("B"), var("C")
    thm = U.W_U_est_injection()
    assert thm.est_clos
    assert thm.conclusion == est_injection_de(U.W_U(va, vb, vc),
                                              U.domaine_U(va, vb, vc),
                                              U.codomaine_U(va, vb, vc))


def test_inf_egal_uncurry():
    """⊢ inf_egal_card(𝓕(C;𝓕(B;A)), 𝓕(B×C;A))  INCONDITIONNEL  ((a^b)^c ≤ a^(b·c))."""
    va, vb, vc = var("A"), var("B"), var("C")
    thm = U.inf_egal_uncurry()
    assert thm.est_clos
    assert thm.conclusion == inf_egal_card(U.domaine_U(va, vb, vc),
                                           U.codomaine_U(va, vb, vc))
