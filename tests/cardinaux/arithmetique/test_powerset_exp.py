"""Tests §III.3.5 — Card(𝔓(X)) = 2^Card X  (E.III.3.5, Proposition 12).

PALIERS SÛRS (tous CERTIFIÉS par le noyau, rien postulé) vers la Proposition 12.
Le CRUX (bijection caractéristique χ : 𝔓(X) → 𝓕(X;{0,1})) est REPORTÉ avec raison
précise (cf. bijection_caracteristique_REPORTE) ; on verrouille ici :

  • deux_membre              : (z ∈ 2) ⇔ (z = ∅ ou z = {∅}) ;
  • zero_dans_deux / un_dans_deux : ∅ ∈ 2 , {∅} ∈ 2 ;
  • deux_elements_distincts  : ¬(∅ = {∅})  (2 a bien DEUX éléments distincts) ;
  • exposant_deux_base       : 2^Card X = Card(𝓕(X; 2))  (pivot définitionnel) ;
  • cible_powerset_exp       : l'énoncé exact Card(𝔓(X)) = 2^Card X.
"""
from bourbaki.logique.formule import var, egal, et, non, ou, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.cardinaux.arithmetique import ensembles_powerset_exp as P


def _deux():
    return E.paire(E.VIDE, E.singleton(E.VIDE))


def test_deux_est_paire_zero_un():
    """2 = {∅, {∅}} = paire(0, 1)  (le 2-élément concret)."""
    assert P.deux() == _deux()


def test_deux_membre():
    """⊢ (z ∈ 2) ⇔ (z = ∅ ou z = {∅}), CLOS  (axiome de la paire en {∅,{∅}})."""
    vz = var("z")
    t = P.deux_membre("z")
    from bourbaki.logique.formule import equiv
    assert t.conclusion == equiv(appartient(vz, _deux()),
                                 ou(egal(vz, E.VIDE), egal(vz, E.singleton(E.VIDE))))
    assert t.est_clos


def test_zero_dans_deux():
    """⊢ ∅ ∈ 2, CLOS  (0 est élément du 2-élément)."""
    t = P.zero_dans_deux()
    assert t.conclusion == appartient(E.VIDE, _deux())
    assert t.est_clos


def test_un_dans_deux():
    """⊢ {∅} ∈ 2, CLOS  (1 est élément du 2-élément)."""
    t = P.un_dans_deux()
    assert t.conclusion == appartient(E.singleton(E.VIDE), _deux())
    assert t.est_clos


def test_deux_elements_distincts():
    """⊢ ¬(∅ = {∅}), CLOS  (0 ≠ 1 : 2 a bien DEUX éléments distincts)."""
    t = P.deux_elements_distincts()
    assert t.conclusion == non(egal(E.VIDE, E.singleton(E.VIDE)))
    assert t.est_clos


def test_exposant_deux_base():
    """⊢ exposant_cardinal_binaire(2, X) = Card(𝓕(X; 2)), CLOS  (= 2^Card X)."""
    vX = var("X")
    t = P.exposant_deux_base("X")
    assert t.conclusion == egal(exposant_cardinal_binaire(_deux(), vX),
                                cardinal(E.applications(vX, _deux())))
    assert t.est_clos


def test_exposant_deux_base_terme_compose():
    """Robustesse : 2^Card X tient quand X est un TERME composé (X = U × V)."""
    T = E.produit(var("U"), var("V"))
    t = P.exposant_deux_base(T)
    assert t.conclusion == egal(exposant_cardinal_binaire(_deux(), T),
                                cardinal(E.applications(T, _deux())))
    assert t.est_clos


def test_cible_powerset_exp_signature():
    """L'énoncé-cible (Proposition 12) : Card(𝔓(X)) = exposant_cardinal_binaire(2, X)."""
    vX = var("X")
    f = P.cible_powerset_exp("X")
    assert f == egal(cardinal(E.parties(vX)), exposant_cardinal_binaire(_deux(), vX))


def test_crux_reporte():
    """Le CRUX (bijection χ) est explicitement REPORTÉ (NotImplementedError)."""
    import pytest
    with pytest.raises(NotImplementedError):
        P.bijection_caracteristique_REPORTE()
