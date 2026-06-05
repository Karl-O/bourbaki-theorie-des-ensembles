"""Tests §III.3.3 — Équipotence canonique avec la COPIE MARQUÉE  A ≅ A×{m}
(brique du cœur back-and-forth de la Proposition 8, §III.3.4).

Vérifie (conclusions EXACTES + clos) les paliers de la bijection a↦(a,m), graphe
Δ_m = graphe_terme(A, (e,m), "e") :
  • copie_graphe_fonctionnel  : Δ_m fonctionnel                                   ;
  • copie_graphe_domaine      : dom Δ_m = A                                       ;
  • copie_graphe_valeur       : {a∈A} ⊢ Δ_m(a) = (a,m)                            ;
  • copie_graphe_injective    : injective_dans(Δ_m, A)                            ;
  • copie_graphe_image        : image(Δ_m, A) = A×{m}                             ;
  • copie_est_bijection       : est_bijection_de(Δ_m, A, A×{m})                   ;
  • eq_copie_marquee          : Eq(A, A×{m})                                      ;
  • eq_copie_gauche/droite    : Eq(A, A×{0}) / Eq(B, B×{1})                       ;
  • eq_copies_gauches_implique_eq : Eq(A×{0}, B×{0}) ⇒ Eq(A, B)  (transport CAS 1).
"""
from bourbaki.logique.formule import var, egal, impl
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import equipotent, est_bijection_de
from bourbaki.ensembles.familles.ensembles_somme_disjointe import ZERO, UN
from bourbaki.cardinaux.arithmetique import ensembles_copie_marquee as C


def _DX(t, m):
    return C._copie_graphe(t, m)


def _AM(t, m):
    return E.produit(t, E.singleton(m))


def test_copie_graphe_fonctionnel():
    """⊢ est_fonctionnel(Δ_0), CLOS."""
    A = var("A")
    t = C.copie_graphe_fonctionnel(A, ZERO)
    assert t.conclusion == E.est_fonctionnel(_DX(A, ZERO))
    assert t.est_clos


def test_copie_graphe_domaine():
    """⊢ dom(Δ_0) = A, CLOS."""
    A = var("A")
    t = C.copie_graphe_domaine(A, ZERO)
    assert t.conclusion == egal(E.dom(_DX(A, ZERO)), A)
    assert t.est_clos


def test_copie_graphe_valeur():
    """{a∈A} ⊢ Δ_0(a) = (a,0)."""
    A, a = var("A"), var("a")
    t = C.copie_graphe_valeur(A, ZERO, "a")
    assert t.conclusion == egal(E.valeur(_DX(A, ZERO), a), E.couple(a, ZERO))
    # unique hypothèse : a∈A
    from bourbaki.logique.formule import appartient
    assert list(t.hypotheses) == [appartient(a, A)]


def test_copie_graphe_injective():
    """⊢ injective_dans(Δ_0, A), CLOS."""
    A = var("A")
    t = C.copie_graphe_injective(A, ZERO)
    assert t.conclusion == E.injective_dans(_DX(A, ZERO), A)
    assert t.est_clos


def test_copie_graphe_image():
    """⊢ image(Δ_0, A) = A×{0}, CLOS."""
    A = var("A")
    t = C.copie_graphe_image(A, ZERO)
    assert t.conclusion == egal(E.image(_DX(A, ZERO), A), _AM(A, ZERO))
    assert t.est_clos


def test_copie_est_bijection():
    """⊢ est_bijection_de(Δ_0, A, A×{0}), CLOS."""
    A = var("A")
    t = C.copie_est_bijection(A, ZERO)
    assert t.conclusion == est_bijection_de(_DX(A, ZERO), A, _AM(A, ZERO))
    assert t.est_clos


def test_eq_copie_marquee():
    """⊢ Eq(A, A×{0}), CLOS."""
    A = var("A")
    t = C.eq_copie_marquee(A, ZERO)
    assert t.conclusion == equipotent(A, _AM(A, ZERO))
    assert t.est_clos


def test_eq_copie_marquee_un():
    """⊢ Eq(A, A×{1}) (marqueur droit), CLOS."""
    A = var("A")
    t = C.eq_copie_marquee(A, UN)
    assert t.conclusion == equipotent(A, _AM(A, UN))
    assert t.est_clos


def test_eq_copie_gauche_droite():
    """⊢ Eq(A, A×{0}) et ⊢ Eq(B, B×{1}), CLOS."""
    A, B = var("A"), var("B")
    tg = C.eq_copie_gauche(A)
    td = C.eq_copie_droite(B)
    assert tg.conclusion == equipotent(A, _AM(A, ZERO))
    assert td.conclusion == equipotent(B, _AM(B, UN))
    assert tg.est_clos and td.est_clos


def test_eq_copie_marquee_terme():
    """Robustesse : Eq(A, A×{0}) tient quand A est un TERME composé (A = U×V), CLOS."""
    U, V = var("U"), var("V")
    AB = E.produit(U, V)
    t = C.eq_copie_marquee(AB, ZERO)
    assert t.conclusion == equipotent(AB, _AM(AB, ZERO))
    assert t.est_clos


def test_eq_copies_gauches_implique_eq():
    """⊢ Eq(A×{0}, B×{0}) ⇒ Eq(A, B)  (transport par les copies, CAS 1), CLOS."""
    A, B = var("A"), var("B")
    t = C.eq_copies_gauches_implique_eq(A, B)
    target = impl(equipotent(_AM(A, ZERO), _AM(B, ZERO)), equipotent(A, B))
    assert t.conclusion == target
    assert t.est_clos
