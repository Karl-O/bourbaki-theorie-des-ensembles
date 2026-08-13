# -*- coding: utf-8 -*-
"""Tests §I.1.3 — constructions formatives (E I.18-19), dont l'EXEMPLE du livre."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, concat, negation, disjonction, tau_x)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_3_constructions_formatives import (
    est_premiere_espece, est_deuxieme_espece, est_construction_formative,
    premiere_faute_formative, termes_de, relations_de)

SIG = {"∈": 2}                                   # théorie des ensembles : ∈ de poids 2


def _app(x, y):                                  # ∈xy (notation préfixe)
    return concat(concat(Assemblage(("∈",)), x), y)


def test_especes():
    A = Assemblage(("A",))
    assert est_premiere_espece(A)                              # lettre
    assert est_premiere_espece(tau_x(_app(A, A), "A"))         # commence par τ
    assert est_deuxieme_espece(_app(A, Assemblage(("B",))))    # signe spécifique en tête
    assert est_deuxieme_espece(negation(_app(A, A)))           # ¬ en tête


def test_exemple_du_livre():
    """E I.18 : A, A', A'', ∈AA', ∈AA'', ¬∈AA', ∨¬∈AA'∈AA'', τ_A(...) — formative,
    et le dernier assemblage est un TERME de la théorie des ensembles."""
    A, Ap, App = Assemblage(("A",)), Assemblage(("A'",)), Assemblage(("A''",))
    e1, e2 = _app(A, Ap), _app(A, App)                     # ∈AA', ∈AA''
    n1 = negation(e1)                                      # ¬∈AA'
    d1 = disjonction(n1, e2)                               # ∨¬∈AA'∈AA''  (⇒)
    t1 = tau_x(d1, "A")                                    # τ_A(∨¬∈AA'∈AA'')
    suite = (A, Ap, App, e1, e2, n1, d1, t1)
    assert est_construction_formative(suite, SIG)
    assert t1 in termes_de(suite, SIG)                     # « est un terme »
    assert d1 in relations_de(suite, SIG)
    assert e1 in relations_de(suite, SIG)


def test_rejet_negation_d_un_terme():
    # b) exige B de DEUXIÈME espèce : ¬A (négation d'une lettre) est injustifiable.
    A = Assemblage(("A",))
    suite = (A, negation(A))
    assert premiere_faute_formative(suite, SIG) == 1
    assert not est_construction_formative(suite, SIG)


def test_rejet_disjonction_de_lettres():
    # c) exige B, C de DEUXIÈME espèce : ∨AA' est injustifiable.
    A, Ap = Assemblage(("A",)), Assemblage(("A'",))
    assert premiere_faute_formative((A, Ap, disjonction(A, Ap)), SIG) == 2


def test_rejet_signe_hors_signature():
    # e) exige un signe spécifique DE LA THÉORIE : « = » n'est pas dans {∈}.
    A, Ap = Assemblage(("A",)), Assemblage(("A'",))
    egal = concat(concat(Assemblage(("=",)), A), Ap)
    assert premiere_faute_formative((A, Ap, egal), SIG) == 2
    assert est_construction_formative((A, Ap, egal), {"=": 2, "∈": 2})


def test_termes_de_exige_une_construction():
    with pytest.raises(ValueError):
        termes_de((negation(Assemblage(("A",))),), SIG)
