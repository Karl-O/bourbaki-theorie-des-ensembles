"""Tests — principe des bergers (binaire), cas à deux fibres constantes.

Voir la note de source dans ensembles_prop9_bergers_iii5 : la « Prop 9 §III.5 »
demandée n'existe pas (la Prop 9 du livre = exponentiation §III.3.5, déjà close ;
le principe fibres→produit = Prop 6 Cor 2 §III.3, famille indexée NON close).  On
certifie ici le CŒUR BINAIRE (I de cardinal 2)."""
from bourbaki.entiers.ensembles_prop9_bergers_iii5 import (
    bergers_binaire_fibres, bergers_binaire_somme)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire)
from bourbaki.logique.formule import var, egal, et


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bergers_binaire_fibres_implication():
    """⊢ (Card E₀ = a et Card E₁ = a) ⇒ Card(E₀⊔E₁) = a + a.  Hyps HONNÊTES."""
    thm = bergers_binaire_fibres("E0", "E1", "A")
    assert thm.est_clos
    # implication non vide : l'antécédent (égalités sur les fibres) figure dans
    # la formule, la conclusion (somme) n'est PAS dans l'antécédent.
    ante = et(egal(cardinal(var("E0")), var("A")),
              egal(cardinal(var("E1")), var("A")))
    from bourbaki.logique.formule import impl
    cons = egal(cardinal(somme_disjointe(var("E0"), var("E1"))),
                somme_cardinale_binaire(var("A"), var("A")))
    assert thm.conclusion == impl(ante, cons)


def test_bergers_binaire_somme_inconditionnel():
    """⊢ Card(A⊔A) = (Card A) + (Card A).   INCONDITIONNEL, conclusion EXACTE."""
    thm = bergers_binaire_somme("A")
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    cible = egal(cardinal(somme_disjointe(var("A"), var("A"))),
                 somme_cardinale_binaire(cardinal(var("A")), cardinal(var("A"))))
    assert thm.conclusion == cible
