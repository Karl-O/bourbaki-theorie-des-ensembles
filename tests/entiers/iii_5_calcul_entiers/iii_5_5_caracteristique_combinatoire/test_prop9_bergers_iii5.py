"""Tests — principe des bergers (binaire), cas à deux fibres constantes.

Voir la note de source dans ensembles_prop9_bergers_iii5 : la « Prop 9 §III.5 »
demandée n'existe pas (la Prop 9 du livre = exponentiation §III.3.5, déjà close ;
le principe fibres→produit = Prop 6 Cor 2 §III.3, famille indexée NON close).  On
certifie ici le CŒUR BINAIRE (I de cardinal 2)."""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_5_caracteristique_combinatoire.ensembles_prop9_bergers_iii5 import (
    bergers_binaire_fibres, bergers_binaire_somme)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire)
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et


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
    from bourbaki.logique.i_1_termes_relations.formule import impl
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
