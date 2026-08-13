"""Tests §III.3.5 — ZÉRO-EXPOSANT  0^a = 0  pour  a ≠ 0  (E.III.3.5, Proposition 11).

VOIE FIDÈLE (rien postulé ; DÉRIVÉ depuis les axiomes de DÉFINITION de F^E et 𝓕) :

  • produit_vide_droit            : A×∅ = ∅ ;
  • exposant_vide_but_est_vide    : G∈∅^A ⇒ G=∅ ;
  • exposant_vide_but_force_base_vide : G∈∅^A ⇒ A=∅ ;
  • exposant_vide_but_vide        : ¬(A=∅) ⇒ ¬(G∈∅^A) ;
  • applications_but_vide_est_vide : ¬(A=∅) ⇒ 𝓕(A;∅)=∅ ;
  • exposant_zero_base_egale_zero : ¬(A=∅) ⇒ Card(𝓕(A;∅))=Card(∅)  (= 0^a = 0) ;
  • exposant_cardinal_zero_base   : ¬(A=∅) ⇒ exposant_cardinal_binaire(∅,A)=Card(∅).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, non, impl, appartient, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition import ensembles_exposant_zero as Z


def test_produit_vide_droit():
    """⊢ A×∅ = ∅, CLOS  (le produit de but vide est vide)."""
    t = Z.produit_vide_droit("A")
    assert t.conclusion == egal(E.produit(var("A"), E.VIDE), E.VIDE)
    assert t.est_clos


def test_exposant_vide_but_est_vide():
    """⊢ (G ∈ ∅^A) ⇒ (G = ∅), CLOS  (un graphe inclus dans A×∅=∅ est vide)."""
    vA, vG = var("A"), var("G")
    t = Z.exposant_vide_but_est_vide("A", "G")
    assert t.conclusion == impl(appartient(vG, E.exposant(vA, E.VIDE)), egal(vG, E.VIDE))
    assert t.est_clos


def test_exposant_vide_but_force_base_vide():
    """⊢ (G ∈ ∅^A) ⇒ (A = ∅), CLOS  (un graphe de ∅^A force A vide)."""
    vA, vG = var("A"), var("G")
    t = Z.exposant_vide_but_force_base_vide("A", "G")
    assert t.conclusion == impl(appartient(vG, E.exposant(vA, E.VIDE)), egal(vA, E.VIDE))
    assert t.est_clos


def test_exposant_vide_but_vide():
    """⊢ ¬(A=∅) ⇒ ¬(G ∈ ∅^A), CLOS  (∅^A est vide quand A≠∅)."""
    vA, vG = var("A"), var("G")
    t = Z.exposant_vide_but_vide("A", "G")
    assert t.conclusion == impl(non(egal(vA, E.VIDE)),
                                non(appartient(vG, E.exposant(vA, E.VIDE))))
    assert t.est_clos


def test_applications_but_vide_est_vide():
    """⊢ ¬(A=∅) ⇒ 𝓕(A;∅) = ∅, CLOS  (aucune application A→∅ quand A≠∅)."""
    vA = var("A")
    t = Z.applications_but_vide_est_vide("A")
    assert t.conclusion == impl(non(egal(vA, E.VIDE)),
                                egal(E.applications(vA, E.VIDE), E.VIDE))
    assert t.est_clos


def test_exposant_zero_base_egale_zero():
    """⊢ ¬(A=∅) ⇒ Card(𝓕(A;∅)) = Card(∅), CLOS  (= 0^a = 0, Proposition 11)."""
    vA = var("A")
    t = Z.exposant_zero_base_egale_zero("A")
    assert t.conclusion == impl(non(egal(vA, E.VIDE)),
                                egal(cardinal(E.applications(vA, E.VIDE)), cardinal(E.VIDE)))
    assert t.est_clos


def test_exposant_cardinal_zero_base():
    """⊢ ¬(A=∅) ⇒ exposant_cardinal_binaire(∅,A) = Card(∅), CLOS  (0^a=0 sur l'OPÉRATEUR)."""
    vA = var("A")
    t = Z.exposant_cardinal_zero_base("A")
    # LHS du = : exposant_cardinal_binaire(∅, A) = Card(applications(A, ∅))
    assert t.conclusion == impl(non(egal(vA, E.VIDE)),
                                egal(Z.exposant_cardinal_binaire(E.VIDE, vA), cardinal(E.VIDE)))
    assert t.est_clos


def test_zero_base_terme_compose():
    """Robustesse : 0^a = 0 tient quand la base A est un TERME composé (A = U×V)."""
    T = E.produit(var("U"), var("V"))
    t = Z.exposant_zero_base_egale_zero(T)
    assert t.conclusion == impl(non(egal(T, E.VIDE)),
                                egal(cardinal(E.applications(T, E.VIDE)), cardinal(E.VIDE)))
    assert t.est_clos
