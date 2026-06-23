"""Tests — §II.4.8 / §III.3.3 : somme disjointe binaire A ⊔ B (fondation de la
somme cardinale, miroir du produit).

        A ⊔ B := (A × {0}) ∪ (B × {1})     (0 = ∅, 1 = {∅}).

Terme DÉRIVÉ (réunion de deux copies marquées) → membership certifié à partir
des axiomes EXISTANTS (réunion + produit + paire), AUCUN axiome nouveau.  On
vérifie la forme, la décomposition par la réunion, les deux injections
canoniques et la caractérisation complète de l'appartenance.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme import ensembles_somme_disjointe as S
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, ou, impl, appartient, existe


def test_somme_disjointe_reunion_clos():
    """A⊔B = (A×{0}) ∪ (B×{1}) : forme exacte, théorème CLOS."""
    thm = S.somme_disjointe_reunion()
    Sab = S.somme_disjointe(var("A"), var("B"))
    assert thm.conclusion == egal(Sab, Sab)
    assert thm.est_clos


def test_membre_somme_reunion_clos():
    """z∈A⊔B ⇔ (z∈A×{0}) ou (z∈B×{1}) : conclusion EXACTE, théorème CLOS."""
    thm = S.membre_somme_reunion()
    vz = var("z")
    GA = E.produit(var("A"), E.singleton(S.ZERO))
    GB = E.produit(var("B"), E.singleton(S.UN))
    cible = E.equiv(appartient(vz, S.somme_disjointe(var("A"), var("B"))),
                    ou(appartient(vz, GA), appartient(vz, GB)))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_injection_gauche_clos():
    """(u∈A) ⇒ (u,0)∈A⊔B : conclusion EXACTE, théorème CLOS."""
    thm = S.injection_gauche_dans_somme()
    vu = var("u")
    cpl = E.couple(vu, S.ZERO)
    Sab = S.somme_disjointe(var("A"), var("B"))
    assert thm.conclusion == impl(appartient(vu, var("A")), appartient(cpl, Sab))
    assert thm.est_clos


def test_injection_droite_clos():
    """(v∈B) ⇒ (v,1)∈A⊔B : conclusion EXACTE, théorème CLOS."""
    thm = S.injection_droite_dans_somme()
    vv = var("v")
    cpl = E.couple(vv, S.UN)
    Sab = S.somme_disjointe(var("A"), var("B"))
    assert thm.conclusion == impl(appartient(vv, var("B")), appartient(cpl, Sab))
    assert thm.est_clos


def test_membre_somme_caracterise_clos():
    """z∈A⊔B ⇔ ((∃u)(u∈A et z=(u,0)) ou (∃v)(v∈B et z=(v,1))) : EXACT, CLOS."""
    thm = S.membre_somme_caracterise()
    vz, vu, vv = var("z"), var("u"), var("v")
    exA = existe("u", et(appartient(vu, var("A")), egal(vz, E.couple(vu, S.ZERO))))
    exB = existe("v", et(appartient(vv, var("B")), egal(vz, E.couple(vv, S.UN))))
    cible = E.equiv(appartient(vz, S.somme_disjointe(var("A"), var("B"))),
                    ou(exA, exB))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_somme_disjointe_termes():
    """Robustesse : la caractérisation tient sur des TERMES composés (ex. Card U)."""
    CU = E.app("card", var("U"))
    thm = S.membre_somme_caracterise(CU, "B", "z")
    vz, vu, vv = var("z"), var("u"), var("v")
    exA = existe("u", et(appartient(vu, CU), egal(vz, E.couple(vu, S.ZERO))))
    exB = existe("v", et(appartient(vv, var("B")), egal(vz, E.couple(vv, S.UN))))
    cible = E.equiv(appartient(vz, S.somme_disjointe(CU, var("B"))), ou(exA, exB))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_somme_cardinale_binaire_forme():
    """a + b := Card(A⊔B) : la somme cardinale binaire est le cardinal de la somme
    disjointe (miroir de ab := Card(A×B)) ; forme exacte."""
    from bourbaki.cardinaux.ensembles_cardinaux import cardinal
    t = S.somme_cardinale_binaire("A", "B")
    assert t == cardinal(S.somme_disjointe(var("A"), var("B")))


def test_injection_gauche_terme():
    """Robustesse : l'injection de gauche tient quand u est un TERME (pr₁ z)."""
    pz = E.pr1(var("z"))
    thm = S.injection_gauche_dans_somme(pz, "A", "B")
    cpl = E.couple(pz, S.ZERO)
    Sab = S.somme_disjointe(var("A"), var("B"))
    assert thm.conclusion == impl(appartient(pz, var("A")), appartient(cpl, Sab))
    assert thm.est_clos
