# -*- coding: utf-8 -*-
"""Les descentes générales — protégées (ev.325).

Deux faces : un but ∀-⇒ jouet FERMÉ par les descentes (généralisation +
loi_deduction, jugé noyau) ; et le contrôle qui peut échouer — un but ∀ dont
la matrice est hors de portée reste NON fermé avec manque nommé.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


@pytest.mark.slow
def test_descentes_ferment_un_but_universel_conditionnel():
    """∀x(Fini x ⇒ card(x+1)) fermé par descente-∀ + descente-⇒ + chaînage."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        fini_implique_fini_successeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        fini_implique_cardinal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, est_cardinal, successeur,
    )
    from outils_ia.decouvertes.autonomie.general import besoins_generaux
    from conjecturer import _comme_impl

    impls = []
    for nom, th in (("fini_succ", fini_implique_fini_successeur("atg")),
                    ("fic", fini_implique_cardinal("atg"))):
        ab = _comme_impl(th.conclusion)
        impls.append((nom, th, ab[0], ab[1]))

    vx = var("xtg")
    but = pourtout("xtg", impl(est_fini(vx), est_cardinal(successeur(vx))))
    th, manques = besoins_generaux(but, impls, {}, profondeur=3)
    assert th is not None and th.est_clos and th.conclusion == but
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_hors_de_portee_reste_nomme():
    """Un ∀ dont la matrice n'a aucune route → non fermé, manque NOMMÉ."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, est_cardinal,
    )
    from outils_ia.decouvertes.autonomie.general import besoins_generaux

    vx = var("xtg")
    but = pourtout("xtg", impl(est_cardinal(vx), est_fini(vx)))   # FAUX en général
    th, manques = besoins_generaux(but, [], {}, profondeur=2)
    assert th is None and manques == [] or th is None
    assert len(E.theorie_ensembles().axiomes) == 22


def test_enonces_euclide_bien_formes():
    """Brique 1 Euclide (ev.327) : les deux énoncés-cibles se construisent,
    sont des ∀-formes, et l'instanciation de la matrice au terme N(7) redonne
    EXACTEMENT l'assemblage manuel par les mêmes combinateurs (par ==)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, et, impl, existe, subst_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_egal_card,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from outils_ia.arithmetique.machine_num import NUM
    from outils_ia.conjectures.goldbach import est_premier
    from outils_ia.decouvertes.autonomie.premiers import (
        enonce_diviseur_premier, enonce_infinitude,
    )

    e1, e2 = enonce_diviseur_premier(), enonce_infinitude()
    for e in (e1, e2):                                     # ∀ = ¬∃¬
        assert e.tag == "non" and e.sous[0].tag == "exists"

    # matrice de l'infinitude instanciée à N(7) == assemblage manuel
    matrice = e2.sous[0].sous[0].sous[0]                   # sous le ∀nep
    inst = subst_f(NUM(7), "nep", matrice)
    vp = var("pep")
    attendu = impl(est_fini(NUM(7)),
                   existe("pep", et(est_premier(vp, d="dep", q="qep"),
                                    et(est_fini(vp),
                                       inf_egal_card(NUM(7), vp)))))
    assert inst == attendu
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_briques_euclide_cas_premier_et_transitivite():
    """Les deux piliers de la récurrence forte (ev.329, 331) : re-prouvés, clos,
    conclusions == cibles-compagnes par ==."""
    from outils_ia.decouvertes.autonomie.euclide_cas_premier import (
        cas_premier_diviseur, cas_premier_diviseur_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_transitivite import (
        transitivite_divise, transitivite_divise_cible,
    )
    th1 = cas_premier_diviseur()
    assert th1.est_clos and th1.conclusion == cas_premier_diviseur_cible()
    th2 = transitivite_divise()
    assert th2.est_clos and th2.conclusion == transitivite_divise_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_brique_extraction_diviseur():
    """Extraction du cas composé (ev.332) : close, conclusion == cible."""
    from outils_ia.decouvertes.autonomie.euclide_extraction import (
        extraction_diviseur, extraction_diviseur_cible,
    )
    th = extraction_diviseur()
    assert th.est_clos and th.conclusion == extraction_diviseur_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_brique_borne_diviseur():
    """La borne d ≤ n (ev.334) : close, conclusion == cible."""
    from outils_ia.decouvertes.autonomie.euclide_borne import (
        borne_diviseur, borne_diviseur_cible,
    )
    th = borne_diviseur()
    assert th.est_clos and th.conclusion == borne_diviseur_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_diviseur_premier_universel():
    """👑 LE théorème (ev.335) : tout entier fini ≥ 2 a un diviseur premier."""
    from outils_ia.decouvertes.autonomie.euclide_c61.envelope import (
        diviseur_premier_universel, _R,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, impl, pourtout,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    th = diviseur_premier_universel()
    assert th.est_clos and not th.hypotheses
    vn = var("nfor")
    assert th.conclusion == pourtout("nfor", impl(est_fini(vn), _R(vn)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_briques_infinitude_cibles():
    """Les cibles des briques infinitude (ev.339-344) sont bien formées,
    et G3 (la seule brique rapide) est close — smoke test du dossier."""
    from outils_ia.decouvertes.autonomie.euclide_c61.divise_produit import (
        divise_produit_gauche, divise_produit_gauche_cible,
        divise_produit_droite_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_c61.fini_factorielle import (
        fini_factorielle_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_c61.minorant_factorielle import (
        minorant_factorielle_cible,
    )
    from outils_ia.decouvertes.autonomie.euclide_c61.diviseur_commun_succ import (
        diviseur_commun_succ_cible,
    )
    for cible in (divise_produit_gauche_cible(), divise_produit_droite_cible(),
                  fini_factorielle_cible(), minorant_factorielle_cible(),
                  diviseur_commun_succ_cible()):
        assert cible is not None
    th = divise_produit_gauche()                     # ~1 s, close
    assert th.est_clos and th.conclusion == divise_produit_gauche_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_euclide_infinitude():
    """👑👑👑 EUCLIDE COMPLET (ev.344) : l'infinitude des premiers, close,
    conclusion == l'énoncé exigé par la machine (ev.325). ~23 min."""
    from outils_ia.decouvertes.autonomie.euclide_c61.assemblage_infinitude import (
        euclide_infinitude,
    )
    from outils_ia.decouvertes.autonomie.premiers import enonce_infinitude
    th = euclide_infinitude()
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == enonce_infinitude()
    assert len(E.theorie_ensembles().axiomes) == 22
