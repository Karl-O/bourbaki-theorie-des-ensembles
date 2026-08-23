"""Tests — PONT couple→valeur : injectif_graphe(F) ⇒ injective_dans(F, dom F)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import injectif_graphe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_injectif_graphe_pont import (
    injectif_graphe_implique_injective_dans,
)


def test_theorie_ensembles_reste_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_pont_conclusion_injective_dans():
    th = injectif_graphe_implique_injective_dans()
    vF = var("Fpont")
    assert th.conclusion == E.injective_dans(vF, E.dom(vF))
    assert th.conclusion not in th.hypotheses


def test_pont_deux_hyps_honnetes():
    th = injectif_graphe_implique_injective_dans()
    vF = var("Fpont")
    assert E.est_fonctionnel(vF) in th.hypotheses
    assert injectif_graphe(vF) in th.hypotheses
    assert len(th.hypotheses) == 2


def test_pont_reciproque_valeur_vers_couple():
    """🎯 { est_fonctionnel(F), injective_dans(F, dom F) } ⊢ injectif_graphe(F).

    La RÉCIPROQUE du pont couple→valeur, exigée par les données du recollement
    (RECHERCHE R-13) : on dispose d'une bijection, donc de l'injectivité au
    niveau VALEUR, et il faut la forme COUPLE-NATIVE."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as EE
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
        injectif_graphe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_injectif_graphe_pont import (
        injective_dans_implique_injectif_graphe,
    )
    vF = var("Fpont")
    t = injective_dans_implique_injectif_graphe()
    assert t.conclusion == injectif_graphe(vF)
    assert set(t.hypotheses) == {EE.est_fonctionnel(vF),
                                 EE.injective_dans(vF, EE.dom(vF))}
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(EE.theorie_ensembles().axiomes) == 22
