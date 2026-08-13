# -*- coding: utf-8 -*-
"""Tests — le prolongement x̃ comme TERME et ses valeurs (§III.7.2).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
    _gleq,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_prolongement_terme import (
    prolongement_famille, faits_clos_prolongement, valeur_prolongement_dans_E,
    REPORTES,
)


def test_faits_clos_sur_le_prolongement():
    """🎯 x̃ est CONSTRUIT : graphe, fonctionnel et domaine sont CLOS.

    Même dividende que pour g et pour la famille des coordonnées — trois des
    quatre clauses de l'appartenance au produit sont gratuites."""
    gr, fn, dm = faits_clos_prolongement()
    assert gr.est_clos and fn.est_clos and dm.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_du_prolongement_dans_E():
    """👑 x̃(m) ∈ E_m — et c'est ICI que sert le typage des transitions.

    L'hypothèse `transitions_typees` est présente NOMMÉMENT : c'est la condition
    que Bourbaki pose en prose, et qui manquait à `est_systeme_projectif`
    (anomalie du 2026-08-04, comblée le 2026-08-05).  Elle est portée ici sous
    son nom propre — la preuve n'a besoin que d'elle, pas de tout le système.
    Le test l'épingle, pour qu'on ne puisse pas la faire disparaître sans s'en
    apercevoir."""
    th = valeur_prolongement_dans_E()
    typage = L.transitions_typees(var("E"), var("f"), _gleq(), var("I"),
                                  "a", "b", "zt")
    assert typage in th.hypotheses
    assert th.conclusion == appartient(
        E.valeur(prolongement_famille(), var("i")),
        E.valeur_famille(var("E"), var("i")))
    assert len(th.hypotheses) == 4
    assert len(E.theorie_ensembles().axiomes) == 22


def test_report_suite_honnete():
    """Les deux reports : x̃ ∈ lim←_I (condition (1) à remettre en forme), puis
    G(x̃)=y et la clôture de la Prop. 3."""
    assert len(REPORTES) == 2
    assert "lim←_I" in REPORTES[0]
    assert "Prop. 3 CLOSE" in REPORTES[1]


def test_coordonnee_de_y_dans_E():
    """La coordonnée du point de départ, lue sur y ∈ lim←_J via le pont du
    système restreint — 3 hypothèses de contexte."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_prolongement_terme import (
        coordonnee_de_y_dans_E,
    )
    assert len(coordonnee_de_y_dans_E().hypotheses) == 3


def test_clause_valeurs_prolongement_est_celle_du_pivot():
    """👑 La clause des valeurs de x̃, QUANTIFIÉE — et c'est LITTÉRALEMENT
    `hypothese_valeurs(E, I, i, x̃)`, la formule qu'attend le pivot."""
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
        hypothese_valeurs,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_prolongement_terme import (
        clause_valeurs_prolongement,
    )
    th = clause_valeurs_prolongement()
    assert th.conclusion == hypothese_valeurs(var("E"), var("I"), "i",
                                              prolongement_famille())
    assert len(th.hypotheses) == 3


def test_prolongement_dans_produit():
    """👑👑 x̃ ∈ ∏_{α∈I} E_α — 3 hypothèses de contexte, aucune propre à x̃.

    ⚠️ Le nom du point d'évaluation devient le LIANT de la clause des valeurs :
    il doit être celui de l'axiome du produit (« i »).  Un autre nom fait
    échouer le modus ponens final — piège mesuré."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_prolongement_terme import (
        prolongement_dans_produit,
    )
    th = prolongement_dans_produit()
    assert th.conclusion == appartient(
        prolongement_famille(), E.produit_famille(var("E"), var("I")))
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
