# -*- coding: utf-8 -*-
"""Tests — système restreint construit + produit sur J (§III.7).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient, libres_t,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    hypothese_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
    famille_coordonnees,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_restriction_systeme import (
    faits_clos_famille, clause_valeurs, famille_dans_produit,
    valeur_dans_produit, restriction_construite, restriction_valeur,
    clause_valeurs_restreinte, valeur_dans_produit_restreint,
)


def test_trois_faits_clos_sur_la_famille():
    """🎯 La famille (f_α(x))_{α∈J} est CONSTRUITE : graphe, fonctionnel et
    domaine sont CLOS — trois des quatre clauses du produit, gratuites."""
    gr, fn, dm = faits_clos_famille()
    assert gr.est_clos and fn.est_clos and dm.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_clause_valeurs_demontree():
    """👑 La 4ᵉ clause DÉMONTRÉE, et c'est LITTÉRALEMENT `hypothese_valeurs`.

    Le test compare à la formule que réclame le pivot, pas à une formule
    ressemblante — sans quoi « démontrée » ne voudrait rien dire."""
    th = clause_valeurs()
    fam = famille_coordonnees("E", "f", "J", "s", "t")
    assert th.conclusion == hypothese_valeurs(var("E"), var("J"), "i", fam)
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_famille_dans_produit_isole_la_clause():
    """Le découpage isole exactement ce qui n'est pas gratuit : UNE hypothèse."""
    th = famille_dans_produit()
    fam = famille_coordonnees("E", "f", "J", "s", "t")
    assert th.conclusion == appartient(fam, E.produit_famille(var("E"), var("J")))
    assert len(th.hypotheses) == 1


def test_valeur_dans_produit():
    """👑 g(x) ∈ ∏_{α∈J} E_α sous les seules hypothèses de contexte."""
    assert len(valeur_dans_produit().hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_restriction_construite_et_son_pont():
    """👑👑 DÉBLOCAGE : le système restreint CONSTRUIT, et le pont (restr)_ι = E_ι.

    Le terme du dépôt `restriction_systeme_indices` n'a aucun axiome — rien n'est
    démontrable sur lim←_J.  Construit comme graphe_terme, il redevient un objet
    dont on peut parler : le pont sort avec UNE hypothèse (ι ∈ J)."""
    th = restriction_valeur()
    assert th.conclusion == egal(
        E.valeur_famille(restriction_construite(), var("i")),
        E.valeur_famille(var("E"), var("i")))
    assert th.hypotheses == frozenset({appartient(var("i"), var("J"))})
    assert len(E.theorie_ensembles().axiomes) == 22


def test_graphe_terme_porte_ses_liants_libres():
    """⚠️ Rappel du piège : un `graphe_terme` ne lie pas — d'où les noms frais."""
    assert libres_t(restriction_construite()) == {"E", "J", "c"}


def test_tout_refait_dans_le_systeme_restreint():
    """👑 Le RACCOURCI : plutôt que de démontrer l'égalité des deux produits, on
    refait la construction dans le bon système — le pivot étant paramétré par la
    famille, le ⋃ de l'inclusion s'aligne tout seul."""
    assert len(clause_valeurs_restreinte().hypotheses) == 2
    th = valeur_dans_produit_restreint()
    assert th.conclusion == appartient(
        famille_coordonnees("E", "f", "J", "s", "t"),
        E.produit_famille(restriction_construite(), var("J")))
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22
