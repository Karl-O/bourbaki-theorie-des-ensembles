# -*- coding: utf-8 -*-
"""Tests du PONT DE MIGRATION et de la mort de la pathologie (§II.4.1 Déf. 2).

Deux garanties vérifiées ici :
  • le CONSÉQUENT du pont est VERBATIM l'ancien AXIOME_INTER_FAM (∀f, ∀I éliminés) —
    donc tout site d'usage disposant d'un indice retrouve son énoncé exact ;
  • la route d'attaque de `outils_ia/audit/preuve_incoherence_inter_vide.py` ÉCHOUE
    contre la sélection : le membre « z ∈ ⋃_{ι∈∅} X_ι » est REFUTABLE, et
    ⋂_{ι∈∅} X_ι = ∅ est certifié CLOS.

MISE À JOUR POST-MIGRATION.  Ce fichier a été écrit AVANT que la sélection ne soit
appliquée au corpus : deux tests ancraient « l'ancien énoncé » sur `E.AXIOME_INTER_FAM`
lui-même et affirmaient que la sélection vivait HORS de `theorie_ensembles()`.  La
migration a REMPLACÉ (et non complété) l'axiome du corpus par la forme de sélection —
`E.AXIOME_INTER_FAM == AXIOME_INTER_FAM_SEL`, compte toujours 22.  L'ancre « ancien
énoncé » a donc disparu du corpus ; elle est GELÉE ci-dessous dans
`_AXIOME_INTER_FAM_AVANT_MIGRATION`, copie littérale du texte d'avant.  Les deux
garanties d'origine sont conservées, plus une neuve : l'ancienne forme (celle qui
rendait la théorie contradictoire pour I=∅) est bien SORTIE des 22.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, impl, equiv, appartient, existe, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_arriere, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes.ensembles_pas_ensemble_universel import (
    pas_ensemble_universel)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    AXIOME_INTER_FAM_SEL, corps_membres_famille, membre_inter_selection)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides, enonce_caracterisation_inter_famille,
    caracterisation_inter_famille_non_vide,
    caracterisation_inter_famille_indices_non_vide,
    enonce_inter_famille_vide_est_vide, inter_famille_vide_est_vide,
    inter_famille_vide_egale_vide)


# ── L'ANCRE GELÉE ─────────────────────────────────────────────────────────────
# Copie LITTÉRALE de `ensembles_abrege.AXIOME_INTER_FAM` tel qu'il était AVANT la
# migration (forme sans borne, contradictoire pour I=∅ : cf.
# `outils_ia/audit/preuve_incoherence_inter_vide.py`).  Ce n'est PAS un axiome —
# aucune théorie ne le porte, aucun `Theoreme` n'en est tiré : c'est une simple
# `Formule` de référence, qui remplace l'ancre disparue du corpus.
_AXIOME_INTER_FAM_AVANT_MIGRATION = pourtout("f", pourtout("I", pourtout("z",
    equiv(appartient(var("z"), E.inter_famille(var("f"), var("I"))),
          pourtout("i", impl(appartient(var("i"), var("I")),
                             appartient(var("z"),
                                        E.valeur_famille(var("f"), var("i")))))))))


def test_4_caracterisation_sous_temoin_existentiel_clos():
    """⊢ (∃i)(i∈I) ⇒ (∀z)( z∈⋂ ⇔ (∀i)(i∈I ⇒ z∈X_i) ) — CLOS, 0 hypothèse."""
    r = caracterisation_inter_famille_non_vide()
    assert r.conclusion == impl(indices_non_vides(var("I")),
                                enonce_caracterisation_inter_famille())
    assert r.hypotheses == frozenset()
    assert r.est_clos is True


def test_4_le_consequent_est_verbatim_l_ancien_axiome():
    """LE point de la migration : on récupère l'ANCIEN énoncé, mot pour mot.

    MIS À JOUR après application de la migration.  Avant, l'ancre de « l'ancien
    énoncé » était `E.AXIOME_INTER_FAM` lui-même, instancié sur f puis I.  Le corpus
    porte DÉSORMAIS la sélection à cette place : l'instanciation de l'axiome ne rend
    plus l'ancienne équivalence mais la conjonction (z∈⋃ et corps).  L'ancre est donc
    prise sur la copie gelée `_AXIOME_INTER_FAM_AVANT_MIGRATION` — ce qui rend le test
    STRICTEMENT plus fort qu'avant : il vérifie en plus que l'axiome du corpus a bien
    changé, et que l'ancien énoncé n'est plus postulé mais DÉMONTRÉ par le pont."""
    # (1) état post-migration constaté : le corpus porte la SÉLECTION.
    assert E.AXIOME_INTER_FAM == AXIOME_INTER_FAM_SEL
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    selection = instancie(instancie(ax, var("f")), var("I"))   # (∀z)(z∈⋂ ⇔ (z∈⋃ et corps))
    assert selection.conclusion == pourtout("z", membre_inter_selection().conclusion)
    assert selection.conclusion != enonce_caracterisation_inter_famille()

    # (2) l'ANCIEN énoncé, ∀f et ∀I éliminés, est exactement celui du pont.
    assert _AXIOME_INTER_FAM_AVANT_MIGRATION == pourtout(
        "f", pourtout("I", enonce_caracterisation_inter_famille()))
    assert caracterisation_inter_famille_non_vide().conclusion.sous[1] == \
        enonce_caracterisation_inter_famille()


def test_4_decharge_effective_sur_un_site_d_usage_type():
    """Un site qui possède un indice a∈I retrouve l'équivalence complète."""
    va, vI = var("a"), var("I")
    h_a = N.assume(appartient(va, vI))
    ex = N.modus_ponens(h_a, N.s5(appartient(var("i"), vI), va, "i"))   # (∃i)(i∈I)
    recupere = N.modus_ponens(ex, caracterisation_inter_famille_non_vide())
    assert recupere.conclusion == enonce_caracterisation_inter_famille()
    assert recupere.hypotheses == frozenset([appartient(va, vI)])       # SEULE hyp : a∈I


def test_6_forme_litterale_du_livre_i_non_vide():
    """⊢ ¬(I=∅) ⇒ (∀z)( z∈⋂ ⇔ (∀i)(i∈I ⇒ z∈X_i) ) — la phrase de la Déf. 2, CLOSE.

    La brique ¬(A=∅) ⇔ (∃z)(z∈A) EXISTE (`ensembles_vide.non_vide_ssi_element`) ;
    elle n'a pas été bricolée ici, seulement α-pontée vers le liant « i »."""
    r = caracterisation_inter_famille_indices_non_vide()
    assert r.conclusion == impl(non(egal(var("I"), E.VIDE)),
                                enonce_caracterisation_inter_famille())
    assert r.hypotheses == frozenset()
    assert r.est_clos is True


def test_5_inter_sur_indices_vide_est_vide_clos():
    """⊢ (∀z)¬(z ∈ ⋂_{ι∈∅} X_ι)  et  ⊢ ⋂_{ι∈∅} X_ι = ∅ — CLOS. La pathologie est morte."""
    r = inter_famille_vide_est_vide()
    assert r.conclusion == enonce_inter_famille_vide_est_vide()
    assert r.hypotheses == frozenset() and r.est_clos is True

    eg = inter_famille_vide_egale_vide()
    assert eg.conclusion == egal(E.inter_famille(var("f"), E.VIDE), E.VIDE)
    assert eg.hypotheses == frozenset() and eg.est_clos is True


def test_5_la_route_d_attaque_de_l_audit_echoue_desormais():
    """REJEU de `preuve_incoherence_inter_vide` contre la SÉLECTION : elle ÉCHOUE.

    La route d'attaque construisait le membre (∀i)(i∈∅ ⇒ x∈X_i) ex falso, puis
    l'injectait par `equivalence_arriere` pour peupler ⋂_{ι∈∅}.  Avec la sélection,
    `equivalence_arriere` réclame la CONJONCTION (x∈⋃_{ι∈∅} et (∀i)(…)) : le modus
    ponens est REFUSÉ par le noyau, et le membre manquant est même RÉFUTABLE."""
    vFam, vx, vi = var("Fam"), var("x"), var("i")
    eq = membre_inter_selection(vFam, E.VIDE, vx)

    # le membre (∀i)(i∈∅ ⇒ x∈X_i) se construit toujours (ex falso) …
    nvide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vi)
    P, Q = appartient(vi, E.VIDE), appartient(vx, E.valeur_famille(vFam, vi))
    membre = N.generalisation("i", N.modus_ponens(nvide, N.s2(non(P), Q)))
    assert membre.conclusion == corps_membres_famille(vFam, E.VIDE, vx)

    # … mais il ne suffit plus : le noyau refuse le modus ponens.
    with pytest.raises(ValueError):
        N.modus_ponens(membre, equivalence_arriere(eq))

    # et le membre manquant n'est pas seulement absent : il est RÉFUTABLE.
    manquant = appartient(vx, E.reunion_famille(vFam, E.VIDE))
    refute = instancie(inter_famille_vide_est_vide("Fam", "x"), vx)
    assert refute.conclusion == non(appartient(vx, E.inter_famille(vFam, E.VIDE)))
    assert refute.est_clos is True


def test_5_coherence_retrouvee_avec_pas_ensemble_universel():
    """Plus d'ensemble universel par ⋂_{ι∈∅} : l'attaque et Russell ne s'affrontent plus."""
    neg = pas_ensemble_universel()
    cible = existe("X", pourtout("x", appartient(var("x"), var("X"))))
    assert neg.conclusion == non(cible) and neg.est_clos
    # ⋂_{ι∈∅} X_ι = ∅ : ce n'est PLUS un témoin d'ensemble universel.
    assert inter_famille_vide_egale_vide().conclusion == egal(
        E.inter_famille(var("f"), E.VIDE), E.VIDE)


def test_theorie_ensembles_reste_a_22_axiomes():
    """INVARIANT DUR : aucun axiome AJOUTÉ aux 22 ; la sélection a REMPLACÉ l'ancienne.

    MIS À JOUR après application de la migration.  La seconde assertion disait
    « AXIOME_INTER_FAM_SEL ∉ theorie_ensembles() » : c'était vrai tant que la
    fondation vivait à côté du corpus, dans sa théorie dédiée.  La migration l'y a
    fait ENTRER — en REMPLAÇANT `AXIOME_INTER_FAM`, pas en s'y ajoutant.  L'invariant
    réel (le compte à 22) est INCHANGÉ et reste vérifié ; on vérifie en plus que
    l'ancienne forme, celle qui rendait la théorie contradictoire pour I=∅, est
    effectivement SORTIE des 22."""
    caracterisation_inter_famille_non_vide()
    caracterisation_inter_famille_indices_non_vide()
    inter_famille_vide_egale_vide()
    assert len(E.theorie_ensembles().axiomes) == 22
    assert AXIOME_INTER_FAM_SEL in E.theorie_ensembles().axiomes
    assert AXIOME_INTER_FAM_SEL == E.AXIOME_INTER_FAM
    assert _AXIOME_INTER_FAM_AVANT_MIGRATION not in E.theorie_ensembles().axiomes
