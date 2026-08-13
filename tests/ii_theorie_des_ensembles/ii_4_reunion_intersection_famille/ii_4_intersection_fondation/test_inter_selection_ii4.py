# -*- coding: utf-8 -*-
"""Tests de la FONDATION ⋂ = sélection dans ⋃ (§II.4.1 Déf. 2, route Grimm B5).

Un test par résultat + les gardes d'invariant : `theorie_ensembles()` reste à 22
axiomes, et l'élimination est LITTÉRALEMENT l'énoncé que produisait l'ancien
AXIOME_INTER_FAM dans ce sens (c'est la moitié gratuite de la migration).

MISE À JOUR POST-MIGRATION (26 juil. 2026).  Ce fichier a été écrit AVANT que la
migration ne soit appliquée au corpus : `ensembles_abrege.AXIOME_INTER_FAM` était
alors l'ancienne forme (équivalence NUE, contradictoire pour I = ∅) et la forme de
sélection ne vivait que dans la théorie dédiée de ce dossier.  Depuis la migration,
`E.AXIOME_INTER_FAM == AXIOME_INTER_FAM_SEL` : les trois assertions qui encodaient
l'état d'AVANT (« la sélection n'est pas dans les 22 », « le noyau la refuse »,
« l'élimination se lit directement sur l'axiome du corpus, sans projeter ») sont
devenues fausses PARCE QUE la migration a réussi.  Elles sont ci-dessous
TRANSFORMÉES en leur énoncé post-migration — aucune n'est supprimée, et la garde de
fond (« rien n'est postulé en douce ») est conservée en la retournant contre
l'ANCIENNE forme, qui doit désormais être refusée par le noyau.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, impl, equiv, appartient, pourtout, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    syllogisme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie, projection_droite)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    AXIOME_INTER_FAM_SEL, theorie_inter_selection, corps_membres_famille,
    membre_inter_selection, reunion_intro_terme,
    enonce_inter_donne_membres, inter_donne_membres,
    enonce_inter_inclus_reunion, inter_inclus_reunion,
    enonce_inter_par_membres_si_temoin, inter_par_membres_si_temoin)


def test_membre_inter_selection_est_l_instance_de_l_axiome():
    """⊢ z∈⋂ ⇔ (z∈⋃ et (∀i)(i∈I⇒z∈X_i)) — instance directe, close."""
    t = membre_inter_selection()
    assert t.est_clos is True and t.hypotheses == frozenset()
    vf, vI, vz = var("f"), var("I"), var("z")
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, equiv
    assert t.conclusion == equiv(
        appartient(vz, E.inter_famille(vf, vI)),
        et(appartient(vz, E.reunion_famille(vf, vI)),
           corps_membres_famille(vf, vI, vz)))


def test_1_inter_donne_membres_clos():
    """⊢ (∀z)( z∈⋂ ⇒ (∀i)(i∈I ⇒ z∈X_i) ) — CLOS, 0 hypothèse."""
    r = inter_donne_membres()
    assert r.conclusion == enonce_inter_donne_membres()
    assert r.hypotheses == frozenset()
    assert r.est_clos is True


def test_1_elimination_verbatim_identique_a_l_ancien_axiome():
    """MIGRATION GRATUITE : l'élimination a EXACTEMENT le même énoncé qu'avant.

    Les sites d'usage qui ne consomment que cette direction migrent sans un mot
    de changement — c'est la moitié de la migration des 34 sites.

    POST-MIGRATION : le membre droit de l'axiome du corpus est désormais une
    CONJONCTION (z∈⋃ et corps), donc `equivalence_avant` seul ne donne plus
    l'élimination — il faut PROJETER à droite (motif (a)).  Ce test dérivait la
    version « ancienne » depuis E.AXIOME_INTER_FAM sans projeter : la projection
    est ajoutée ici.  Ce qu'il certifie ne change pas d'un iota : l'ÉNONCÉ obtenu
    (∀z)(z∈⋂ ⇒ (∀i)(i∈I ⇒ z∈X_i)) est littéralement celui d'avant la migration,
    d'où sa construction explicite ci-dessous, indépendante du module testé."""
    vf, vI, vz = var("f"), var("I"), var("z")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    inst = instancie(instancie(ax, vf), vI)         # (∀z)(z∈⋂ ⇔ (z∈⋃ et corps))
    fwd = equivalence_avant(instancie(inst, vz))    # z∈⋂ ⇒ (z∈⋃ et corps)
    elim = syllogisme(fwd, projection_droite(       # z∈⋂ ⇒ corps
        appartient(vz, E.reunion_famille(vf, vI)), corps_membres_famille(vf, vI, vz)))
    ancien = N.generalisation("z", elim)
    assert ancien.conclusion == inter_donne_membres().conclusion
    # …et cet énoncé est VERBATIM la forme d'avant la migration (aucune trace de ⋃) :
    assert ancien.conclusion == pourtout("z", impl(
        appartient(vz, E.inter_famille(vf, vI)), corps_membres_famille(vf, vI, vz)))


def test_2_inter_inclus_reunion_clos_et_est_bien_une_inclusion():
    """⊢ ⋂_{ι∈I} X_ι ⊂ ⋃_{ι∈I} X_ι — CLOS, et littéralement le terme `inclus`."""
    r = inter_inclus_reunion()
    assert r.conclusion == enonce_inter_inclus_reunion()
    assert r.hypotheses == frozenset() and r.est_clos is True
    vf, vI = var("f"), var("I")
    assert r.conclusion == inclus(E.inter_famille(vf, vI), E.reunion_famille(vf, vI))


def test_3_inter_par_membres_si_temoin_clos():
    """⊢ (a∈I) ⇒ ( (∀i)(i∈I ⇒ z∈X_i) ⇒ z∈⋂ ) — CLOS, 0 hypothèse."""
    r = inter_par_membres_si_temoin()
    assert r.conclusion == enonce_inter_par_membres_si_temoin()
    assert r.hypotheses == frozenset()
    assert r.est_clos is True


def test_3_le_temoin_d_indice_est_bien_en_antecedent():
    """L'introduction porte VRAIMENT l'hypothèse a∈I (pas une tautologie A⇒A)."""
    vf, vI, va, vz = var("f"), var("I"), var("a"), var("z")
    concl = inter_par_membres_si_temoin().conclusion
    assert concl == impl(appartient(va, vI),
                         impl(corps_membres_famille(vf, vI, vz),
                              appartient(vz, E.inter_famille(vf, vI))))
    # l'antécédent a∈I est distinct du conséquent : pas de A⇒A déguisé
    assert appartient(va, vI) != impl(corps_membres_famille(vf, vI, vz),
                                      appartient(vz, E.inter_famille(vf, vI)))


def test_reunion_intro_terme_accepte_un_tau_terme():
    """Le témoin de la réunion peut être un TERME (τ-terme inclus) — clos."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import tau
    vf, vI, vz = var("f"), var("I"), var("z")
    T0 = tau("i", appartient(var("i"), vI))
    r = reunion_intro_terme(vf, vI, T0, vz)
    assert r.est_clos is True
    assert r.conclusion.sous[1] == appartient(vz, E.reunion_famille(vf, vI))


def test_theorie_ensembles_reste_a_22_axiomes():
    """INVARIANT DUR : le COMPTE reste 22 — la migration REMPLACE, elle n'ajoute pas.

    Avant la migration ce test assertait `AXIOME_INTER_FAM_SEL not in ...` : la
    fondation vivait dans sa théorie dédiée et le corpus portait encore l'ancienne
    forme.  Depuis la migration, la sélection A remplacé l'ancien axiome DANS les
    22 : l'assertion devient donc son contraire — présence — et l'invariant réel
    (le compte inchangé, aucun axiome ajouté) est ce qui reste testé."""
    inter_donne_membres(); inter_inclus_reunion(); inter_par_membres_si_temoin()
    assert len(E.theorie_ensembles().axiomes) == 22
    assert AXIOME_INTER_FAM_SEL == E.AXIOME_INTER_FAM      # migration effective
    assert AXIOME_INTER_FAM_SEL in E.theorie_ensembles().axiomes
    assert theorie_inter_selection().axiomes == [AXIOME_INTER_FAM_SEL]


def test_le_noyau_refuse_l_ancienne_forme_sans_hypothese():
    """Rien n'est postulé en douce — garde RETOURNÉE contre l'ANCIENNE forme.

    Avant la migration, ce test (nommé alors `..._refuse_l_axiome_de_selection_
    hors_de_sa_theorie`) vérifiait que la sélection n'était pas un axiome des 22.
    Elle l'est devenue, donc `N.axiome` l'accepte désormais (première assertion).
    La garde de fond survit en visant l'autre bout : l'ANCIENNE équivalence NUE
    (∀f)(∀I)(∀z)( z∈⋂ ⇔ (∀i)(i∈I ⇒ z∈X_i) ) — celle qui rendait ⋂_{ι∈∅} X_ι
    universel et la théorie contradictoire — n'est plus un axiome et le noyau la
    refuse.  Elle ne se récupère que sous (∃i)(i∈I), et alors DÉMONTRÉE
    (`ensembles_inter_migration_ii4.caracterisation_inter_famille_non_vide`)."""
    thm = N.axiome(E.theorie_ensembles(), AXIOME_INTER_FAM_SEL)
    assert thm.conclusion == AXIOME_INTER_FAM_SEL and thm.hypotheses == frozenset()
    vf, vI, vz = var("f"), var("I"), var("z")
    ancienne_forme_nue = pourtout("f", pourtout("I", pourtout("z", equiv(
        appartient(vz, E.inter_famille(vf, vI)),
        corps_membres_famille(vf, vI, vz)))))
    assert ancienne_forme_nue != AXIOME_INTER_FAM_SEL
    with pytest.raises(ValueError):
        N.axiome(E.theorie_ensembles(), ancienne_forme_nue)
