# -*- coding: utf-8 -*-
"""Test n°67 (E.R.27) — « 𝔉 a un plus petit élément pour ⊂ ⇔ ⋂𝔉 ∈ 𝔉 ».

Couvre aussi, en garde de RÉGRESSION, la décharge de la famille identité dont ce
résultat dépend.  ⚠️ MISE À JOUR 2026-07-26 : `ensembles_famille_identite_ii4.py`
a DÉSORMAIS son test miroir propre (`test_famille_identite_ii4.py`, 10ᵉ et dernier
fichier du dossier — le cap ≤10 est atteint pile, en miroir exact des 10 modules
de `bourbaki/…/ii_4_1_definitions_algebre/`).  Les gardes ci-dessous restent : ce
sont celles du SITE D'USAGE, complémentaires de celles du module.
"""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, appartient, equiv)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_famille_identite_ii4 import (
    pont_fam_valeur, famille_identite_est_identite, membre_inter_parties)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_reunion_ensemble_membre_ii4 import (
    inter_parties, reunion_parties,
    a_plus_petit_pour_inclusion, a_plus_grand_pour_inclusion,
    plus_petit_est_inter, enonce_plus_petit_est_inter,
    plus_petit_ssi_inter_membre, enonce_plus_petit_ssi_inter_membre,
    plus_grand_est_reunion, enonce_plus_grand_est_reunion,
    plus_grand_ssi_reunion_membre, enonce_plus_grand_ssi_reunion_membre)


def _hyps_attendues(u="F"):
    """{PONT(𝔉), 𝔉≠∅} — les deux hypothèses honnêtes, et RIEN d'autre."""
    return frozenset([pont_fam_valeur(u), non(egal(var(u), E.VIDE))])


def test_plus_petit_est_inter():
    """{PONT,𝔉≠∅} ⊢ (A∈𝔉 et (∀B)(B∈𝔉⇒A⊂B)) ⇒ A = ⋂𝔉."""
    r = plus_petit_est_inter()
    assert r.conclusion == enonce_plus_petit_est_inter()
    assert r.hypotheses == _hyps_attendues()
    assert r.est_clos is False


def test_plus_petit_ssi_inter_membre():
    """{PONT,𝔉≠∅} ⊢ (∃A)(A∈𝔉 et (∀B)(B∈𝔉⇒A⊂B)) ⇔ (⋂𝔉 ∈ 𝔉).   [n°67, E.R.27]"""
    r = plus_petit_ssi_inter_membre()
    assert r.conclusion == enonce_plus_petit_ssi_inter_membre()
    assert r.hypotheses == _hyps_attendues()
    assert r.est_clos is False


def test_enonce_non_vacuous():
    """L'énoncé porte bien sur ⋂𝔉 et sur l'∃ déplié — pas une tautologie."""
    concl = plus_petit_ssi_inter_membre().conclusion
    gauche = a_plus_petit_pour_inclusion()                  # (∃A)(...)
    droite = appartient(inter_parties(), var("F"))          # ⋂𝔉 ∈ 𝔉
    assert concl == equiv(gauche, droite)
    assert gauche != droite                                 # pas une tautologie A⇔A
    # les deux membres mentionnent bien la famille identité / l'inclusion
    assert "inter_fam" in repr(droite)
    assert "graphe_terme" in repr(droite)


def test_parametrage_ensemble_autre_nom():
    """Le résultat n'est pas accidentellement lié au nom « F »."""
    r = plus_petit_ssi_inter_membre("Frak")
    assert r.conclusion == enonce_plus_petit_ssi_inter_membre("Frak")
    assert r.hypotheses == _hyps_attendues("Frak")


def test_regression_famille_identite_dechargee():
    """Garde : la décharge de est_famille_identite tient sous {PONT} seul."""
    d = famille_identite_est_identite("F")
    assert d.hypotheses == frozenset([pont_fam_valeur("F")])
    m = membre_inter_parties("F", "z")
    assert m.hypotheses == _hyps_attendues()


def test_plus_grand_est_reunion():
    """{PONT} ⊢ (A∈𝔉 et (∀B)(B∈𝔉⇒B⊂A)) ⇒ A = ⋃𝔉.   (dual : PAS de 𝔉≠∅.)"""
    r = plus_grand_est_reunion()
    assert r.conclusion == enonce_plus_grand_est_reunion()
    assert r.hypotheses == frozenset([pont_fam_valeur("F")])
    assert r.est_clos is False


def test_plus_grand_ssi_reunion_membre():
    """{PONT} ⊢ (∃A)(A∈𝔉 et (∀B)(B∈𝔉⇒B⊂A)) ⇔ (⋃𝔉 ∈ 𝔉).   [n°67, E.R.27]"""
    r = plus_grand_ssi_reunion_membre()
    assert r.conclusion == enonce_plus_grand_ssi_reunion_membre()
    assert r.hypotheses == frozenset([pont_fam_valeur("F")])
    assert r.est_clos is False


def test_dual_non_vacuous_et_distinct():
    """⋃ et ⋂ donnent bien DEUX énoncés distincts, chacun non trivial."""
    haut = plus_grand_ssi_reunion_membre().conclusion
    bas = plus_petit_ssi_inter_membre().conclusion
    assert haut != bas
    assert haut == equiv(a_plus_grand_pour_inclusion(),
                         appartient(reunion_parties(), var("F")))
    # les corps ⊂ sont bien retournés (A⊂B contre B⊂A)
    assert a_plus_grand_pour_inclusion() != a_plus_petit_pour_inclusion()
    assert "reunion_fam" in repr(reunion_parties())
    assert "inter_fam" in repr(inter_parties())


def test_theorie_inchangee():
    plus_petit_est_inter()
    plus_petit_ssi_inter_membre()
    plus_grand_est_reunion()
    plus_grand_ssi_reunion_membre()
    assert len(E.theorie_ensembles().axiomes) == 22
