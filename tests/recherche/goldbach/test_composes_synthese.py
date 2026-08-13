# -*- coding: utf-8 -*-
"""Tests — réduction aux composés, synthèse, audit de fidélité.

⚠️ AUCUN de ces tests ne démontre la conjecture de Goldbach, et aucun ne doit
jamais être lu comme tel. Ils vérifient des ÉQUIVALENCES et des RÉDUCTIONS :
la conjecture reste ouverte, et le dernier test le rend explicite."""
from __future__ import annotations

import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    impl,
)
from outils_ia.conjectures.goldbach_reduction import hypothese_moities
from recherche.goldbach.audit_fidelite import (
    indivisible_implique_premier, premier_ent_deux,
)
from recherche.goldbach.composes import (
    equivalence_composes, famille_doubles, pont_alpha_premier,
)
from recherche.goldbach.enonces import (
    hypothese_composes_decomposition, hypothese_composes_rencontre,
)
from recherche.goldbach.synthese import (
    composes_impliquent_goldbach, gardee_implique_depot, rencontre_des_premiers,
)


def _clos(th):
    return th.est_clos and not th.hypotheses


def test_pont_alpha_et_famille_des_doubles():
    """Les deux briques de la branche « k premier ».

    `famille_doubles` n'existait QUE dans le scratchpad : sans elle la
    réduction aux composés est irreproductible."""
    assert _clos(pont_alpha_premier())
    assert _clos(famille_doubles())
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equivalence_composes():
    """⊢ HC ⇒ H et ⊢ H ⇒ HC — la conjecture ÉQUIVAUT à sa restriction.

    Le cas `k` premier se démontre seul : `2k = k + k` est déjà une somme de
    deux premiers. Il ne reste donc que les `k` composés — et c'est certifié,
    pas seulement plausible."""
    aller, retour = equivalence_composes()
    H, HC = hypothese_moities("kgb"), hypothese_composes_decomposition()
    assert _clos(aller) and aller.conclusion == impl(HC, H)
    assert _clos(retour) and retour.conclusion == impl(H, HC)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_gardee_implique_depot_sans_axiome_ad_hoc():
    """⊢ ∀k( DEC_ent(2k) ⇒ DEP(2k) ) — et SANS toucher au crible.

    On jette les gardes `Fini` : affaiblissement pur. ⚠️ La réciproque n'est
    pas disponible, et ce n'est pas un oubli — c'est le défaut de fidélité."""
    assert _clos(gardee_implique_depot())
    assert len(E.theorie_ensembles().axiomes) == 22


def test_rencontre_des_premiers():
    """Si `k` est premier, la rencontre a lieu — témoin `m := k`, miroir `y := k`."""
    assert _clos(rencontre_des_premiers())
    assert len(E.theorie_ensembles().axiomes) == 22


def test_synthese_composes_impliquent_goldbach():
    """🎯 ⊢ [ ∀k composé, rencontre(k) ] ⇒ H.

    LE livrable de l'arc : les trois lignes du projet convergent sur un seul
    objet. ⚠️ C'est une IMPLICATION — son hypothèse n'est pas démontrée, et
    cette hypothèse EST la conjecture restreinte aux composés."""
    th = composes_impliquent_goldbach()
    assert _clos(th)
    assert th.conclusion == impl(hypothese_composes_rencontre(),
                                 hypothese_moities("kgb"))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pont_alpha_dans_les_deux_sens():
    """Le pont d'habit α est PARAMÉTRÉ : `1 ⇒ 2` et `2 ⇒ 1`, nu et gardé.

    Le second sens n'existait pas : la symétrie du crible en a eu besoin, et
    plutôt qu'une seconde preuve identique aux noms près, le pont a été
    paramétré. Les deux sont le même théorème."""
    from recherche.goldbach.composes import (
        HABIT_1, HABIT_2, pont_alpha_premier_ent,
    )
    for (s, c) in ((HABIT_1, HABIT_2), (HABIT_2, HABIT_1)):
        assert _clos(pont_alpha_premier(source=s, cible=c))
        assert _clos(pont_alpha_premier_ent(source=s, cible=c))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_symetrie_du_crible():
    """⊢ ∀k ∀m ( m ∈ P∩Q ⇒ ∃m' ( m' ∈ P∩Q ∧ 2k = m+m' ) ).

    Les solutions vont par PAIRES : la rencontre est stable par l'involution
    `m ↦ 2k − m`, de point fixe `k`. C'est une contrainte de RÉPARTITION —
    la seule famille d'information que la carte n'a pas encore refermée.

    ⚠️ Conditionnel : « s'il y a une solution, il y en a deux ». Rien sur
    l'existence."""
    from recherche.goldbach.symetrie import cible_partenaire, symetrie_du_crible
    th = symetrie_du_crible()
    assert _clos(th)
    assert cible_partenaire().tag == "exists"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_audit_defaut_de_fidelite():
    """⊢ ( p ≠ 1 ∧ rien ne divise p ) ⇒ est_premier(p), pour un `p` QUELCONQUE.

    Le théorème de défaut : `est_premier` ne contraint pas son argument à être
    un entier. Soundness intacte, fidélité en défaut."""
    assert _clos(indivisible_implique_premier())
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_demi_intervalle():
    """⊢ ( Fini k,m,m' ∧ 2k = m+m' ) ⇒ ( m ≤ k OU m' ≤ k ).

    Avec la symétrie : chercher une décomposition de Goldbach ne demande
    d'explorer que la MOITIÉ de l'intervalle. Route sans inégalité stricte —
    comparabilité, complément, associativité itérée, simplification additive
    FINIE, Prop. 2.

    ⚠️ La garde `Fini` n'est pas de la prudence : la simplification additive
    est FAUSSE pour les cardinaux infinis (ℵ₀+1 = ℵ₀+2 sans que 1 = 2).
    Lent (~305 s) : la récurrence de la simplification domine."""
    from recherche.goldbach.demi import demi_intervalle
    th = demi_intervalle()
    assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_la_garde_fini_est_gratuite():
    """`premier_ent(2)` se démontre sans coût — la correction est indolore.

    Lent (~90 s) : `est_premier_num(2)` reconstruit la primalité de 2."""
    assert _clos(premier_ent_deux())
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_chaine_entiere_verte():
    """Le capstone : tous les maillons rejoués et jugés PAR LE NOYAU.

    Pas de sous-processus, pas de test textuel sur `stdout` — chaque maillon
    est un `Theoreme` inspecté. Lent (~110 s) : il reconstruit tout."""
    from recherche.goldbach.capstone import verifie_chaine
    lignes, vert = verifie_chaine(bavard=False)
    casses = [nom for (nom, ok, _d, _t) in lignes if not ok]
    assert not casses, "maillons cassés : %s" % ", ".join(casses)
    assert vert


def test_goldbach_reste_ouverte():
    """LE TEST QUI DIT LA VÉRITÉ : rien ici ne démontre la conjecture.

    Tout ce que le dossier produit est de la forme « X ⇒ Goldbach » ou
    « Goldbach ⟺ Y ». Aucune fonction n'expose un théorème dont la conclusion
    serait `H` toute seule — et si un jour l'une le faisait, ce test tomberait,
    ce qui est exactement le comportement voulu."""
    import inspect

    from recherche.goldbach import composes, pont_tau, synthese

    H = hypothese_moities("kgb")
    for module in (composes, pont_tau, synthese):
        for nom in getattr(module, "__all__", ()):
            objet = getattr(module, nom)
            if not inspect.isfunction(objet):
                continue
            params = inspect.signature(objet).parameters
            if any(p.default is inspect.Parameter.empty for p in params.values()):
                continue                               # exige un terme : hors test
            resultat = objet()
            for th in (resultat if isinstance(resultat, tuple) else (resultat,)):
                if hasattr(th, "conclusion"):
                    assert th.conclusion != H, (
                        "%s.%s conclut H — la conjecture serait DÉMONTRÉE ; "
                        "auditer immédiatement l'énoncé." % (module.__name__, nom))
