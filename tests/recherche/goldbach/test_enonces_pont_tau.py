# -*- coding: utf-8 -*-
"""Tests — le socle d'énoncés et le pont ∃ ↔ τ de l'arc Goldbach."""
from __future__ import annotations

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    impl,
)
from outils_ia.conjectures.goldbach_reduction import hypothese_moities
from recherche.goldbach.enonces import (
    antecedent_et_decomposition, atteste, hypothese_composes_decomposition,
    hypothese_composes_rencontre,
)
from recherche.goldbach.pont_tau import (
    double, forme_canonique, hypothese_canonique, plus_grand_premier,
    pont_tau_aller, pont_tau_retour, route_temoin, somme_du_temoin,
    temoins_canoniques,
)


def _clos(th):
    return th.est_clos and not th.hypotheses


def test_prelevement_recompose_bien_H():
    """Le prélèvement de A(k) et DEP(2k) redonne H à l'identique.

    C'est LA garde du dossier : `pourtout` vaut `¬∃¬` et `impl` vaut
    `ou(¬·, ·)`, si bien qu'un cran de trop dans `.sous` donne une
    sous-formule plausible et fausse. La recomposition l'interdit."""
    a, dep = antecedent_et_decomposition()
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        pourtout,
    )
    assert pourtout("kgb", impl(a, dep)) == hypothese_moities("kgb")
    assert dep.tag == "exists" and dep.lieur == "pgb"


def test_les_deux_hypotheses_composees_sont_distinctes():
    """HC-décomposition et HC-rencontre ne doivent JAMAIS être confondues.

    Même antécédent, conséquent différent — la confusion a déjà été faite
    dans les scripts d'exploration, où les deux s'appelaient « HC »."""
    assert hypothese_composes_decomposition() != hypothese_composes_rencontre()


def test_temoins_canoniques_lisent_les_vrais_liants():
    """Les liants sont LUS sur la formule du noyau, jamais devinés."""
    _, _, p = temoins_canoniques()
    assert p["xp"] == "pgb" and p["xq"] == "qgb"
    assert p["DEP"].tag == "exists" and p["inner_T"].tag == "exists"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pont_tau_les_deux_sens():
    """⊢ ∀k( DEP ⇒ C ) et ⊢ ∀k( C ⇒ DEP ), tous deux clos."""
    for th in (pont_tau_aller(), pont_tau_retour()):
        assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_forme_canonique_est_une_equivalence():
    """⊢ H ⇒ H_τ et ⊢ H_τ ⇒ H — Goldbach s'écrit SANS existentiel.

    Reformulation à contenu arithmétique nul : `H_τ` est exactement aussi
    ouverte que la conjecture. C'est un changement d'adresse, pas de statut."""
    directe, reciproque = forme_canonique()
    H, H_tau = hypothese_moities("kgb"), hypothese_canonique()
    assert _clos(directe) and directe.conclusion == impl(H, H_tau)
    assert _clos(reciproque) and reciproque.conclusion == impl(H_tau, H)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_route_temoin_accepte_n_importe_quels_termes():
    """Le générateur transporte l'obligation vers TOUTE stratégie de témoins.

    Il ne démontre rien d'arithmétique : la clôture du théorème ne dit pas
    que les témoins conviennent, seulement que s'ils conviennent la
    conjecture suit."""
    T = plus_grand_premier(double())
    for (t, q) in ((T, T), (double(), T)):
        th = route_temoin(t, q)
        assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_somme_du_temoin_decharge_la_clause_de_somme():
    """Pour un témoin DÉFINI, `2k = T + (2k−T)` n'est plus une obligation.

    Premier résultat de la famille avec du contenu réel : reste la seule
    vraie question, « T est-il premier, et son complément aussi ? »."""
    th = somme_du_temoin(plus_grand_premier(double()))
    assert _clos(th)
    assert "CLOS" in atteste(th)
    assert len(E.theorie_ensembles().axiomes) == 22
