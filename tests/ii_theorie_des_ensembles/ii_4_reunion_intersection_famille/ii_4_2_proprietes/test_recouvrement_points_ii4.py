# -*- coding: utf-8 -*-
"""Test du pont « recouvrement ⇒ lecture ponctuelle » (§II.4.6 Déf. 5).

Le dernier test EFFECTUE la décharge de H_rec sur `relation_partition_reflexive_dans`
(ii_6) : c'est ici — et pas dans bourbaki/ii_4_* — qu'on a le droit d'importer ii_6,
la direction des dépendances du code de preuve devant rester ii_6 → ii_4.
"""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_2_proprietes.ensembles_recouvrement_points_ii4 import (
    recouvrement_points, enonce_recouvrement_donne_points, recouvrement_donne_points)


def test_recouvrement_donne_points_clos():
    """⊢ (E ⊂ ⋃X_ι) ⇒ (∀x)(x∈E ⇒ (∃i)(i∈I et x∈X_i)) — CLOS, 0 hypothèse."""
    r = recouvrement_donne_points()
    assert r.conclusion == enonce_recouvrement_donne_points()
    assert r.hypotheses == frozenset()
    assert r.est_clos is True


def test_enonce_non_vacuous():
    """L'antécédent est bien est_recouvrement, le conséquent bien H_rec."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    rec = E.est_recouvrement(var("f"), var("I"), var("E"))
    hrec = recouvrement_points()
    assert rec != hrec                                   # pas une tautologie A⇒A
    assert enonce_recouvrement_donne_points() == impl(rec, hrec)
    assert "reunion_fam" in repr(rec)                    # le ⋃ de famille est présent
    # Migration d'encodage du 2 août 2026 : X_i = valeur_famille(f,i) = valeur(f,i)
    # = τy((i,y)∈f) — le symbole libre 'fam' n'existe plus, le τ le remplace.
    assert "nom='fam'" not in repr(hrec)                 # l'ancien encodage est mort
    assert "lieur=" in repr(hrec)                        # X_i = τ-terme de valeur


def test_formule_hrec_verbatim_identique_a_ii6():
    """GARDE ANTI-DÉRIVE : la formule locale == celle attendue par ii_6."""
    from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ensembles_egalite_equivalence import (
        recouvrement_points as recouvrement_points_ii6)
    assert recouvrement_points("f", "I", "E") == \
        recouvrement_points_ii6(var("f"), var("I"), var("E"))


def test_decharge_effective_de_h_rec_dans_ii6():
    """H_rec DISPARAÎT de relation_partition_reflexive_dans, remplacée par est_recouvrement.

    C'est la raison d'être du pont : ii_6 portait H_rec en hypothèse honnête au
    motif que le maillon z∈⋃X_ι ⇔ (∃ι)(…) serait absent — il ne l'est pas."""
    from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ensembles_egalite_equivalence import (
        relation_partition_reflexive_dans, recouvrement_points as hrec_ii6,
        parties_points)
    cible = relation_partition_reflexive_dans()
    h_rec = hrec_ii6(var("f"), var("I"), var("E"))
    h_par = parties_points(var("f"), var("I"), var("E"), i="i")
    assert cible.hypotheses == frozenset([h_rec, h_par])          # état de départ

    rec = E.est_recouvrement(var("f"), var("I"), var("E"))
    # {est_recouvrement} ⊢ H_rec
    h_rec_derive = N.modus_ponens(N.assume(rec), recouvrement_donne_points())
    assert h_rec_derive.conclusion == h_rec
    # ... donc {est_recouvrement, H_parties} ⊢ est_reflexive_dans(R, E)
    dechargee = N.modus_ponens(h_rec_derive, N.loi_deduction(h_rec, cible))
    assert dechargee.conclusion == cible.conclusion
    assert dechargee.hypotheses == frozenset([rec, h_par])
    assert h_rec not in dechargee.hypotheses                      # H_rec est PARTIE


def test_theorie_inchangee():
    recouvrement_donne_points()
    assert len(E.theorie_ensembles().axiomes) == 22
