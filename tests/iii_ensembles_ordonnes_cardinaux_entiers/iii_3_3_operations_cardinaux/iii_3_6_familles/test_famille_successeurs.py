# -*- coding: utf-8 -*-
"""Test — famille (i+1)_{i<n}, terme n!=∏_{i<n}(i+1) (Déf.2 FIDÈLE), et 0!=1.

Le CAS DE BASE de la Déf. 2 (`factorielle_def2_zero`) est vérifié en MIROIR : la
conclusion attendue est reconstruite À LA MAIN ici, hors du module testé, et les
hypothèses sont assertées par égalité EXACTE de frozenset (`len(...)==0` ne dirait
pas LESQUELLES).  Les mutants sont en bas : un test qui ne mord pas est décoratif.

⚠️ theorie==22 avant ET après.  ⚠️ N_existe (~5 min, mémoïsé par process).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, UN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (
    un_egale_card_singleton,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (
    famille_successeurs, famille_successeurs_fonctionnelle,
    famille_successeurs_valeur, factorielle_def2,
    produit_cardinal_vide, factorielle_def2_zero_enonce, factorielle_def2_zero,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_terme_def2_bien_forme():
    """n! = ∏_{i<n}(i+1) : le terme du livre est bien formé (app produit_cardinal→Card)."""
    t = factorielle_def2("ntest")
    assert t.tag in ("app", "tau")


def test_famille_fonctionnelle_close():
    """⊢ est_fonctionnel((i+1)_{i<n}) — CLOS."""
    assert famille_successeurs_fonctionnelle().est_clos


def test_famille_valeur():
    """{i0∈seg} ⊢ F(i0)=succ(i0) — 1 hyp."""
    th = famille_successeurs_valeur()
    assert len(th.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


# ═══════════════════════════════════════════════════════════════════════════════
# LE CAS DE BASE DE LA DÉF. 2 :  0! = 1   (E III.41 L.30 → E II.32 L.22-23)
# ═══════════════════════════════════════════════════════════════════════════════
U_QCQ = var("upv")                                  # famille QUELCONQUE
SGL_MAIN = E.paire(E.VIDE, E.VIDE)                  # {∅} RECONSTRUIT à la main


def test_produit_cardinal_vide():
    """⊢ Card ∏(u,∅) = 1 — CLOS, 0 hypothèse ; cible reconstruite à la main.

    ⚠️ CETTE DOCSTRING A DIT « SOUS LES 22 AXIOMES SEULS » : c'était FAUX, et la mesure
    l'a établi (27 juil. 2026, vérificateur adverse). `Ax(D)` = 14 axiomes consommés =
    12 de `Ensembles` + **2 de la théorie dédiée « Graphe-terme »**, hérités de
    `un_egale_card_singleton`. Dette = 2, `invariant_reel` = FAUX.
    Seul `produit_famille_vide_est_singleton_vide` mérite la phrase « sous les 22 seuls »
    (Ax(D) = 7, tous dans T₀, Dette = 0 — mesuré).
    Mesurer avec `outils_ia/verite/axiomes_consommes.py`, en PREMIÈRE position d'un
    process FRAIS : au 2ᵉ appel la mémoïsation sous-compte (−62 % mesuré ailleurs).

    `produit_cardinal(u,∅)` est par définition `cardinal(produit_famille(u,∅))` :
    on l'écrit ICI sous cette forme dépliée, pour ne pas comparer le module à
    lui-même via son propre constructeur."""
    thm = produit_cardinal_vide(U_QCQ)
    attendu = egal(cardinal(E.produit_famille(U_QCQ, E.VIDE)), UN)
    assert thm.conclusion == attendu
    assert thm.hypotheses == frozenset(), "résidu non déchargé : %r" % (thm.hypotheses,)
    assert thm.est_clos
    # le DERNIER maillon, reconstruit à la main : le « 1 » est bien Card({∅}).
    assert un_egale_card_singleton().conclusion == egal(UN, cardinal(SGL_MAIN))


@pytest.mark.slow
def test_factorielle_def2_zero():
    """🎯 ⊢ 0! = 1 sur le TERME RÉEL ∏_{i<0}(i+1), SANS RÉSIDU.   [N_existe ~5 min]

    Le LHS est reconstruit à la main : `cardinal(produit_famille(famille, seg))`,
    avec le MÊME segment seg(ℕ,0) que le terme de la Déf. 2 — c'est ce raccord
    (et non ∅) qui distingue ce théorème d'un énoncé sur un produit déjà vide."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux \
        .iii_3_6_familles.ensembles_famille_successeurs import _seg_NN
    thm = factorielle_def2_zero()
    fam, seg0 = famille_successeurs(ZERO), _seg_NN(ZERO)
    attendu = egal(cardinal(E.produit_famille(fam, seg0)), UN)
    assert thm.conclusion == attendu
    assert thm.conclusion == factorielle_def2_zero_enonce()
    assert thm.conclusion.termes[0] == factorielle_def2(ZERO), "LHS ≠ le terme de la Déf. 2"
    assert thm.conclusion.termes[1] == UN
    assert thm.hypotheses == frozenset(), "résidu non déchargé : %r" % (thm.hypotheses,)
    assert thm.est_clos
    # NON VACUEUX : le segment d'indices n'est PAS écrit « ∅ » dans la Déf. 2.
    assert seg0 != E.VIDE, "le cas de base serait trivial si l'indice était déjà ∅"


@pytest.mark.slow
def test_les_mutants_de_zero_meurent():
    """MUTATION : deux mutants du 🎯, tués par les assertions du test ci-dessus.

    ⚠️ Chaque mutant est un vrai `Theoreme` du noyau, obtenu par gestes purs — un
    mutant qui mourrait sur TypeError/AttributeError serait CASSÉ et ne prouverait
    rien sur le mordant du test."""
    thm = factorielle_def2_zero()

    # (1) POLLUTION : même conclusion, hypothèse parasite empilée.
    parasite = appartient(var("ztst"), var("Atst"))
    pollue = N.modus_ponens(N.assume(parasite), N.loi_deduction(parasite, thm))
    assert isinstance(pollue, type(thm)), "mutant CASSÉ : ce n'est pas un Theoreme"
    assert pollue.conclusion == factorielle_def2_zero_enonce()      # conclusion intacte
    assert pollue.hypotheses == frozenset({parasite})
    assert pollue.hypotheses != frozenset()        # ⇒ l'assertion de frozenset le TUE
    assert not pollue.est_clos                     # ⇒ l'assertion est_clos le TUE aussi

    # (2) SUBSTITUTION : conclusion remplacée (0! = 0 au lieu de 0! = 1).
    faux = egal(factorielle_def2(ZERO), ZERO)
    substitue = N.assume(faux)
    assert isinstance(substitue, type(thm)), "mutant CASSÉ : ce n'est pas un Theoreme"
    assert substitue.conclusion != factorielle_def2_zero_enonce()   # ⇒ TUÉ
    assert substitue.conclusion.termes[1] != UN


def test_invariant_22_axiomes_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
