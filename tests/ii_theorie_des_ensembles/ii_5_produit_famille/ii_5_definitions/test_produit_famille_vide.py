# -*- coding: utf-8 -*-
"""Tests §II.5.3 — le produit d'index vide :  ∏_{ι∈∅} X_ι = {∅}.   (E II.32 L.22-23.)

MÉTHODE (imposée par l'incident du 2026-07-26 : un théorème CORRECT mais VACUEUX
avait été livré sous une hypothèse réfutable).  Ici :
  1. la conclusion attendue est RECONSTRUITE À LA MAIN, hors du module testé
     (`E.paire(∅,∅)` au lieu de `E.singleton(∅)`, etc.) — sinon on comparerait le
     module à lui-même ;
  2. les hypothèses sont assertées par ÉGALITÉ EXACTE de frozenset — `len(...) == 0`
     ne dit pas LESQUELLES ;
  3. les tests sont MUTÉS (`test_les_mutants_meurent`) pour prouver qu'ils mordent :
     pollution d'hypothèse, substitution de conclusion, α-variante de liant.  Un
     mutant SURVIVANT signerait un test décoratif.  Les mutants sont construits par
     GESTES PURS DU NOYAU (assume/loi_deduction/α-renommage), jamais fabriqués ;
  4. `theorie_ensembles()` vaut 22 avant ET après.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, non, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille_vide import (
    produit_famille_vide_enonce, produit_famille_vide_est_singleton_vide,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille_graphe import (
    singleton_vide_hors_produit_vide,
)

U = var("upv")                                    # famille QUELCONQUE
SGL_MAIN = E.paire(E.VIDE, E.VIDE)                # {∅} RECONSTRUIT à la main
PROD_MAIN = E.produit_famille(U, E.VIDE)          # ∏_{ι∈∅} X_ι reconstruit à la main
CIBLE_MAIN = egal(PROD_MAIN, SGL_MAIN)            # la conclusion attendue, à la main


def _inclusion(liant, a, b):
    """(∀<liant>)(<liant> ∈ A ⇒ <liant> ∈ B)  — l'inclusion, à la main, liant EXPLICITE."""
    return pourtout(liant, impl(appartient(var(liant), a), appartient(var(liant), b)))


def test_invariant_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_la_cible_reconstruite_coincide():
    """Le témoin {∅} et la cible sont bien ceux du module (contrôle du contrôle)."""
    assert SGL_MAIN == E.singleton(E.VIDE)
    assert CIBLE_MAIN == produit_famille_vide_enonce(U)


def test_produit_famille_vide_est_singleton_vide():
    """🎯 ⊢ ∏(u,∅) = {∅} SOUS LES 22 AXIOMES SEULS — E II.32, sans résidu.

    Jusqu'au 2026-07-26 ce sens était indémontrable : `AXIOME_PRODUIT_FAM` avait
    perdu son conjoint de tête, et « tout élément du produit est un graphe » devait
    être supposé — hypothèse alors RÉFUTABLE, donc théorème vacueux.  L'assertion
    qui compte ici est `hypotheses == frozenset()`."""
    thm = produit_famille_vide_est_singleton_vide(U)
    assert thm.conclusion == CIBLE_MAIN
    assert thm.hypotheses == frozenset(), \
        "résidu non déchargé : %r" % (thm.hypotheses,)
    assert thm.est_clos


def test_pas_de_confusion_singleton_fonction_vide():
    """LE PIÈGE DE LECTURE, mesuré : {∅} = ∏(u,∅) ET ¬({∅} ∈ ∏(u,∅)) coexistent.

    L'élément du produit est ∅ (la FONCTION VIDE), pas {∅} (le SINGLETON).  Les
    deux théorèmes donnent ensemble ¬({∅} ∈ {∅}) — vrai, et nullement absurde.
    Ce test verrouille que la réparation n'a PAS rendu la théorie incohérente sur
    ce point précis : on VÉRIFIE que la composée conclut ¬({∅}∈{∅}), pas ∅∈∅."""
    eq = produit_famille_vide_est_singleton_vide(U)          # ∏(u,∅) = {∅}
    hors = singleton_vide_hors_produit_vide(U)              # ¬({∅} ∈ ∏(u,∅))
    assert eq.est_clos and hors.est_clos
    leib = N.s6(PROD_MAIN, SGL_MAIN, "wtst",
                non(appartient(SGL_MAIN, var("wtst"))))
    compose = N.modus_ponens(hors, equivalence_avant(N.modus_ponens(eq, leib)))
    assert compose.conclusion == non(appartient(SGL_MAIN, SGL_MAIN))
    assert compose.est_clos
    # et ce n'est PAS une absurdité : la conclusion n'est pas « ∅ ∈ ∅ ».
    assert compose.conclusion != appartient(E.VIDE, E.VIDE)


def test_les_mutants_meurent():
    """MUTATION du test : trois mutants, tous tués — sinon le test est décoratif.

    ⚠️ Un mutant qui mourrait sur TypeError serait un mutant CASSÉ : chaque mutant
    est ici un vrai `Theoreme` du noyau, construit par gestes purs, et c'est bien
    l'ASSERTION du test qui le tue."""
    thm = produit_famille_vide_est_singleton_vide(U)

    # (1) POLLUTION : même conclusion, une hypothèse parasite empilée.
    parasite = appartient(var("ztst"), var("Atst"))
    pollue = N.modus_ponens(N.assume(parasite),
                            N.loi_deduction(parasite, thm))
    assert isinstance(pollue, type(thm))
    assert pollue.conclusion == CIBLE_MAIN            # la conclusion, elle, survit
    assert pollue.hypotheses == frozenset({parasite})
    assert not pollue.est_clos
    assert pollue.hypotheses != frozenset()           # ⇒ l'assertion du 🎯 le TUE

    # (2) SUBSTITUTION : conclusion remplacée (∏(u,∅) = ∅ au lieu de = {∅}).
    faux = egal(PROD_MAIN, E.VIDE)
    substitue = N.assume(faux)
    assert substitue.conclusion != CIBLE_MAIN         # ⇒ l'assertion de conclusion le TUE
    assert substitue.conclusion == faux

    # (3) α-VARIANTE : le liant des deux inclusions renommé « z » → « ytst ».
    #     A1 écrit ses inclusions au liant « z » ; le noyau N'IDENTIFIE PAS les
    #     α-variantes, donc l'α-conversion faite dans le module est LOAD-BEARING.
    #     Le mutant est un vrai Theoreme (assume), et c'est le NOYAU qui le tue.
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), PROD_MAIN), SGL_MAIN)
    bon = conjonction_intro(N.assume(_inclusion("z", PROD_MAIN, SGL_MAIN)),
                            N.assume(_inclusion("z", SGL_MAIN, PROD_MAIN)))
    assert N.modus_ponens(bon, a1).conclusion == CIBLE_MAIN      # le témoin sain passe
    mutant = conjonction_intro(N.assume(_inclusion("ytst", PROD_MAIN, SGL_MAIN)),
                               N.assume(_inclusion("ytst", SGL_MAIN, PROD_MAIN)))
    assert isinstance(mutant, type(thm)), "mutant CASSÉ : ce n'est pas un Theoreme"
    with pytest.raises(ValueError) as capture:
        N.modus_ponens(mutant, a1)                               # ⇒ le NOYAU le TUE
    assert "modus ponens" in str(capture.value), \
        "mutant tué par la mauvaise cause (mutant cassé ?) : %s" % capture.value


def test_invariant_22_axiomes_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
