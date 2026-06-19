"""Tests §III.5 — Prop. 6, socle « bien ordonné »
(ensembles_prop6_bien_ordonne_iii5).

  • partie_finie_est_finie          — (X⊂E et E fini) ⇒ X fini          (CLOS) ;
  • clause_plus_petit_fini_total    — (tot et E fini) ⇒ clause plus-petit (CLOS) ;
  • fini_total_est_bien_ordonne     — (ordre et tot et E fini) ⇒ bien-ordonné (CLOS).

Le facteur ORDRE de est_bien_ordonne_graphe est pris en HYPOTHÈSE explicite
(est_relation_ordre_dans(R_G,E)), non dérivable de totalement_ordonne seul (pas
de G⊂E×E) ; la clause SUBSTANTIELLE « plus petit » est, elle, INCONDITIONNELLE.
"""
import pytest

from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.entiers.ensembles_prop6_bien_ordonne_iii5 import (
    partie_finie_est_finie, partie_finie_est_finie_enonce,
    clause_plus_petit_fini_total, _petit_clause,
    fini_total_est_bien_ordonne, fini_total_est_bien_ordonne_enonce,
)


def test_partie_finie_est_finie_close():
    t = partie_finie_est_finie("Xpf", "Epf")
    assert t.est_clos
    assert t.conclusion == partie_finie_est_finie_enonce("Xpf", "Epf")
    assert len(theorie_ensembles().axiomes) == 22


def test_clause_plus_petit_close():
    from bourbaki.logique.formule import et, impl
    from bourbaki.ordre.ensembles_ordre_relation import totalement_ordonne
    from bourbaki.entiers.ensembles_entiers import est_fini_ensemble
    from bourbaki.logique.formule import var
    t = clause_plus_petit_fini_total("Gbo", "Ebo")
    assert t.est_clos
    hyp = et(totalement_ordonne("Gbo", "Ebo"), est_fini_ensemble(var("Ebo")))
    assert t.conclusion == impl(hyp, _petit_clause("Gbo", "Ebo"))
    assert len(theorie_ensembles().axiomes) == 22


def test_fini_total_est_bien_ordonne_close():
    t = fini_total_est_bien_ordonne("Gbo", "Ebo")
    assert t.est_clos
    assert t.conclusion == fini_total_est_bien_ordonne_enonce("Gbo", "Ebo")
    assert len(theorie_ensembles().axiomes) == 22


def test_non_vacuous():
    # la conclusion n'est PAS une hypothèse (pas P⇒P) : la clause plus-petit est
    # un vrai contenu, distincte du facteur ordre pris en hyp.
    t = fini_total_est_bien_ordonne("Gbo", "Ebo")
    assert t.conclusion not in t.hypotheses
