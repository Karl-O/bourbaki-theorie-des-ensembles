# -*- coding: utf-8 -*-
"""§III.3.5 Prop.12, brique (iv) — LA BIJECTION χ : P(A) → F(A;2).

Design (DECISIONS 21 août 22h40) : B := graphe_terme(parties(A), chi_appli(x,A))
— le graphe de Y ↦ ((χ_Y, A), 2). Sous-lemmes (un commit testé chacun) :
  (a) B fonctionnel + dom B = parties(A)   [C54, ce fichier, en cours]
  (b) B injectif   [couple_egal_implique_composantes ×2 + rho_chi_identite]
  (c) image B = F(A;2)   [chi_dans_applications ; chi_rho_identite]
  (d) est_bijection_de(B, P(A), F(A;2)) puis Eq par S5.
X := a cardinal dès le départ — F(a;2) est LITTÉRALEMENT le support de 2^a
(exposant_cardinal_binaire, Déf. 4) : la brique (v) sera Prop.1 directe.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_fin import (
    chi_appli)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def bijection_graphe(a="Abij"):
    """B := graphe_terme(parties(A), chi_appli(x, A)) — le graphe de Y ↦ χ-triple."""
    vA = _t(a)
    return E.graphe_terme(E.parties(vA), chi_appli(var("x"), vA))


# Sous-lemme (a) : B fonctionnel, dom B = parties(A).
def bijection_fonctionnel(a="Abij"):
    """⊢ B fonctionnel.   (C54 : un graphe-de-terme est fonctionnel.)"""
    vA = _t(a)
    return graphe_terme_fonctionnel(E.parties(vA), chi_appli(var("x"), vA))


def bijection_domaine(a="Abij"):
    """⊢ dom B = parties(A).   (C54 : le domaine d'un graphe-de-terme est A.)"""
    vA = _t(a)
    return graphe_terme_domaine(E.parties(vA), chi_appli(var("x"), vA))


__all__ = ["bijection_graphe", "bijection_fonctionnel", "bijection_domaine"]
