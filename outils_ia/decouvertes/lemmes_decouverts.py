#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CATALOGUE de LEMMES auto-decouverts — AUTO-GENERE par promouvoir_decouvertes.py.

Chaque lemme est une DECOUVERTE du conjectureur (chainage de deux theoremes du corpus par
transitivite), promue en fonction NOMMEE dont la preuve est RE-DERIVEE au noyau a l'appel
(aucun Theoreme force ; frontiere 22 axiomes intacte). VRAIS et certifies, mais HORS de la
table des matieres de Bourbaki (ce ne sont pas des resultats du livre). Ne pas editer a la main.
"""
from __future__ import annotations
import importlib, sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(_V9 / "outils_ia" / "corpus"))
from conjecturer import _comme_impl, _match
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, libres_f


def lemme_0():
    """(∃e e∈Y ⇒ ¬∃z ¬(z∈image(reciproque(produit(X,Y)),Z) ⇒ z∈X))

    Auto-decouvert (transitivite) : pr1_produit o image_reciproque_inclus_domaine. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_projection_produit'), 'pr1_produit')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_reciproque_inclus_domaine')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_1():
    """(dom(f)=E ⇒ ¬∃z ¬(z∈image(G,image(reciproque(f),Z)) ⇒ z∈image(G,E)))

    Auto-decouvert (transitivite) : image_reciproque_inclus_domaine o image_croissante. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_reciproque_inclus_domaine')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_2():
    """(¬∃z ¬(z∈X ⇒ z∈Y) ⇒ ¬∃z ¬(z∈image(G,X) ⇒ z∈image(G,image(reciproque(G),image(G,X)))))

    Auto-decouvert (transitivite) : image_croissante o image_image_reciproque_contient_si_surjective. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_image_reciproque_contient_si_surjective')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_3():
    """(dom(f)=E ⇒ image(reciproque(graphe_terme(produit(E,F),τi1(…))),image(reciproque(f),Z))=produit(image(reciproque(f),Z),F))

    Auto-decouvert (transitivite) : image_reciproque_inclus_domaine o pr1_reciproque_produit. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_reciproque_inclus_domaine')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_projection_reciproque_produit'), 'pr1_reciproque_produit')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_4():
    """(¬∃z ¬(z∈X ⇒ z∈Y) ⇒ image(reciproque(graphe_terme(produit(image(G,Y),F),τi1(…))),image(G,X))=produit(image(G,X),F))

    Auto-decouvert (transitivite) : image_croissante o pr1_reciproque_produit. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_projection_reciproque_produit'), 'pr1_reciproque_produit')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_5():
    """(∃e e∈Y ⇒ ¬∃x ¬(x∈dom(dom(produit(X,Y))) ⇒ τy(…)=τy(…)))

    Auto-decouvert (transitivite) : pr1_produit o coincidence_meme_graphe. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_projection_produit'), 'pr1_produit')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'coincidence_meme_graphe')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_6():
    """(∃e e∈X ⇒ ¬∃x ¬(x∈dom(img(produit(X,Y))) ⇒ τy(…)=τy(…)))

    Auto-decouvert (transitivite) : pr2_produit o coincidence_meme_graphe. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_projection_produit'), 'pr2_produit')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'coincidence_meme_graphe')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_7():
    """(¬(¬∃z ¬(z∈F ⇒ z∈G) ⇒ ¬¬∃z ¬(z∈G ⇒ z∈H)) ⇒ ¬∃z ¬(z∈image(G,F) ⇒ z∈image(G,H)))

    Auto-decouvert (transitivite) : prolongement_transitif o image_croissante. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'prolongement_transitif')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_8():
    """(¬∃k ¬(k∈K ⇒ τy(…)∈I) ⇒ ¬∃z ¬(z∈image(G,reunion_fam(fam_reparam(X,phi),K)) ⇒ z∈image(G,reunion_fam(X,I))))

    Auto-decouvert (transitivite) : reparam_reunion_incluse o image_croissante. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ensembles_chap2_props_restantes'), 'reparam_reunion_incluse')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_9():
    """(¬(¬∃z ¬(z∈Ap ⇒ z∈A) ⇒ ¬¬∃z ¬(z∈Bp ⇒ z∈B)) ⇒ ¬∃z ¬(z∈image(G,produit(Ap,Bp)) ⇒ z∈image(G,produit(A,B))))

    Auto-decouvert (transitivite) : produit_inclusion_facile o image_croissante. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit'), 'produit_inclusion_facile')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_10():
    """(¬∃x ¬(x∈X ⇒ paire(paire(x,x),paire(x,τy(…)))∈f) ⇒ ¬∃z ¬(z∈image(G,X) ⇒ z∈image(G,image(reciproque(f),image(f,X)))))

    Auto-decouvert (transitivite) : inclus_image_reciproque_image o image_croissante. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'inclus_image_reciproque_image')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_11():
    """(¬(¬∃z ¬(z∈F ⇒ z∈G) ⇒ ¬¬∃z ¬(z∈G ⇒ z∈H)) ⇒ image(reciproque(graphe_terme(produit(H,F),τi1(…))),F)=produit(F,F))

    Auto-decouvert (transitivite) : prolongement_transitif o pr1_reciproque_produit. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'prolongement_transitif')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_projection_reciproque_produit'), 'pr1_reciproque_produit')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_12():
    """(¬∃u ¬¬∃v ¬¬∃z ¬(¬(paire(paire(v,v),paire(v,u))∈F ⇒ ¬paire(paire(z,z),paire(z,u))∈F) ⇒ v=z) ⇒ ¬∃z ¬(z∈image(reciproque(F),image(F,X)) ⇒ z∈X))

    Auto-decouvert (transitivite) : injectif_implique_reciproque_fonctionnel o image_reciproque_image_inclus_si_injective. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_prop7_9_ii3'), 'injectif_implique_reciproque_fonctionnel')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_reciproque_image_inclus_si_injective')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_13():
    """(¬(¬∃z ¬(z∈Ap ⇒ z∈A) ⇒ ¬¬∃z ¬(z∈Bp ⇒ z∈B)) ⇒ image(reciproque(graphe_terme(produit(produit(A,B),F),τi1(…))),produit(Ap,Bp))=produit(produit(Ap,Bp),F))

    Auto-decouvert (transitivite) : produit_inclusion_facile o pr1_reciproque_produit. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit'), 'produit_inclusion_facile')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_projection_reciproque_produit'), 'pr1_reciproque_produit')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_14():
    """(¬∃u ¬¬∃v ¬¬∃z ¬(¬(paire(paire(v,v),paire(v,u))∈F ⇒ ¬paire(paire(z,z),paire(z,u))∈F) ⇒ v=z) ⇒ ¬∃z ¬(z∈image(reciproque(F),image(reciproque(reciproque(F)),Y)) ⇒ z∈Y))

    Auto-decouvert (transitivite) : injectif_implique_reciproque_fonctionnel o image_image_reciproque_inclus. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_prop7_9_ii3'), 'injectif_implique_reciproque_fonctionnel')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_image_reciproque_inclus')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_15():
    """(¬∃u ¬¬∃v ¬¬∃z ¬(¬(paire(paire(u,u),paire(u,v))∈f ⇒ ¬paire(paire(u,u),paire(u,z))∈f) ⇒ v=z) ⇒ ¬∃z ¬(z∈image(G,image(f,image(reciproque(f),Y))) ⇒ z∈image(G,Y)))

    Auto-decouvert (transitivite) : image_image_reciproque_inclus o image_croissante. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_image_reciproque_inclus')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances'), 'image_croissante')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_16():
    """(¬(¬∃z ¬(z∈a ⇒ z∈b) ⇒ ¬¬∃z ¬(z∈b ⇒ z∈a)) ⇒ ¬∃x ¬(x∈dom(a) ⇒ τy(…)=τy(…)))

    Auto-decouvert (transitivite) : extensionnalite_appliquee o coincidence_meme_graphe. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes'), 'extensionnalite_appliquee')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'coincidence_meme_graphe')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_17():
    """(¬(x=xp ⇒ ¬y=yp) ⇒ ¬∃@0 ¬(@0∈dom(paire(paire(x,x),paire(x,y))) ⇒ τ@1(…)=τ@1(…)))

    Auto-decouvert (transitivite) : couple_egal_si_composantes o coincidence_meme_graphe. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes'), 'couple_egal_si_composantes')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'coincidence_meme_graphe')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_18():
    """(¬∃u ¬¬∃v ¬¬∃z ¬(¬(paire(paire(v,v),paire(v,u))∈F ⇒ ¬paire(paire(z,z),paire(z,u))∈F) ⇒ v=z) ⇒ (¬∃z ¬(z∈Z ⇒ z∈image(reciproque(F),E)) ⇒ image(reciproque(F),image(reciproque(reciproque(F)),Z))=Z))

    Auto-decouvert (transitivite) : injectif_implique_reciproque_fonctionnel o image_image_reciproque_egal_si_surjective. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_prop7_9_ii3'), 'injectif_implique_reciproque_fonctionnel')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_image_reciproque_props'), 'image_image_reciproque_egal_si_surjective')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


def lemme_19():
    """(¬∃z ¬(z∈X ⇒ z∈E) ⇒ ¬∃x ¬(x∈dom(image(reciproque(graphe_terme(produit(E,F),τi1(…))),X)) ⇒ τy(…)=τy(…)))

    Auto-decouvert (transitivite) : pr1_reciproque_produit o coincidence_meme_graphe. Preuve RE-DERIVEE au noyau (clos, 22 axiomes).
    """
    T1 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_projection_reciproque_produit'), 'pr1_reciproque_produit')()
    T2 = getattr(importlib.import_module('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions'), 'coincidence_meme_graphe')()
    A, B = _comme_impl(T1.conclusion)
    s = {}
    _match(_comme_impl(T2.conclusion)[0], B, s, libres_f(T2.conclusion))
    for v, t in s.items():
        if t != var(v):
            T2 = instancie(N.generalisation(v, T2), t)
    return N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2))


IDS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

_CIBLES = {
    0: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='e', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='e', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))),)), Terme('var', nom='Z', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),))))",
    1: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('=', lieur='', termes=(Terme('app', nom='dom', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('var', nom='E', lieur='', args=())), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('var', nom='Z', lieur='', args=())))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='E', lieur='', args=())))), sous=()))),)),)),))))",
    2: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='X', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='G', lieur='', args=()),)), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='X', lieur='', args=())))))))), sous=()))),)),)),))))",
    3: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('=', lieur='', termes=(Terme('app', nom='dom', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('var', nom='E', lieur='', args=())), sous=()),)), Formule('=', lieur='', termes=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='graphe_terme', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='F', lieur='', args=()))), Terme('tau', nom='', lieur='i1', args=(Formule('exists', lieur='j1', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='i1', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='j1', lieur='', args=())))))), sous=()),)),)))),)), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('var', nom='Z', lieur='', args=()))))), Terme('app', nom='produit', lieur='', args=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('var', nom='Z', lieur='', args=()))), Terme('var', nom='F', lieur='', args=())))), sous=())))",
    4: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()))),)),)),)),)), Formule('=', lieur='', termes=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='graphe_terme', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))), Terme('var', nom='F', lieur='', args=()))), Terme('tau', nom='', lieur='i1', args=(Formule('exists', lieur='j1', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='i1', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='j1', lieur='', args=())))))), sous=()),)),)))),)), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='X', lieur='', args=()))))), Terme('app', nom='produit', lieur='', args=(Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='X', lieur='', args=()))), Terme('var', nom='F', lieur='', args=())))), sous=())))",
    5: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='e', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='e', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='x', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('app', nom='dom', lieur='', args=(Terme('app', nom='dom', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))),)),))), sous=()),)), Formule('=', lieur='', termes=(Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='dom', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))),))), sous=()),)), Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('var', nom='X', lieur='', args=())), sous=()),))), sous=()))),)),)),))))",
    6: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='e', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='e', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='x', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('app', nom='dom', lieur='', args=(Terme('app', nom='img', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))),)),))), sous=()),)), Formule('=', lieur='', termes=(Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='img', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))),))), sous=()),)), Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('var', nom='Y', lieur='', args=())), sous=()),))), sous=()))),)),)),))))",
    7: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='F', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='G', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='G', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='H', lieur='', args=())), sous=()))),)),)),)),)))),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='F', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='H', lieur='', args=())))), sous=()))),)),)),))))",
    8: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='k', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('var', nom='K', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='k', lieur='', args=()), Terme('var', nom='k', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='k', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('var', nom='phi', lieur='', args=())), sous=()),)), Terme('var', nom='I', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='reunion_fam', lieur='', args=(Terme('app', nom='fam_reparam', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='phi', lieur='', args=()))), Terme('var', nom='K', lieur='', args=())))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='reunion_fam', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='I', lieur='', args=())))))), sous=()))),)),)),))))",
    9: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Ap', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Bp', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='B', lieur='', args=())), sous=()))),)),)),)),)))),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='Ap', lieur='', args=()), Terme('var', nom='Bp', lieur='', args=())))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=())))))), sous=()))),)),)),))))",
    10: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='x', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('var', nom='f', lieur='', args=())), sous=()),)))))), Terme('var', nom='f', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='X', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('app', nom='image', lieur='', args=(Terme('var', nom='f', lieur='', args=()), Terme('var', nom='X', lieur='', args=())))))))), sous=()))),)),)),))))",
    11: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='F', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='G', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='G', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='H', lieur='', args=())), sous=()))),)),)),)),)))),)),)), Formule('=', lieur='', termes=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='graphe_terme', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='H', lieur='', args=()), Terme('var', nom='F', lieur='', args=()))), Terme('tau', nom='', lieur='i1', args=(Formule('exists', lieur='j1', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='i1', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='j1', lieur='', args=())))))), sous=()),)),)))),)), Terme('var', nom='F', lieur='', args=()))), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='F', lieur='', args=()), Terme('var', nom='F', lieur='', args=())))), sous=())))",
    12: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='u', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='v', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))))), Terme('var', nom='F', lieur='', args=())), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='z', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))))), Terme('var', nom='F', lieur='', args=())), sous=()),)))),)),)), Formule('=', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='z', lieur='', args=())), sous=()))),)),)),)),)),)),)),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='F', lieur='', args=()),)), Terme('app', nom='image', lieur='', args=(Terme('var', nom='F', lieur='', args=()), Terme('var', nom='X', lieur='', args=())))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),))))",
    13: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Ap', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Bp', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='B', lieur='', args=())), sous=()))),)),)),)),)))),)),)), Formule('=', lieur='', termes=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='graphe_terme', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='F', lieur='', args=()))), Terme('tau', nom='', lieur='i1', args=(Formule('exists', lieur='j1', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='i1', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='j1', lieur='', args=())))))), sous=()),)),)))),)), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='Ap', lieur='', args=()), Terme('var', nom='Bp', lieur='', args=()))))), Terme('app', nom='produit', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='Ap', lieur='', args=()), Terme('var', nom='Bp', lieur='', args=()))), Terme('var', nom='F', lieur='', args=())))), sous=())))",
    14: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='u', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='v', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))))), Terme('var', nom='F', lieur='', args=())), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='z', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))))), Terme('var', nom='F', lieur='', args=())), sous=()),)))),)),)), Formule('=', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='z', lieur='', args=())), sous=()))),)),)),)),)),)),)),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='F', lieur='', args=()),)), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='F', lieur='', args=()),)),)), Terme('var', nom='Y', lieur='', args=())))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()))),)),)),))))",
    15: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='u', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='v', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))))), Terme('var', nom='f', lieur='', args=())), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='z', lieur='', args=()))))), Terme('var', nom='f', lieur='', args=())), sous=()),)))),)),)), Formule('=', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='z', lieur='', args=())), sous=()))),)),)),)),)),)),)),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='f', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='f', lieur='', args=()),)), Terme('var', nom='Y', lieur='', args=())))))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())))), sous=()))),)),)),))))",
    16: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='a', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='b', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='b', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='a', lieur='', args=())), sous=()))),)),)),)),)))),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='x', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('app', nom='dom', lieur='', args=(Terme('var', nom='a', lieur='', args=()),))), sous=()),)), Formule('=', lieur='', termes=(Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('var', nom='a', lieur='', args=())), sous=()),)), Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('var', nom='b', lieur='', args=())), sous=()),))), sous=()))),)),)),))))",
    # 17 RE-CALE 8 aout 2026 : derive alpha (@n) du fix subst 24 juil — le
    #    lemme se re-certifie CLOS ; seul le nom des lieurs canoniques change.
    17: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='xp', lieur='', args=())), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='y', lieur='', args=()), Terme('var', nom='yp', lieur='', args=())), sous=()),)))),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='@0', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='@0', lieur='', args=()), Terme('app', nom='dom', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))),))), sous=()),)), Formule('=', lieur='', termes=(Terme('tau', nom='', lieur='@1', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='@0', lieur='', args=()), Terme('var', nom='@0', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='@0', lieur='', args=()), Terme('var', nom='@1', lieur='', args=()))))), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=())))))), sous=()),)), Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='@0', lieur='', args=()), Terme('var', nom='@0', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='@0', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='xp', lieur='', args=()), Terme('var', nom='xp', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='xp', lieur='', args=()), Terme('var', nom='yp', lieur='', args=())))))), sous=()),))), sous=()))),)),)),))))",
    18: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='u', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='v', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))))), Terme('var', nom='F', lieur='', args=())), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='z', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))))), Terme('var', nom='F', lieur='', args=())), sous=()),)))),)),)), Formule('=', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='z', lieur='', args=())), sous=()))),)),)),)),)),)),)),)),)),)),)), Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='Z', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='F', lieur='', args=()),)), Terme('var', nom='E', lieur='', args=())))), sous=()))),)),)),)),)), Formule('=', lieur='', termes=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='F', lieur='', args=()),)), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('var', nom='F', lieur='', args=()),)),)), Terme('var', nom='Z', lieur='', args=()))))), Terme('var', nom='Z', lieur='', args=())), sous=())))))",
    19: "Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='E', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='x', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('app', nom='dom', lieur='', args=(Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='graphe_terme', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='F', lieur='', args=()))), Terme('tau', nom='', lieur='i1', args=(Formule('exists', lieur='j1', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='i1', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='j1', lieur='', args=())))))), sous=()),)),)))),)), Terme('var', nom='X', lieur='', args=()))),))), sous=()),)), Formule('=', lieur='', termes=(Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='image', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='graphe_terme', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='F', lieur='', args=()))), Terme('tau', nom='', lieur='i1', args=(Formule('exists', lieur='j1', termes=(), sous=(Formule('=', lieur='', termes=(Terme('var', nom='k', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='i1', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='i1', lieur='', args=()), Terme('var', nom='j1', lieur='', args=())))))), sous=()),)),)))),)), Terme('var', nom='X', lieur='', args=())))), sous=()),)), Terme('tau', nom='', lieur='y', args=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='F', lieur='', args=())))), sous=()),))), sous=()))),)),)),))))",
}

