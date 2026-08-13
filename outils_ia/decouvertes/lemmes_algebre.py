#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CATALOGUE de LEMMES ALGÉBRIQUES auto-découverts — AUTO-GÉNÉRÉ par promouvoir_algebre.py.

Chaque lemme est une découverte des régimes =, ⊂ ou ⇔ (chaînage de deux théorèmes du corpus,
éventuellement via le pont S6 égalité→inclusions), re-DÉRIVÉE au noyau à l'appel. Aucun
Theoreme forgé ; frontière 22 axiomes. Vrais mais HORS table des matières de Bourbaki.
Ne pas éditer à la main.
"""
from __future__ import annotations
import importlib, sys
from pathlib import Path
_V9 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_V9))
sys.path.insert(0, str(_V9 / "outils_ia" / "corpus"))
from conjecturer import (_comme_egal, _comme_equiv, _comme_inclus, _match, _instancier,
                         egal_vers_inclusions, _composer_inclusions)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, libres_f


def _theoreme(mf):
    mod, func = mf.rsplit(".", 1)
    return getattr(importlib.import_module(mod), func)()


def _sources(spec):
    kind, mf = spec
    if kind == "c":
        return [_theoreme(mf)]
    return list(egal_vers_inclusions(_theoreme(mf)))       # pont S6 : les 2 sens


def _sigma(T2, milieu, detecteur):
    s = {}
    _match(detecteur(T2.conclusion)[0], milieu, s, libres_f(T2.conclusion))
    return _instancier(T2, {v: t for v, t in s.items() if t != var(v)})


def _egal(m1, m2, attendu):
    T1 = _theoreme(m1)
    _, b = _comme_egal(T1.conclusion)
    t = composer_egalites(T1, _sigma(_theoreme(m2), b, _comme_egal))
    assert t.est_clos and repr(t.conclusion) == attendu
    return t


def _incl(s1, s2, attendu):
    for T1 in _sources(s1):
        r1 = _comme_inclus(T1.conclusion)
        if not r1:
            continue
        for T2x in _sources(s2):
            try:
                T2 = _sigma(T2x, r1[1], _comme_inclus)
                r2 = _comme_inclus(T2.conclusion)
                tac, _ = _composer_inclusions(T1, T2, r1[0], r1[1], r2[1])
            except Exception:
                continue
            if tac.est_clos and repr(tac.conclusion) == attendu:
                return tac
    raise AssertionError("re-dérivation inclusion échouée")


def _equiv(m1, m2, attendu):
    T1 = _theoreme(m1)
    A, B = _comme_equiv(T1.conclusion)
    T2 = _sigma(_theoreme(m2), B, _comme_equiv)
    Cp = _comme_equiv(T2.conclusion)[1]
    fwd = N.loi_deduction(A, N.modus_ponens(
        N.modus_ponens(N.assume(A), equivalence_avant(T1)), equivalence_avant(T2)))
    bwd = N.loi_deduction(Cp, N.modus_ponens(
        N.modus_ponens(N.assume(Cp), equivalence_arriere(T2)), equivalence_arriere(T1)))
    t = conjonction_intro(fwd, bwd)
    assert t.est_clos and repr(t.conclusion) == attendu
    return t


def lemme_alg_0():
    """[egal] reunion(reunion(A,B),C)=reunion(reunion(B,C),A)

    Auto-découvert : associativite_reunion ∘ commutativite_reunion. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne.associativite_reunion', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_reunion', _CIBLES[0])


def lemme_alg_1():
    """[egal] inter(inter(A,B),C)=inter(inter(B,C),A)

    Auto-découvert : associativite_intersection ∘ commutativite_intersection. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne.associativite_intersection', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_intersection', _CIBLES[1])


def lemme_alg_2():
    """[egal] difference(E,reunion(A,B))=difference(inter(difference(E,A),E),B)

    Auto-découvert : de_morgan_reunion ∘ intersection_difference_associe. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_difference.de_morgan_reunion', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_difference_identites.intersection_difference_associe', _CIBLES[2])


def lemme_alg_3():
    """[egal] difference(E,reunion(A,B))=inter(difference(E,B),difference(E,A))

    Auto-découvert : de_morgan_reunion ∘ commutativite_intersection. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_difference.de_morgan_reunion', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_intersection', _CIBLES[3])


def lemme_alg_4():
    """[egal] difference(E,inter(A,B))=reunion(difference(E,B),difference(E,A))

    Auto-découvert : de_morgan_inter ∘ commutativite_reunion. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_difference.de_morgan_inter', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_reunion', _CIBLES[4])


def lemme_alg_5():
    """[egal] inter(inter(A,B),C)=inter(inter(A,B),inter(A,C))

    Auto-découvert : associativite_intersection ∘ trace_intersection. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne.associativite_intersection', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_trace.trace_intersection', _CIBLES[5])


def lemme_alg_6():
    """[egal] inter(A,reunion(B,C))=reunion(inter(A,C),inter(A,B))

    Auto-découvert : distributivite_intersection_reunion ∘ commutativite_reunion. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne.distributivite_intersection_reunion', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_reunion', _CIBLES[6])


def lemme_alg_7():
    """[egal] reunion(A,inter(B,C))=inter(reunion(A,C),reunion(A,B))

    Auto-découvert : distributivite_reunion_intersection ∘ commutativite_intersection. Re-dérivé au noyau (clos, 22 ax.)."""
    return _egal('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne.distributivite_reunion_intersection', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_intersection', _CIBLES[7])


def lemme_alg_8():
    """[equiv] ¬((x∈X ⇒ reunion(paire(x,x),X)=X) ⇒ ¬(reunion(paire(x,x),X)=X ⇒ x∈X))

    Auto-découvert : appartient_singleton_inclus ∘ inclusion_ssi_reunion_egale. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.appartient_singleton_inclus', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_inclusion_treillis.inclusion_ssi_reunion_egale', _CIBLES[8])


def lemme_alg_9():
    """[equiv] ¬((x∈X ⇒ inter(paire(x,x),X)=paire(x,x)) ⇒ ¬(inter(paire(x,x),X)=paire(x,x) ⇒ x∈X))

    Auto-découvert : appartient_singleton_inclus ∘ inclusion_ssi_intersection_egale. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.appartient_singleton_inclus', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_inclusion_treillis.inclusion_ssi_intersection_egale', _CIBLES[9])


def lemme_alg_10():
    """[equiv] ¬((¬∃z ¬(z∈X ⇒ z∈vide()) ⇒ ¬∃@0 ¬(X∈@0 ⇒ vide()∈@0)) ⇒ ¬(¬∃@0 ¬(X∈@0 ⇒ vide()∈@0) ⇒ ¬∃z ¬(z∈X ⇒ z∈vide())))

    Auto-découvert : sous_ensemble_vide_ssi_egal ∘ egalite_leibniz_parties. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide.sous_ensemble_vide_ssi_egal', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_egalite_leibniz.egalite_leibniz_parties', _CIBLES[10])


def lemme_alg_11():
    """[equiv] ¬((¬∃z ¬(z∈A ⇒ z∈B) ⇒ ¬∃X ¬(inter(A,B)∈X ⇒ A∈X)) ⇒ ¬(¬∃X ¬(inter(A,B)∈X ⇒ A∈X) ⇒ ¬∃z ¬(z∈A ⇒ z∈B)))

    Auto-découvert : inclusion_ssi_intersection_egale ∘ egalite_leibniz_parties. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_inclusion_treillis.inclusion_ssi_intersection_egale', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_egalite_leibniz.egalite_leibniz_parties', _CIBLES[11])


def lemme_alg_12():
    """[equiv] ¬((¬∃z ¬(z∈A ⇒ z∈B) ⇒ ¬∃X ¬(reunion(A,B)∈X ⇒ B∈X)) ⇒ ¬(¬∃X ¬(reunion(A,B)∈X ⇒ B∈X) ⇒ ¬∃z ¬(z∈A ⇒ z∈B)))

    Auto-découvert : inclusion_ssi_reunion_egale ∘ egalite_leibniz_parties. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_inclusion_treillis.inclusion_ssi_reunion_egale', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_egalite_leibniz.egalite_leibniz_parties', _CIBLES[12])


def lemme_alg_13():
    """[equiv] ¬((paire(paire(u,u),paire(u,v))∈reunion(produit(X,Y),produit(Xp,Y)) ⇒ ¬(u∈reunion(X,Xp) ⇒ ¬v∈Y)) ⇒ ¬(¬(u∈reunion(X,Xp) ⇒ ¬v∈Y) ⇒ paire(paire(u,u),paire(u,v))∈reunion(produit(X,Y...

    Auto-découvert : couple_dans_produit_distrib_reunion_premier_facteur ∘ couple_dans_produit_ssi. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_distrib_reunion_gauche.couple_dans_produit_distrib_reunion_premier_facteur', 'bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit.couple_dans_produit_ssi', _CIBLES[13])


def lemme_alg_14():
    """[equiv] ¬((paire(paire(u,u),paire(u,v))∈inter(produit(A,B),produit(C,D)) ⇒ ¬(u∈inter(A,C) ⇒ ¬v∈inter(B,D))) ⇒ ¬(¬(u∈inter(A,C) ⇒ ¬v∈inter(B,D)) ⇒ paire(paire(u,u),paire(u,v))∈inter(prod...

    Auto-découvert : couple_dans_intersection_produits ∘ couple_dans_produit_ssi. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit_distributif.couple_dans_intersection_produits', 'bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit.couple_dans_produit_ssi', _CIBLES[14])


def lemme_alg_15():
    """[equiv] ¬((y∈image(G,paire(a,a)) ⇒ ¬∃z ¬(z∈paire(paire(paire(a,a),paire(a,y)),paire(paire(a,a),paire(a,y))) ⇒ z∈G)) ⇒ ¬(¬∃z ¬(z∈paire(paire(paire(a,a),paire(a,y)),paire(paire(a,a),paire...

    Auto-découvert : coupe_caracterisation ∘ appartient_singleton_inclus. Re-dérivé au noyau (clos, 22 ax.)."""
    return _equiv('bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions_complements.coupe_caracterisation', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.appartient_singleton_inclus', _CIBLES[15])


def lemme_alg_16():
    """[incl] ¬∃z ¬(z∈A ⇒ z∈reunion(vide(),A))

    Auto-découvert : reunion_vide_neutre ∘ commutativite_reunion. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide_identites.reunion_vide_neutre'), ('p', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_reunion'), _CIBLES[16])


def lemme_alg_17():
    """[incl] ¬∃z ¬(z∈inter(A,vide()) ⇒ z∈X)

    Auto-découvert : intersection_vide ∘ vide_inclus_partout. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide_identites.intersection_vide'), ('c', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide.vide_inclus_partout'), _CIBLES[17])


def lemme_alg_18():
    """[incl] ¬∃z ¬(z∈difference(A,A) ⇒ z∈X)

    Auto-découvert : difference_self ∘ vide_inclus_partout. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide_identites.difference_self'), ('c', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide.vide_inclus_partout'), _CIBLES[18])


def lemme_alg_19():
    """[incl] ¬∃z ¬(z∈A ⇒ z∈inter(A,A))

    Auto-découvert : idempotence_intersection ∘ commutativite_intersection. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_algebre_booleenne.ensembles_algebre_booleenne.idempotence_intersection'), ('p', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.commutativite_intersection'), _CIBLES[19])


def lemme_alg_20():
    """[incl] ¬∃z ¬(z∈image(G,vide()) ⇒ z∈X)

    Auto-découvert : image_vide ∘ vide_inclus_partout. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances.image_vide'), ('c', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide.vide_inclus_partout'), _CIBLES[20])


def lemme_alg_21():
    """[incl] ¬∃z ¬(z∈X ⇒ z∈img(reciproque(diagonale(X))))

    Auto-découvert : pr1_diagonale ∘ pr2_reciproque. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple.pr1_diagonale'), ('p', 'bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque.pr2_reciproque'), _CIBLES[21])


def lemme_alg_22():
    """[incl] ¬∃z ¬(z∈X ⇒ z∈dom(reciproque(diagonale(X))))

    Auto-découvert : pr2_diagonale ∘ pr1_reciproque. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('p', 'bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple.pr2_diagonale'), ('p', 'bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque.pr1_reciproque'), _CIBLES[22])


def lemme_alg_23():
    """[incl] ¬∃z ¬(z∈restriction(F,X) ⇒ z∈reunion(F,b))

    Auto-découvert : restriction_incluse ∘ inclusion_reunion_gauche. Re-dérivé au noyau (clos, 22 ax.)."""
    return _incl(('c', 'bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions.restriction_incluse'), ('c', 'bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes.inclusion_reunion_gauche'), _CIBLES[23])


IDS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

_CIBLES = {
    0: "Formule('=', lieur='', termes=(Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='C', lieur='', args=()))), Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='C', lieur='', args=()))), Terme('var', nom='A', lieur='', args=())))), sous=())",
    1: "Formule('=', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='C', lieur='', args=()))), Terme('app', nom='inter', lieur='', args=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='C', lieur='', args=()))), Terme('var', nom='A', lieur='', args=())))), sous=())",
    2: "Formule('=', lieur='', termes=(Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))))), Terme('app', nom='difference', lieur='', args=(Terme('app', nom='inter', lieur='', args=(Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='A', lieur='', args=()))), Terme('var', nom='E', lieur='', args=()))), Terme('var', nom='B', lieur='', args=())))), sous=())",
    3: "Formule('=', lieur='', termes=(Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))))), Terme('app', nom='inter', lieur='', args=(Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='A', lieur='', args=())))))), sous=())",
    4: "Formule('=', lieur='', termes=(Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))))), Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('app', nom='difference', lieur='', args=(Terme('var', nom='E', lieur='', args=()), Terme('var', nom='A', lieur='', args=())))))), sous=())",
    5: "Formule('=', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='C', lieur='', args=()))), Terme('app', nom='inter', lieur='', args=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='C', lieur='', args=())))))), sous=())",
    6: "Formule('=', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='C', lieur='', args=()))))), Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='C', lieur='', args=()))), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=())))))), sous=())",
    7: "Formule('=', lieur='', termes=(Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='C', lieur='', args=()))))), Terme('app', nom='inter', lieur='', args=(Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='C', lieur='', args=()))), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=())))))), sous=())",
    8: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('=', lieur='', termes=(Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('var', nom='X', lieur='', args=()))), Terme('var', nom='X', lieur='', args=())), sous=()))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('=', lieur='', termes=(Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('var', nom='X', lieur='', args=()))), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)))),))",
    9: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('=', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('var', nom='X', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=())))), sous=()))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('=', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=()))), Terme('var', nom='X', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='x', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='x', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)))),))",
    10: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='vide', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='@0', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='@0', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('app', nom='vide', lieur='', args=()), Terme('var', nom='@0', lieur='', args=())), sous=()))),)),)),)))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='@0', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='@0', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('app', nom='vide', lieur='', args=()), Terme('var', nom='@0', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='vide', lieur='', args=())), sous=()))),)),)),)))),)))),))",
    11: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='B', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='X', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),)))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='X', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='B', lieur='', args=())), sous=()))),)),)),)))),)))),))",
    12: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='B', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='X', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),)))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='X', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),)),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='B', lieur='', args=())), sous=()))),)),)),)))),)))),))",
    13: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))))), Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='Xp', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())))))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='u', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Xp', lieur='', args=())))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()),)))),)))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='u', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Xp', lieur='', args=())))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())), sous=()),)))),)),)), Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))))), Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='X', lieur='', args=()), Terme('var', nom='Y', lieur='', args=()))), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='Xp', lieur='', args=()), Terme('var', nom='Y', lieur='', args=())))))), sous=()))),)))),))",
    14: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))))), Terme('app', nom='inter', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='C', lieur='', args=()), Terme('var', nom='D', lieur='', args=())))))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='u', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='C', lieur='', args=())))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='D', lieur='', args=())))), sous=()),)))),)))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='u', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='C', lieur='', args=())))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='v', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='B', lieur='', args=()), Terme('var', nom='D', lieur='', args=())))), sous=()),)))),)),)), Formule('in', lieur='', termes=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='u', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='u', lieur='', args=()), Terme('var', nom='v', lieur='', args=()))))), Terme('app', nom='inter', lieur='', args=(Terme('app', nom='produit', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='B', lieur='', args=()))), Terme('app', nom='produit', lieur='', args=(Terme('var', nom='C', lieur='', args=()), Terme('var', nom='D', lieur='', args=())))))), sous=()))),)))),))",
    15: "Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='y', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='a', lieur='', args=())))))), sous=()),)), Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='a', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='a', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='y', lieur='', args=())))))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='G', lieur='', args=())), sous=()))),)),)),)))),)), Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='a', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='y', lieur='', args=()))))), Terme('app', nom='paire', lieur='', args=(Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='a', lieur='', args=()))), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='y', lieur='', args=())))))))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='G', lieur='', args=())), sous=()))),)),)),)),)), Formule('in', lieur='', termes=(Terme('var', nom='y', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='paire', lieur='', args=(Terme('var', nom='a', lieur='', args=()), Terme('var', nom='a', lieur='', args=())))))), sous=()))),)))),))",
    16: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('app', nom='vide', lieur='', args=()), Terme('var', nom='A', lieur='', args=())))), sous=()))),)),)),))",
    17: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('app', nom='vide', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),))",
    18: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='difference', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='A', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),))",
    19: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='A', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='inter', lieur='', args=(Terme('var', nom='A', lieur='', args=()), Terme('var', nom='A', lieur='', args=())))), sous=()))),)),)),))",
    20: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='image', lieur='', args=(Terme('var', nom='G', lieur='', args=()), Terme('app', nom='vide', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()))),)),)),))",
    21: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='img', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='diagonale', lieur='', args=(Terme('var', nom='X', lieur='', args=()),)),)),))), sous=()))),)),)),))",
    22: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('var', nom='X', lieur='', args=())), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='dom', lieur='', args=(Terme('app', nom='reciproque', lieur='', args=(Terme('app', nom='diagonale', lieur='', args=(Terme('var', nom='X', lieur='', args=()),)),)),))), sous=()))),)),)),))",
    23: "Formule('non', lieur='', termes=(), sous=(Formule('exists', lieur='z', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('ou', lieur='', termes=(), sous=(Formule('non', lieur='', termes=(), sous=(Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='restriction', lieur='', args=(Terme('var', nom='F', lieur='', args=()), Terme('var', nom='X', lieur='', args=())))), sous=()),)), Formule('in', lieur='', termes=(Terme('var', nom='z', lieur='', args=()), Terme('app', nom='reunion', lieur='', args=(Terme('var', nom='F', lieur='', args=()), Terme('var', nom='b', lieur='', args=())))), sous=()))),)),)),))",
}
