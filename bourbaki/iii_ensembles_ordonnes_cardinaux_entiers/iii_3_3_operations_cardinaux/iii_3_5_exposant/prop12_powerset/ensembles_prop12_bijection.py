# -*- coding: utf-8 -*-
"""§III.3.5 Prop.12, brique (iv) — LA BIJECTION χ : P(A) → F(A;2).

Design (DECISIONS 21 août 22h40) : B := graphe_terme(parties(A), chi_appli(x,A))
— le graphe de Y ↦ ((χ_Y, A), 2). Sous-lemmes (un commit testé chacun) :
  (a) B fonctionnel + dom B = parties(A)   [C54, ce fichier, en cours]
  (b) B injectif   [couple_egal_implique_composantes ×2 + rho_chi_identite]
  (c) image B = F(A;2)   [chi_dans_applications ; chi_rho_identite]
  (d) est_bijection_de(B, P(A), F(A;2)) puis Eq par S5.
FORME CIBLE (lue 22h50) : est_bijection_de(F,X,Y) = (fonctionnel ∧ dom=X)
∧ est_bijective(F,X,Y) [= injectif ∧ image F<X> = Y, E.II.49 — lire sa déf
exacte au prochain sous-lemme] ; (a) couvre déjà les 2 premiers conjoints.
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


# Sous-lemme (b) : B injectif sur P(A).
def bijection_injective(a="Abij"):
    """⊢ injective_dans(B, P(A)).   ({u}→χ-triples : égaux ⇒ χ égaux ⇒ Pre
    égaux ⇒ u = u' — patron de l'injection-singleton de cantor l.160-183)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        et, appartient, inclus)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite, instancie, equivalence_avant)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites, congruence_terme)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal as _egal
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
        couple_egal_implique_composantes)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        preimage_un, membre_parties_t)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_powerset import (
        chi)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_exp import (
        deux)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_fin import (
        rho_chi_identite)

    def _cut(thm, P, pr):
        return N.modus_ponens(pr, N.loi_deduction(P, thm))

    def _gi(thm, nom, terme):
        return instancie(N.generalisation(nom, thm), terme)

    vA = _t(a)
    B = bijection_graphe(a)
    PA = E.parties(vA)
    #   "u"/"up" sont des lieurs INTERNES de la machinerie χ/graphe_terme
    #   (4e échec mesuré) : on prouve avec ub/upb puis α-passage final.
    vu, vup = var("ub"), var("upb")
    T_u = chi_appli(vu, vA)
    T_up = chi_appli(vup, vA)

    corps = et(et(appartient(vu, PA), appartient(vup, PA)),
               _egal(E.valeur(B, vu), E.valeur(B, vup)))
    h = N.assume(corps)
    h_u = conjonction_elim_gauche(conjonction_elim_gauche(h))     # u ∈ P(A)
    h_up = conjonction_elim_droite(conjonction_elim_gauche(h))    # u' ∈ P(A)
    h_eq = conjonction_elim_droite(h)                             # B(u) = B(u')

    #   B(u) = chi_appli(u), B(u') = chi_appli(u')   (valeur du graphe-terme)
    v_u = _cut(graphe_terme_valeur(PA, chi_appli(var("x"), vA), "ub"),
               appartient(vu, PA), h_u)                           # B(u) = T[u]
    v_up_brut = graphe_terme_valeur(PA, chi_appli(var("x"), vA), "upb")
    v_up = _cut(v_up_brut, appartient(vup, PA), h_up)             # B(u') = T[u']

    #   chi_appli(u) = chi_appli(u')
    eq_T = composer_egalites(composer_egalites(
        N.modus_ponens(v_u, symetrie(E.valeur(B, vu), T_u)), h_eq), v_up)

    #   éplucher les deux couples : ((χ_u,A),2)=((χ_u',A),2) → χ_u=χ_u'
    #   le lemme accepte les TERMES directement (noms OU termes)
    c1 = N.modus_ponens(eq_T, couple_egal_implique_composantes(
        E.couple(chi(vu, vA), vA), deux(), E.couple(chi(vup, vA), vA), deux()))
    eq_int = conjonction_elim_gauche(c1)                          # (χ_u,A)=(χ_u',A)
    c2 = N.modus_ponens(eq_int, couple_egal_implique_composantes(
        chi(vu, vA), vA, chi(vup, vA), vA))
    eq_chi = conjonction_elim_gauche(c2)                          # χ_u = χ_u'

    #   Pre(χ_u) = Pre(χ_u') puis u = u'
    eq_pre = N.modus_ponens(eq_chi, congruence_terme(
        chi(vu, vA), chi(vup, vA), preimage_un(var("w"), vA)))
    sub_u = N.modus_ponens(h_u, equivalence_avant(membre_parties_t(vu, vA)))   # u ⊂ A
    sub_up = N.modus_ponens(h_up, equivalence_avant(membre_parties_t(vup, vA)))
    rho_u = N.modus_ponens(sub_u, rho_chi_identite(vu, vA))           # Pre(χ_u)=u
    rho_up = N.modus_ponens(sub_up, rho_chi_identite(vup, vA))
    u_eq = composer_egalites(composer_egalites(
        N.modus_ponens(rho_u, symetrie(preimage_un(chi(vu, vA), vA), vu)),
        eq_pre), rho_up)                                          # u = u'

    inner = N.loi_deduction(corps, u_eq)
    gen = N.generalisation("ub", N.generalisation("upb", inner))
    #   α-passage vers les lieurs u/up d'injective_dans (inst+gen, légal :
    #   théorème clos)
    t1 = instancie(gen, var("u"))
    t2 = instancie(t1, var("up"))
    return N.generalisation("u", N.generalisation("up", t2))


__all__ = ["bijection_graphe", "bijection_fonctionnel", "bijection_domaine",
           "bijection_injective"]
