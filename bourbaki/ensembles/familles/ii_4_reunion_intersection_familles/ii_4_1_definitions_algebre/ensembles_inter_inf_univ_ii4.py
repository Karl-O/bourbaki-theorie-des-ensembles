"""§II.4 — PROPRIÉTÉ UNIVERSELLE de l'intersection d'une famille (caractérisation inf).

Module NEUF, DUAL de `ensembles_reunion_sup_univ_ii4`.  Ne modifie aucun fichier
existant ; complète l'algèbre des familles SANS rien dupliquer.

On formalise, comme énoncé AUTONOME et INCONDITIONNEL (0 hypothèse), la propriété
universelle de l'intersection ⋂_{ι∈I} X_ι : c'est le PLUS GRAND MINORANT (au sens
de ⊂) de la famille (X_ι).  Précisément (E.II.4.1, dual de la réunion) :

        ⊢  ( A ⊂ ⋂_{ι∈I} X_ι )  ⟺  ( (∀i)(i∈I ⇒ A ⊂ X_i) )   (`inter_inf_universelle`)

C'est la caractérisation « borne inférieure » de l'intersection : A est inclus
dans ⋂ X_ι si et seulement si A est inclus dans CHAQUE terme X_ι.

STRATÉGIE : appartenance via AXIOME_INTER_FAM (réutilisé, theorie_ensembles=22),
loi de déduction et généralisation.  Point courant nommé « w » via le binder « z »
de l'abréviation ⊂, capture-safe vis-à-vis du liant « i » de l'axiome
d'intersection et du liant « k » du ∀ externe.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, et, impl, appartient,
                                       pourtout, inclus, equiv)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _enonce(vf, vI, vA):
    """A ⊂ ⋂X_ι  ⟺  (∀i)(i∈I ⇒ A ⊂ X_i)."""
    inter = E.inter_famille(vf, vI)
    gauche = inclus(vA, inter)
    droite = pourtout("k", impl(appartient(var("k"), vI),
                                inclus(vA, E.valeur_famille(vf, var("k")))))
    return equiv(gauche, droite)


def cible_inter_inf_universelle(f="X", i="I", a="A"):
    """L'énoncé Bourbaki visé (E.II.4.1, propriété universelle de l'intersection)."""
    return _enonce(var(f), var(i), var(a))


def inter_inf_universelle(f="X", i="I", a="A"):
    """⊢ ( A ⊂ ⋂_{ι∈I} X_ι ) ⟺ ( (∀i)(i∈I ⇒ A ⊂ X_i) ).   (E.II.4.1, inf de la famille.)

    INCONDITIONNEL (0 hypothèse).  ⋂ est le plus grand minorant (⊂) de (X_ι)."""
    vf, vI, vA = var(f), var(i), var(a)
    vz, vk = var("z"), var("k")
    inter = E.inter_famille(vf, vI)
    Xk = E.valeur_famille(vf, vk)
    gauche = inclus(vA, inter)                              # A ⊂ ⋂  = (∀z)(z∈A ⇒ z∈⋂)
    droite = pourtout("k", impl(appartient(vk, vI), inclus(vA, Xk)))

    # ── sens « ⇒ » :  A⊂⋂  ⊢  (∀k)(k∈I ⇒ A ⊂ X_k) ─────────────────────────
    hG = N.assume(gauche)                                  # A⊂⋂
    hk = N.assume(appartient(vk, vI))                      # k∈I
    hw = N.assume(appartient(vz, vA))                      # w∈A
    w_inter = N.modus_ponens(hw, instancie(hG, vz))        # w∈⋂
    # w∈⋂ ⇒ (∀i)(i∈I ⇒ w∈X_i)
    forall_i = N.modus_ponens(w_inter, equivalence_avant(_inst_inter(vf, vI, vz)))
    w_Xk = N.modus_ponens(hk, instancie(forall_i, vk))     # w∈X_k
    Xk_sup = N.generalisation("z", N.loi_deduction(appartient(vz, vA), w_Xk))  # A ⊂ X_k
    imp_k = N.loi_deduction(appartient(vk, vI), Xk_sup)    # k∈I ⇒ A ⊂ X_k
    droite_de_gauche = N.generalisation("k", imp_k)        # {gauche} ⊢ droite
    sens_avant = N.loi_deduction(gauche, droite_de_gauche)

    # ── sens « ⇐ » :  (∀k)(k∈I ⇒ A ⊂ X_k)  ⊢  A⊂⋂ ─────────────────────────
    hD = N.assume(droite)                                  # (∀k)(k∈I ⇒ A ⊂ X_k)
    hwA = N.assume(appartient(vz, vA))                     # w∈A
    # but : (∀i)(i∈I ⇒ w∈X_i), puis w∈⋂ via l'axiome
    vi = var("i")
    Xi = E.valeur_famille(vf, vi)
    hi = N.assume(appartient(vi, vI))                      # i∈I
    A_Xi = N.modus_ponens(hi, instancie(hD, vi))           # A ⊂ X_i
    w_Xi = N.modus_ponens(hwA, instancie(A_Xi, vz))        # w∈X_i
    imp_i = N.loi_deduction(appartient(vi, vI), w_Xi)      # i∈I ⇒ w∈X_i
    forall = N.generalisation("i", imp_i)                  # (∀i)(i∈I ⇒ w∈X_i)
    w_inter2 = N.modus_ponens(forall, equivalence_arriere(_inst_inter(vf, vI, vz)))  # w∈⋂
    gauche_de_droite = N.generalisation("z", N.loi_deduction(appartient(vz, vA), w_inter2))
    sens_arriere = N.loi_deduction(droite, gauche_de_droite)

    return conjonction_intro(sens_avant, sens_arriere)
