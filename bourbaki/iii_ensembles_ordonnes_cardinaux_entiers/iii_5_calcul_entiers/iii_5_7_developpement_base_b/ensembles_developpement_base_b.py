"""§III.5.7 — Développement de base b (E III.40-41) : Prop. 8 et la définition.

Le dossier était VIDE (trou structurel signalé par LIVRE.md) : ce module y
formalise les ÉNONCÉS de la page E III.40 — la Prop. 8 (l'application
f_k(r) = Σ r_h·b^(k−h−1) est un isomorphisme d'ensembles ordonnés du produit
lexicographique E_k sur l'intervalle (0, b^k−1)), la majoration a < b^a, et
l'existence/unicité du développement de base b.

STATUT : ÉNONCÉS FORMALISÉS, DÉMONSTRATIONS NON DÉRIVÉES (PARTIEL — la démo
du livre est une récurrence sur k qui enchaîne Prop.2 §4.2, Prop.3 §5.2,
Prop.5 §5.4 et Cor.4 §4.4 ; chantier listé dans CAMPAGNE_TROUS).  Les objets
de famille (produit lexicographique E_k, la somme Σ r_h·b^(k−h−1), la suite
(r_h)) restent des TERMES OPAQUES fournis par l'appelant — rien n'est
postulé, aucun `Theoreme` n'est forgé.

Prédicats et termes RÉELS du dépôt utilisés : est_isomorphisme_ordre
(déf. verbatim E.III.1.3), exposant_cardinal_binaire (b^k), inf_strict_card,
inf_egal_card, est_fini, UN.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, pourtout)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    est_isomorphisme_ordre)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, UN)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §5.7 Def.- | E III.40 L.1-1 | PDF p.143  (titre « 7. Développement de base b »)
# @livre Ch.III §5.7 Prop.8 | E III.40 L.2-5 | PDF p.143
#   (f_k isomorphisme ordonné de E_k [produit lexicographique] sur (0, b^k−1) ;
#    démo par récurrence sur k L.6-21 : NON dérivée)
def enonce_prop8_iso(fk, Ek, R_lex, intervalle_0_bk1, R_int) -> Terme:
    """Prop. 8 :  « f_k est un isomorphisme de l'ensemble ordonné E_k sur
    l'intervalle (0, b^k − 1) ».

    L'appelant fournit : fk (le terme-application r ↦ Σ r_h·b^(k−h−1)), Ek,
    le terme-intervalle (0, b^k−1) (théorie dédiée S8+A1 du §1.13), et les
    deux ordres comme RELATIONS BINAIRES callables (x,y) ↦ Terme — R_lex
    l'ordre lexicographique (§2.6), R_int l'ordre induit sur l'intervalle.
    Le prédicat est la définition VERBATIM E.III.1.3 du dépôt."""
    return est_isomorphisme_ordre(_t(fk), _t(Ek), _t(intervalle_0_bk1),
                                  R_lex, R_int)


# @livre Ch.III §5.7 Rem.- | E III.40 L.22-25 | PDF p.143
#   (majoration a < b^a, par récurrence sur a — démo NON dérivée)
def enonce_majoration_a_inf_b_puiss_a(a, b) -> Terme:
    """(∀a)( a entier ⇒ a < b^a )  (E III.40 L.22).  b est un terme (entier >1)."""
    va, vb = _t(a), _t(b)
    nom = a if isinstance(a, str) else "adev"
    return pourtout(nom, impl(est_fini(va),
                              inf_strict_card(va, exposant_cardinal_binaire(vb, va))))


# @livre Ch.III §5.7 Def.- | E III.40 L.25-29 | PDF p.143
#   (existence et unicité de la suite (r_h) : 0≤r_h≤b−1, a = Σ r_h·b^(k−h−1),
#    r₀>0 — LE développement de base b de a ; unicité via Prop.8, NON dérivée)
def enonce_developpement(a, somme_dev) -> Terme:
    """« a = Σ_{h=0}^{k−1} r_h·b^(k−h−1) »  (E III.40 L.27) — l'identité du
    développement, la somme-famille restant un terme opaque somme_dev."""
    return egal(_t(a), _t(somme_dev))


def enonce_chiffre_borne(r_h, b_moins_1) -> Terme:
    """« 0 ≤ r_h ≤ b−1 »  (E III.40 L.27) — au niveau cardinal, 0 ≤ r_h est
    automatique : on garde la borne supérieure r_h ≤ b−1."""
    return inf_egal_card(_t(r_h), _t(b_moins_1))


def enonce_premier_chiffre_non_nul(r_0) -> Terme:
    """« r₀ > 0 »  (E III.40 L.28), lu 1 ≤ r₀ (ordre cardinal : 0 < x ⇔ 1 ≤ x)."""
    return inf_egal_card(UN, _t(r_0))


# @livre Ch.III §5.7 Rem.- | E III.40 L.30-40 | PDF p.143
#   (petits textes : intérêt pour b premier ; chiffres et symbole numérique
#    r₀r₁…r_{k−1} — prose métamathématique de notation, rien à formaliser ;
#    la suite du petit texte continue en E III.41, page annotée par ailleurs)

__all__ = [
    "enonce_prop8_iso", "enonce_majoration_a_inf_b_puiss_a",
    "enonce_developpement", "enonce_chiffre_borne",
    "enonce_premier_chiffre_non_nul",
]
