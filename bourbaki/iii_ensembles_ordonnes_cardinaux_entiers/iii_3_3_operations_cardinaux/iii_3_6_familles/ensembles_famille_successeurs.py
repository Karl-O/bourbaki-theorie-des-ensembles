"""§III.5.8 Déf.2 / §III.3.3 — LA FAMILLE i↦i+1 SUR [0,n[ ET LE TERME  n! = ∏_{i<n}(i+1).

Le livre (E III.41 L.28-29) : « Soit n un entier ; on note n! le produit ∏_{i<n}(i+1) ».
Ce module pose FIDÈLEMENT ce terme (T1a du chantier familles) :

  • `famille_successeurs(n)` := graphe_terme( seg(≤_G,ℕ,n), successeur(ι), ι )
      — la famille (i+1)_{i<n}, sur le segment OUVERT seg(ℕ,n)={i∈ℕ | i<n}
        (le même segment que la chaîne factorielle C62 : cohérence des deux routes).
  • `famille_successeurs_fonctionnelle` ⊢ est_fonctionnel(...)         [CLOS]
  • `famille_successeurs_valeur`  { i0∈seg } ⊢ F(i0) = successeur(i0)  [1 hyp]
      — terme-valeur τ-LÉGER (successeur = somme_cardinale_binaire, pas de verrou).
  • `factorielle_def2(n)` := produit_cardinal( famille_successeurs(n), seg(ℕ,n) )
      — LE TERME n! du livre (Card du produit de la famille, Déf.3 §3.3).

La CONVERGENCE avec la caractérisation C62 close (factorielle_zero / succ_fallback :
0!=1, (n+1)!) exige la récursion du produit fini indexé (T1b, chantier suivant) —
le livre lui-même : « cette relation…caractérise le terme n!, par récurrence sur n ».

Et, depuis le 2026-07-27, LE CAS DE BASE de la Déf. 2, sur ce terme réel :

  • `produit_cardinal_vide(u)`   ⊢ Card ∏(u, ∅) = 1            [CLOS] (E II.32)
  • `factorielle_def2_zero()`    ⊢ factorielle_def2(0) = 1     [CLOS] (E III.41 L.30)

⚠️ Le PAS de récurrence n'est PAS fermé : `ensembles_factorielle_def2_rec` porte
encore les hypothèses HW/HN, INDÉPENDANTES (le symbole de famille n'est relié à
`valeur` par aucun des 22 axiomes).  Seul le CAS DE BASE est clos ici : dire que
« la boucle de la Déf. 2 est fermée » serait FAUX.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import produit_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import G_ordre_NN


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _seg_NN(n):
    """[0,n[ := seg( ≤_G≤ , ℕ , n )  — le segment ouvert des i<n (même forme que C62)."""
    return E.segment_extremite(G_ordre_NN(), ensemble_NN(), _t(n))


# @livre Ch.III §5.8 Def.2 | E III.41 L.28-29 | PDF p.144  (la famille (i+1)_{i<n} de la Déf. 2 — le graphe-terme i↦successeur(i) sur [0,n[)
def famille_successeurs(n, iota="ifs"):
    """(i+1)_{i<n} := graphe_terme( seg(ℕ,n), successeur(ι), ι )   (C54, liant exotique)."""
    return E.graphe_terme(_seg_NN(n), successeur(var(iota)), iota)


def famille_successeurs_fonctionnelle(n="nfs", iota="ifs"):
    """⊢ est_fonctionnel( (i+1)_{i<n} )                                [CLOS, 0 hyp]."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    res = graphe_terme_fonctionnel(_seg_NN(n), successeur(var(iota)), iota)
    assert res.conclusion == E.est_fonctionnel(famille_successeurs(n, iota)), \
        "famille_successeurs_fonctionnelle : ≠ est_fonctionnel"
    assert res.est_clos, "famille_successeurs_fonctionnelle : non clos"
    return res


def famille_successeurs_valeur(n="nfs", i0="i0fs", iota="ifs"):
    """{ i0 ∈ seg(ℕ,n) } ⊢ F(i0) = successeur(i0)                      [1 hyp honnête].

    graphe_terme_valeur (noms) sur le terme-valeur τ-LÉGER successeur(ι)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur
    res = graphe_terme_valeur(_seg_NN(n), successeur(var(iota)), i0, iota)
    cible = egal(E.valeur(famille_successeurs(n, iota), var(i0)), successeur(var(i0)))
    assert res.conclusion == cible, "famille_successeurs_valeur : ≠ F(i0)=succ(i0)"
    assert len(res.hypotheses) == 1, "famille_successeurs_valeur : hyps ≠ 1"
    return res


# @livre Ch.III §5.8 Def.2 | E III.41 L.28-29 | PDF p.144  (« on note n! le produit ∏_{i<n}(i+1) » — LE TERME de la Déf. 2, produit de famille de cardinaux, Déf.3 §3.3)
def factorielle_def2(n, iota="ifs"):
    """n! := ∏_{i<n}(i+1) = produit_cardinal( (i+1)_{i<n}, seg(ℕ,n) )   (Déf.2 FIDÈLE).

    Terme du livre, posé sur les opérations réelles (produit_cardinal = Card du
    produit de la famille, Déf.3 §3.3 — supplante le `factorielle` opaque
    d'ensembles_entiers).  La convergence avec la caractérisation récursive close
    (0!=1, cas successeur) attend la récursion du produit fini (T1b)."""
    return produit_cardinal(famille_successeurs(n, iota), _seg_NN(n))


# ═══════════════════════════════════════════════════════════════════════════════
# LE CAS DE BASE DE LA DÉF. 2 :  0! = 1,  sur le terme réel ∏_{i<0}(i+1).
# ═══════════════════════════════════════════════════════════════════════════════
#: Trous des congruences de Leibniz (Card, slot d'indice) — exotiques, vérifiés absents.
_TROU_CARD, _TROU_INDICE = "wcv", "wfz"


# @livre Ch.II §5.3 Rem.- | E II.32 L.22-23 | PDF p.83
#   (la même remarque « si I = ∅ … un seul élément, savoir l'ensemble vide », lue au
#    niveau CARDINAL : le produit d'index vide a UN élément, donc son cardinal est 1.)
def produit_cardinal_vide(u="upv"):
    """⊢ Card ∏_{ι∈∅} X_ι = 1.                          [CLOS, 0 hyp, u quelconque]

    `produit_famille_vide_est_singleton_vide` (E II.32, §II.5.3) sous Card par
    congruence, puis `un_egale_card_singleton` (1 = Card{∅}) RETOURNÉE — `symetrie`
    prend deux TERMES et rend l'implication, elle ne s'applique pas à un théorème."""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires \
        .i_5_2_tactiques_abrege_egalite import composer_egalites, congruence_terme, symetrie
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux \
        .definitions_cardinaux.ensembles_cardinaux import cardinal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis \
        .iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis \
        .iii_4_1_definitions_premiers_entiers.ensembles_fini_un import un_egale_card_singleton
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions \
        .ensembles_produit_famille_vide import produit_famille_vide_est_singleton_vide

    vu = _t(u)
    prod, sgl = E.produit_famille(vu, E.VIDE), E.singleton(E.VIDE)
    sous_card = N.modus_ponens(
        produit_famille_vide_est_singleton_vide(vu),
        congruence_terme(prod, sgl, cardinal(var(_TROU_CARD)), _TROU_CARD))
    un_eq = un_egale_card_singleton()                                   # 1 = Card{∅}
    retourne = N.modus_ponens(un_eq, symetrie(*un_eq.conclusion.termes))  # Card{∅} = 1
    res = composer_egalites(sous_card, retourne)
    assert res.conclusion == egal(produit_cardinal(vu, E.VIDE), UN), \
        "produit_cardinal_vide : conclusion ≠ Card ∏(u,∅) = 1"
    assert res.est_clos and res.hypotheses == frozenset(), \
        "produit_cardinal_vide : hypothèses résiduelles %r" % (res.hypotheses,)
    return res


def factorielle_def2_zero_enonce():
    """Formule cible :  factorielle_def2(0) = 1   — le « 0! = 1 » du livre."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis \
        .iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN
    return egal(factorielle_def2(ZERO), UN)


# @livre Ch.III §5.8 Def.2 | E III.41 L.30-30 | PDF p.144
#   (« On a 0! = 1 (II, p. 32) » — le renvoi porte TOUT le contenu : c'est E II.32
#    L.22-23 qui donne ∏ d'index vide = {∅}, donc de cardinal 1.)
def factorielle_def2_zero():
    """🎯 ⊢ factorielle_def2(0) = 1.                             [CLOS, 0 hypothèse]

    Le « 0! = 1 » de Bourbaki, sur le TERME RÉEL ∏_{i<0}(i+1) de la Déf. 2 — pas
    sur un `factorielle` opaque.  Trois maillons :

     (A) seg(≤_G, ℕ, 0) = ∅  [`segment_zero_NN_est_vide`, §III.6.1, CLOS].  C'est ce
         qui rend le cas de base NON trivial : l'indice de la Déf. 2 en n = 0 n'est
         pas écrit « ∅ », c'est le TERME seg(ℕ,0), qu'il faut prouver vide.
     (B) congruence-TROU sur le SEUL slot d'indice de produit_cardinal(F, ·).
     (C) E II.32 au terme-famille (i+1)_{i<0} : Card ∏(F, ∅) = 1.

    ⚠️ LE TROU DE CONGRUENCE EST DÉLICAT (maillon B).  Le terme-famille
    `famille_successeurs(0)` CONTIENT lui aussi seg(ℕ,0) — c'est son ensemble
    d'indices.  Réécrire seg(ℕ,0) → ∅ PARTOUT donnerait un terme qui ne se raccorde
    plus à `factorielle_def2(0)`.  On réécrit donc le SEUL slot d'indice, via un
    trou de nom exotique dont l'absence du terme-famille est ASSERTÉE.

    ⚠️ PERF : tout contact avec ensemble_NN() déclenche N_existe (~4-8 min, mémoïsé
    par process) — les tests de ce résultat sont lents."""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires \
        .i_5_2_tactiques_abrege_egalite import composer_egalites, congruence_terme
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques \
        .tactiques_abrege2 import instancie
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis \
        .iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis \
        .iii_6_1_n_objet_existence.ensembles_segment_zero_NN import segment_zero_NN_est_vide

    fam, seg0 = famille_successeurs(ZERO), _seg_NN(ZERO)
    # (A) le segment de 0 dans ℕ est vide — CLOS, aucune hypothèse importée.
    seg_vide = segment_zero_NN_est_vide()
    assert seg_vide.est_clos and seg_vide.conclusion == egal(seg0, E.VIDE), \
        "factorielle_def2_zero : §III.6.1 ne donne pas seg(ℕ,0) = ∅ [CLOS]"
    # (B) congruence-TROU sur le SLOT D'INDICE SEUL (trou vérifié absent de la famille).
    assert _TROU_INDICE not in libres_t(fam), \
        "factorielle_def2_zero : le trou %s est libre dans la famille (réécriture double)" \
        % _TROU_INDICE
    gabarit = produit_cardinal(fam, var(_TROU_INDICE))
    reecrit = N.modus_ponens(seg_vide, instancie(N.generalisation(
        _TROU_INDICE, congruence_terme(var(_TROU_INDICE), E.VIDE, gabarit, _TROU_INDICE)), seg0))
    assert reecrit.est_clos, "factorielle_def2_zero : le maillon (B) devrait être CLOS"
    assert reecrit.conclusion.termes[0] == factorielle_def2(ZERO), \
        "factorielle_def2_zero : (B) ne part pas de factorielle_def2(0)"
    # (C) E II.32 au terme-famille (i+1)_{i<0}.
    sur_vide = produit_cardinal_vide(fam)
    assert reecrit.conclusion.termes[1] == sur_vide.conclusion.termes[0], \
        "factorielle_def2_zero : (B) et (C) ne se raccordent pas"
    res = composer_egalites(reecrit, sur_vide)
    assert res.conclusion == factorielle_def2_zero_enonce(), \
        "factorielle_def2_zero : conclusion ≠ factorielle_def2(0) = 1"
    assert res.conclusion.termes[0] == produit_cardinal(fam, seg0), \
        "factorielle_def2_zero : LHS ≠ ∏_{i<0}(i+1) (Déf. 2 au point 0)"
    assert res.conclusion.termes[1] == UN, "factorielle_def2_zero : RHS ≠ 1"
    assert res.est_clos and res.hypotheses == frozenset(), \
        "factorielle_def2_zero : hypothèses résiduelles %r" % (res.hypotheses,)
    return res


__all__ = ["famille_successeurs", "famille_successeurs_fonctionnelle",
           "famille_successeurs_valeur", "factorielle_def2",
           "produit_cardinal_vide", "factorielle_def2_zero_enonce",
           "factorielle_def2_zero"]
