# -*- coding: utf-8 -*-
"""Division euclidienne (E III.5.6, Th.1) — RECOMPOSITION du pas de récurrence.

Deuxième pièce de la campagne : le maillon central du cas a ≥ b. Si l'hypothèse de récurrence
donne la division de a−b (a−b = b·q + r), alors la recomposition remonte à a :

    { est_cardinal(b), est_cardinal(a), b ≤ a,  a−b = b·q + r }  ⊢  b + (b·q + r) = a

Chaîne (3 pas d'égalité, hypothèses HONNÊTES — ce lemme est un maillon du Th.1, pas le Th.1) :
    b + (a−b) = a                soustraction_caracterisation (rôles échangés : a:=b, b:=a)
    b + (a−b) = b + (b·q + r)    congruence dans le contexte  b + w   (HR)
    b + (b·q + r) = a            symétrie + composer_egalites.
Le réarrangement b + (b·q+r) = b·(q+1) + r (associativité/commutativité/distributivité) et la
récurrence C61 encodée viendront dans les pièces suivantes. Frontière : noyau seul, theorie == 22.

NB fidélité : maillon de la DÉMONSTRATION du Th.1 ; @livre posé (campagne 2026-07) : Th.1 =
E III.39 L.10-11, démo L.12-19 (PDF p.142). Cas PARTIEL — le Th.1 général reste ouvert.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme, symetrie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    diff_somme, soustraction_caracterisation)


def division_pas_recomposition_cible(a="a", b="b", q="q", r="r"):
    """b + (b·q + r) = a   (la conclusion du maillon)."""
    va, vb, vq, vr = var(a), var(b), var(q), var(r)
    bqr = somme_cardinale_binaire(produit_cardinal_binaire(vb, vq), vr)
    return egal(somme_cardinale_binaire(vb, bqr), va)


# @livre Ch.III §5.6 Th.1 | E III.39 L.10-11 | PDF p.142
# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142
def division_pas_recomposition(a="a", b="b", q="q", r="r"):
    """{est_cardinal b, est_cardinal a, b≤a, a−b = b·q+r} ⊢ b + (b·q + r) = a.

    Hypothèses honnêtes (4) : la garde cardinale + l'ordre (le cas a≥b) + l'HR de récurrence."""
    va, vb, vq, vr = var(a), var(b), var(q), var(r)
    diff = diff_somme(va, vb, "c")                      # a−b  =  τc(a = b + c)
    bqr = somme_cardinale_binaire(produit_cardinal_binaire(vb, vq), vr)

    # (1) b + (a−b) = a   — Cor.4 §III.5 avec les rôles échangés (a:=b, b:=a).
    ante = et(et(est_cardinal(vb), est_cardinal(va)), inf_egal_card(vb, va))
    rec = N.modus_ponens(N.assume(ante), soustraction_caracterisation(b, a))

    # (2) b + (a−b) = b + (b·q + r)   — congruence de l'HR dans le contexte  b + w.
    hr = N.assume(egal(diff, bqr))                      # a−b = b·q + r   (HR)
    V = somme_cardinale_binaire(vb, var("w"))
    cg = N.modus_ponens(hr, congruence_terme(diff, bqr, V))

    # (3) symétrie + transitivité :  b + (b·q + r) = a.
    sym = N.modus_ponens(cg, symetrie(somme_cardinale_binaire(vb, diff),
                                      somme_cardinale_binaire(vb, bqr)))
    return composer_egalites(sym, rec)


__all__ = ["division_pas_recomposition", "division_pas_recomposition_cible"]
