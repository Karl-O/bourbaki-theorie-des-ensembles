# -*- coding: utf-8 -*-
"""Division euclidienne (E III.5.6, Th.1) — l'identité du SUCCESSEUR :  b·(q+1) = b + b·q.

Troisième pièce de la campagne : l'identité arithmétique qui referme le pas de récurrence
(b + (b·q + r) deviendra b·(q+1) + r). Énoncée avec les opérations réelles :

    ⊢  Card( b × Card(q ⊔ {∅}) )  =  Card( b ⊔ Card(b×q) )        (b·(q+1M) = b + b·q, CLOS)

où q+1M := successeur(q) = Card(q⊔{∅}). Le cœur du travail est le PONT entre les trois niveaux
(ensembles bruts / Card / opérations) : les lois (distributivité, commutativité, x·1=x) vivent au
niveau ensembles, mais les opérations composent à travers des Card IMBRIQUÉS — on traverse par
l'invariance (eq_produit_invariant, somme_cardinale_bien_definie) et Eq(X, Card X).

Chaîne :  Card(b×q1) = Card(b×(q⊔{∅}))                [invariance produit + Eq(q1, q⊔{∅})]
                    = Card((b×q) ⊔ (b×{∅}))           [distributivité, niveau ensembles]
                    = Card( Card(b×q) ⊔ b )           [bien-définition somme : Eq(b×q, Card(b×q)),
                                                        Eq(b×{∅}, b) = eq_produit_un]
                    = Card( b ⊔ Card(b×q) )           [commutativité].
Frontière : primitives noyau seules, theorie == 22. @livre posé (campagne 2026-07) : Th.1 =
E III.39 L.10-11, démo L.12-19 (PDF p.142). Cas PARTIEL — le Th.1 général reste ouvert.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_son_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (
    equipotence_symetrique)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.equipotence_retrait.ensembles_equipotence_retrait import (
    equipotence_reflexive_pour)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    _prop1_direct_tt)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
    eq_produit_invariant)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_distributivite_cardinale import (
    distributivite_cardinale)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (
    eq_produit_un)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
    somme_cardinale_bien_definie)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie


def _esc_t(t):
    """⊢ Eq(T, Card T) pour un TERME T (term-wrapper d'equipotent_son_cardinal, à nom)."""
    return instancie(N.generalisation("X", equipotent_son_cardinal("X")), t)


def _wrap4(thm_vars, noms, termes):
    """Term-wrapper du playbook : ∀-clôt un théorème CLOS énoncé sur des VARIABLES puis
    l'instancie aux TERMES (τ-lourds). La substitution ne touche que la CONCLUSION — on
    évite la collision de liants des constructeurs de graphes internes (recapture @0)."""
    g = thm_vars
    for n in reversed(noms):
        g = N.generalisation(n, g)
    for t in termes:
        g = instancie(g, t)
    return g


def _sym_eq(thm, x_t, y_t):
    """⊢ Eq(X,Y) → ⊢ Eq(Y,X) (term-wrapper d'equipotence_symetrique, à noms)."""
    gen = N.generalisation("X", N.generalisation("Y", equipotence_symetrique("F", "X", "Y")))
    return N.modus_ponens(thm, instancie(instancie(gen, x_t), y_t))


def division_successeur_cible(b="b", q="q"):
    """Card(b × Card(q⊔{∅})) = Card(b ⊔ Card(b×q))   (b·(q+1M) = b + b·q)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal
    vb, vq = var(b), var(q)
    q1 = cardinal(E.somme_disjointe(vq, E.singleton(E.VIDE))) if hasattr(E, "somme_disjointe") else None
    # somme_disjointe vit dans le module familles ; on la prend là-bas :
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_disjointe)
    q1 = cardinal(somme_disjointe(vq, E.singleton(E.VIDE)))
    gauche = cardinal(E.produit(vb, q1))
    droite = cardinal(somme_disjointe(vb, cardinal(E.produit(vb, vq))))
    return egal(gauche, droite)


# @livre Ch.III §5.6 Th.1 | E III.39 L.10-11 | PDF p.142
# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142
def division_successeur(b="b", q="q"):
    """⊢ b·(q+1M) = b + b·q   (identité du successeur, CLOS)."""
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_disjointe)
    vb, vq = var(b), var(q)
    un = E.singleton(E.VIDE)                             # {∅} = 1
    S1 = somme_disjointe(vq, un)                         # q ⊔ {∅}
    q1 = cardinal(S1)                                    # q+1M = successeur(q)
    P = cardinal(E.produit(vb, vq))                      # b·q

    # (1) Card(b×q1) = Card(b×S1) — invariance du produit, Eq(q1,S1) = sym(Eq(S1, Card S1)).
    #     Constructeurs appelés au niveau VARIABLES puis _wrap4 (τ-termes ⇒ collision sinon).
    eq_q1 = _sym_eq(_esc_t(S1), S1, q1)                  # Eq(q1, S1)
    conj1 = conjonction_intro(equipotence_reflexive_pour(vb), eq_q1)
    inv_v = eq_produit_invariant("F", "G", "Xw", "Yw", "X1w", "Y1w")
    inv = N.modus_ponens(conj1, _wrap4(inv_v, ["Xw", "Yw", "X1w", "Y1w"], [vb, q1, vb, S1]))
    c1 = N.modus_ponens(inv, _prop1_direct_tt(E.produit(vb, q1), E.produit(vb, S1)))

    # (2) Card(b×S1) = Card((b×q)⊔(b×{∅})) — distributivité. Wrapper OBLIGATOIRE même sans τ :
    #     l'argument NOMMÉ « q » collisionne avec le témoin interne « q » de la machinerie
    #     produit (_membre_produit_pr2_ab ⇒ « 'q' libre dans C ») — noms symboliques puis instancie.
    c2 = _wrap4(distributivite_cardinale("Aw", "Bw", "Cw"), ["Aw", "Bw", "Cw"], [vb, vq, un])

    # (3) Card((b×q)⊔(b×{∅})) = Card(P ⊔ b) — bien-définition : Eq(b×q, P), Eq(b×{∅}, b).
    conj3 = conjonction_intro(_esc_t(E.produit(vb, vq)), eq_produit_un(vb))
    bd_v = somme_cardinale_bien_definie("Aw", "Bw", "A1w", "B1w")
    c3 = N.modus_ponens(conj3, _wrap4(bd_v, ["Aw", "Bw", "A1w", "B1w"],
                                      [E.produit(vb, vq), E.produit(vb, un), P, vb]))

    # (4) Card(P⊔b) = Card(b⊔P) — commutativité (P est τ-lourd ⇒ wrapper aussi).
    c4 = _wrap4(somme_cardinale_commutative("Aw", "Bw"), ["Aw", "Bw"], [P, vb])

    return composer_egalites(composer_egalites(composer_egalites(c1, c2), c3), c4)


__all__ = ["division_successeur", "division_successeur_cible"]
