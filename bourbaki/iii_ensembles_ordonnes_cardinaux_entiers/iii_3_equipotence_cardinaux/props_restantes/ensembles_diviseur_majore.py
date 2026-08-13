"""§III.5.6 — Un diviseur est MAJORÉ par son dividende.

    ⊢ ( est_fini(d)  et  ¬(p = 0)  et  divise_propre(d, p) )  ⇒  d ≤ p

────────────────────────────────────────────────────────────────────────────────
CE QUE CE LEMME DÉBLOQUE.  Sans lui, la clause universelle de la primalité —
« (∀d)( (d fini et d | p) ⇒ (d = 1 ou d = p) ) » — n'a aucune prise : il faut
traiter TOUS les d, et rien ne les borne.  Avec lui, le domaine se referme sur
les d ≤ p, et une analyse par cas devient possible.  C'est ce lemme qui rend
`est_premier(2)` atteignable.

Il n'existait pas au dépôt : mesuré par grep sur tous les usages de
`divise_propre` (parité §III.5, injection dénombrable §III.6, et la conjecture de
Goldbach) — aucun n'énonce de majoration, et `ensembles_division_multiples` ne
contient que `multiple_de_multiple` et `somme_multiples`.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE, EN CINQ MAILLONS.  `divise_propre(d,p)` donne p = Card(d×q) avec q fini.

  (1) **q ≠ ∅**, et c'est le maillon qu'on croyait venir de la borne « 1 ≤ x ».
      Il vient en fait de ¬(p = 0) : si q = ∅ alors Card(d×q) = Card(∅) = 0 = p.
      Contraposition, après transport par `congruence_terme`.
  (2) {∅} ≤ q, par `un_inf_egal`.  ⚠️ Ce théorème conclut sur le SUPPORT
      ensembliste {∅}, non sur Card({∅}) — et c'est exactement ce qu'il faut,
      car `produit_cardinal_un` parle lui aussi de Card(A×{∅}).  Aucun pont
      « 1 = Card({∅}) » n'est donc nécessaire ; en chercher un fait perdre du temps.
  (3) Card(d×{∅}) ≤ Card(d×q), par `produit_cardinale_monotone_droite`.
  (4) Card(d×{∅}) = Card(d) = d, par `_produit_cardinal_un_t` puis
      `_card_de_card_t` — ce dernier consomme `est_cardinal(d)`, qui est le
      premier conjoint de `est_fini(d)`.
  (5) deux réécritures S6, à gauche puis à droite, et élimination de l'existentielle.

────────────────────────────────────────────────────────────────────────────────
HYPOTHÈSES MESURÉES, NON DÉCLARÉES.  `diviseur_majore_brut` rend la forme séquent :
`N.assume` ne fait entrer une hypothèse que si elle a réellement servi, donc en
trouver exactement TROIS prouve que les trois portent.  Mesuré au passage :
`est_fini(p)` — que l'énoncé cible réclamait au départ — **ne porte pas**.  Le
lemme est donc strictement plus fort que ce qui était visé.  De même `est_fini(q)`
est inutile : la majoration vaut pour un quotient quelconque non vide.

ANTI-VACUITÉ.  Une implication close dont l'antécédent serait contradictoire ne
vaudrait rien.  `instance_un` l'écarte en PROUVANT l'antécédent en d = p = 1 et en
dérivant ⊢ 1 ≤ 1 *à travers* le lemme.

INVARIANT : theorie_ensembles() reste à 22 axiomes ; rien n'est postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, impl, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre, _card_de_card_t, _produit_cardinal_un_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (
    produit_cardinal_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_un_borne import (
    un_inf_egal, UN as UN_ENS,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinal_ordre_props import (
    produit_cardinale_monotone_droite,
)

#: liants par défaut ; `qdiv` est celui de `divise_propre`, ne pas le changer.
D, P, Q = "ddm", "pdm", "qdiv"


def _produit_cardinal_zero_t(t):
    """⊢ Card(T×∅) = Card(∅) pour un TERME T.

    ⚠️ `produit_cardinal_zero` n'accepte PAS un terme : lui en passer un casse le
    modus ponens interne. Même recette de contournement que `_produit_cardinal_un_t`
    du dépôt — généraliser sur une lettre fraîche, puis instancier."""
    return instancie(N.generalisation("Apcz", produit_cardinal_zero("Apcz")), t)


# @livre Ch.III §5.6 Lem.- | E III.39 L.20-23 | PDF p.142  (majoration d'un diviseur : lemme DÉRIVÉ de la Déf. 1 de la divisibilité, non un énoncé numéroté du livre)
def cible(d=D, p=P, q=Q):
    """L'énoncé, écrit avec les fonctions DU DÉPÔT et jamais recopié à la main."""
    vd, vp = var(d), var(p)
    return impl(et(et(est_fini(vd), non(egal(vp, ZERO))), divise_propre(vd, vp, q=q)),
                inf_egal_card(vd, vp))


def quotient_non_vide(d=D, p=P, q=Q):
    """{ p = Card(d×q), ¬(p=0) } ⊢ ¬(q = ∅).                          [2 hyps].

    Contraposée de « q = ∅ ⇒ p = 0 »."""
    vd, vp, vq = var(d), var(p), var(q)
    B = produit_cardinal_binaire(vd, vq)
    h_eq = N.assume(egal(vp, B))
    h_p0 = N.assume(non(egal(vp, ZERO)))
    trou = cardinal(E.produit(vd, var("wtrou")))
    congr = congruence_terme(vq, E.VIDE, trou, w="wtrou")
    eq1 = N.modus_ponens(N.assume(egal(vq, E.VIDE)), congr)
    eq2 = composer_egalites(eq1, _produit_cardinal_zero_t(vd))
    p_zero = composer_egalites(h_eq, eq2)
    imp = N.loi_deduction(egal(vq, E.VIDE), p_zero)
    return N.modus_ponens(h_p0, contraposition(imp))


def diviseur_majore_brut(d=D, p=P, q=Q):
    """{ Fini(d), ¬(p=0), divise_propre(d,p) } ⊢ d ≤ p.               [3 hyps].

    Forme SÉQUENT : les trois hypothèses sont MESURÉES porteuses (cf. en-tête)."""
    vd, vp, vq = var(d), var(p), var(q)
    B = produit_cardinal_binaire(vd, vq)
    A = cardinal(E.produit(vd, UN_ENS))

    card_d = conjonction_elim_gauche(N.assume(est_fini(vd)))
    Cd_eq_d = N.modus_ponens(card_d, _card_de_card_t(vd))

    corps = et(est_fini(vq), egal(vp, B))
    eq_p = conjonction_elim_droite(N.assume(corps))

    qnv = quotient_non_vide(d, p, q)
    qnv = N.modus_ponens(eq_p, N.loi_deduction(egal(vp, B), qnv))
    le_un_q = N.modus_ponens(qnv, un_inf_egal(vq))
    le_prod = N.modus_ponens(le_un_q,
                             produit_cardinale_monotone_droite(UN_ENS, vq, vd))
    A_eq_d = composer_egalites(_produit_cardinal_un_t(vd), Cd_eq_d)

    leib_g = N.s6(A, vd, "wg", inf_egal_card(var("wg"), B))
    le_d_B = N.modus_ponens(le_prod,
                            equivalence_avant(N.modus_ponens(A_eq_d, leib_g)))
    B_eq_p = N.modus_ponens(eq_p, symetrie(vp, B))
    leib_d = N.s6(B, vp, "wd", inf_egal_card(vd, var("wd")))
    le_d_p = N.modus_ponens(le_d_B,
                            equivalence_avant(N.modus_ponens(B_eq_p, leib_d)))

    ex_imp = existe_elimination(N.loi_deduction(corps, le_d_p), q)
    div = divise_propre(vd, vp, q=q)
    assert existe(q, corps) == div, "le corps ne recompose pas divise_propre"
    return N.modus_ponens(N.assume(div), ex_imp)


# @livre Ch.III §5.6 Lem.- | E III.39 L.20-23 | PDF p.142  (👑 le lemme CLOS : un diviseur est majoré par son dividende)
def diviseur_majore(d=D, p=P, q=Q):
    """👑 ⊢ (Fini(d) et ¬(p=0) et divise_propre(d,p)) ⇒ d ≤ p.        [CLOS]."""
    vd, vp = var(d), var(p)
    div = divise_propre(vd, vp, q=q)
    concl = diviseur_majore_brut(d, p, q)
    ante = et(et(est_fini(vd), non(egal(vp, ZERO))), div)
    h = N.assume(ante)
    reconstruit = N.modus_ponens(
        conjonction_elim_droite(h),
        N.loi_deduction(div, N.modus_ponens(
            conjonction_elim_droite(conjonction_elim_gauche(h)),
            N.loi_deduction(non(egal(vp, ZERO)), N.modus_ponens(
                conjonction_elim_gauche(conjonction_elim_gauche(h)),
                N.loi_deduction(est_fini(vd), concl))))))
    res = N.loi_deduction(ante, reconstruit)
    assert res.conclusion == cible(d, p, q), "diviseur_majore : ≠ cible"
    assert res.est_clos, "diviseur_majore : devrait être clos"
    return res


# @livre Ch.III §5.6 Lem.- | E III.39 L.20-23 | PDF p.142  (la forme quantifiée, taillée pour le (∀d) de la primalité)
def diviseur_majore_quantifie(d=D, p=P, q=Q):
    """👑 ⊢ ¬(p = 0) ⇒ (∀d)( (Fini(d) et divise_propre(d,p)) ⇒ d ≤ p ).  [CLOS].

    L'antécédent interne est LITTÉRALEMENT celui du (∀d) de la primalité : c'est
    ce qui permet de l'y emboîter sans transport."""
    vd, vp = var(d), var(p)
    base = diviseur_majore(d, p, q)
    ante_d = et(est_fini(vd), divise_propre(vd, vp, q=q))
    h_p0 = N.assume(non(egal(vp, ZERO)))
    h_d = N.assume(ante_d)
    triple = conjonction_intro(
        conjonction_intro(conjonction_elim_gauche(h_d), h_p0),
        conjonction_elim_droite(h_d))
    inner = N.loi_deduction(ante_d, N.modus_ponens(triple, base))
    return N.loi_deduction(non(egal(vp, ZERO)), N.generalisation(d, inner))


def instance_un():
    """⊢ 1 ≤ 1, obtenu EN PASSANT PAR le lemme — contrôle d'ANTI-VACUITÉ.

    Rend (instance, antécédent prouvé, conclusion). Si l'antécédent était
    contradictoire, rien de tout cela ne se construirait."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (
        fini_un, un_est_un_cardinal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_ordre_strict_petits import (
        zero_distinct_un,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
        divise_propre_reflexif,
    )
    gen = N.generalisation(P, N.generalisation(D, diviseur_majore()))
    inst = instancie(instancie(gen, UN), UN)
    ne = N.modus_ponens(zero_distinct_un(), contraposition(symetrie(UN, ZERO)))
    d11 = N.modus_ponens(un_est_un_cardinal(), divise_propre_reflexif(UN))
    ante = conjonction_intro(conjonction_intro(fini_un(), ne), d11)
    return inst, ante, N.modus_ponens(ante, inst)


__all__ = ["cible", "quotient_non_vide", "diviseur_majore_brut", "diviseur_majore",
           "diviseur_majore_quantifie", "instance_un"]
