"""Chapitre III §1.13 — PROPOSITION 13 : l'intersection de deux intervalles fermés
est un intervalle fermé (FORME MEMBERSHIP, E.III.1.13).

Énoncé Bourbaki (§III.1.13, Proposition 13) : l'intersection [a,b]∩[c,d] de deux
intervalles fermés est encore un intervalle fermé.  La preuve « treillis » identifie
[a,b]∩[c,d] = [sup(a,c), inf(b,d)] ; mais cela suppose l'existence des bornes sup/inf
des paires (structure de treillis).  On formalise ICI la FORME MEMBERSHIP, fidèle et
indépendante du treillis :

    ⊢ (∀x)( x∈[a,b]∩[c,d] ⇔
            ( x∈E et (a,x)∈G et (c,x)∈G et (x,b)∈G et (x,d)∈G ) ).

C.-à-d. : un point appartient à l'intersection des deux intervalles ssi il est dans E,
au-dessus des deux extrémités gauches (a≤x, c≤x) et au-dessous des deux extrémités
droites (x≤b, x≤d) — exactement la caractérisation d'un intervalle de bornes « max »
à gauche et « min » à droite, SANS introduire les termes sup(a,c)/inf(b,d).

STRATÉGIE (LCF, primitives N.* uniquement) :
  • axiome de membership de [a,b] et de [c,d] (théorie dédiée theorie_intervalle_ferme),
    instancié en (E,a,b,x) resp. (E,c,d,x) ;
  • lemme de membership de l'intersection x∈X∩Y ⇔ (x∈X et x∈Y)
    (_instance_intersection, AXIOME_INTER) ;
  • sens ⇒ : x∈[a,b]∩[c,d] → x∈[a,b] et x∈[c,d] → (x∈E ∧ a≤x ∧ x≤b) et
    (x∈E ∧ c≤x ∧ x≤d) → recombiner (x∈E ∧ a≤x ∧ c≤x ∧ x≤b ∧ x≤d) ;
  • sens ⇐ : de (x∈E ∧ a≤x ∧ c≤x ∧ x≤b ∧ x≤d) reconstruire les deux memberships,
    réinjecter dans les axiomes (arrière) puis dans l'intersection (arrière) ;
  • conjonction des deux sens = équivalence ; généralisation en x.

RÉSIDU HONNÊTE (documenté) : la FORME TREILLIS [a,b]∩[c,d]=[sup(a,c),inf(b,d)] n'est
PAS prouvée — elle exige l'existence de sup/inf de paires (treillis).  La forme
membership ci-dessus est la caractérisation order-théorique complète et exacte.

theorie_ensembles INTANGIBLE = 22 : le SEUL axiome utilisé pour [a,b]/[c,d] vit dans
la THÉORIE DÉDIÉE theorie_intervalle_ferme (S8+A1) ; l'intersection emploie l'axiome
de séparation binaire AXIOME_INTER de theorie_ensembles (déjà compté).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, equiv, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_intersection
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_treillis_props import (
    axiome_intervalle_ferme, theorie_intervalle_ferme, _rg, _couple_dans,
)


def _terme(t):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme
    return t if isinstance(t, Terme) else var(t)


def cible_intersection_intervalles(G="G", e="E", a="a", b="b", c="c", d="d", x="x"):
    """Énoncé EXACT visé (associativité à gauche, fixée une fois pour toutes) :

        (∀x)( x∈[a,b]∩[c,d] ⇔
              ((((x∈E et (a,x)∈G) et (c,x)∈G) et (x,b)∈G) et (x,d)∈G) ).
    """
    vE, va, vb, vc, vd, vx = _terme(e), _terme(a), _terme(b), _terme(c), _terme(d), var(x)
    Iab = E.intervalle_ferme(_rg(G), vE, va, vb)
    Icd = E.intervalle_ferme(_rg(G), vE, vc, vd)
    inter = E.intersection(Iab, Icd)
    rhs = et(et(et(et(appartient(vx, vE), _couple_dans(va, vx, G)),
                    _couple_dans(vc, vx, G)),
                 _couple_dans(vx, vb, G)),
             _couple_dans(vx, vd, G))
    return pourtout(x, equiv(appartient(vx, inter), rhs))


# @livre Ch.III §1.13 Prop.13 | E III.15 L.10-13 | PDF p.118
def intersection_intervalles_fermes(G="G", e="E", a="a", b="b", c="c", d="d", x="x"):
    """⊢ (∀x)( x∈[a,b]∩[c,d] ⇔ (x∈E et a≤x et c≤x et x≤b et x≤d) ).

    PROPOSITION 13 (E.III.1.13), forme membership : l'intersection de deux intervalles
    fermés [a,b] et [c,d] (de même ensemble support E, même ordre de graphe G) est
    caractérisée comme l'ensemble des x∈E vérifiant a≤x, c≤x, x≤b et x≤d.  Preuve
    purement order-théorique (intervalles), sans bornes sup/inf de paires.

    THÉORÈME CLOS (0 hypothèse) : l'axiome de membership de [·,·] est interne à la
    théorie dédiée theorie_intervalle_ferme et déchargé via N.axiome ; l'intersection
    repose sur AXIOME_INTER de theorie_ensembles.  Aucune hypothèse libre.
    """
    th = theorie_intervalle_ferme(G, e, a, b, x)
    ax = N.axiome(th, axiome_intervalle_ferme(G, e, a, b, x))   # (∀E∀a∀b∀x) x∈[a,b]⇔(...)
    vE, va, vb, vc, vd, vx = _terme(e), _terme(a), _terme(b), _terme(c), _terme(d), var(x)

    # ── axiomes de membership instanciés en x ────────────────────────────────────
    # x∈[a,b] ⇔ ((x∈E et (a,x)∈G) et (x,b)∈G)
    ax_ab = instancie(instancie(instancie(instancie(ax, vE), va), vb), vx)
    # x∈[c,d] ⇔ ((x∈E et (c,x)∈G) et (x,d)∈G)
    ax_cd = instancie(instancie(instancie(instancie(ax, vE), vc), vd), vx)

    Iab = E.intervalle_ferme(_rg(G), vE, va, vb)
    Icd = E.intervalle_ferme(_rg(G), vE, vc, vd)
    # x∈[a,b]∩[c,d] ⇔ (x∈[a,b] et x∈[c,d])
    inter_eq = _instance_intersection(Iab, Icd, vx)

    x_in_inter = appartient(vx, E.intersection(Iab, Icd))
    rhs = et(et(et(et(appartient(vx, vE), _couple_dans(va, vx, G)),
                    _couple_dans(vc, vx, G)),
                 _couple_dans(vx, vb, G)),
             _couple_dans(vx, vd, G))

    # ── sens ⇒ : x∈[a,b]∩[c,d] → rhs ─────────────────────────────────────────────
    Hin = N.assume(x_in_inter)
    both = N.modus_ponens(Hin, equivalence_avant(inter_eq))     # x∈[a,b] et x∈[c,d]
    in_ab = conjonction_elim_gauche(both)                        # x∈[a,b]
    in_cd = conjonction_elim_droite(both)                        # x∈[c,d]
    mab = N.modus_ponens(in_ab, equivalence_avant(ax_ab))        # (x∈E et a≤x) et x≤b
    mcd = N.modus_ponens(in_cd, equivalence_avant(ax_cd))        # (x∈E et c≤x) et x≤d
    x_in_E = conjonction_elim_gauche(conjonction_elim_gauche(mab))   # x∈E
    a_le_x = conjonction_elim_droite(conjonction_elim_gauche(mab))   # (a,x)∈G
    x_le_b = conjonction_elim_droite(mab)                            # (x,b)∈G
    c_le_x = conjonction_elim_droite(conjonction_elim_gauche(mcd))   # (c,x)∈G
    x_le_d = conjonction_elim_droite(mcd)                            # (x,d)∈G
    rhs_thm = conjonction_intro(
        conjonction_intro(
            conjonction_intro(conjonction_intro(x_in_E, a_le_x), c_le_x),
            x_le_b),
        x_le_d)                                                  # = rhs (assoc. gauche)
    avant = N.loi_deduction(x_in_inter, rhs_thm)                 # x∈[a,b]∩[c,d] ⇒ rhs

    # ── sens ⇐ : rhs → x∈[a,b]∩[c,d] ─────────────────────────────────────────────
    Hr = N.assume(rhs)
    p4 = conjonction_elim_gauche(Hr)            # (((x∈E et a≤x) et c≤x) et x≤b)
    r_x_le_d = conjonction_elim_droite(Hr)      # (x,d)∈G
    p3 = conjonction_elim_gauche(p4)            # ((x∈E et a≤x) et c≤x)
    r_x_le_b = conjonction_elim_droite(p4)      # (x,b)∈G
    p2 = conjonction_elim_gauche(p3)            # (x∈E et a≤x)
    r_c_le_x = conjonction_elim_droite(p3)      # (c,x)∈G
    r_x_in_E = conjonction_elim_gauche(p2)      # x∈E
    r_a_le_x = conjonction_elim_droite(p2)      # (a,x)∈G
    # reconstruire les memberships (associativité de l'axiome : (x∈E et ≤g) et ≤d)
    mab_re = conjonction_intro(conjonction_intro(r_x_in_E, r_a_le_x), r_x_le_b)  # = M_ab
    mcd_re = conjonction_intro(conjonction_intro(r_x_in_E, r_c_le_x), r_x_le_d)  # = M_cd
    in_ab_re = N.modus_ponens(mab_re, equivalence_arriere(ax_ab))   # x∈[a,b]
    in_cd_re = N.modus_ponens(mcd_re, equivalence_arriere(ax_cd))   # x∈[c,d]
    both_re = conjonction_intro(in_ab_re, in_cd_re)                 # x∈[a,b] et x∈[c,d]
    in_inter_re = N.modus_ponens(both_re, equivalence_arriere(inter_eq))  # x∈[a,b]∩[c,d]
    arriere = N.loi_deduction(rhs, in_inter_re)                     # rhs ⇒ x∈[a,b]∩[c,d]

    # ── équivalence + généralisation ─────────────────────────────────────────────
    eqv = conjonction_intro(avant, arriere)                        # x∈... ⇔ rhs
    return N.generalisation(x, eqv)


__all__ = [
    "cible_intersection_intervalles",
    "intersection_intervalles_fermes",
]
