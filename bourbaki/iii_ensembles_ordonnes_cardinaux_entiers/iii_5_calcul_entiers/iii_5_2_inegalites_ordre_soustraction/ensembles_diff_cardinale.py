# -*- coding: utf-8 -*-
"""§III.5.2 — LA DIFFÉRENCE CARDINALE PAR CONSTRUCTION (réparation R-12, étape 2).

🎯 CIBLES :

    diff_cardinale(a, b)             le terme  τc.( est_cardinal(c) et a = b + c )
    diff_cardinale_garde(a, b)  :    { est_cardinal(a), est_cardinal(b), b ≤ a }
                                       ⊢ est_cardinal( a − b )
    diff_cardinale_equation(a, b) :  mêmes gardes ⊢ a = b + (a − b)

POURQUOI CE TERME EXISTE, et pourquoi `diff_somme` ne suffit pas (R-12).

`diff_somme(a,b) = τc.( a = b + c )` porte un τ sur une formule dont les témoins
ne sont PAS tous des cardinaux : `somme_cardinale_binaire(b,c) = Card(b ⊔ c)` ne
contraint en rien `c`, et tout ensemble équipotent à un témoin valable en est un.
Le τ en choisit un arbitrairement, donc `est_cardinal(τc.(a = b+c))` n'est PAS
dérivable.  Or `est_fini(x) = est_cardinal(x) et x ≠ x+1` : la finitude de la
différence est alors hors de portée, et c'est précisément ce que l'universel NU
de `fini_downward` — hypothèse NON SATISFAITE — masquait dans §III.5.6.  Une
hypothèse fausse ne manque pas seulement de justification : elle TRAVAILLE.

La réparation ne consiste donc pas à prouver un lemme manquant, mais à rendre la
différence cardinale **par construction** : on met la garde DANS le τ.

⚠️ CE MODULE AJOUTE ; il ne modifie ni ne remplace `diff_somme`, dont les
appelants historiques restent inchangés.

FIDÉLITÉ.  Bourbaki définit b − a en E III.37 (L.17-20) sur des ENTIERS, où la
question ne se pose pas — un entier est un cardinal par définition.  Le τ gardé
est donc PLUS PROCHE du livre que le τ nu, qui admet des témoins non cardinaux
que Bourbaki n'envisage jamais.  L'écart est consigné.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, existe, tau,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    existe_complement_depuis_inf_egal, _cardinal_est_son_cardinal_t,
)

_C = "cdif"


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _corps(a, b, c=_C):
    """Le CORPS du τ : est_cardinal(c) et a = b + c."""
    va, vb = _t(a), _t(b)
    return et(est_cardinal(var(c)), egal(va, somme_cardinale_binaire(vb, var(c))))


# @livre Ch.III §5.2 Def.- | E III.37 L.17-20 | PDF p.140
#   (b − a, ici sous sa forme GARDÉE : le témoin est déclaré cardinal)
def diff_cardinale(a, b, c=_C):
    """a − b := τc.( est_cardinal(c) et a = b + c ).

    La différence, cardinale PAR CONSTRUCTION.  À comparer à `diff_somme`, dont
    le τ ne porte que l'équation et admet donc des témoins non cardinaux."""
    return tau(c, _corps(a, b, c))


def _existentiel_garde(a, b, c=_C):
    """{ est_cardinal(a), est_cardinal(b), b ≤ a } ⊢ (∃c)( est_cardinal(c) et a = b+c ).

    La Prop. 13 RENFORCÉE conclut sur `Card a` ; sous `est_cardinal(a)` on
    réécrit `Card a` en `a` par Leibniz — S6 appliqué à la formule ENTIÈRE,
    donc à travers le ∃, ce qui est licite : le liant du motif est frais."""
    va, vb = _t(a), _t(b)
    base = existe_complement_depuis_inf_egal(vb, va, c, fort=True)
    ex_card = N.modus_ponens(conjonction_intro(N.assume(est_cardinal(vb)),
                                               N.assume(inf_egal_card(vb, va))), base)

    #  Card a = a, puis réécriture SOUS le ∃
    card_a = N.modus_ponens(N.assume(est_cardinal(va)), _cardinal_est_son_cardinal_t(va))
    motif = existe(c, et(est_cardinal(var(c)),
                         egal(var("wdif"), somme_cardinale_binaire(vb, var(c)))))
    res = N.modus_ponens(ex_card, equivalence_avant(
        N.modus_ponens(card_a, N.s6(cardinal(va), va, "wdif", motif))))
    assert res.conclusion == existe(c, _corps(a, b, c)), "_existentiel_garde : forme"
    return res


def _temoin(a, b, c=_C):
    """{ gardes } ⊢ est_cardinal(a−b) et a = b + (a−b).   [le τ, par existe_temoin]."""
    ex = _existentiel_garde(a, b, c)
    return N.modus_ponens(ex, N.existe_temoin(_corps(a, b, c), c))


# @livre Ch.III §5.2 Def.- | E III.37 L.17-20 | PDF p.140
def diff_cardinale_garde(a, b, c=_C):
    """🎯 { est_cardinal(a), est_cardinal(b), b ≤ a } ⊢ est_cardinal( a − b ).

    LA BRIQUE QUE R-12 RÉCLAMAIT, et qui était indérivable pour `diff_somme`.
    Avec le τ gardé elle ne coûte qu'une élimination de conjonction : la garde
    voyage DANS le terme."""
    res = conjonction_elim_gauche(_temoin(a, b, c))
    assert res.conclusion == est_cardinal(diff_cardinale(a, b, c)), \
        "diff_cardinale_garde : forme"
    return res


# @livre Ch.III §5.2 Def.- | E III.37 L.17-20 | PDF p.140
def diff_cardinale_equation(a, b, c=_C):
    """🎯 { est_cardinal(a), est_cardinal(b), b ≤ a } ⊢ a = b + ( a − b ).

    L'équation caractéristique, celle que `diff_somme` fournissait déjà — mais
    ici elle vient AVEC la garde, du même `existe_temoin`."""
    va, vb = _t(a), _t(b)
    res = conjonction_elim_droite(_temoin(a, b, c))
    assert res.conclusion == egal(va, somme_cardinale_binaire(
        vb, diff_cardinale(a, b, c))), "diff_cardinale_equation : forme"
    return res


__all__ = ["diff_cardinale", "diff_cardinale_garde", "diff_cardinale_equation"]
