# -*- coding: utf-8 -*-
"""§III.5.2 — LA DIFFÉRENCE CARDINALE EST FINIE (réparation R-12, étape 3).

🎯 CIBLES :

    diff_cardinale_inf_egal(a, b) : { card a, card b, b ≤ a } ⊢ ( a − b ) ≤ a
    diff_cardinale_fini(a, b)     : { card a, card b, b ≤ a, Fini a }
                                        ⊢ Fini( a − b )

CE QUE CE MODULE RÉPARE.  `_diff_est_fini` (§III.5.6) conclut `Fini(diff_somme)`
en instanciant l'universel **NU** de `fini_downward` — une hypothèse NON
SATISFAITE (ANOMALIES 2026-08-23).  Tout ce qui en dépend est donc VRAI ET VIDE,
et les deux modules de division euclidienne avec.

Le recâblage était impossible tant que la différence n'était pas cardinale : la
version GARDÉE de la downward-closure exige `est_cardinal` de son argument, et
`est_cardinal(diff_somme)` n'est pas dérivable (R-12).  Avec `diff_cardinale`,
la garde est acquise (`diff_cardinale_garde`) et le recâblage devient direct.

⚠️ LA BORNE ( a − b ) ≤ a NE DEMANDE PLUS DE MACHINERIE.  `_diff_inf_egal`
passait par l'invariance de ≤ par équipotence ; ici l'équation caractéristique
`a = b + (a−b)` la donne immédiatement : la différence s'injecte dans la somme
dont elle est un terme.  Il ne reste qu'à traverser le pont ENSEMBLE → CARDINAL,
`inf_egal_somme_droite` concluant au niveau des ensembles.

⚠️ `predecesseur_fini_universel` n'est PAS un résidu : le dépôt la PROUVE
(Prop. 2 §III.5) et on la décharge ici, comme le fait `fini_downward_cardinal`.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie,
)

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire, somme_disjointe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_cardinaux_bornes_somme import (
    inf_egal_somme_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_structural_discharge import (
    _set_le_eq_card, _le_trans_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_fini_downward_garde import (
    fini_downward_garde_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.soustraction_cardinale.ensembles_diff_cardinale import (
    diff_cardinale, diff_cardinale_garde, diff_cardinale_equation, _C,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §5.2 Prop.- | E III.37 L.21-24 | PDF p.140   (b − a ≤ b)
def diff_cardinale_inf_egal(a="adf", b="bdf", c=_C):
    """🎯 { card a, card b, b ≤ a } ⊢ ( a − b ) ≤ a.

    Directement depuis l'équation caractéristique : (a−b) s'injecte dans
    b ⊔ (a−b), dont le cardinal EST b + (a−b) = a.  Trois pas, là où la version
    `diff_somme` demandait l'invariance de ≤ par équipotence."""
    va, vb = _t(a), _t(b)
    d = diff_cardinale(va, vb, c)
    disj = somme_disjointe(vb, d)
    somme = somme_cardinale_binaire(vb, d)

    #  (a−b) ≤ b ⊔ (a−b)  [ENSEMBLE]  puis  ≤ Card(b ⊔ (a−b)) = b + (a−b)
    bas = N.modus_ponens(conjonction_intro(inf_egal_somme_droite(vb, d),
                                           _set_le_eq_card(disj)),
                         _le_trans_t(d, disj, somme))
    assert bas.conclusion == inf_egal_card(d, somme), \
        "diff_cardinale_inf_egal : le pont ENSEMBLE → CARDINAL a échoué"

    #  réécriture par l'équation : b + (a−b) = a
    #  ⚠️ sens ARRIÈRE : S6 sous « a = b+(a−b) » donne (d ≤ a) ⇔ (d ≤ b+(a−b)),
    #  et c'est le membre DROIT qu'on tient.  Vérifié par comparaison des
    #  formules avant toute retouche de la preuve (LEÇON 18).
    eq = diff_cardinale_equation(va, vb, c)          # a = b + (a−b)
    res = N.modus_ponens(bas, equivalence_arriere(N.modus_ponens(
        eq, N.s6(va, somme, "wdfi", inf_egal_card(d, var("wdfi"))))))
    assert res.conclusion == inf_egal_card(d, va), "diff_cardinale_inf_egal : forme"
    return res


# @livre Ch.III §5.6 Demo.- | E III.39 L.12-19 | PDF p.142   (a − b fini)
def diff_cardinale_fini(a="adf", b="bdf", c=_C):
    """🎯🎯 { card a, card b, b ≤ a, Fini a } ⊢ Fini( a − b ).

    LE REMPLAÇANT SÛR de `_diff_est_fini`, qui instanciait l'universel NU de
    `fini_downward` — hypothèse NON SATISFAITE.  Ici la version GARDÉE suffit,
    sa garde `est_cardinal(a−b)` étant fournie par la construction du τ.

    `predecesseur_fini_universel` est déchargée sur place : le dépôt la PROUVE
    (Prop. 2 §III.5), elle n'était pas branchée."""
    va, vb = _t(a), _t(b)
    d = diff_cardinale(va, vb, c)

    gen = fini_downward_garde_universel()            # (∀x)(card x ⇒ (∀y) fini_downward)
    sous_garde = instancie(gen, d)
    tous = N.modus_ponens(diff_cardinale_garde(va, vb, c), sous_garde)
    inst = instancie(tous, va)                       # ((a−b) ≤ a et Fini a) ⇒ Fini(a−b)

    res = N.modus_ponens(conjonction_intro(diff_cardinale_inf_egal(va, vb, c),
                                           N.assume(est_fini(va))), inst)

    #  `predecesseur_fini_universel` : PROUVÉE par le dépôt, pas un résidu.
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    pfu = predecesseur_fini_universel_preuve()
    if pfu.conclusion in res.hypotheses:
        res = N.modus_ponens(pfu, N.loi_deduction(pfu.conclusion, res))

    assert res.conclusion == est_fini(d), "diff_cardinale_fini : forme"
    assert res.conclusion not in res.hypotheses, "diff_cardinale_fini : VACUOUS"
    attendu = {est_cardinal(va), est_cardinal(vb), inf_egal_card(vb, va),
               est_fini(va)}
    assert set(res.hypotheses) == attendu, \
        "diff_cardinale_fini : hypothèses résiduelles inattendues (%d)" % len(res.hypotheses)
    return res


__all__ = ["diff_cardinale_inf_egal", "diff_cardinale_fini"]
