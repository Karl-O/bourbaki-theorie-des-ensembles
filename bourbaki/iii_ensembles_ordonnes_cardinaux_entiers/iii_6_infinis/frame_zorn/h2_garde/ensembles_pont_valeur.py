# -*- coding: utf-8 -*-
"""§III.6.3 — H2 (β) : DU NIVEAU COUPLE AU NIVEAU VALEUR pour le recollement.

🎯 CIBLE : supprimer les hypothèses VALEUR de `union_chaine_est_bijection`
(dom(⋃φ)=US×US, injective_dans, image=US) en les DÉRIVANT du niveau couple,
déjà établi par l'amont.

    dom_union_egale :
        { recollement_domaine(𝔇, US×US),  dom(⋃𝔇) ⊂ US×US }
            ⊢ dom(⋃𝔇) = US×US

Les deux briques existaient séparément — `union_chaine_dom` (couverture du
domaine, niveau couple) et `couple_domaine_implique_dom_egale` (le pont
générique) — mais avec des LIANTS différents ; alpha_bridge les raccorde,
conformément à la leçon 15 (partir des théorèmes, ponter en α, ne jamais
reconstruire).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_surjective_frame import (
    union_chaine_dom, recollement_domaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_ponts_couple_valeur_surj import (
    domaine_couple, couple_domaine_implique_dom_egale,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def dom_union_egale(D="Dchaine", US="USchaine"):
    """🎯 { recollement_domaine(𝔇, US×US), dom(⋃𝔇) ⊂ US×US } ⊢ dom(⋃𝔇) = US×US.

    La couverture couple-niveau du recollement (union_chaine_dom) est
    exactement `domaine_couple` à un renommage de liants près ; le pont
    générique conclut à l'égalité des ensembles."""
    vD, vUS = _t(D), _t(US)
    U = union_famille(vD)
    Prod = E.produit(vUS, vUS)

    couverture = alpha_bridge(union_chaine_dom(vD, Prod), domaine_couple(U, Prod))
    pont = couple_domaine_implique_dom_egale(U, Prod)
    res = _cut(couverture, domaine_couple(U, Prod), pont)

    assert res.conclusion == egal(E.dom(U), Prod), "dom_union_egale : forme"
    assert set(res.hypotheses) == {recollement_domaine(vD, Prod),
                                   inclus(E.dom(U), Prod)}, \
        "dom_union_egale : hyps ≠ {recollement_domaine, inclusion}"
    return res


__all__ = ["dom_union_egale"]
