# -*- coding: utf-8 -*-
"""§III.2.2 — R7' (étape 5) : 🎯🎯🎯 LE CRITÈRE C60 VÉRITABLE.

    existence_solution :  { bo, regle_dans_V }
        ⊢ (∃gcap)( func gcap ∧ dom gcap = E ∧ (∀z∈dom gcap)(gcap(z)=vh(gcap|seg z)) )

    (et l'UNICITÉ, unicite_globale, étape 4 : deux solutions sont le même graphe.)

C'est le critère C60 de Bourbaki (E III.18) avec la VRAIE équation de
récursion — la règle vh lit LA RESTRICTION f|seg(z), tout le passé — et non la
tabulation déposée.  L'existence est TÉMOIGNÉE : f := ⋃Dglob_rec(G,E,V), dont
les trois conjoints sont les étapes 1-3 (fonctionnalité par compatibilité,
domaine par la couverture totale, équation par le transfert).  Sous DEUX
hypothèses honnêtes seulement : le bon ordre, et la règle à valeurs dans V
(la donnée de Bourbaki : « T à valeurs dans un ensemble V »).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible, union_famille_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_capstone_rec import (
    Dglob_rec, compatibilite_Dglob,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_domaine_global import (
    dom_f_egal_E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_equation_globale import (
    equation_f,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def solution_f(vh, G="Gsr", e="Esr", V="Vval"):
    """{ bo, regle_dans_V } ⊢ est_solution_rec( ⋃Dglob_rec )   [2 hyps].

    Le témoin assemblé : fonctionnalité (étape 1), domaine (étape 2),
    équation (étape 3)."""
    vG, ve = _t(G), _t(e)
    D = Dglob_rec(vG, ve, V)
    f = union_famille(D)
    func_f = _cut(compatibilite_Dglob(vh, G, e, V), famille_compatible(D),
                  union_famille_fonctionnelle(D))
    res = conjonction_intro(conjonction_intro(func_f, dom_f_egal_E(vh, G, e, V)),
                            equation_f(vh, G, e, V))
    assert res.conclusion == est_solution_rec(f, vh, vG, ve), "solution_f : forme"
    return res


# @livre Ch.III §2.2 Crit.C60 | E III.18 L.24-33 | PDF p.121  (critère de récurrence
#   transfinie : existence — LA VRAIE ÉQUATION f(x)=T(f|seg x), pas la tabulation)
def existence_solution(vh, G="Gsr", e="Esr", V="Vval", g="gcap"):
    """🎯🎯🎯 LE CRITÈRE C60-VRAI (existence) :
       { bo, regle_dans_V }  ⊢  (∃g)( est_solution_rec(g, vh, G, E) ).

    Avec unicite_globale (étape 4), le couple existence+unicité EST le critère
    C60 de Bourbaki pour la récursion transfinie VÉRITABLE."""
    vG, ve = _t(G), _t(e)
    f = union_famille(Dglob_rec(vG, ve, V))
    sol = solution_f(vh, G, e, V)                           # {bo, règle} sol(f)
    cible_corps = est_solution_rec(var(g), vh, vG, ve)      # sol au nom gcap
    res = N.modus_ponens(sol, N.s5(cible_corps, f, g))      # (∃gcap) sol(gcap)
    assert res.conclusion == existe(g, cible_corps), "existence_solution : forme"
    assert len(res.hypotheses) == 2, "existence_solution : hyps ≠ 2"
    return res


__all__ = ["solution_f", "existence_solution"]
