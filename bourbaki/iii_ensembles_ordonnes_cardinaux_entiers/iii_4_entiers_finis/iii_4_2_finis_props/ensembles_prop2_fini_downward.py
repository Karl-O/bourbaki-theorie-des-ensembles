# -*- coding: utf-8 -*-
"""§III.4.2 — PROPOSITION 2 (gardée) : un CARDINAL inférieur à un entier est un entier.

🎯 CIBLE (prop2_fini_downward) :
    ⊢ est_cardinal(a) ⇒ (∀x)( (a ≤ x et Fini x) ⇒ Fini a ).

« Soit n un entier.  Tout cardinal 𝔞 tel que 𝔞 ≤ n est un entier. »  C'est la
downward-closure de Fini, GARDÉE par est_cardinal (la forme universelle NUE
(∀a)(∀x) est FAUSSE pour a non-cardinal — cf. docstring de recurrence_vraie).

DÉCHARGE (3 mouvements) : `fini_downward_garde_thm` (recurrence_vraie, la
récurrence C61 « vraie ») porte {est_cardinal(a), predecesseur_fini_universel} ;
pfu se décharge par `predecesseur_fini_universel_preuve` (Prop. 2 §III.5, CLOSE) ;
la garde passe en antécédent (loi de déduction).

Ce théorème était l'ÉNONCÉ-CIBLE REPORTÉ `prop2_cardinal_inf_n_est_entier`
(finis_props l.412) — il est désormais DÉRIVÉ, sous la seule garde est_cardinal.
Conséquence immédiate (contraposée) : un cardinal INFINI n'est ≤ à aucun entier.

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, pourtout, impl, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import (
    fini_downward_garde_thm,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    predecesseur_fini_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def prop2_fini_downward_cible(a="a", x="x"):
    va, vx = var(a), var(x)
    return impl(est_cardinal(va),
                pourtout(x, impl(et(inf_egal_card(va, vx), est_fini(vx)),
                                 est_fini(va))))


# @livre Ch.III §4.2 Prop.2 | E III.31 L.29-32 | PDF p.134
def prop2_fini_downward(a="a", x="x", c="c", b="b", k="kpred"):
    """🎯 ⊢ est_cardinal(a) ⇒ (∀x)( (a ≤ x et Fini x) ⇒ Fini a ).   (Prop. 2, CLOS.)"""
    g = fini_downward_garde_thm(a, x, c, b)
    pfu = predecesseur_fini_universel(k=k)
    if pfu in g.hypotheses:
        g = N.modus_ponens(predecesseur_fini_universel_preuve(k=k),
                           N.loi_deduction(pfu, g))
    res = N.loi_deduction(est_cardinal(var(a)), g)
    assert res.conclusion == prop2_fini_downward_cible(a, x), \
        f"prop2_fini_downward : conclusion inattendue\n{res.conclusion}"
    assert not res.hypotheses, "prop2_fini_downward : hypothèses résiduelles"
    return res


__all__ = ["prop2_fini_downward", "prop2_fini_downward_cible"]
