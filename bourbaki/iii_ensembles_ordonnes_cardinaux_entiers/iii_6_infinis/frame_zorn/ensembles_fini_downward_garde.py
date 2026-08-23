# -*- coding: utf-8 -*-
"""§III.4.2 (réparation, consommée en §III.6.3) — DOWNWARD-CLOSURE DE Fini, GARDÉE.

🎯 CIBLE :

    fini_downward_cardinal(A, tX) :
        { predecesseur_fini_universel }  ⊢  ( Card A ≤ tX  et  Fini tX ) ⇒ Fini(Card A)

⚠️ POURQUOI CE MODULE EXISTE (cf. ANOMALIES 2026-08-23).  `fini_downward_thm`
livre le même énoncé, mais sous DEUX hypothèses closes dont l'une — la
∀∀-clôture NUE de `cardinal_pas_entre` — n'est PAS satisfaite : le dépôt ne
prouve que sa forme GARDÉE, `est_cardinal(b) ⇒ cardinal_pas_entre(b,c)`
(`cardinal_pas_entre_inconditionnel`, CLOS, 0 hypothèse), et la version nue est
fausse dès que b n'est pas un cardinal — alors `Fini(b)` est faux par
définition tandis que `b ≤ c` peut tenir.  Le noyau reste sound (la dérivation
est correcte), mais tout théorème portant cette hypothèse est VRAI et VIDE.

La réparation consiste à passer par `fini_downward_garde_thm`, qui prouve la
downward-closure POUR UN CARDINAL sous la seule `predecesseur_fini_universel`
(Prop. 2 §III.5) — une hypothèse VRAIE, simplement pas encore prouvée.  La
garde `est_cardinal` se décharge sans effort là où on l'applique : l'aval
n'instancie jamais qu'à des `Card(...)`, et `est_cardinal_de_cardinal` en est
la preuve close.

On échange donc une hypothèse FAUSSE contre une hypothèse VRAIE-NON-PROUVÉE,
et un théorème vide contre un théorème conditionnel légitime.

Ce module AJOUTE ; il ne remplace ni ne modifie `fini_downward_thm`, dont les
appelants historiques restent inchangés.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, impl, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import (
    est_cardinal_de_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import (
    fini_downward_garde_thm,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §4.2 Prop.3 | E III.31 L.9-12 | PDF p.134
#   (« tout cardinal inférieur à un cardinal fini est fini » — forme GARDÉE)
def fini_downward_garde_universel(a="a", x="x", c="c", b="b"):
    """{ predecesseur_fini_universel } ⊢ (∀a)( est_cardinal(a) ⇒ (∀x) fini_downward(a,x) ).

    `fini_downward_garde_thm` sous forme ∀-close et RÉUTILISABLE : la garde est
    passée en antécédent AVANT la généralisation sur a — sans quoi celle-ci
    serait illicite, « a » étant libre dans l'hypothèse `est_cardinal(a)`."""
    va = _t(a)
    garde = est_cardinal(va)
    base = fini_downward_garde_thm(a, x, c, b)       # {est_cardinal(a), pfu}
    assert garde in base.hypotheses, \
        "fini_downward_garde_universel : garde absente (le module amont a changé)"
    res = N.generalisation(a, N.loi_deduction(garde, base))
    assert a not in libres_f(res.conclusion), "fini_downward_garde_universel : a libre"
    return res


def fini_downward_cardinal(A, tX, a="a", x="x", c="c", b="b"):
    """🎯 { predecesseur_fini_universel } ⊢
           ( Card A ≤ tX  et  Fini tX ) ⇒ Fini( Card A ).

    La forme que l'aval consomme réellement (cf. `z_infini_derive`, qui
    instancie à a := Card S₀ et x := Card Z).  La garde `est_cardinal(Card A)`
    est déchargée par `est_cardinal_de_cardinal`, close ; et
    `predecesseur_fini_universel` l'est aussi depuis le 2026-08-23 — le dépôt le
    PROUVE (Prop. 2 §III.5), il n'était pas branché.  Le résultat est donc CLOS.

    C'est le REMPLAÇANT sûr de `fini_downward_thm` instancié : même conclusion,
    mais sans l'hypothèse non satisfaite (ANOMALIES 2026-08-23)."""
    vA, vX = _t(A), _t(tX)
    cA = cardinal(vA)
    gen = fini_downward_garde_universel(a, x, c, b)
    sous_garde = instancie(gen, cA)                  # est_cardinal(Card A) ⇒ (∀x)…
    tous_x = N.modus_ponens(est_cardinal_de_cardinal(vA), sous_garde)
    res = instancie(tous_x, vX)

    #  ⚠️ 2026-08-23 : `predecesseur_fini_universel` n'est PAS un résidu — le dépôt
    #  le PROUVE (Prop. 2 §III.5, `predecesseur_fini_universel_preuve`, CLOS, 7,7 s).
    #  Il n'était simplement pas branché.  On le décharge ici, à la source, pour que
    #  toute la chaîne en aval en hérite.
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    pfu = predecesseur_fini_universel_preuve()
    if pfu.conclusion in res.hypotheses:
        res = N.modus_ponens(pfu, N.loi_deduction(pfu.conclusion, res))

    cible = impl(et(inf_egal_card(cA, vX), est_fini(vX)), est_fini(cA))
    assert res.conclusion == cible, "fini_downward_cardinal : forme"
    assert res.conclusion not in res.hypotheses, "fini_downward_cardinal : VACUOUS"
    return res


__all__ = ["fini_downward_garde_universel", "fini_downward_cardinal"]
