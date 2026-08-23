# -*- coding: utf-8 -*-
"""§III.6.3 — L'ARGUMENT D'EXTENSION (E.III.48), ÉTAPES (2) ET (3).

🎯 CIBLES (sous l'hypothèse de l'absurde « 𝔟 < Card E », 𝔟 := Card S₀) :

    b_le_complement  : { S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<Card E } ⊢ 𝔟 ≤ Card(E∖S₀)
    existe_u_cadre   : … ⊢ (∃Ucadre)( Ucadre ⊂ E∖S₀  et  Card Ucadre = 𝔟 )

Bourbaki : « De l'hypothèse 𝔟 < 𝔞 il résulte que Card(E∖F) > 𝔟 ; il existe donc
une partie Y ⊂ E∖F équipotente à F. »  Les deux moitiés :

  • `complement_grand` donne la forme NÉGATIVE ¬( Card(E∖S₀) ≤ 𝔟 ) ; la
    COMPARABILITÉ des cardinaux (inconditionnelle, Zermelo) la retourne en la
    forme POSITIVE 𝔟 ≤ Card(E∖S₀) par syllogisme disjonctif — chez Bourbaki
    « A ou B » est un assemblage brut, pas une implication, d'où le passage par
    `disj_syll_thm` plutôt qu'un modus ponens direct ;
  • `existe_sous_ensemble_cardinal` réalise alors ce cardinal comme une PARTIE
    de E∖S₀ : c'est le U de l'extension, à éliminer en témoin LOCAL Ucadre.

Hypothèses honnêtes portées (jamais postulées) : S₀⊂E et 𝔟<Card E (fournies par
la portée du maximal et par l'absurde) et l'ABSORPTION 𝔟+𝔟=𝔟 — cette dernière
étant elle-même DÉRIVÉE au maximal (`ensembles_absorption`).  Le transport, lui,
est CLOS en amont (GAP B, `existe_sous_ensemble_cardinal_transporte`).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, existe, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, disj_syll_thm,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_sup_cardinal import (
    comparabilite_cardinaux_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import (
    est_cardinal_de_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_extension import (
    complement_grand,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.realisation_segment.ensembles_transport_sous_ensemble import (
    existe_sous_ensemble_cardinal_transporte,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _reste(E_set, S):
    """Le terme E ∖ S₀ (le « complément du maximal »)."""
    return E.difference(_t(E_set), _t(S))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.28-29 | PDF p.151
#   (« il résulte que Card(E∖F) > 𝔟 » — forme POSITIVE, via comparabilité)
def b_le_complement(E_set="E", S="S0"):
    """{ S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<Card E } ⊢ 𝔟 ≤ Card(E∖S₀)      [3 hyps honnêtes].

    `complement_grand` réfute « Card(E∖S₀) ≤ 𝔟 » ; la comparabilité (CLOSE)
    donne « Card(E∖S₀) ≤ 𝔟  ou  𝔟 ≤ Card(E∖S₀) », dont le premier membre tombe."""
    vS = _t(S)
    cS, cR = cardinal(vS), cardinal(_reste(E_set, S))
    petit, grand = inf_egal_card(cR, cS), inf_egal_card(cS, cR)

    refute = complement_grand(E_set, S)                      # ⊢ ¬( Card(E∖S₀) ≤ 𝔟 )
    compar = comparabilite_cardinaux_terme(cR, cS)           # ⊢ petit ou grand  [CLOS]
    res = N.modus_ponens(refute,
                         N.modus_ponens(compar, disj_syll_thm(petit, grand)))

    assert res.conclusion == grand, "b_le_complement : forme"
    assert len(res.hypotheses) == 3, "b_le_complement : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "b_le_complement : VACUOUS"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.29-30 | PDF p.151
#   (« il existe donc une partie Y ⊂ E∖F équipotente à F »)
def existe_u_cadre(E_set="E", S="S0", U="Ucard", V="Ucadre"):
    """{ S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<Card E } ⊢
           (∃Ucadre)( Ucadre ⊂ E∖S₀  et  Card Ucadre = 𝔟 )   [3 hyps].

    Le U de l'extension.  Son témoin sera éliminé LOCALEMENT (la conclusion de
    l'argument, ⊥, ne le mentionne pas), ce qui rend l'élimination licite.

    ⚠️ On emploie `existe_sous_ensemble_cardinal_transporte` (CLOS, 0 hypothèse)
    et NON `existe_sous_ensemble_cardinal`, qui portait le transport en résidu
    honnête : le dépôt avait déjà fermé ce trou (GAP B), en réalisant c ≤ A
    directement au lieu de transporter une partie de Card A vers A."""
    vS = _t(S)
    cS = cardinal(vS)
    R = _reste(E_set, S)
    Vn = V if isinstance(V, str) else V.nom

    ante = et(est_cardinal(cS), inf_egal_card(cS, cardinal(R)))
    donnees = conjonction_intro(est_cardinal_de_cardinal(vS),   # est_cardinal(𝔟)  [CLOS]
                               b_le_complement(E_set, S))       # 𝔟 ≤ Card(E∖S₀)
    assert donnees.conclusion == ante, "existe_u_cadre : antécédent inattendu"
    res = N.modus_ponens(donnees,
                         existe_sous_ensemble_cardinal_transporte(cS, R, V))

    cible = existe(Vn, et(inclus(var(Vn), R), egal(cardinal(var(Vn)), cS)))
    assert res.conclusion == cible, "existe_u_cadre : forme"
    assert res.conclusion not in res.hypotheses, "existe_u_cadre : VACUOUS"
    return res


__all__ = ["b_le_complement", "existe_u_cadre"]
