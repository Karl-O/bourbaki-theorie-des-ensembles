# -*- coding: utf-8 -*-
"""§III.6.3 — 🎯 LE RECOLLEMENT D'UNE CHAÎNE EST UNE FRAME-PAIR.

    recollement_de_chaine : { chaine(Γ𝔉,𝔉,C), C ≠ ∅ } ⊢ ( ⋃S(C), ⋃𝔇(C) ) ∈ 𝔉(E)

L'aboutissement des ONZE données (R-13) : `frame_de_recollement` les réclamait
toutes, elles sont maintenant toutes DÉRIVÉES du seul garde « C chaîne non vide ».
Le recollement d'une chaîne est donc une frame-pair sans qu'aucune propriété
élémentaire ne soit postulée.

⚠️ Trois des onze doivent être demandées avec le liant « z » (le défaut de
`inclus`) : leurs liants naturels — xdc, zdu, wiu — ne coïncideraient pas avec
ceux qu'attend `frame_de_recollement`.  Vérifié par comparaison AVANT le
branchement, ce qui a évité trois essais (LEÇON 18).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, non, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine, membres_famille_injectifs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_donnees_chaine import (
    us_inclus_E, us_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_pont_valeur import (
    frame_de_recollement,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_famille_dirigee import (
    famille_dirigee_de_chaine, union_dirigee_injective,
    famille_compatible_de_chaine, union_compatible_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_dom_union import (
    dom_union_inclus_carre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_img_union import (
    img_union_inclus_us,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_surj_union import (
    surj_union_us,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_dom_couvrant import (
    dom_couvrant,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def les_onze_donnees(E_set="E", C="Cch"):
    """Les onze théorèmes qui closent les onze données du recollement (R-13).

    Les trois inclusions sont demandées avec le liant « z » pour coïncider avec
    ce qu'attend `frame_de_recollement`."""
    return [dom_couvrant(E_set, C), union_dirigee_injective(E_set, C),
            famille_compatible_de_chaine(E_set, C), famille_dirigee_de_chaine(E_set, C),
            membres_famille_injectifs(E_set, C), union_compatible_fonctionnelle(E_set, C),
            surj_union_us(E_set, C), us_inclus_E(E_set, C, x="z"),
            dom_union_inclus_carre(E_set, C, z="z"), img_union_inclus_us(E_set, C, w="z"),
            us_infini(E_set, C)]


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151
#   (« la réunion d'une chaîne de prolongements est encore un prolongement »)
def recollement_de_chaine(E_set="E", C="Cch"):
    """🎯🎯 { chaine(Γ𝔉,𝔉,C), C ≠ ∅ } ⊢ ( ⋃S(C), ⋃𝔇(C) ) ∈ 𝔉(E).   [2 hyps].

    Les onze données de `frame_de_recollement` déchargées par les onze
    théorèmes ; il ne subsiste que le GARDE de Bourbaki, « C chaîne NON VIDE »,
    qui est exactement l'antécédent de `donnees_recollement`."""
    vE, vC = _t(E_set), _t(C)
    D, US = famille_de_chaine(vC), union_premiere(vC)
    base = frame_de_recollement(D, US, E_set)
    for th in les_onze_donnees(E_set, C):
        assert th.conclusion in base.hypotheses, \
            "recollement_de_chaine : donnée hors des hypothèses (liant ?)"
        base = N.modus_ponens(th, N.loi_deduction(th.conclusion, base))

    assert base.conclusion == appartient(E.couple(US, union_famille(D)),
                                         frame_pair(vE)), \
        "recollement_de_chaine : forme"
    #  Il reste EXACTEMENT le garde de Bourbaki : « C est une chaîne NON VIDE ».
    #  Le second conjoint vient de `us_infini` — c'est là que « C non vide » sert
    #  vraiment : une chaîne vide n'a aucun membre dont hériter l'infinité.
    attendu = {chaine(frame_ordre(vE), frame_pair(vE), vC, "xmaj", "y", "z"),
               non(egal(vC, E.VIDE))}
    assert set(base.hypotheses) == attendu, \
        "recollement_de_chaine : hypothèses résiduelles inattendues"
    return base


__all__ = ["les_onze_donnees", "recollement_de_chaine"]
