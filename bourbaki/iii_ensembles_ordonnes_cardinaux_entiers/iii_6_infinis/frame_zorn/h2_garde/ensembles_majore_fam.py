# -*- coding: utf-8 -*-
"""§III.6.3 — H2 : LE TÉMOIN-MAJORANT AVEC LA RÉUNION DE FAMILLE.

🎯 CIBLE (m' := ( ⋃S(C), ⋃𝔇(C) ) où 𝔇(C) = pr₂⟨C⟩) :

    majore_fam :  { p∈C, p∈𝔉(E), m'∈𝔉(E) }  ⊢  ( p, m' ) ∈ Γ𝔉(E)

C'est `temoin_majore_membre` avec la seconde composante du témoin changée :
⋃𝔇 (réunion de la famille des graphes) au lieu de ⋃φ (seconde projection de
la chaîne).  L'unique différence de preuve est l'inclusion pr₂(p)⊂⋃𝔇, que
`inclus_dans_union_fam` fournit — ce qui évite entièrement l'égalité des deux
unions, restée en chantier (leçon 15).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
    projection_premiere, projection_seconde,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_donne_inclus_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import (
    frame_ordre_membre_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine, inclus_dans_union_fam,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def temoin_fam(C):
    """m'(C) := ( ⋃S(C), ⋃𝔇(C) ) — le témoin-majorant version famille."""
    vC = _t(C)
    return E.couple(union_premiere(vC), union_famille(famille_de_chaine(vC)))


def majore_fam(E_set="E", C="Cch", p="pmemb"):
    """🎯 { p∈C, p∈𝔉(E), m'∈𝔉(E) } ⊢ ( p, m' ) ∈ Γ𝔉(E)   [3 hyps honnêtes].

    Patron de temoin_majore_membre : l'ordre d'extension demande les deux
    inclusions de projections ; la première vient de l'amont, la seconde de
    inclus_dans_union_fam."""
    vE, vC, vp = _t(E_set), _t(C), _t(p)
    US = union_premiere(vC)
    UD = union_famille(famille_de_chaine(vC))
    m = E.couple(US, UD)
    Fr = frame_pair(vE)
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)

    incl1 = membre_donne_inclus_premiere(C, p)              # {p∈C} ⊢ pr₁p⊂⋃S
    incl2 = inclus_dans_union_fam(C, p)                     # {p∈C} ⊢ pr₂p⊂⋃𝔇

    #   identification des projections du couple-témoin (formes PROUVÉES)
    pp = N.generalisation("u", N.generalisation("v", projection_premiere("u", "v")))
    e1 = instancie(instancie(pp, US), UD)                   # pr₁(m')=⋃S
    ps = N.generalisation("u", N.generalisation("v", projection_seconde("u", "v")))
    e2 = instancie(instancie(ps, US), UD)                   # pr₂(m')=⋃𝔇
    pr1m = e1.conclusion.termes[0]
    pr2m = e2.conclusion.termes[0]

    #   transport des inclusions vers les projections du témoin
    eq1 = N.modus_ponens(e1, symetrie(pr1m, US))            # ⋃S = pr₁(m')
    incl1_m = N.modus_ponens(incl1, equivalence_avant(N.modus_ponens(
        eq1, N.s6(US, pr1m, "wmf", inclus(pr1p, var("wmf"))))))
    eq2 = N.modus_ponens(e2, symetrie(pr2m, UD))            # ⋃𝔇 = pr₂(m')
    incl2_m = N.modus_ponens(incl2, equivalence_avant(N.modus_ponens(
        eq2, N.s6(UD, pr2m, "wmf", inclus(pr2p, var("wmf"))))))

    h_pFr = N.assume(appartient(vp, Fr))                    # p∈𝔉  [HONNÊTE]
    h_mFr = N.assume(appartient(m, Fr))                     # m'∈𝔉 [HONNÊTE]
    corps = conjonction_intro(conjonction_intro(
        conjonction_intro(h_pFr, h_mFr), incl1_m), incl2_m)
    res = N.modus_ponens(corps, equivalence_arriere(
        frame_ordre_membre_t(vE, vp, m)))

    assert res.conclusion == appartient(E.couple(vp, m), _ordre(vE)), \
        "majore_fam : forme"
    assert len(res.hypotheses) == 3, "majore_fam : hyps ≠ 3"
    return res


def _ordre(vE):
    """Γ𝔉(E) — le graphe d'ordre d'extension du frame."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
        frame_ordre,
    )
    return frame_ordre(vE)


__all__ = ["temoin_fam", "majore_fam"]
