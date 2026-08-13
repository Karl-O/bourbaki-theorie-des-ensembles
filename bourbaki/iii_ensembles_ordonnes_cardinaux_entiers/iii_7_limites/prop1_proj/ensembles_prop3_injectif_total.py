"""§III.7.2 Prop. 3 — l'injectivité de g : de « à λ fixé » à « pour TOUT λ ».

────────────────────────────────────────────────────────────────────────────────
`prop3_g_injective_pointwise` (ensembles_limites_prop2_3_iii7) établit le cœur
de l'injectivité SOUS UN TÉMOIN cofinal : pour λ∈I et un α∈J majorant de λ,
g(x)=g(x') entraîne pr_λ x = pr_λ x'.  Le témoin α y est une hypothèse libre,
ce qui empêche de généraliser sur λ (α dépend de λ).

Ce module lève cet obstacle en substituant au témoin quelconque le **témoin
CANONIQUE** β(λ) := τ_y(y∈J et λ≤y) — dont l'existence et les propriétés sont
prouvées sans axiome du choix (`ensembles_temoin_cofinal`, ev. 163) :

  `coordonnees_egales_partout`
      ⊢ (∀λ)( λ∈I ⇒ pr_λ x = pr_λ x' )                            [4 hyps]

La prémisse est RÉDUITE à « λ∈I » : les trois conditions de témoin sont
FOURNIES sous cette seule garde — β(λ)∈J et λ≤β(λ) par `temoin_cofinal`,
β(λ)∈I par l'inclusion J⊂I que porte la cofinalité, et la prémisse COMPOSITE
((λ∈I et β(λ)∈I) et λ≤β(λ)) reconstruite par conjonction (c'est elle qui
résistait aux coupes naïves).  C'est donc exactement la forme attendue par
`extensionnalite_produit` : (∀ι)(ι∈I ⇒ pr_ι x = pr_ι x').
✅ `prop3_g_injective` conclut alors **x = x'** (4 hyps) en branchant
`extensionnalite_produit` (motif `cone_unicite` : paramètres BRUTS,
`_lim_dans_produit`, images-graphes) — l'INJECTIVITÉ de g est complète.
Les deux conditions `est_un_graphe` réclamées par l'extensionnalité sont
DÉDUITES et non supposées (`point_limite_est_graphe`, §7.1) : la prémisse de la
forme universelle se réduit ainsi à « x,x' ∈ lim← et g(x)=g(x') ».
⚠️ RESTE : conjoindre avec la surjectivité (`ensembles_prolongement_cofinal`)
en un énoncé unique « g bijective ».
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_prop2_3_iii7 import (
    prop3_g_injective_pointwise,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
    porter_aux_termes,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
    beta_cofinal, temoin_cofinal,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        if p.conclusion in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(p.conclusion, thm))
    return thm


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158  (injectivité de g : le cœur pointwise, porté au témoin canonique, se généralise à TOUT λ)
def coordonnees_egales_partout(jj="J", i="I", lam="lam", gterme=None,
                               formule_3=None):
    """{ g(x)=g(x'), x,x'∈lim←_I, J cofinale, … }
        ⊢ (∀λ)( λ∈I ⇒ pr_λ x = pr_λ x' ).                          [4 hyps].

    Passage du « λ fixé avec témoin » au « pour tout λ » en DEUX temps :

    1. le témoin cofinal quelconque est remplacé par le témoin CANONIQUE β(λ)
       (`porter_aux_termes`) : la dépendance en λ devient fonctionnelle au lieu
       de libre, ce qui est la condition pour pouvoir généraliser ;
    2. les trois conditions de témoin sont FOURNIES sous λ∈I :
         • β(λ)∈J et λ≤β(λ)  par `temoin_cofinal` ;
         • β(λ)∈I            par l'inclusion J⊂I que porte la cofinalité
                             (`cofinale_dans_inclusion`) ;
         • la prémisse COMPOSITE ((λ∈I et β(λ)∈I) et λ≤β(λ)) reconstruite par
           conjonction — c'est elle qui résistait aux coupes naïves.
    Il ne reste alors que λ∈I à décharger, d'où une prémisse de la forme EXACTE
    attendue par `extensionnalite_produit` : (∀ι)(ι∈I ⇒ pr_ι x = pr_ι x')."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        appartient,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, instancie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cofinal import (
        cofinale_dans_inclusion,
    )
    # ⚠️ La relation d'ordre doit être LA MÊME que celle de `temoin_cofinal`
    # (`_gleq` = « (u,v) ∈ Gleq ») : le défaut de `cofinale_dans_inclusion` est
    # « (u,v) ∈ G », d'où DEUX hypothèses « J cofinale » syntaxiquement
    # distinctes portées en parallèle.  Corrigé le 4 août 2026.
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _gleq,
    )
    inj = prop3_g_injective_pointwise(gterme=gterme, formule_3=formule_3)
    blam = beta_cofinal(_t(jj), var(lam))
    inj_t = porter_aux_termes(inj, {"a": blam})            # témoin → canonique
    tc = temoin_cofinal(jj, i, lam)                        # β(λ)∈J et λ≤β(λ)
    b_in_J, lam_leq_b = conjonction_elim_gauche(tc), conjonction_elim_droite(tc)
    h_lam = N.assume(appartient(var(lam), _t(i)))
    b_in_I = N.modus_ponens(b_in_J, instancie(
        cofinale_dans_inclusion(_gleq(), jj, i), blam))        # β(λ) ∈ I  (J⊂I)
    prem = conjonction_intro(conjonction_intro(h_lam, b_in_I), lam_leq_b)
    inj_c = _cut(inj_t, prem, b_in_I, b_in_J, lam_leq_b, tc)

    portantes = [h for h in inj_c.hypotheses if lam in libres_f(h)]
    assert len(portantes) == 1, \
        f"coordonnees_egales_partout : prémisse non réduite ({len(portantes)})"
    res = N.generalisation(lam, N.loi_deduction(portantes[0], inj_c))
    assert all(lam not in libres_f(h) for h in res.hypotheses), \
        "coordonnees_egales_partout : λ encore libre dans une hypothèse"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158  (INJECTIVITÉ de la canonique cofinale : g(x)=g(x') ⇒ x=x')
def prop3_g_injective(jj="J", i="I", lam="lam", Efam="E", f="f", leq=None,
                      x="xx", xp="xp", gterme=None, formule_3=None):
    """{ g(x)=g(x'), x,x'∈lim←_I, J cofinale, … } ⊢ x = x'.            [4 hyps].

    L'INJECTIVITÉ de g, complète.  Les coordonnées coïncident partout
    (`coordonnees_egales_partout`, prémisse réduite à λ∈I), les deux points
    sont dans le produit (`_lim_dans_produit`, depuis lim←⊂∏), donc
    l'extensionnalité du produit conclut.  Motif : `cone_unicite`.

    Les deux conditions `est_un_graphe` qu'exige l'extensionnalité ne sont plus
    SUPPOSÉES mais DÉDUITES de l'appartenance à la limite
    (`point_limite_est_graphe`, §7.1) : d'où 7 hypothèses et non 9, et surtout
    une prémisse universelle débarrassée de deux conjoints parasites.  Puis la
    correction du DOUBLE ENVELOPPAGE dans `prop3_g_injective_pointwise` a
    fusionné les deux écritures de « x ∈ lim← » : 7 → 5, puis l'unification
    de la relation d'ordre de la cofinalité : 5 → **4**.

    ⚠️ LIANT : `extensionnalite_produit` doit être construite AVEC LE MÊME
    index que celui du ∀ des coordonnées (ici « lam ») — sinon les deux
    formules ne s'apparient pas, bien qu'elles disent la même chose."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        appartient, egal,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, instancie,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_extensionnalite_produit import (
        extensionnalite_produit,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites as L,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _lim_dans_produit, _gleq,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_lim_graphe import (
        point_limite_est_graphe,
    )
    if leq is None:
        leq = _gleq()
    vE, vi, vx, vxp = _t(Efam), _t(i), var(x), var(xp)
    coords = coordonnees_egales_partout(jj, i, lam, gterme, formule_3)
    lim = L.lim_proj(vE, _t(f))
    h_x, h_xp = N.assume(appartient(vx, lim)), N.assume(appartient(vxp, lim))
    x_prod = _lim_dans_produit(Efam, f, leq, i, vx, h_x)
    xp_prod = _lim_dans_produit(Efam, f, leq, i, vxp, h_xp)
    g_x = point_limite_est_graphe(Efam, f, leq, i, vx, h_x)     # DÉDUIT, non supposé
    g_xp = point_limite_est_graphe(Efam, f, leq, i, vxp, h_xp)
    ext = instancie(instancie(N.generalisation("zextp", N.generalisation(
        "zext", extensionnalite_produit(vE, vi, var("zext"), var("zextp"), lam))),
        vxp), vx)
    hyp = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        x_prod, xp_prod), g_x), g_xp), coords)
    res = N.modus_ponens(hyp, ext)
    assert res.conclusion == egal(vx, vxp), "prop3_g_injective : ≠ (x = x')"
    assert len(res.hypotheses) == 4, \
        f"prop3_g_injective : hyps ≠ 4 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.6-13 | PDF p.158  (injectivité UNIVERSELLE : (∀x)(∀x')(… ⇒ x=x') — il ne reste que 2 hypothèses, sur J et le système)
def prop3_g_injective_universelle(jj="J", i="I", lam="lam", Efam="E", f="f",
                                  leq=None, x="xx", xp="xp", gterme=None,
                                  formule_3=None):
    """⊢ (∀x)(∀x')( (x,x' ∈ lim←_I  et  g(x)=g(x')) ⇒ x = x' ).       [2 hyps].

    L'injectivité de g sous forme UNIVERSELLE : on décharge en prémisse les
    trois hypothèses qui portent l'un des deux points, puis on généralise.  Ne
    subsistent que les deux hypothèses de contexte (J cofinale dans I, et le
    système projectif) — celles qui ne dépendent d'aucun point.

    ✅ La prémisse ne porte PLUS les conditions « x, x' sont des graphes » :
    depuis `point_limite_est_graphe` (§7.1) elles sont déduites de
    l'appartenance à la limite, déjà présente.  Il reste exactement les deux
    conjoints attendus — appartenance et égalité des images."""
    th = prop3_g_injective(jj, i, lam, Efam, f, leq, x, xp, gterme, formule_3)
    portantes = [h for h in th.hypotheses
                 if x in libres_f(h) or xp in libres_f(h)]
    imp = th
    for h in portantes:
        imp = N.loi_deduction(h, imp)
    res = N.generalisation(xp, N.generalisation(x, imp))
    assert all(x not in libres_f(h) and xp not in libres_f(h)
               for h in res.hypotheses),         "prop3_g_injective_universelle : un point reste libre dans une hypothèse"
    assert len(res.hypotheses) == 1,         f"prop3_g_injective_universelle : hyps ≠ 1 ({len(res.hypotheses)})"
    return res



REPORTES = [
    "Prop. 3 §III.7.2 — les DEUX SENS sont prouvés et quantifiés : INJECTIVITÉ "
    "(ponctuelle `prop3_g_injective`, 4 hyps ; UNIVERSELLE "
    "`prop3_g_injective_universelle`, 2 hyps) et SURJECTIVITÉ "
    "(`ensembles_prolongement_cofinal`, `prolongement_coherent_universel`).  "
    "L'ajustement de forme (a) — lemme « tout point de lim← est un graphe » — "
    "est RÉSOLU (`ensembles_lim_graphe`, CLOS) : la prémisse universelle ne "
    "porte plus de condition de graphe.  RESTE (b) : conjoindre les deux sens "
    "en un `est_bijection_de(g, lim←_I, lim←_J)` unique, ce qui suppose "
    "d'exhiber g comme FONCTION (func + dom) et non seulement comme "
    "application ponctuelle — c'est le pont manquant.",
]

__all__ = ["coordonnees_egales_partout", "prop3_g_injective",
           "prop3_g_injective_universelle", "REPORTES"]
