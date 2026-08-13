# -*- coding: utf-8 -*-
"""Goldbach — LA RÉDUCTION AUX INSTANCES COMPOSÉES.

🎯 CIBLE de ce module :
    `equivalence_composes()` :  ⊢ HC ⟺ H          [les DEUX sens, CLOS]

où `H` est la forme « moitiés » et `HC` la même restreinte aux `k` composés :

    HC := (∀k)[ ( A(k) ∧ ¬premier₁(k) ) ⇒ DEP(2k) ]

L'IDÉE, en une phrase : **le cas `k` premier se démontre tout seul**. Si `k`
est premier, alors `2k = k + k` est déjà une décomposition en deux premiers —
le témoin est `k` lui-même. Il ne reste donc à démontrer que les `k` composés,
et la conjecture est *équivalente* à sa propre restriction.

Le sens `H ⇒ HC` est un affaiblissement pur (trois lignes). Le sens `HC ⇒ H`
est le contenu : disjonction des cas sur « `k` est premier », branche premier
close par la famille des doubles, branche composé par l'hypothèse.

⚠️ CE QUE ÇA N'ÉTABLIT PAS. `HC` n'est pas démontré : c'est une réduction, pas
une preuve. Goldbach reste ouverte. Ce qui est acquis est que l'on peut
travailler sur les composés sans rien perdre — et c'est certifié, plus
seulement dit.

⚠️ DEUX HABITS α DE `est_premier`. `decomposition` place `premier₁` (liants
`d1`/`q1`) au premier témoin et `premier₂` (`d2`/`q2`) au second. Un même `k`
premier doit donc porter LES DEUX habits pour servir de témoin jumeau — d'où
le pont `pont_alpha_premier`, **paramétré dans les deux sens** (la symétrie du
crible a besoin de `premier₂ ⇒ premier₁`), et sa variante gardée
`pont_alpha_premier_ent`.

⚠️ NE PAS CONFONDRE avec le pont NIÉ. `¬premier₂ ⇒ ¬premier₁` n'est PAS
disponible et ne se déduit pas de ce qui précède : une implication ne se
contrapose pas gratuitement ici, il faudrait la démontrer séparément. `HC`
porte bien `¬premier₁`, et c'est délibéré.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, et, existe, non, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    cas, conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
    instancie, tiers_exclu,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from outils_ia.arithmetique.machine_num import existe_temoin_verifie
from outils_ia.conjectures.goldbach import est_premier
from outils_ia.conjectures.goldbach_borne import decomposition
from outils_ia.conjectures.goldbach_reduction import hypothese_moities
from recherche.goldbach.enonces import (
    LIANT_K, antecedent_et_decomposition, hypothese_composes_decomposition,
)

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite

#: liants de travail, frais vis-à-vis de p/q et de k
LIANT_W6 = "wgg6"
LIANT_W2 = "wgg2b"


#: les deux habits α de `est_premier` imposés par `decomposition`
HABIT_1 = ("d1", "q1")
HABIT_2 = ("d2", "q2")


def pont_alpha_premier(w=LIANT_W6, source=HABIT_1, cible=HABIT_2):
    """⊢ premier[source](w) ⇒ premier[cible](w)   — le changement d'habit α.

    Les deux formules ne diffèrent QUE par les noms des liants `d`/`q`, mais
    ce sont deux formules distinctes pour le noyau : il faut le démontrer.

    ⚠️ LE PONT EST CONTRAVARIANT. Le `∃q` de `divise_propre` vit dans
    l'ANTÉCÉDENT de la clause `(∀d)(… ⇒ …)` : on assume donc le `∃` de la
    CIBLE, on l'élimine, et l'on RÉINTRODUIT celui de la SOURCE au témoin de
    la cible. C'est le sens inverse de l'intuition.

    ⚠️ PARAMÉTRÉ, ET C'EST NÉCESSAIRE (12 août). La version d'origine était
    câblée sur `d1/q1 ⇒ d2/q2`. Or la symétrie du crible a besoin de l'AUTRE
    sens : le partenaire d'un point de la rencontre sort du miroir en habit 2
    et doit entrer dans `P` en habit 1. Plutôt que d'écrire une seconde preuve
    identique aux noms près, on paramètre — les deux ponts sont le même
    théorème. (Le pont NIÉ `¬premier₂ ⇒ ¬premier₁` reste, lui, indisponible :
    ce n'est pas la même chose, et `HC` porte bien `¬premier₁`.)"""
    assert source != cible, "pont-α : source et cible doivent différer"
    ds, qs = source
    dc, qc = cible
    vw, vdc = var(w), var(dc)
    P_src = est_premier(vw, d=ds, q=qs)
    P_cbl = est_premier(vw, d=dc, q=qc)

    h1 = N.assume(P_src)
    ne1, clause1 = _cg(h1), _cd(h1)
    inst_dc = instancie(clause1, vdc)          # antécédent en qs, conclusion ok

    X_c = et(est_fini(vdc), divise_propre(vdc, vw, q=qc))
    hxc = N.assume(X_c)
    fin_dc, div_qc = _cg(hxc), _cd(hxc)

    #   pont-α sur le ∃ de la divisibilité : qc ⟶ qs
    m_qc = et(est_fini(var(qc)), egal(vw, produit_cardinal_binaire(vdc, var(qc))))
    mat_qs = et(est_fini(var(qs)), egal(vw, produit_cardinal_binaire(vdc, var(qs))))
    ex_qs = existe_temoin_verifie(N.assume(m_qc), mat_qs, var(qc), qs)
    div_qs = _mp(div_qc, existe_elimination(N.loi_deduction(m_qc, ex_qs), qc))

    ccl = _mp(conjonction_intro(fin_dc, div_qs), inst_dc)
    corps = N.generalisation(dc, N.loi_deduction(X_c, ccl))
    P_th = conjonction_intro(ne1, corps)
    assert P_th.conclusion == P_cbl, "pont-α : la conclusion n'est pas la cible"
    th = N.loi_deduction(P_src, P_th)
    assert th.est_clos and not th.hypotheses, "pont-α : non clos"
    return th


def pont_alpha_premier_ent(w=LIANT_W6, source=HABIT_1, cible=HABIT_2):
    """⊢ premier_ent[source](w) ⇒ premier_ent[cible](w)  — version GARDÉE.

    Même pont, sous la garde `Fini` : c'est la forme dont le crible a besoin,
    puisque ses deux ensembles sont bâtis sur `premier_ent` et non sur
    `est_premier` nu."""
    vw = var(w)
    from recherche.goldbach.crible import premier_ent
    src = premier_ent(vw, d=source[0], q=source[1])
    h = N.assume(src)
    th = N.loi_deduction(src, conjonction_intro(
        _cg(h), _mp(_cd(h), pont_alpha_premier(w, source, cible))))
    assert th.conclusion.sous[1] == premier_ent(vw, d=cible[0], q=cible[1]), \
        "pont-α gardé : conclusion ≠ premier_ent[cible]"
    assert th.est_clos and not th.hypotheses, "pont-α gardé : non clos"
    return th


def famille_doubles(w=LIANT_W2):
    """⊢ (∀w)[ ( (premier₁(w) ∧ premier₂(w)) ∧ Fini w ) ⇒ DEP(2w) ].  [CLOS]

    LA FAMILLE {2p} : si `w` est premier (dans les deux habits), alors
    `2w = w + w` est une décomposition — témoin JUMEAU `p = q = w`, et la
    clause de somme est une simple réflexivité.

    ⚠️ Ce résultat n'existait QUE dans le scratchpad. Sans lui la réduction
    aux composés est irreproductible : c'est la brique qui ferme la branche
    « k premier »."""
    vw = var(w)
    M = SC(vw, vw)
    P1, P2 = est_premier(vw, d="d1", q="q1"), est_premier(vw, d="d2", q="q2")
    H = et(et(P1, P2), est_fini(vw))

    h = N.assume(H)
    fait = conjonction_intro(conjonction_intro(_cg(_cg(h)), _cd(_cg(h))),
                            N.reflexivite(M))
    #   matrices ÉCRITES, jamais devinées : on remonte le double ∃ à la main
    vp, vq = var("pgb"), var("qgb")
    mat_q = et(et(est_premier(vw, d="d1", q="q1"),
                  est_premier(vq, d="d2", q="q2")),
               egal(M, SC(vw, vq)))
    ex_q = existe_temoin_verifie(fait, mat_q, vw, "qgb")
    mat_p = existe("qgb", et(et(est_premier(vp, d="d1", q="q1"),
                                est_premier(vq, d="d2", q="q2")),
                             egal(M, SC(vp, vq))))
    ex_p = existe_temoin_verifie(ex_q, mat_p, vw, "pgb")
    assert ex_p.conclusion == decomposition(M), "famille_doubles : ≠ DEP(2w)"
    th = N.generalisation(w, N.loi_deduction(H, ex_p))
    assert th.est_clos and not th.hypotheses, "famille_doubles : non clos"
    return th


def composes_implique_moities(k=LIANT_K):
    """🎯 ⊢ HC ⇒ H.   [CLOS]  — LE SENS QUI PORTE LE CONTENU.

    Sous `HC` et sous `A(k)`, disjonction des cas sur `premier₁(k)` :
      · **k premier** — le pont-α lui donne le second habit, la famille des
        doubles conclut `DEP(2k)` avec le témoin jumeau `k` ;
      · **k composé** — `HC` s'applique directement.
    Les deux branches concluent la même formule : `cas` les recolle.

    ⚠️ ORDRE OBLIGATOIRE : décharger `A(k)` par `loi_deduction` AVANT de
    généraliser sur `k` — `k` est libre dans l'hypothèse vivante."""
    GG2P = famille_doubles()
    GG6 = pont_alpha_premier()
    H = hypothese_moities(k)
    a, _ = antecedent_et_decomposition(k)
    HC = hypothese_composes_decomposition(k)
    vk = var(k)
    P1k = est_premier(vk, d="d1", q="q1")

    hHC, hA = N.assume(HC), N.assume(a)
    fini_k = _cg(_cg(hA))

    #   branche « k premier » : le témoin jumeau
    hp = N.assume(P1k)
    #   ⚠️ GG6 est prouvé à `wgg6` LIBRE : re-généraliser puis instancier.
    p2k = _mp(hp, instancie(N.generalisation(LIANT_W6, GG6), vk))
    dec_p = _mp(conjonction_intro(conjonction_intro(hp, p2k), fini_k),
                instancie(GG2P, vk))
    br_p = N.loi_deduction(P1k, dec_p)

    #   branche « k composé » : l'hypothèse s'applique
    hnp = N.assume(non(P1k))
    dec_c = _mp(conjonction_intro(hA, hnp), instancie(hHC, vk))
    br_c = N.loi_deduction(non(P1k), dec_c)

    corps = N.generalisation(
        k, N.loi_deduction(a, cas(tiers_exclu(P1k), br_p, br_c)))
    assert corps.conclusion == H, "composes ⇒ moitiés : le corps ne redonne pas H"
    th = N.loi_deduction(HC, corps)
    assert th.est_clos and not th.hypotheses, "composes ⇒ moitiés : non clos"
    return th


def moities_implique_composes(k=LIANT_K):
    """⊢ H ⇒ HC.   [CLOS]  — l'affaiblissement, trois lignes.

    Restreindre la conjecture aux `k` composés est évidemment une conséquence
    de la conjecture. Aucun cas, aucun pont-α."""
    H = hypothese_moities(k)
    a, _ = antecedent_et_decomposition(k)
    HC = hypothese_composes_decomposition(k)
    vk = var(k)
    ac = et(a, non(est_premier(vk, d="d1", q="q1")))

    hH, hAC = N.assume(H), N.assume(ac)
    dec = _mp(_cg(hAC), instancie(hH, vk))
    corps = N.generalisation(k, N.loi_deduction(ac, dec))
    assert corps.conclusion == HC, "moitiés ⇒ composes : le corps ne redonne pas HC"
    th = N.loi_deduction(H, corps)
    assert th.est_clos and not th.hypotheses, "moitiés ⇒ composes : non clos"
    return th


def equivalence_composes(k=LIANT_K):
    """🎯🎯 → (HC ⇒ H, H ⇒ HC), les deux CLOS.

    « La conjecture de Goldbach est équivalente à sa restriction aux entiers
    composés » — démontré, pas seulement plausible."""
    return composes_implique_moities(k), moities_implique_composes(k)


__all__ = [
    "LIANT_W6", "LIANT_W2", "HABIT_1", "HABIT_2", "pont_alpha_premier",
    "pont_alpha_premier_ent", "famille_doubles",
    "composes_implique_moities", "moities_implique_composes",
    "equivalence_composes",
]
