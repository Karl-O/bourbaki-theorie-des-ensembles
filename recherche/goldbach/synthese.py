# -*- coding: utf-8 -*-
"""Goldbach — LA SYNTHÈSE : les trois lignes du projet convergent sur un objet.

🎯 CIBLE de ce module :
    `composes_impliquent_goldbach()` :

        ⊢ [ (∀k) ( A(k) ∧ ¬premier₁(k) ) ⇒ rencontre(k) ]  ⇒  H

    « pour démontrer Goldbach, il suffit de démontrer que, pour tout `k`
    COMPOSÉ, les premiers ≤ 2k rencontrent leur miroir. »

C'est le point de convergence de l'arc : la forme CRIBLE (`crible`), la
RÉDUCTION aux composés (`composes`) et l'énoncé du dépôt (`enonces`) se
recollent sur un seul objet, `rencontre(k)`.

LES TROIS MAILLONS.
  · `gardee_implique_depot` — de la décomposition GARDÉE vers celle du dépôt.
    On jette les gardes `Fini` : c'est un affaiblissement, donc gratuit, et
    c'est ce qui raccorde l'arc gardé à l'énoncé historique.
  · `rencontre_des_premiers` — si `k` est premier, la rencontre a lieu, avec
    `m := k` et le témoin miroir `y := k` (car `2k = k + k`).
  · `crible_implique_decomposition` (dans `crible`) — de la rencontre à la
    décomposition gardée.

⚠️ CE QUE ÇA N'ÉTABLIT PAS. **Goldbach reste ouverte.** C'est une implication
dont l'hypothèse n'est pas démontrée — et cette hypothèse EST la conjecture,
restreinte aux composés. La valeur est de désigner **un seul but** à attaquer
au lieu de trois formulations éparses.

⚠️ HONNÊTETÉ SUR LA CLÔTURE. `rencontre_des_premiers` et la synthèse sont
« clos » au sens du noyau (zéro hypothèse) mais **relatifs à 2 axiomes ad hoc**
— ceux de la théorie dédiée `Crible-Goldbach` (`AXIOMES_CRIBLE` ci-dessous).
`N.axiome` rend un théorème sans hypothèse : `est_clos` ne veut donc PAS dire
« sans axiome ». Toutes les fonctions concernées passent par `atteste(th,
axiomes=AXIOMES_CRIBLE)`, qui l'affiche. Seul `gardee_implique_depot` est
libre de tout axiome ad hoc.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, et, impl, non, subst_f, var,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_intervalle import (
    membre_intervalle_entiers_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    zero_inf_egal_cardinal,
)
from outils_ia.arithmetique.lemmes_conjectures import prop2_sous_fini
from outils_ia.arithmetique.machine_num import NUM, fic_t
from outils_ia.conjectures.goldbach import est_premier
from outils_ia.conjectures.goldbach_reduction import hypothese_moities
from recherche.goldbach.composes import LIANT_W6, pont_alpha_premier
from recherche.goldbach.crible import (
    LIANT_M, crible_implique_decomposition, decomposition_gardee, membre_miroir,
    membre_premiers_bornes, miroir, premiers_bornes, rencontre,
)
from recherche.goldbach.enonces import (
    LIANT_K, antecedent_et_decomposition, hypothese_composes_rencontre,
)

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite
ZERO = NUM(0)

#: les axiomes ad hoc consommés par tout ce qui touche au crible
AXIOMES_CRIBLE = ("axiome_premiers_bornes", "axiome_miroir")


def _double(k=LIANT_K):
    return SC(var(k), var(k))


def gardee_implique_depot(k=LIANT_K, generalise=True):
    """⊢ DEC_ent(2k) ⇒ DEP(2k)   — et sa forme ∀ si `generalise`.  [CLOS]

    Le raccord entre l'arc GARDÉ (témoins contraints à être des entiers) et
    l'énoncé HISTORIQUE du dépôt, qui ne les contraint pas. On **jette** les
    gardes `Fini` : affaiblissement pur, donc gratuit.

    ⚠️ LA RÉCIPROQUE N'EST PAS DISPONIBLE, et ce n'est pas un oubli : c'est
    exactement le défaut de fidélité mesuré (`audit_fidelite`). Ne jamais
    substituer `DEC_ent` et `DEP` l'un à l'autre.

    ⚠️ SEULE FONCTION DU MODULE SANS AXIOME AD HOC : elle ne touche ni à la
    théorie du crible ni à aucun ensemble opaque."""
    DEC = decomposition_gardee(k)
    assert getattr(DEC, "tag", None) == "exists", "DEC_ent n'est pas un ∃"
    xp_e, inner_e = DEC.lieur, DEC.sous[0]
    xq_e, mat_e = inner_e.lieur, inner_e.sous[0]
    vp, vq = var(xp_e), var(xq_e)

    _, DEP = antecedent_et_decomposition(k)
    xp, inner_dep = DEP.lieur, DEP.sous[0]
    inner_p = subst_f(vp, xp, inner_dep)
    xq, mat_pq = inner_p.lieur, inner_p.sous[0]

    h = N.assume(mat_e)
    #   mat_e = ( (Fini p ∧ prem₁ p) ∧ (Fini q ∧ prem₂ q) ) ∧ 2k = p+q
    prem_p, prem_q, somme = _cd(_cg(_cg(h))), _cd(_cd(_cg(h))), _cd(h)
    c_b = conjonction_intro(conjonction_intro(prem_p, prem_q), somme)
    assert c_b.conclusion == subst_f(vq, xq, mat_pq), \
        "gardee ⇒ dépôt : matrice recomposée ≠ matrice substituée"
    #   route-témoin : INTERNE d'abord, externe ensuite (ordre imposé)
    dep = _mp(_mp(c_b, N.s5(mat_pq, vq, xq)), N.s5(inner_dep, vp, xp))
    assert dep.conclusion == DEP, "gardee ⇒ dépôt : conclusion ≠ DEP"

    imp_q = existe_elimination(N.loi_deduction(mat_e, dep), xq_e)
    th = existe_elimination(
        N.loi_deduction(inner_e, _mp(N.assume(inner_e), imp_q)), xp_e)
    assert th.conclusion == impl(DEC, DEP), "gardee ⇒ dépôt : forme"
    if generalise:
        th = N.generalisation(k, th)
    assert th.est_clos and not th.hypotheses, "gardee ⇒ dépôt : non clos"
    return th


def hypothese_premier_double(k=LIANT_K):
    """( Fini k ∧ premier₁(k) ) ∧ premier₂(k) — « k premier, dans les deux habits »."""
    vk = var(k)
    return et(et(est_fini(vk), est_premier(vk, d="d1", q="q1")),
              est_premier(vk, d="d2", q="q2"))


def rencontre_des_premiers(k=LIANT_K):
    """⊢ (∀k)[ ( Fini k ∧ premier₁(k) ) ∧ premier₂(k) ⇒ rencontre(k) ].

    LA BRANCHE FACILE, isolée. Si `k` est premier, la rencontre est réalisée
    par `m := k` : `k` est dans `P₂ₖ` (premier, et `k ≤ 2k` par la Prop. 2),
    et dans le miroir `Q₂ₖ` avec le témoin interne `y := k`, puisque
    `2k = k + k` — une simple réflexivité.

    [CLOS au sens du noyau, SOUS les 2 axiomes de la théorie du crible.]"""
    vk = var(k)
    M = _double(k)
    HYP = hypothese_premier_double(k)
    h = N.assume(HYP)
    fini_k, prem1_k, prem2_k = _cg(_cg(h)), _cd(_cg(h)), _cd(h)

    #   k ≤ 2k — ⚠️ prop2_sous_fini est CURRYFIÉ : deux `mp` ENCHAÎNÉS.
    p2 = instancie(instancie(instancie(
        N.generalisation("a", N.generalisation("b", N.generalisation(
            "c", prop2_sous_fini("a", "b", "c")))), vk), M), vk)
    le_k = _mp(N.reflexivite(M), _mp(fini_k, p2))
    card_k = _mp(fini_k, fic_t(vk))
    zero_le_k = _mp(card_k, N.loi_deduction(est_cardinal(vk),
                                            zero_inf_egal_cardinal(vk)))
    k_in_int = _mp(conjonction_intro(conjonction_intro(card_k, zero_le_k), le_k),
                   _cd(membre_intervalle_entiers_t(ZERO, M, vk)))
    k_in_P = _mp(conjonction_intro(conjonction_intro(fini_k, prem1_k), k_in_int),
                 _cd(membre_premiers_bornes(M, vk)))

    #   k ∈ Q₂ₖ avec le témoin y := k — on LIT le liant produit par le noyau
    impQ = _cd(membre_miroir(M, vk))
    exY = impQ.conclusion.sous[0].sous[0]
    assert getattr(exY, "tag", None) == "exists", "miroir : forme du ∃ inattendue"
    fourni = conjonction_intro(conjonction_intro(fini_k, prem2_k),
                              N.reflexivite(M))
    assert fourni.conclusion == subst_f(vk, exY.lieur, exY.sous[0]), \
        "rencontre des premiers : matrice du miroir ≠ attendue"
    k_in_Q = _mp(_mp(fourni, N.s5(exY.sous[0], vk, exY.lieur)), impQ)

    vm = var(LIANT_M)
    mat_renc = et(appartient(vm, premiers_bornes(M)), appartient(vm, miroir(M)))
    ex_m = _mp(conjonction_intro(k_in_P, k_in_Q), N.s5(mat_renc, vk, LIANT_M))
    assert ex_m.conclusion == rencontre(k), "rencontre des premiers : ≠ rencontre"
    th = N.generalisation(k, N.loi_deduction(HYP, ex_m))
    assert th.est_clos and not th.hypotheses, "rencontre des premiers : non clos"
    return th


def rencontre_implique_depot(k=LIANT_K):
    """⊢ rencontre(k) ⇒ DEP(2k)   (à `k` libre) — le maillon composé.

    Chaîne `crible_implique_decomposition` (rencontre ⇒ DEC_ent) puis
    `gardee_implique_depot` (DEC_ent ⇒ DEP)."""
    vk = var(k)
    RENC = rencontre(k)
    _, DEP = antecedent_et_decomposition(k)
    hR = N.assume(RENC)
    th = N.loi_deduction(RENC, _mp(_mp(hR, instancie(
        crible_implique_decomposition(k), vk)),
        gardee_implique_depot(k, generalise=False)))
    assert th.conclusion == impl(RENC, DEP), "rencontre ⇒ dépôt : forme"
    return th


def composes_impliquent_goldbach(k=LIANT_K):
    """🎯🎯 ⊢ HC_renc ⇒ H.   LE LIVRABLE DE L'ARC.

        HC_renc := (∀k)[ ( A(k) ∧ ¬premier₁(k) ) ⇒ rencontre(k) ]

    Disjonction des cas sur « `k` premier » :
      · **premier** — `rencontre_des_premiers` (le pont-α fournit le second
        habit de primalité) ;
      · **composé** — l'hypothèse `HC_renc` s'applique.
    Les deux branches donnent `rencontre(k)`, que `rencontre_implique_depot`
    convertit en `DEP(2k)`.

    ⚠️ NE FERME PAS GOLDBACH. `HC_renc` n'est pas démontré : c'est la
    conjecture restreinte aux composés. Ce qui est acquis, c'est qu'il n'y a
    plus qu'UN but à viser.

    [CLOS au sens du noyau, SOUS les 2 axiomes de la théorie du crible.]"""
    vk = var(k)
    H = hypothese_moities(k)
    a, _ = antecedent_et_decomposition(k)
    HC = hypothese_composes_rencontre(k)
    P1k = est_premier(vk, d="d1", q="q1")
    renc_dep = rencontre_implique_depot(k)

    hHC, hA = N.assume(HC), N.assume(a)
    fini_k = _cg(_cg(hA))

    #   branche « k premier » : ⚠️ le pont-α est prouvé à `wgg6` LIBRE
    hp = N.assume(P1k)
    prem2_k = _mp(hp, instancie(N.generalisation(LIANT_W6,
                                                 pont_alpha_premier()), vk))
    renc_p = _mp(conjonction_intro(conjonction_intro(fini_k, hp), prem2_k),
                 instancie(rencontre_des_premiers(k), vk))
    br_p = N.loi_deduction(P1k, _mp(renc_p, renc_dep))

    #   branche « k composé » : l'hypothèse s'applique
    hnp = N.assume(non(P1k))
    renc_c = _mp(conjonction_intro(hA, hnp), instancie(hHC, vk))
    br_c = N.loi_deduction(non(P1k), _mp(renc_c, renc_dep))

    corps = N.generalisation(
        k, N.loi_deduction(a, cas(tiers_exclu(P1k), br_p, br_c)))
    assert corps.conclusion == H, "synthèse : le corps ne redonne pas H"
    th = N.loi_deduction(HC, corps)
    assert th.est_clos and not th.hypotheses, "synthèse : non clos"
    assert th.conclusion == impl(HC, H), "synthèse : forme"
    return th


__all__ = [
    "AXIOMES_CRIBLE", "gardee_implique_depot", "hypothese_premier_double",
    "rencontre_des_premiers", "rencontre_implique_depot",
    "composes_impliquent_goldbach",
]
