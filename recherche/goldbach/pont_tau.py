# -*- coding: utf-8 -*-
"""Goldbach — LE PONT ∃ ↔ τ : la conjecture SANS quantificateur existentiel.

🎯 CIBLE de ce module :
    `forme_canonique()` :  ⊢ H ⟺ H_τ          [les DEUX sens, CLOS]

où `H` est la forme « moitiés » de la conjecture (`enonces`) et

    H_τ := (∀k)[ A(k) ⇒ ( premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q ) ]

avec **T et Q des termes NOMMÉS**, pas des variables liées :

    T := τp( (∃q)( premier₁(p) ∧ premier₂(q) ∧ k+k = p+q ) )
    Q := τq( premier₁(T) ∧ premier₂(q) ∧ k+k = T+q )

L'IDÉE. Le critère E I.32 du livre dit qu'un énoncé existentiel est équivalent
à sa propre instance au témoin canonique : `(∃x)R ⇒ (τx(R)|x)R` d'un côté
(`existe_temoin`), `(T|x)R ⇒ (∃x)R` de l'autre (`s5`, pour n'importe quel `T`).
En l'appliquant deux fois — au ∃ externe puis au ∃ interne — on remplace le
double existentiel de Goldbach par deux **objets désignés**. La conjecture
devient : *« ces deux termes-là sont premiers et somment à 2k »*.

⚠️ CE QUE ÇA N'ÉTABLIT PAS. Rien, sur Goldbach. C'est un changement de FORME,
à contenu arithmétique nul : `H_τ` est exactement aussi ouverte que `H`, donc
que la conjecture (le dépôt démontre `H ⟺ goldbach()`). L'intérêt est
instrumental : un but sans `∃` s'attaque par les organes équationnels, un but
avec `∃` demande un témoin. C'est un changement d'**adresse**, pas de statut.

⚠️ LE SENS RETOUR EST GRATUIT, L'ALLER NE L'EST PAS. `s5` vaut pour TOUS
termes : le retour est donc un **générateur** (`route_temoin`), qui transporte
l'obligation vers n'importe quelle stratégie de témoins — gloutonne, jumelle,
canonique. Seul l'aller exige les τ-termes canoniques. Le générateur ne
démontre aucune arithmétique : il déplace l'obligation, il ne la décharge pas.

⚠️ PIÈGE DES LIANTS, mesuré. On ne devine JAMAIS le nom d'un liant : le noyau
α-renomme. Tous les prélèvements lisent `.lieur` sur la formule produite, et
`temoins_canoniques` est le SEUL endroit qui descend dans la structure.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, et, impl, pourtout, subst_f, tau, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    diff_somme, existe_complement_somme,
)
from outils_ia.conjectures.goldbach import est_premier
from outils_ia.conjectures.goldbach_reduction import hypothese_moities
from recherche.goldbach.enonces import LIANT_K, antecedent_et_decomposition

_mp = N.modus_ponens

#: liant du complément dans `diff_somme` — frais vis-à-vis de p/q
LIANT_C = "cgb"


def double(k=LIANT_K):
    """Le terme 2k := k + k."""
    return SC(var(k), var(k))


def temoins_canoniques(k=LIANT_K):
    """→ (T, Q, pieces) — LE seul prélèvement structurel du module.

    `pieces` est le dictionnaire des morceaux nécessaires aux routes :
    `DEP` (le double ∃), `inner` (le ∃ interne), `mat_T` (sa matrice avec
    p := T), `C` (la conclusion sans ∃), `xp`/`xq` (les liants RÉELS).

    Les liants sont LUS sur les formules produites par le noyau, jamais
    devinés — un α-renommage rendrait toute reconstruction fausse."""
    _, DEP = antecedent_et_decomposition(k)
    assert getattr(DEP, "tag", None) == "exists", "DEP n'est pas un ∃"
    xp, inner = DEP.lieur, DEP.sous[0]

    T = tau(xp, inner)
    inner_T = subst_f(T, xp, inner)
    assert getattr(inner_T, "tag", None) == "exists", "∃ interne introuvable"
    xq, mat_T = inner_T.lieur, inner_T.sous[0]

    Q = tau(xq, mat_T)
    C = subst_f(Q, xq, mat_T)
    return T, Q, {"DEP": DEP, "inner": inner, "inner_T": inner_T,
                  "mat_T": mat_T, "C": C, "xp": xp, "xq": xq}


def route_temoin(T, Q, k=LIANT_K):
    """GÉNÉRATEUR — pour TOUS termes T, Q :

        ⊢ (∀k)[ ( premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q )  ⇒  DEP(2k) ]

    Deux `s5` : témoin INTERNE d'abord (q := Q), externe ensuite (p := T).
    L'ordre est imposé — l'inverse ne typerait pas.

    ⚠️ Ce théorème est CLOS et ne prouve RIEN d'arithmétique : il transporte
    l'obligation « T et Q sont premiers et somment à 2k » vers la conjecture.
    Choisir T et Q, c'est choisir une stratégie ; la décharger reste à faire."""
    _, _, p = temoins_canoniques(k)
    inner, xp, xq = p["inner"], p["xp"], p["xq"]

    inner_T = subst_f(T, xp, inner)
    assert getattr(inner_T, "tag", None) == "exists", "route : ∃ interne perdu"
    mat_T = inner_T.sous[0]
    C = subst_f(Q, inner_T.lieur, mat_T)

    r1 = N.s5(mat_T, Q, inner_T.lieur)             # C ⇒ (∃q) mat_T
    r2 = N.s5(inner, T, xp)                        # (∃q) mat_T ⇒ DEP
    th = N.generalisation(
        k, N.loi_deduction(C, _mp(_mp(N.assume(C), r1), r2)))
    assert th.est_clos and not th.hypotheses, "route_temoin : non clos"
    return th


def pont_tau_aller(k=LIANT_K):
    """⊢ (∀k)[ DEP(2k) ⇒ ( premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q ) ].  [CLOS]

    Deux `existe_temoin` (E I.32) : le ∃ externe donne p := T, puis le ∃
    interne — déjà instancié en T — donne q := Q."""
    return N.generalisation(k, _implication_aller(k))


def _implication_aller(k=LIANT_K):
    """L'aller SANS généralisation (la forme dont `forme_canonique` a besoin)."""
    _, _, p = temoins_canoniques(k)
    DEP, inner, mat_T = p["DEP"], p["inner"], p["mat_T"]
    a1 = N.existe_temoin(inner, p["xp"])           # DEP ⇒ (∃q) mat_T
    assert a1.conclusion == impl(DEP, p["inner_T"]), "aller : 1er témoin"
    a2 = N.existe_temoin(mat_T, p["xq"])           # (∃q) mat_T ⇒ C
    assert a2.conclusion == impl(p["inner_T"], p["C"]), "aller : 2e témoin"
    return N.loi_deduction(DEP, _mp(_mp(N.assume(DEP), a1), a2))


def pont_tau_retour(k=LIANT_K):
    """⊢ (∀k)[ ( premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q ) ⇒ DEP(2k) ].  [CLOS]

    C'est `route_temoin` appliqué aux témoins canoniques — le même théorème
    sous un autre nom. Il n'existe qu'une preuve, pas quatre."""
    T, Q, _ = temoins_canoniques(k)
    return route_temoin(T, Q, k)


def _implication_retour(k=LIANT_K):
    """Le retour SANS généralisation."""
    _, _, p = temoins_canoniques(k)
    T, Q = tau(p["xp"], p["inner"]), tau(p["xq"], p["mat_T"])
    r1 = N.s5(p["mat_T"], Q, p["xq"])
    r2 = N.s5(p["inner"], T, p["xp"])
    return N.loi_deduction(p["C"], _mp(_mp(N.assume(p["C"]), r1), r2))


def hypothese_canonique(k=LIANT_K):
    """H_τ := (∀k)[ A(k) ⇒ ( premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q ) ].

    AUCUN `∃` au-delà de ceux enfouis dans `premier`/`Fini`/`Card`."""
    a, _ = antecedent_et_decomposition(k)
    _, _, p = temoins_canoniques(k)
    return pourtout(k, impl(a, p["C"]))


def forme_canonique(k=LIANT_K):
    """🎯 → (H ⇒ H_τ, H_τ ⇒ H), les deux CLOS et sans hypothèse.

    Sous `H` et sous `A(k)` : on instancie `H` en `k`, on décharge `A(k)`, et
    l'on transporte par l'aller ; la réciproque emprunte le retour. La
    généralisation vient APRÈS la déduction — jamais généraliser une variable
    libre dans une hypothèse vivante."""
    H = hypothese_moities(k)
    H_tau = hypothese_canonique(k)
    a, DEP = antecedent_et_decomposition(k)
    vk = var(k)

    def _sens(source, cible, transport, attendu):
        hs, ha = N.assume(source), N.assume(a)
        milieu = _mp(_mp(ha, instancie(hs, vk)), transport)
        corps = N.generalisation(k, N.loi_deduction(a, milieu))
        assert corps.conclusion == cible, "forme_canonique : corps ≠ cible"
        th = N.loi_deduction(source, corps)
        assert th.est_clos and not th.hypotheses, "forme_canonique : non clos"
        assert th.conclusion == impl(source, cible), attendu
        return th

    directe = _sens(H, H_tau, _implication_aller(k), "H ⇒ H_τ attendu")
    reciproque = _sens(H_tau, H, _implication_retour(k), "H_τ ⇒ H attendu")
    return directe, reciproque


# ══════════════════════════════════════════════════════════════════════════════
#  TÉMOINS DÉFINIS — des STRATÉGIES pour le générateur `route_temoin`
# ══════════════════════════════════════════════════════════════════════════════

def plus_grand_premier(borne, p="pmax", r="rmax", d1="d1", q1="q1",
                       d3="d3", q3="q3"):
    """Le terme « le plus grand premier ≤ borne » (τ, sans preuve d'existence).

    ⚠️ Liants `d3`/`q3` pour la primalité SOUS le ∀ interne : deux primalités
    imbriquées sur les mêmes liants entreraient en collision."""
    vp, vr = var(p), var(r)
    return tau(p, et(et(est_premier(vp, d=d1, q=q1), inf_egal_card(vp, borne)),
                     pourtout(r, impl(et(est_premier(vr, d=d3, q=q3),
                                         inf_egal_card(vr, borne)),
                                      inf_egal_card(vr, vp)))))


def somme_du_temoin(T, k=LIANT_K):
    """⊢ (∀k)[ ( card T ∧ card 2k ∧ T ≤ 2k ) ⇒ 2k = T + (2k − T) ].  [CLOS]

    LE PREMIER RÉSULTAT DE LA FAMILLE AVEC DU CONTENU RÉEL : pour un témoin
    défini `T`, la clause de somme n'est plus une obligation — elle est
    DÉCHARGÉE par la Proposition 13 §III.5 (existence du complément) suivie du
    τ-axiome. Reste alors la seule vraie question : « T est-il premier, et son
    complément aussi ? »"""
    M = double(k)
    Qb = diff_somme(M, T, LIANT_C)
    th_ex = existe_complement_somme(T, M, LIANT_C)
    H12 = et(et(est_cardinal(T), est_cardinal(M)), inf_egal_card(T, M))
    assert th_ex.conclusion.sous[0].sous[0] == H12, \
        "somme_du_temoin : antécédent de la Prop. 13 non littéral"
    th_tau = N.existe_temoin(egal(M, SC(T, var(LIANT_C))), LIANT_C)
    somme = _mp(_mp(N.assume(H12), th_ex), th_tau)
    assert somme.conclusion == egal(M, SC(T, Qb)), "somme_du_temoin : conclusion"
    th = N.generalisation(k, N.loi_deduction(H12, somme))
    assert th.est_clos and not th.hypotheses, "somme_du_temoin : non clos"
    return th


__all__ = [
    "LIANT_C", "double", "temoins_canoniques", "route_temoin",
    "pont_tau_aller", "pont_tau_retour", "hypothese_canonique",
    "forme_canonique", "plus_grand_premier", "somme_du_temoin",
]
