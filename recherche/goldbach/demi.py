# -*- coding: utf-8 -*-
"""Goldbach — LA MOITIÉ SUFFIT : chercher dans [0,k] au lieu de [0,2k].

🎯 CIBLE de ce module :

    ⊢ (∀k)[ Fini k ⇒ ( rencontre(k) ⟺ (∃m)( m ∈ P₂ₖ ∩ Q₂ₖ ∧ m ≤ k ) ) ]

DEUX RÉSULTATS, l'un arithmétique, l'autre sur le crible.

**Le demi-intervalle** est un fait d'arithmétique cardinale, sans rapport avec
les nombres premiers : d'une paire d'entiers sommant à `2k`, l'un des deux est
toujours `≤ k`. Il est démontré ici parce que c'est ici qu'on en a eu besoin,
mais il ne parle que de sommes.

**La restriction de la rencontre** l'assemble avec la symétrie du crible
(`symetrie.py`) : les solutions vont par paires sommant à `2k`, et l'un des
deux membres de chaque paire tombe dans la première moitié. Donc s'il existe
une décomposition, il en existe une dont le petit facteur est `≤ k`.

POURQUOI ÇA COMPTE. La carte avait refermé le comptage brut (§7) et
l'équationnel (§8), en désignant chaque fois la **répartition** de `P₂ₖ` comme
la seule information manquante. La symétrie en était le premier fait ; la
restriction au demi-intervalle en est la conséquence exploitable — elle divise
par deux l'espace où une solution peut se cacher.

⚠️ CE QUE ÇA N'ÉTABLIT PAS. Rien sur l'EXISTENCE d'une solution. Diviser par
deux un espace de recherche infini en `k` ne rapproche d'aucune preuve :
Goldbach reste ouverte. Ce qui est acquis est une équivalence certifiée de
plus, et une contrainte structurelle exacte.

⚠️ LA GARDE `Fini` N'EST PAS DE LA PRUDENCE. La preuve du demi-intervalle passe
par la simplification additive, **fausse** pour les cardinaux infinis :
`ℵ₀ + 1 = ℵ₀ + 2` sans que `1 = 2`. Sans la garde, l'énoncé serait FAUX, pas
seulement indémontrable.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, et, existe, impl, pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    cas, conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
    instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_cardinale_commutative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from outils_ia.arithmetique.machine_num import fic_t
from recherche.goldbach.crible import (
    LIANT_K, LIANT_M, membre_premiers_bornes, miroir, premiers_bornes, rencontre,
)

_mp = N.modus_ponens
_cg, _cd = conjonction_elim_gauche, conjonction_elim_droite


def _double(k=LIANT_K):
    return SC(var(k), var(k))


# ══════════════════════════════════════════════════════════════════════════════
#  LE DEMI-INTERVALLE — fait d'arithmétique cardinale PURE
# ══════════════════════════════════════════════════════════════════════════════

#: liants de travail du demi-intervalle, frais vis-à-vis de m, y, p, q
LIANT_DEMI_K, LIANT_DEMI_M, LIANT_DEMI_MP = "kdi", "mdi", "mpdi"
LIANT_DEMI_D = "ddi"


def hypothese_demi(k=LIANT_DEMI_K, m=LIANT_DEMI_M, mp_=LIANT_DEMI_MP):
    """( Fini k ∧ Fini m ∧ Fini m' ) ∧ 2k = m + m'."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    vk, vm, vmp = var(k), var(m), var(mp_)
    return et(et(et(est_fini(vk), est_fini(vm)), est_fini(vmp)),
              egal(SC(vk, vk), SC(vm, vmp)))


def demi_intervalle(k=LIANT_DEMI_K, m=LIANT_DEMI_M, mp_=LIANT_DEMI_MP):
    """🎯 ⊢ (∀k)(∀m)(∀m')[ ( Fini k ∧ Fini m ∧ Fini m' ∧ 2k = m+m' )
                            ⇒ ( m ≤ k  OU  m' ≤ k ) ].   [CLOS, 0 hypothèse]

    AVEC LA SYMÉTRIE, C'EST LA MOITIÉ DE L'INTERVALLE. Les solutions de
    Goldbach vont par paires sommant à `2k` ; ce lemme dit que l'un des deux
    membres de la paire est toujours `≤ k`. Chercher une décomposition ne
    demande donc d'explorer que `[0, k]`, pas `[0, 2k]`.

    ROUTE — **sans aucune inégalité STRICTE**, qui coûterait cher ici :
      · comparabilité des cardinaux : `m ≤ k` OU `k ≤ m` (inconditionnel) ;
      · dans le second cas le complément existe (Prop. 13) : `m = k + d` ;
      · `k+k = m+m' = (k+d)+m' = k+(d+m')`  [associativité ITÉRÉE] ;
      · simplification additive FINIE (Cor. 3 §III.5.2) : `k = d+m'` ;
      · commutativité, puis Prop. 2 : `m' ≤ k`.

    ⚠️ LA GARDE `Fini` EST ESSENTIELLE DEUX FOIS, et pas par prudence : la
    simplification additive est **fausse** pour les cardinaux infinis
    (`ℵ₀+1 = ℵ₀+2` sans que `1 = 2`), et la Prop. 2 l'exige aussi.

    ⚠️ PIÈGE MESURÉ (voir `ANOMALIES.md`, règle des liants canoniques) :
    `simplification_additive_finie` est une preuve par RÉCURRENCE à liant
    canonique `aSA`. Lui passer un terme casse un modus ponens **interne** —
    on l'appelle sur son propre nom, on généralise, puis on instancie.

    COÛT MESURÉ : ~305 s (la récurrence de la simplification domine)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        ou,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_disjointe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
        somme_cardinale_associative_iteree,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_sup_cardinal import (
        comparabilite_cardinaux_terme,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        card_est_un_cardinal,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_simplification_additive import (
        simplification_additive_finie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
        existe_complement_somme,
    )
    from outils_ia.arithmetique.lemmes_conjectures import prop2_sous_fini

    vk, vm, vmp = var(k), var(m), var(mp_)
    DEUXK = SC(vk, vk)
    HYP = hypothese_demi(k, m, mp_)
    LE_MK, LE_MPK = inf_egal_card(vm, vk), inf_egal_card(vmp, vk)
    CIBLE = ou(LE_MK, LE_MPK)

    h = N.assume(HYP)
    fini_k, fini_m = _cg(_cg(_cg(h))), _cd(_cg(_cg(h)))
    fini_mp, somme = _cd(_cg(h)), _cd(h)
    card_k, card_m = _mp(fini_k, fic_t(vk)), _mp(fini_m, fic_t(vm))

    #   branche 1 : m ≤ k — c'est déjà le disjoint gauche
    br1 = N.loi_deduction(LE_MK, _mp(N.assume(LE_MK), N.s2(LE_MK, LE_MPK)))
    assert br1.conclusion == impl(LE_MK, CIBLE), "demi-intervalle : branche 1"

    #   branche 2 : k ≤ m  ⟹  m' ≤ k
    LE_KM = inf_egal_card(vk, vm)
    ex_d = _mp(conjonction_intro(conjonction_intro(card_k, card_m),
                                 N.assume(LE_KM)),
               existe_complement_somme(vk, vm, LIANT_DEMI_D))    # (∃d) m = k+d
    mat_d = ex_d.conclusion.sous[0]
    vd = var(LIANT_DEMI_D)

    #   2k = m+m'  →  2k = (k+d)+m'  →  2k = k+(d+m')
    s6m = N.s6(vm, SC(vk, vd), "wdi", egal(DEUXK, SC(var("wdi"), vmp)))
    somme3 = composer_egalites(
        _mp(somme, _cg(_mp(N.assume(mat_d), s6m))),
        somme_cardinale_associative_iteree(vk, vd, vmp))

    #   simplification additive FINIE — liant canonique `aSA` : voir le piège
    DPM = SC(vd, vmp)
    simp_i = instancie(instancie(
        _mp(fini_k, instancie(N.generalisation(
            "aSA", simplification_additive_finie("aSA")), vk)), vk), DPM)
    card_dpm = card_est_un_cardinal(somme_disjointe(vd, vmp),
                                    est_cardinal(DPM).lieur)
    eq_k = composer_egalites(
        _mp(conjonction_intro(conjonction_intro(card_k, card_dpm), somme3),
            simp_i),                                             # k = d+m'
        somme_cardinale_commutative(vd, vmp))                    # k = m'+d
    p2 = instancie(instancie(instancie(
        N.generalisation("a", N.generalisation("b", N.generalisation(
            "c", prop2_sous_fini("a", "b", "c")))), vmp), vk), vd)
    ou_droite = _mp(_mp(_mp(eq_k, _mp(fini_mp, p2)), N.s2(LE_MPK, LE_MK)),
                    N.s3(LE_MPK, LE_MK))
    assert ou_droite.conclusion == CIBLE, "demi-intervalle : branche 2"
    br2 = N.loi_deduction(LE_KM, _mp(ex_d, existe_elimination(
        N.loi_deduction(mat_d, ou_droite), LIANT_DEMI_D)))

    th = N.generalisation(mp_, N.generalisation(m, N.generalisation(
        k, N.loi_deduction(HYP, cas(comparabilite_cardinaux_terme(vm, vk),
                                    br1, br2)))))
    assert th.est_clos and not th.hypotheses, "demi-intervalle : non clos"
    return th




# ══════════════════════════════════════════════════════════════════════════════
#  LA RENCONTRE SE RESTREINT À LA MOITIÉ DE L'INTERVALLE
# ══════════════════════════════════════════════════════════════════════════════

def rencontre_demi(k=LIANT_K):
    """(∃m)( ( m ∈ P₂ₖ ∧ m ∈ Q₂ₖ ) ∧ m ≤ k )  — la rencontre CHERCHÉE DANS [0,k]."""
    M = _double(k)
    vm = var(LIANT_M)
    return existe(LIANT_M, et(et(appartient(vm, premiers_bornes(M)),
                                 appartient(vm, miroir(M))),
                              inf_egal_card(vm, var(k))))


def _fini_du_membre_de_P(M, vx):
    """De `x ∈ P_b` tirer `Fini x` — la garde vit dans `premier_ent`."""
    return _cg(_cg(_mp(vx[1], _cg(membre_premiers_bornes(M, vx[0])))))


def rencontre_se_restreint(k=LIANT_K):
    """🎯 ⊢ (∀k)[ Fini k ⇒ ( rencontre(k) ⇒ rencontre_demi(k) ) ].   [CLOS]

    **CHERCHER DANS LA MOITIÉ DE L'INTERVALLE SUFFIT.** S'il existe un point
    de la rencontre dans `[0, 2k]`, il en existe un dans `[0, k]`.

    ASSEMBLAGE de deux acquis :
      · `symetrie_du_crible` — le point `m` vient avec son partenaire `m'`,
        lui aussi dans la rencontre, et `2k = m + m'` ;
      · `demi_intervalle` — d'une telle paire, l'un des deux est `≤ k`.
    Disjonction des cas sur lequel des deux : dans chaque branche le témoin
    est fourni, et la cible est la même.

    ⚠️ `Fini k` est REQUIS et ne se déduit pas de la rencontre : `k` y est
    quelconque. Dans l'usage réel il est gratuit — l'antécédent `A(k)` de la
    forme « moitiés » le contient. Les finitudes de `m` et `m'`, elles,
    viennent de `P₂ₖ` : c'est la garde `premier_ent` qui les fournit.

    [CLOS au sens du noyau, SOUS les 2 axiomes de la théorie du crible.]"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from recherche.goldbach.symetrie import (
        LIANT_PARTENAIRE, symetrie_du_crible,
    )

    vk, vm = var(k), var(LIANT_M)
    vmp = var(LIANT_PARTENAIRE)
    M = _double(k)
    CIBLE = rencontre_demi(k)
    mat_cible = CIBLE.sous[0]

    h_fini_k = N.assume(est_fini(vk))
    mat_renc = et(appartient(vm, premiers_bornes(M)),
                  appartient(vm, miroir(M)))
    hm = N.assume(mat_renc)
    fini_m = _fini_du_membre_de_P(M, (vm, _cg(hm)))

    #   le partenaire, par la symétrie
    sym = instancie(instancie(symetrie_du_crible(k, LIANT_M), vk), vm)
    ex_mp = _mp(hm, sym)
    matp = ex_mp.conclusion.sous[0]
    hmp = N.assume(matp)
    mp_in_PQ, somme = _cg(hmp), _cd(hmp)
    fini_mp = _fini_du_membre_de_P(M, (vmp, _cg(mp_in_PQ)))

    #   ⚠️ ORDRE D'INSTANCIATION : `demi_intervalle` généralise m' EN DERNIER,
    #   donc c'est le ∀ le plus EXTERNE — on l'instancie en premier.
    di = instancie(instancie(instancie(demi_intervalle(), vmp), vm), vk)
    ou_th = _mp(conjonction_intro(conjonction_intro(
        conjonction_intro(h_fini_k, fini_m), fini_mp), somme), di)

    LE_M, LE_MP = inf_egal_card(vm, vk), inf_egal_card(vmp, vk)
    br1 = N.loi_deduction(LE_M, _mp(conjonction_intro(hm, N.assume(LE_M)),
                                    N.s5(mat_cible, vm, LIANT_M)))
    br2 = N.loi_deduction(LE_MP, _mp(conjonction_intro(mp_in_PQ,
                                                       N.assume(LE_MP)),
                                     N.s5(mat_cible, vmp, LIANT_M)))
    concl = cas(ou_th, br1, br2)
    assert concl.conclusion == CIBLE, "demi-rencontre : cible mal formée"

    sous_m = _mp(ex_mp, existe_elimination(N.loi_deduction(matp, concl),
                                           LIANT_PARTENAIRE))
    imp = existe_elimination(N.loi_deduction(mat_renc, sous_m), LIANT_M)
    th = N.generalisation(k, N.loi_deduction(est_fini(vk), imp))
    assert th.est_clos and not th.hypotheses, "demi-rencontre : non clos"
    return th


def demi_implique_rencontre(k=LIANT_K):
    """⊢ (∀k)( rencontre_demi(k) ⇒ rencontre(k) )  — l'affaiblissement.  [CLOS]

    Trivial : on oublie la borne `m ≤ k`. Avec `rencontre_se_restreint`, cela
    donne l'ÉQUIVALENCE — chercher dans `[0, k]` n'est pas seulement suffisant,
    c'est exactement la même chose."""
    vk, vm = var(k), var(LIANT_M)
    M = _double(k)
    src = rencontre_demi(k)
    mat_src = src.sous[0]
    h = N.assume(mat_src)
    mat_renc = et(appartient(vm, premiers_bornes(M)), appartient(vm, miroir(M)))
    ex = _mp(_cg(h), N.s5(mat_renc, vm, LIANT_M))
    assert ex.conclusion == rencontre(k), "demi ⇒ rencontre : cible"
    th = N.generalisation(k, existe_elimination(
        N.loi_deduction(mat_src, ex), LIANT_M))
    assert th.conclusion == pourtout_impl(k), "demi ⇒ rencontre : forme"
    assert th.est_clos and not th.hypotheses, "demi ⇒ rencontre : non clos"
    return th


def pourtout_impl(k=LIANT_K):
    """(∀k)( rencontre_demi(k) ⇒ rencontre(k) ) — la cible de l'affaiblissement."""
    return pourtout(k, impl(rencontre_demi(k), rencontre(k)))


__all__ = [
    "LIANT_DEMI_K", "LIANT_DEMI_M", "LIANT_DEMI_MP", "LIANT_DEMI_D",
    "hypothese_demi", "demi_intervalle",
    "rencontre_demi", "rencontre_se_restreint", "demi_implique_rencontre",
]
