"""§III.5.3 / §III.6.2 — LE PONT DE SEGMENT : le segment OUVERT en k+1 EST le FERMÉ [0,k].

  🎯🎯 `segment_succ_est_intervalle`  { k ∈ ℕ } ⊢ seg(ℕ, k+1) = [0, k]

────────────────────────────────────────────────────────────────────────────────
LE PROBLÈME FERMÉ.  C62 (E III.46) applique M au domaine de la RESTRICTION
f⁽ⁿ⁾ := f | [0, n[ (SEMI-OUVERT), tandis que `max_intervalle_vaut_n_entier` n'évalue
M que sur le FERMÉ : { est_entier n } ⊢ M([0,n]) = n.  Sans pont, `M(D u)` ne se
réduit pas.  On ÉNONCE AU POINT SUCCESSEUR : en k+1 le domaine de la restriction est
[0, k], un FERMÉ, et M y vaut k DIRECTEMENT.  ⚠️ La route « n−1 » n'est PAS empruntée :
`difference_entiers` est OPAQUE, sans axiome caractérisant (réserve consignée dans
iii_4_1/ensembles_entiers.py) — rien n'est prouvé ici sur n−1.
Le TRANSPORT de ce pont au domaine de la fonction globale de C62, puis sous M(·),
est le module VOISIN `ensembles_pont_domaine_iii5.py`, qui consomme ce fichier.

ROUTE DU PONT — double inclusion pointwise (liant exotique « ipd ») + antisym. de ⊂ :
  seg(ℕ, k+1) := segment_extremite(≤_G, ℕ, k+1) = { i∈ℕ | (i,k+1)∈G et i≠k+1 }
  [0, k]      := intervalle_entiers(0, k)      = { x | x cardinal et 0≤x et x≤k }
  (⊆) i∈seg(k+1) ⇒ i∈ℕ, i≤k+1, i≠k+1 [membre_segment, couple_dans_G_ordre] ⇒ i<k+1
        ⇒ i≤k [successeur_ordre_strict ⇒] ; i cardinal (i∈ℕ⇒Fini i⇒card) et 0≤i
        [zero_inf_egal_cardinal] ⇒ i∈[0,k].
  (⊇) i∈[0,k] ⇒ i cardinal, i≤k ⇒ Fini i ← LE MAILLON : downward-closure de Fini pour
        un CARDINAL (`fini_downward_garde_thm` ; son résidu `predecesseur_fini_universel`
        DÉCHARGÉ par la preuve CLOSE de §III.5) ⇒ i∈ℕ [appartenance_NN ⇐] ;
        i≤k ⇒ i<k+1 [succ_ordre_strict ⇐] ⇒ i∈seg(k+1).
L'unique hypothèse { k ∈ ℕ } est NÉCESSAIRE (elle fournit Fini k — garde de
`successeur_ordre_strict` ET de la downward-closure — et k+1 ∈ ℕ).

⚠️ PERF MESURÉE (2026-07-27, pytest fichier seul, machine chargée par 2 autres process) :
le PREMIER `segment_succ_est_intervalle` coûte 485 s (`fini_downward_garde_thm` +
`N_existe` dominent) ; les appels SUIVANTS ~20 s grâce à la mémoïsation.  Fichier de
test entier : 9 passed en 590 s.  Tests marqués `slow`.
⚠️ THÉORIES AUXILIAIRES — « n hypothèses » ≠ « aucune prémisse invisible » : `N.axiome`
rend un théorème à hypothèses VIDES, donc les théories DÉDIÉES échappent au compte
d'hypothèses ET à l'invariant 22 (qui ne certifie que `theorie_ensembles()`).  AUCUNE
théorie n'est créée ici ; toutes sont PRÉEXISTANTES, héritées des briques appelées.
Le compte EXACT, mesuré sur le capstone qui consomme ce pont, est publié dans
`ensembles_pont_domaine_iii5.py` (en-tête).

INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient, inclus, libres_t)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import membre_segment
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal, axiome_intervalle_entiers, theorie_intervalle_entiers)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import fini_downward_garde_thm
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import predecesseur_fini_universel
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import successeur_ordre_strict
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_max_intervalle_iii5 import intervalle_zero
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import zero_inf_egal_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee, NN_clos_successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, couple_dans_G_ordre)

#: Liant pointwise EXOTIQUE de la double inclusion (jamais un nom banal : `inf_egal_card`
#: lie en interne {F, u, up, v, y, z} et `est_cardinal` lie « X »).
LIANT_POINT = "ipd"
#: Nom par défaut de l'entier k (exotique, pour ne heurter aucun liant interne).
NOM_K = "kpd"
#: Trou FRAIS de la congruence M(·) — CONSOMMÉ par `ensembles_pont_domaine_iii5`, mais
#: DÉCLARÉ ici pour que `NOMS_RESERVES` couvre toute la chaîne du pont (ni lié dans
#: `est_plus_grand_element`/`inf_egal_card`, ni libre dans les termes réécrits).
TROU_MAX = "wdm"
#: Noms RÉSERVÉS par la preuve — le nom de k ne doit heurter aucun.
NOMS_RESERVES = frozenset({LIANT_POINT, TROU_MAX, "z", "a", "xso", "bso", "zlt"})


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def segment_succ_NN(k=NOM_K):
    """seg(ℕ, k+1) := segment_extremite(≤_G, ℕ, successeur(k)) — le segment OUVERT [0,k+1[.

    MÊME terme que `_seg_NN(successeur(k))` (iii_3_6_familles) et que celui de la chaîne
    C62/factorielle — et depuis la MIGRATION seg_ext le terme PORTE le graphe
    G_ordre_NN() : l'identité avec `_seg_NN` est donc désormais une coïncidence
    D'ORDRE aussi, plus seulement d'ensemble et de borne."""
    return E.segment_extremite(G_ordre_NN(), ensemble_NN(), successeur(_t(k)))


# ── Briques génériques instanciées à des TERMES (motif _inst_gen : ∀-clôture sur noms
#    EXOTIQUES puis instanciation — blindage anti-collision de liants) ─────────────────
def _membre_intervalle(b, x):
    """⊢ ( x ∈ [0,b] ) ⇔ ( (est_cardinal x et 0≤x) et x≤b )   pour des TERMES b, x."""
    ax = N.axiome(theorie_intervalle_entiers(), axiome_intervalle_entiers())
    return instancie(instancie(instancie(ax, ZERO), _t(b)), _t(x))


def _zero_minore(t):
    """⊢ est_cardinal(t) ⇒ 0 ≤ t   pour un TERME t."""
    base = zero_inf_egal_cardinal("zlt")
    return instancie(N.generalisation(
        "zlt", N.loi_deduction(est_cardinal(var("zlt")), base)), _t(t))


def _strict_succ(x, b):
    """⊢ ( est_cardinal(x) et Fini(b) ) ⇒ ( (x < b+1) ⇔ (x ≤ b) )   pour des TERMES."""
    g = N.generalisation("xso", N.generalisation(
        "bso", successeur_ordre_strict("xso", "bso")))
    return instancie(instancie(g, _t(x)), _t(b))


@lru_cache(maxsize=None)
def _downward_fini_cardinal():
    """⊢ (∀a)( est_cardinal(a) ⇒ (∀x)( (a ≤ x et Fini x) ⇒ Fini a ) ).      [CLOS, 0 hyp]

    Downward-closure de « Fini » pour un CARDINAL (E.III.4.2, Prop. 2 : « tout cardinal
    𝔞 ≤ n est un entier »).  `fini_downward_garde_thm` la donne sous { est_cardinal(a),
    predecesseur_fini_universel } ; ce résidu est DÉCHARGÉ par la preuve CLOSE de §III.5,
    la garde passe en antécédent puis on ∀-clôt.  La forme NON gardée est FAUSSE
    (contre-exemple b={{∅}}, cf. ensembles_recurrence_vraie) : la garde n'est PAS un
    affaiblissement gratuit.  ⚠️ PERF : poste dominant du premier appel (cf. en-tête,
    485 s pour l'ensemble de la preuve ; la mesure ISOLÉE de cette brique n'a PAS été
    refaite ici) — MÉMOÏSÉ."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    garde = fini_downward_garde_thm()                    # {card a, pfu} ⊢ (∀x)fd(a,x)
    pfu = predecesseur_fini_universel()
    assert pfu in garde.hypotheses, \
        "_downward_fini_cardinal : predecesseur_fini_universel absent (forme changée ?)"
    libre = N.modus_ponens(predecesseur_fini_universel_preuve(),
                           N.loi_deduction(pfu, garde))  # {card a} ⊢ (∀x)fd(a,x)
    res = N.generalisation("a", N.loi_deduction(est_cardinal(var("a")), libre))
    assert res.est_clos, "_downward_fini_cardinal : hypothèses résiduelles"
    return res


def _fini_de_borne(vi, vk, thm_card_i):
    """De Γ ⊢ est_cardinal(i) :  Γ ⊢ ( i ≤ k et Fini k ) ⇒ Fini i   (TERMES i, k)."""
    tout_x = N.modus_ponens(thm_card_i, instancie(_downward_fini_cardinal(), vi))
    return instancie(tout_x, vk)


# ══ 🎯🎯 LE PONT :  seg(ℕ, k+1) = [0, k] ═══════════════════════════════════════
def cible_segment_succ_intervalle(k=NOM_K):
    """ÉNONCÉ-cible (test miroir) :  seg(ℕ, successeur(k)) = [0, k]."""
    vk = _t(k)
    return egal(segment_succ_NN(vk), intervalle_zero(vk))


# @livre Ch.III §6.2 Rem.- | E III.46 L.12-13 | PDF p.149  (« une suite finie ayant pour ensemble d'indices [1, n] ou [0, n − 1] en rangeant la famille dans l'ordre défini par une bijection de I sur l'un des intervalles précédents » — Bourbaki ne propose ici que deux intervalles FERMÉS, [1,n] et [0,n−1], comme plages d'indices canoniques d'une suite finie à n termes : c'est l'ancrage du MEMBRE DROIT du pont. Le semi-ouvert [0,n[ n'apparaît qu'en L.19 (f⁽ⁿ⁾) ; le RACCORD entre les deux plages, que Bourbaki laisse implicite, est ce que ce module certifie. Lignes RECOMPTÉES sur le PNG le 27 juil. 2026 : L.14 = le titre « 2. Définition d'applications par récurrence ».)
# @livre Ch.III §5.3 Rem.- | E III.37 L.22-26 | PDF p.140  (« l'ensemble des x vérifiant cette relation … que l'on peut donc noter [0, a] » — la DÉFINITION du membre droit, l'intervalle d'entiers)
def segment_succ_est_intervalle(k=NOM_K, i=LIANT_POINT):
    """🎯🎯 { k ∈ ℕ } ⊢ seg(ℕ, k+1) = [0, k].                        [1 hyp HONNÊTE]

    LE SEGMENT OUVERT D'EXTRÉMITÉ k+1 EST L'INTERVALLE FERMÉ [0,k] — la pièce qui
    manquait pour réduire `M(D u)`.  Conclusion ÉGALE LITTÉRALEMENT
    `cible_segment_succ_intervalle(k)`.  Double inclusion pointwise (liant exotique
    « ipd ») + antisymétrie de ⊂ (A1) ; l'inclusion est ramenée au liant CANONIQUE
    « z » par ∀-clôture sur ipd, instanciation en z (licite : z libre ni dans seg,
    ni dans [0,k], ni dans l'hypothèse) puis ∀-clôture sur z — pas d'α-bricolage.
    NON vacueux : l'arithmétique d'ordre et la downward-closure servent RÉELLEMENT."""
    vk, vi = _t(k), var(i)
    assert not (NOMS_RESERVES & libres_t(vk)), \
        "segment_succ_est_intervalle : nom de k heurtant un nom réservé de la preuve"
    NN, G = ensemble_NN(), G_ordre_NN()
    sk = successeur(vk)
    S, IV = segment_succ_NN(vk), intervalle_zero(vk)

    ms = membre_segment(G, NN, sk, vi)      # (i∈seg(k+1)) ⇔ ((i∈ℕ et (i,k+1)∈G) et i≠k+1)
    cg = couple_dans_G_ordre(vi, sk)        # ((i,k+1)∈G)  ⇔ ((i≤k+1 et i∈ℕ) et k+1∈ℕ)
    mi = _membre_intervalle(vk, vi)         # (i∈[0,k])    ⇔ ((i cardinal et 0≤i) et i≤k)
    sos = _strict_succ(vi, vk)              # (card i et Fini k) ⇒ ((i<k+1) ⇔ (i≤k))

    # ── L'HYPOTHÈSE HONNÊTE et ses conséquences sur k ─────────────────────────
    Hk = N.assume(appartient(vk, NN))                                   # k ∈ ℕ  (LA seule)
    fini_k = N.modus_ponens(Hk, equivalence_avant(appartenance_NN_instanciee(vk)))
    sk_NN = N.modus_ponens(Hk, instancie(NN_clos_successeur(), vk))     # k+1 ∈ ℕ

    # ══ (⊆)  i ∈ seg(ℕ,k+1)  ⇒  i ∈ [0,k] ════════════════════════════════════
    Hi = N.assume(appartient(vi, S))
    corps = N.modus_ponens(Hi, equivalence_avant(ms))
    g1 = conjonction_elim_gauche(corps)
    i_NN = conjonction_elim_gauche(g1)                                  # i ∈ ℕ
    i_ne = conjonction_elim_droite(corps)                               # ¬(i = k+1)
    ordr = N.modus_ponens(conjonction_elim_droite(g1), equivalence_avant(cg))
    i_le_sk = conjonction_elim_gauche(conjonction_elim_gauche(ordr))    # i ≤ k+1
    strict = conjonction_intro(i_le_sk, i_ne)
    assert strict.conclusion == inf_strict_card(vi, sk), \
        "(⊆) : la conjonction n'est PAS littéralement i < k+1"
    fini_i = N.modus_ponens(i_NN, equivalence_avant(appartenance_NN_instanciee(vi)))
    card_i = N.modus_ponens(fini_i, fini_implique_cardinal(vi))         # est_cardinal(i)
    eq_si = N.modus_ponens(conjonction_intro(card_i, fini_k), sos)      # (i<k+1) ⇔ (i≤k)
    i_le_k = N.modus_ponens(strict, conjonction_elim_gauche(eq_si))     # i ≤ k
    zero_le_i = N.modus_ponens(card_i, _zero_minore(vi))                # 0 ≤ i
    dedans = N.modus_ponens(
        conjonction_intro(conjonction_intro(card_i, zero_le_i), i_le_k),
        equivalence_arriere(mi))                                        # i ∈ [0,k]
    imp_sub = N.loi_deduction(appartient(vi, S), dedans)

    # ══ (⊇)  i ∈ [0,k]  ⇒  i ∈ seg(ℕ,k+1) ════════════════════════════════════
    Hj = N.assume(appartient(vi, IV))
    corps2 = N.modus_ponens(Hj, equivalence_avant(mi))
    card_i2 = conjonction_elim_gauche(conjonction_elim_gauche(corps2))  # est_cardinal(i)
    i_le_k2 = conjonction_elim_droite(corps2)                           # i ≤ k
    fini_i2 = N.modus_ponens(conjonction_intro(i_le_k2, fini_k),
                             _fini_de_borne(vi, vk, card_i2))           # Fini i
    i_NN2 = N.modus_ponens(fini_i2,
                           equivalence_arriere(appartenance_NN_instanciee(vi)))  # i ∈ ℕ
    eq_si2 = N.modus_ponens(conjonction_intro(card_i2, fini_k), sos)
    strict2 = N.modus_ponens(i_le_k2, conjonction_elim_droite(eq_si2))  # i < k+1
    i_G = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_elim_gauche(strict2), i_NN2),
                          sk_NN), equivalence_arriere(cg))              # (i,k+1) ∈ G
    dans_S = N.modus_ponens(
        conjonction_intro(conjonction_intro(i_NN2, i_G),
                          conjonction_elim_droite(strict2)),
        equivalence_arriere(ms))                                        # i ∈ seg(k+1)
    imp_sup = N.loi_deduction(appartient(vi, IV), dans_S)

    # ══ double inclusion → ÉGALITÉ (antisymétrie de ⊂ = A1) ═══════════════════
    def _inclusion(imp_thm, ta, tb):
        """(i∈A ⇒ i∈B) [i exotique] → ⊢ A ⊂ B  (liant CANONIQUE « z » de ⊂)."""
        incl = N.generalisation("z", instancie(N.generalisation(i, imp_thm), var("z")))
        assert incl.conclusion == inclus(ta, tb), "inclusion : liant ≠ « z »"
        return incl

    res = N.modus_ponens(
        conjonction_intro(_inclusion(imp_sub, S, IV), _inclusion(imp_sup, IV, S)),
        inclusion_antisymetrique(S, IV))

    assert res.conclusion == cible_segment_succ_intervalle(vk), \
        "segment_succ_est_intervalle : conclusion ≠ seg(ℕ,k+1) = [0,k]"
    assert res.hypotheses == frozenset({appartient(vk, ensemble_NN())}), \
        "segment_succ_est_intervalle : hypothèses ≠ { k ∈ ℕ }"
    assert res.conclusion not in res.hypotheses, "segment_succ_est_intervalle : VACUOUS"
    return res


__all__ = ["LIANT_POINT", "NOM_K", "TROU_MAX", "NOMS_RESERVES", "_t",
           "segment_succ_NN",
           "cible_segment_succ_intervalle", "segment_succ_est_intervalle"]
