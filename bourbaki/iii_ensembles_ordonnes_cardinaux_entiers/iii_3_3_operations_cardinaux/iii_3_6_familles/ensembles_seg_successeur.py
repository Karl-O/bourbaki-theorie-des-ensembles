"""§III.5.8 / §III.3.6 — T1b-(1) : DÉCOMPOSITION DU SEGMENT OUVERT de (ℕ, ≤_G).

  🎯 segment_succ_decomposition(n) :
        { n ∈ ℕ }  ⊢  seg(ℕ, n+1) = seg(ℕ, n) ∪ { n }

où seg(ℕ, t) := segment_extremite(≤_G, ℕ, t) = { i∈ℕ | i ≤ t et i≠t } — le segment
OUVERT [0, t[ de la chaîne C62/factorielle (MÊME terme que _seg_NN de
ensembles_famille_successeurs) — et n+1 = successeur(n).

HYPOTHÈSE HONNÊTE (unique) : n ∈ ℕ  (appartient(n, ensemble_NN())).  Elle fournit
Fini n (appartenance_NN), ¬(n=n+1) (Déf.1 §III.4.1) et n+1∈ℕ (NN_clos_successeur).

────────────────────────────────────────────────────────────────────────────────
ROUTE — double inclusion pointwise + antisymétrie de ⊂ (A1), i le liant :

  (⊆)  i∈seg(n+1)  ⇒  i∈ℕ, (i,n+1)∈G, i≠n+1                      [membre_segment]
         ⇒  i ≤ n+1                                        [couple_dans_G_ordre ⇒]
         ⇒  i < n+1  (= i≤n+1 ∧ i≠n+1 littéralement)  ⇒  i ≤ n
                       [successeur_ordre_strict ⇒, sous est_cardinal(i) ∧ Fini(n)]
         ⇒  cas sur (i=n) [tiers exclu, motif _nn] :
              i=n  ⇒ i∈{n}          [singleton_membre ⇐]        ⇒ i∈seg(n)∪{n} ;
              i≠n  ⇒ i∈seg(n)  (i≤n ∧ i∈ℕ ∧ n∈ℕ ∧ i≠n)         ⇒ i∈seg(n)∪{n}.

  (⊇)  i∈seg(n)∪{n}  ⇒  cas [membre_reunion_graphes ⇒] :
         i∈seg(n) ⇒ i≤n ⇒ i<n+1     [successeur_ordre_strict ⇐] ⇒ i∈seg(n+1) ;
         i∈{n}    ⇒ i=n ; n≤n+1 (_inf_egal_k_successeur) et ¬(n=n+1) (Déf.1) sont
                    TRANSPORTÉS à i par Leibniz S6 (liants frais wsg*) ⇒ i∈seg(n+1).

GARDE-FOUS.  Rien postulé (theorie_ensembles()==22, asserté au test) ; toutes les
briques NOM-basées (successeur_ordre_strict) sont construites sur noms EXOTIQUES
puis ∀-closes et instanciées (motif _inst_gen) ; le liant pointwise « isg » est
exotique, et l'inclusion finale est RAMENÉE au liant canonique « z » de ⊂ par
∀-clôture sur isg + instanciation en z + ∀-clôture sur z (licite : z n'est libre
ni dans seg ni dans ℕ ni dans les hypothèses) — jamais d'alpha-bricolage.

⚠️ PERF : appartenance_NN déclenche N_existe (~5 min, mémoïsé une fois par session)
— le test est marqué slow.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, non, appartient, inclus, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import membre_segment
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import membre_reunion_graphes
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal, fini_implique_distinct_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import _inf_egal_k_successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import successeur_ordre_strict
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee, NN_clos_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_n_bien_ordonne import ordre_induit_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, couple_dans_G_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import _seg_NN


#: Noms RÉSERVÉS par la preuve (liant pointwise, liants Leibniz frais, noms des
#: briques ∀-closes, liant canonique de ⊂) — le nom de n ne doit heurter aucun.
_NOMS_RESERVES = frozenset({"isg", "wsg1", "wsg2", "wsg3", "xso", "bso", "z"})


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _tiers_exclu(p):
    """⊢ P ∨ ¬P.   (a_implique_a(P) = ¬P∨P, retournée par S3 — motif _nn.)"""
    return N.modus_ponens(a_implique_a(p), N.s3(non(p), p))


def _card_de_NN(vi, thm_in_NN):
    """De Γ ⊢ i∈ℕ [thm_in_NN] :  (Γ ⊢ Fini i,  Γ ⊢ est_cardinal i).

    appartenance_NN instanciée au TERME i (sens ⇒) puis Déf.1 §III.4.1 (1er conjoint).
    ⚠️ déclenche N_existe au premier appel de la session (mémoïsé)."""
    fini = N.modus_ponens(thm_in_NN, equivalence_avant(appartenance_NN_instanciee(vi)))
    return fini, N.modus_ponens(fini, fini_implique_cardinal(vi))


def _strict_succ_terme(vi, vn):
    """⊢ (est_cardinal(i) et Fini n) ⇒ ( (i < n+1) ⇔ (i ≤ n) )   pour des TERMES.

    successeur_ordre_strict CLOS sur les noms exotiques xso/bso, ∀-clos puis
    instancié (motif _inst_gen — blindage anti-collision de liants)."""
    g = N.generalisation("xso", N.generalisation("bso", successeur_ordre_strict("xso", "bso")))
    return instancie(instancie(g, vi), vn)


def segment_succ_decomposition_enonce(n="nsg"):
    """Formule cible :  seg(ℕ, successeur(n)) = seg(ℕ, n) ∪ { n }."""
    vn = _t(n)
    return egal(_seg_NN(successeur(vn)), E.reunion(_seg_NN(vn), E.singleton(vn)))


# @livre Ch.III §5.8 Def.2 | E III.41 L.28-31 | PDF p.144  (infra de la récurrence « cette relation, jointe à 0!=1, caractérise n! » : le pas ∏_{i<n+1} = ∏_{i<n}·(n+1) exige seg(n+1) = seg(n)∪{n})
def segment_succ_decomposition(n="nsg", i="isg"):
    """🎯 { n ∈ ℕ } ⊢ seg(ℕ, n+1) = seg(ℕ, n) ∪ { n }.        (1 hypothèse HONNÊTE.)

    Conclusion ÉGALE LITTÉRALEMENT segment_succ_decomposition_enonce(n).
    Double inclusion pointwise (liant exotique i) + antisymétrie de ⊂ (A1).
    NON vacueux : la conclusion n'est pas l'hypothèse ; l'arithmétique d'ordre
    (successeur_ordre_strict) est RÉELLEMENT utilisée dans les deux sens."""
    vn, vi = _t(n), var(i)
    assert not (_NOMS_RESERVES & libres_t(vn)), \
        "segment_succ_decomposition : nom de n heurtant un nom réservé de la preuve"
    G, NN = G_ordre_NN(), ensemble_NN()
    sn = successeur(vn)
    Ssn, Sn, Sing = _seg_NN(sn), _seg_NN(vn), E.singleton(vn)
    U = E.reunion(Sn, Sing)
    in_Ssn, in_Sn, in_Sing, in_U = (appartient(vi, X) for X in (Ssn, Sn, Sing, U))

    # ── briques instanciées UNE fois (chacune construite sur noms exotiques) ──
    ms_sn = membre_segment(G, NN, sn, vi)   # (i∈seg(n+1)) ⇔ ((i∈ℕ ∧ (i,n+1)∈G) ∧ i≠n+1)
    ms_n = membre_segment(G, NN, vn, vi)    # (i∈seg(n))  ⇔ ((i∈ℕ ∧ (i,n)∈G) ∧ i≠n)
    cg_sn = couple_dans_G_ordre(vi, sn)     # ((i,n+1)∈G) ⇔ ((i≤n+1 ∧ i∈ℕ) ∧ n+1∈ℕ)
    cg_n = couple_dans_G_ordre(vi, vn)      # ((i,n)∈G)   ⇔ ((i≤n ∧ i∈ℕ) ∧ n∈ℕ)
    assert equivalence_avant(cg_sn).conclusion.sous[1] == ordre_induit_NN(vi, sn), \
        "couple_dans_G_ordre(i,n+1) : RHS ≠ ordre_induit_NN (α-divergence inattendue)"
    assert equivalence_avant(cg_n).conclusion.sous[1] == ordre_induit_NN(vi, vn), \
        "couple_dans_G_ordre(i,n) : RHS ≠ ordre_induit_NN (α-divergence inattendue)"
    mru = membre_reunion_graphes(Sn, Sing, vi)   # (i∈seg(n)∪{n}) ⇔ (i∈seg(n) ∨ i∈{n})
    sm = singleton_membre(vi, vn)                # (i∈{n}) ⇔ (i=n)
    sos = _strict_succ_terme(vi, vn)             # (card i ∧ Fini n) ⇒ ((i<n+1) ⇔ (i≤n))

    # ── L'HYPOTHÈSE HONNÊTE et ses conséquences sur n ─────────────────────────
    Hn = N.assume(appartient(vn, NN))                       # n ∈ ℕ   (LA seule hyp.)
    fini_n, _ = _card_de_NN(vn, Hn)                         # Fini n
    sn_NN = N.modus_ponens(Hn, instancie(NN_clos_successeur(), vn))     # n+1 ∈ ℕ
    n_le_sn = _inf_egal_k_successeur(vn)                    # n ≤ n+1        [CLOS]
    n_ne_sn = N.modus_ponens(fini_n, fini_implique_distinct_successeur(vn))  # ¬(n=n+1)

    # ══ (⊆)  i∈seg(n+1) ⇒ i∈seg(n)∪{n} ═══════════════════════════════════════
    Hi = N.assume(in_Ssn)                                   # i ∈ seg(n+1)
    corps = N.modus_ponens(Hi, equivalence_avant(ms_sn))    # (i∈ℕ ∧ (i,n+1)∈G) ∧ i≠n+1
    g1 = conjonction_elim_gauche(corps)                     # i∈ℕ ∧ (i,n+1)∈G
    i_NN = conjonction_elim_gauche(g1)                      # i∈ℕ
    i_ne_sn = conjonction_elim_droite(corps)                # ¬(i=n+1)
    ordr = N.modus_ponens(conjonction_elim_droite(g1), equivalence_avant(cg_sn))
    i_le_sn = conjonction_elim_gauche(conjonction_elim_gauche(ordr))    # i ≤ n+1
    strict = conjonction_intro(i_le_sn, i_ne_sn)            # i≤n+1 ∧ i≠n+1 = i<n+1
    assert strict.conclusion == inf_strict_card(vi, sn), \
        "(⊆) : la conjonction n'est PAS littéralement i < n+1"
    _, card_i = _card_de_NN(vi, i_NN)                       # est_cardinal(i)
    eq_si = N.modus_ponens(conjonction_intro(card_i, fini_n), sos)   # (i<n+1) ⇔ (i≤n)
    i_le_n = N.modus_ponens(strict, conjonction_elim_gauche(eq_si))  # i ≤ n

    p_eq = egal(vi, vn)                                     # cas sur (i=n)
    #  branche i=n : i∈{n}, injection DROITE de la réunion (S2 puis S3)
    h_eq = N.assume(p_eq)
    i_sing = N.modus_ponens(h_eq, equivalence_arriere(sm))  # i∈{n}
    d_r = N.modus_ponens(N.modus_ponens(i_sing, N.s2(in_Sing, in_Sn)),
                         N.s3(in_Sing, in_Sn))              # i∈seg(n) ∨ i∈{n}
    br_eq = N.loi_deduction(p_eq, N.modus_ponens(d_r, equivalence_arriere(mru)))
    #  branche i≠n : i∈seg(n) (i≤n ∧ i∈ℕ ∧ n∈ℕ ∧ i≠n), injection GAUCHE (S2)
    h_ne = N.assume(non(p_eq))
    ord_n = conjonction_intro(conjonction_intro(i_le_n, i_NN), Hn)   # = ordre_induit_NN(i,n)
    i_G_n = N.modus_ponens(ord_n, equivalence_arriere(cg_n))         # (i,n)∈G
    corps_n = conjonction_intro(conjonction_intro(i_NN, i_G_n), h_ne)
    i_Sn = N.modus_ponens(corps_n, equivalence_arriere(ms_n))        # i∈seg(n)
    d_l = N.modus_ponens(i_Sn, N.s2(in_Sn, in_Sing))        # i∈seg(n) ∨ i∈{n}
    br_ne = N.loi_deduction(non(p_eq), N.modus_ponens(d_l, equivalence_arriere(mru)))

    i_U = cas(_tiers_exclu(p_eq), br_eq, br_ne)             # i ∈ seg(n)∪{n}
    imp_sub = N.loi_deduction(in_Ssn, i_U)                  # (i∈seg(n+1)) ⇒ (i∈seg(n)∪{n})

    # ══ (⊇)  i∈seg(n)∪{n} ⇒ i∈seg(n+1) ═══════════════════════════════════════
    def _dans_Ssn(t_iNN, t_le, t_ne):
        """(Γ ⊢ i∈ℕ, Γ ⊢ i≤n+1, Γ ⊢ i≠n+1)  →  Γ∪{n∈ℕ} ⊢ i∈seg(n+1)."""
        o = conjonction_intro(conjonction_intro(t_le, t_iNN), sn_NN)
        gG = N.modus_ponens(o, equivalence_arriere(cg_sn))  # (i,n+1)∈G
        c = conjonction_intro(conjonction_intro(t_iNN, gG), t_ne)
        return N.modus_ponens(c, equivalence_arriere(ms_sn))

    #  branche i∈seg(n) : i≤n donne i<n+1 (successeur_ordre_strict, sens ⇐)
    h_Sn = N.assume(in_Sn)
    corps2 = N.modus_ponens(h_Sn, equivalence_avant(ms_n))  # (i∈ℕ ∧ (i,n)∈G) ∧ i≠n
    g2 = conjonction_elim_gauche(corps2)
    i_NN2 = conjonction_elim_gauche(g2)                     # i∈ℕ
    ord2 = N.modus_ponens(conjonction_elim_droite(g2), equivalence_avant(cg_n))
    i_le_n2 = conjonction_elim_gauche(conjonction_elim_gauche(ord2))    # i ≤ n
    _, card_i2 = _card_de_NN(vi, i_NN2)
    eq_si2 = N.modus_ponens(conjonction_intro(card_i2, fini_n), sos)    # (i<n+1) ⇔ (i≤n)
    strict2 = N.modus_ponens(i_le_n2, conjonction_elim_droite(eq_si2))  # i < n+1
    br_seg = N.loi_deduction(in_Sn, _dans_Ssn(
        i_NN2, conjonction_elim_gauche(strict2), conjonction_elim_droite(strict2)))

    #  branche i∈{n} : i=n ; n≤n+1 et ¬(n=n+1) transportés par Leibniz (liants FRAIS)
    h_sing = N.assume(in_Sing)
    i_eq_n = N.modus_ponens(h_sing, equivalence_avant(sm))  # i = n

    def _leibniz(f_de_w, w, thm_n):
        """De i=n et Γ ⊢ F(n) :  Γ ⊢ F(i).   (S6, sens arrière, liant frais w.)"""
        eqv = N.modus_ponens(i_eq_n, N.s6(vi, vn, w, f_de_w))   # F(i) ⇔ F(n)
        return N.modus_ponens(thm_n, equivalence_arriere(eqv))

    i_NN3 = _leibniz(appartient(var("wsg1"), NN), "wsg1", Hn)              # i∈ℕ
    i_le3 = _leibniz(inf_egal_card(var("wsg2"), sn), "wsg2", n_le_sn)      # i ≤ n+1
    i_ne3 = _leibniz(non(egal(var("wsg3"), sn)), "wsg3", n_ne_sn)          # ¬(i=n+1)
    br_sing = N.loi_deduction(in_Sing, _dans_Ssn(i_NN3, i_le3, i_ne3))

    Hu = N.assume(in_U)
    disj = N.modus_ponens(Hu, equivalence_avant(mru))       # i∈seg(n) ∨ i∈{n}
    imp_sup = N.loi_deduction(in_U, cas(disj, br_seg, br_sing))

    # ══ double inclusion → ÉGALITÉ (antisymétrie de ⊂ = A1) ═══════════════════
    def _inclusion(imp_thm, ta, tb):
        """(i∈A ⇒ i∈B) [i exotique] → ⊢ A ⊂ B  (liant canonique « z » de ⊂).

        ∀-clôture sur i, instanciation en z (licite : z ∉ libres(A)∪libres(B)),
        ∀-clôture sur z — la conclusion EST inclus(A, B), pas un α-variant."""
        z_inst = instancie(N.generalisation(i, imp_thm), var("z"))
        incl = N.generalisation("z", z_inst)
        assert incl.conclusion == inclus(ta, tb), "inclusion : liant ≠ « z »"
        return incl

    incl_sub = _inclusion(imp_sub, Ssn, U)                  # seg(n+1) ⊂ seg(n)∪{n}
    incl_sup = _inclusion(imp_sup, U, Ssn)                  # seg(n)∪{n} ⊂ seg(n+1)
    res = N.modus_ponens(conjonction_intro(incl_sub, incl_sup),
                         inclusion_antisymetrique(Ssn, U))  # seg(n+1) = seg(n)∪{n}

    assert res.conclusion == segment_succ_decomposition_enonce(n), \
        "segment_succ_decomposition : conclusion ≠ énoncé cible"
    assert res.hypotheses == frozenset({appartient(vn, NN)}), \
        "segment_succ_decomposition : hypothèses ≠ { n∈ℕ }"
    assert res.conclusion not in res.hypotheses, "segment_succ_decomposition : VACUOUS"
    return res


__all__ = ["segment_succ_decomposition_enonce", "segment_succ_decomposition"]
