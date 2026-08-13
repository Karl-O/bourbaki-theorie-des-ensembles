"""§III.4.3 — RÉCURRENCE FORTE, dérivation (E III.33, variante 1) — ÉTAPE 1 : S{0}.

La variante 1 (E III.33 L.4-15) se dérive de C61 en trois maillons (le livre) :
  (1)  S{0} est vraie                              ← CE FICHIER (vacuité : ¬(p<0)) ;
  (2)  S{n} ⇒ S{n+1} sous « S{n} entraîne R{n} »   ← via successeur_ordre_strict + C58 ;
  (3)  C61 sur S puis retour à R.

Ce fichier dérive (1) pour une relation R OPAQUE (callable Terme→Formule) :

    ⊢ S{0}   où  S{n} := (∀p)((n fini et p fini et p<n) ⇒ R{p})
                  (constructeur s_recurrence_forte du fichier variantes voisin)

VACUITÉ : sous l'antécédent, p<0 donne p≤0 et p≠0 ; or 0≤p (borne inférieure,
cardinal_zero_inf_egal, CLOS) et p, 0 sont des cardinaux (élim. gauche de
est_fini ; fini_zero CLOS) — l'ANTISYMÉTRIE de ≤ (Cantor-Bernstein, CLOS)
force p=0, contradiction, d'où R{p} par ex falso.  theorie==22, rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, egal)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_bornes import (
    zero_inf_egal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    fini_zero)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    s_recurrence_forte)


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible  (ex falso quodlibet, S2+MP)."""
    a = thm_a.conclusion
    imp = N.modus_ponens(thm_na, N.s2(non(a), cible))
    return N.modus_ponens(thm_a, imp)


# @livre Ch.III §4.3 Demo.- | E III.33 L.8-8 | PDF p.136
#   (« la relation S{0} est vraie » — le maillon (1) de la démo de la variante 1, DÉRIVÉ)
def s_forte_en_zero(R, p: str = "pfor"):
    """🎯 ⊢ S{0}   (S de la récurrence forte, en n=0 : VACUITÉ car ¬(p<0)). CLOS."""
    vp = var(p)
    S0 = s_recurrence_forte(R, ZERO, p)          # (∀p)((0 fini et p fini et p<0) ⇒ R{p})
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_strict_card
    antecedent = et(et(est_fini(ZERO), est_fini(vp)), inf_strict_card(vp, ZERO))

    h = N.assume(antecedent)
    fini_p = conjonction_elim_droite(conjonction_elim_gauche(h))     # p fini
    lt = conjonction_elim_droite(h)                                  # p < 0
    p_le_0 = conjonction_elim_gauche(lt)                             # p ≤ 0
    p_ne_0 = conjonction_elim_droite(lt)                             # ¬(p = 0)
    card_p = conjonction_elim_gauche(fini_p)                         # est_cardinal(p)
    card_0 = conjonction_elim_gauche(fini_zero())                    # est_cardinal(0)
    # 0 ≤ p : (∀A)(∅≤A) instancié à p, puis réécriture ∅ ↦ Card(∅)=ZERO (Leibniz)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_egal_card, cardinal)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
        cardinal_vide_egale_vide)
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_avant
    le_vp = instancie(N.generalisation("A", zero_inf_egal("A")), vp)  # ∅ ≤ p
    vide_eq_zero = N.modus_ponens(cardinal_vide_egale_vide(),
                                  symetrie(cardinal(E.VIDE), E.VIDE))  # ∅ = Card(∅)
    leib0 = N.s6(E.VIDE, cardinal(E.VIDE), "w96",
                 inf_egal_card(var("w96"), vp))                      # (∅=Card∅)⇒(∅≤p ⇔ 0≤p)
    zero_le_p = N.modus_ponens(le_vp, equivalence_avant(
        N.modus_ponens(vide_eq_zero, leib0)))                        # 0 ≤ p

    anti = instancie(instancie(inf_egal_antisymetrique_card(), vp), ZERO)
    # antécédent de l'antisymétrie (associativité inconnue) : on le prouve en
    # suivant SA structure, à partir des quatre feuilles déjà démontrées.
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent
    C_anti, _ = antecedent_consequent(anti.conclusion)
    feuilles = {p_le_0.conclusion: p_le_0, zero_le_p.conclusion: zero_le_p,
                card_p.conclusion: card_p, card_0.conclusion: card_0}

    def _moities_et(f):
        """Retrouve (a, b) tels que et(a, b) == f (encodage ¬(¬a ∨ ¬b))."""
        interieur = f.sous[0]              # ou(¬a, ¬b)
        na, nb = interieur.sous
        return na.sous[0], nb.sous[0]

    def _prouve(f):
        if f in feuilles:
            return feuilles[f]
        a, b = _moities_et(f)
        return conjonction_intro(_prouve(a), _prouve(b))

    preuve_C = _prouve(C_anti)
    p_eq_0 = N.modus_ponens(preuve_C, anti)                          # p = 0
    r_p = _ex_falso(p_eq_0, p_ne_0, R(vp))                           # R{p}  (ex falso)
    imp = N.loi_deduction(antecedent, r_p)
    res = N.generalisation(p, imp)
    assert res.conclusion == S0, "S{0} : conclusion ≠ s_recurrence_forte(R, 0)"
    assert not res.hypotheses, "S{0} : hypothèses non déchargées"
    return res


# @livre Ch.III §4.3 Demo.- | E III.33 L.9-11 | PDF p.136
#   (« S{n} entraîne S{n+1} » — maillon (2) : m<n+1 ⇔ m≤n [Prop.2, successeur_
#    ordre_strict CLOS] puis m≤n ⇔ (m<n ou m=n) [C58, CLOS] — DÉRIVÉ)
def heredite_s_forte(R, n: str = "nhrd", p: str = "pfor"):
    """🎯 { H } ⊢ (∀n)((Fini n et S{n}) ⇒ S{n+1}),  H = (∀n)(S{n} ⇒ R{n}).

    Sous Fini(n) et S{n}, soit p avec (n+1 fini et p fini et p<n+1) :
    p<n+1 ⇔ p≤n (successeur_ordre_strict, gardes card(p)/fini(n)) ;
    p≤n ⇔ (p<n ou p=n) (C58) ; cas p<n → S{n} instancié donne R{p} ;
    cas p=n → H donne R{n}, Leibniz conclut R{p}."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        cas, equivalence_avant, equivalence_arriere)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (
        successeur_ordre_strict)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_c58_ordre_strict import (
        c58_ordre_strict)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini, successeur)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_strict_card)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
        hypothese_recurrence_forte)

    vn, vp = var(n), var(p)
    sn = successeur(vn)
    S_n = s_recurrence_forte(R, vn, p)
    S_sn = s_recurrence_forte(R, sn, p)
    H = hypothese_recurrence_forte(R, "nfor", p)

    hH = N.assume(H)                                     # (∀nfor)(S ⇒ R)   [à décharger]
    hFS = N.assume(et(est_fini(vn), S_n))                # Fini n et S{n}   [à décharger]
    fini_n = conjonction_elim_gauche(hFS)
    thm_Sn = conjonction_elim_droite(hFS)                # ⊢ S{n} (∀p …)

    ant2 = et(et(est_fini(sn), est_fini(vp)), inf_strict_card(vp, sn))
    h2 = N.assume(ant2)                                  # antécédent de S{n+1} en p
    fini_p = conjonction_elim_droite(conjonction_elim_gauche(h2))
    p_lt_sn = conjonction_elim_droite(h2)                # p < n+1
    card_p = conjonction_elim_gauche(fini_p)             # est_cardinal(p)

    # p<n+1 ⇔ p≤n  (Prop.2 strict, gardes)
    sos = successeur_ordre_strict(p, n)                  # (card p et fini n) ⇒ (p<n+1 ⇔ p≤n)
    eq1 = N.modus_ponens(conjonction_intro(card_p, fini_n), sos)
    p_le_n = N.modus_ponens(p_lt_sn, equivalence_avant(eq1))       # p ≤ n
    # p≤n ⇔ (p<n ou p=n)  (C58)
    disj = N.modus_ponens(p_le_n, equivalence_avant(c58_ordre_strict(p, n)))

    # cas 1 : p<n  →  S{n} instancié en p
    h_lt = N.assume(inf_strict_card(vp, vn))
    ant1 = conjonction_intro(conjonction_intro(fini_n, fini_p), h_lt)
    r_p1 = N.modus_ponens(ant1, instancie(thm_Sn, vp))             # R{p}
    br1 = N.loi_deduction(inf_strict_card(vp, vn), r_p1)
    # cas 2 : p=n  →  R{n} par H, puis Leibniz
    h_eq = N.assume(egal(vp, vn))
    r_n = N.modus_ponens(thm_Sn, instancie(hH, vn))                # R{n}
    leib = N.s6(vp, vn, "w96h", R(var("w96h")))                    # (p=n)⇒(R{p}⇔R{n})
    r_p2 = N.modus_ponens(r_n, equivalence_arriere(N.modus_ponens(h_eq, leib)))
    br2 = N.loi_deduction(egal(vp, vn), r_p2)

    r_p = cas(disj, br1, br2)                                      # R{p}
    imp2 = N.loi_deduction(ant2, r_p)
    S_sn_thm = N.generalisation(p, imp2)                           # S{n+1}
    her = N.loi_deduction(et(est_fini(vn), S_n), S_sn_thm)
    res = N.generalisation(n, her)                                 # (∀n)((Fini n et S{n})⇒S{n+1})
    assert res.conclusion.sous[0] is not None
    assert res.hypotheses == frozenset({H}), "hérédité : hypothèses ≠ {H}"
    return res


# @livre Ch.III §4.3 Rem.1 | E III.33 L.4-15 | PDF p.136
# @livre Ch.III §4.3 Demo.- | E III.33 L.12-15 | PDF p.136
#   (maillon (3) : « Le critère C61 prouve alors (∀n)(n entier ⇒ S{n}), et comme
#    S{n} entraîne R{n}, (∀n)(n entier ⇒ R{n}) est vraie » — DÉRIVÉ)
def recurrence_forte(R, p: str = "pfor"):
    """🎯🎯 VARIANTE 1 (récurrence FORTE, E III.33 L.4-15) — DÉRIVÉE DE C61 :

        { H ,  predecesseur_fini_universel }  ⊢  (∀n)( n entier ⇒ R{n} )

    où H = (∀n)(S{n} ⇒ R{n}) est LA prémisse de la variante (« S{n} entraîne
    R{n} ») et predecesseur_fini_universel l'unique résidu honnête de C61
    (Prop. 2 §III.5, non close — commun à toute la chaîne C61).
    Route = exactement le livre : S{0} (vacuité), S{n}⇒S{n+1} (Prop.2 + C58),
    C61 sur S, puis retour à R par H."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
        hypothese_recurrence_forte, conclusion_recurrence)

    def P(t):
        return s_recurrence_forte(R, t, p)

    base = s_forte_en_zero(R, p)                          # ⊢ S{0}          (CLOS)
    her = heredite_s_forte(R, "nhrd", p)                  # {H} ⊢ ∀n((Fini n et S{n})⇒S{n+1})
    c61 = principe_recurrence_preuve(P, n="nhrd")         # {pred_univ} ⊢ (S0 et her) ⇒ ∀n(Fini⇒S)
    tout_S = N.modus_ponens(conjonction_intro(base, her), c61)
    # retour à R : Fini n ⇒ S{n} ⇒ R{n}, généralisé
    vn = var("nfor")
    H = hypothese_recurrence_forte(R, "nfor", p)
    hH = N.assume(H)
    fini_vers_R = syllogisme(instancie(tout_S, vn), instancie(hH, vn))
    res = N.generalisation("nfor", fini_vers_R)
    assert res.conclusion == conclusion_recurrence(R, "nfor"), \
        "variante 1 : conclusion ≠ (∀n)(n entier ⇒ R{n})"
    assert len(res.hypotheses) == 2, "variante 1 : hypothèses ≠ {H, pred_univ}"
    return res


__all__ = ["s_forte_en_zero", "heredite_s_forte", "recurrence_forte"]
