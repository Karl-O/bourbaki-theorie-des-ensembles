"""§III.5.3 / §III.6.2 — LE PONT DE DOMAINE : le domaine de f⁽ᵏ⁺¹⁾ EST l'intervalle [0,k].

  🎯   `domaine_restriction_est_intervalle` { 2 résidus C62, k ∈ ℕ } ⊢
                                              dom( f | seg(ℕ, k+1) ) = [0, k]
  🎯🎯 `max_domaine_restriction_succ`       { 2 résidus C62, k ∈ ℕ } ⊢
                                              M( dom( f | seg(ℕ, k+1) ) ) = k

Le pont de SEGMENT lui-même — { k ∈ ℕ } ⊢ seg(ℕ, k+1) = [0, k] — est le module
voisin `ensembles_pont_segment_iii5.py` ; ICI on le TRANSPORTE au domaine de la
fonction globale de C62, puis sous le τ de M(·).

────────────────────────────────────────────────────────────────────────────────
LE PROBLÈME FERMÉ.  C62 (E III.46) applique M au domaine de la RESTRICTION
f⁽ⁿ⁾ := f | [0, n[ (SEMI-OUVERT), tandis que `max_intervalle_vaut_n_entier` n'évalue
M que sur le FERMÉ : { est_entier n } ⊢ M([0,n]) = n.  Au point SUCCESSEUR k+1 le
domaine de la restriction est [0, k], un FERMÉ, et M y vaut k DIRECTEMENT.

RÉSIDUS — DEUX, et ce sont les DONNÉES DE LA RÈGLE.  `dom_restriction_seg`
(§III.5.8) sort sous TROIS résidus C62 : { bo, essais_bien_formes, rule_codomain }.
Le premier, bo = est_bien_ordonne(R_G≤, ℕ), N'EN EST PAS UN sur le VRAI ℕ : c'est un
THÉORÈME du dépôt (`bo_graphe_NN`, iii_6_1_n_objet_existence, CLOS, 0 hypothèse).  Il
est donc DÉCHARGÉ ici par modus ponens (geste `_cut` du dépôt, celui de
`c62_recursion_sur_NN`) — le garder serait un affaiblissement GRATUIT.  Ne restent
que { essais_bien_formes(T), rule_codomain(T,V) } : les données de la règle T, plus
l'hypothèse honnête { k ∈ ℕ }.  C'est aussi la lettre du livre : « L'ensemble ℕ
ÉTANT BIEN ORDONNÉ, on peut lui appliquer le critère C60 » (E III.46 L.15-16) —
chez Bourbaki une justification, chez nous un théorème, pas une prémisse.

────────────────────────────────────────────────────────────────────────────────
⚠️ CE MODULE NE RECÂBLE PAS `regle_factorielle` : cela changerait une conclusion
PUBLIQUE consommée ailleurs (chantier SÉPARÉ).  Il fournit la formule à consommer.
⚠️ ÉCART DE FIDÉLITÉ HÉRITÉ, non refermé ici : Bourbaki écrit « M(u) = la BORNE
SUPÉRIEURE de D(u) » (E III.46 L.28-29), le dépôt explicite le τ du PLUS GRAND ÉLÉMENT
(`iii_1_7_plus_grand_plus_petit/ensembles_terme_plus_grand.py`) ; ils coïncident quand
le maximum EXISTE — donc sur [0,k] — pas en général.
⚠️ PERF MESURÉE (2026-07-27, pytest fichier seul, machine chargée par 2 autres process) :
9 passed en 581 s, dont 545 s pour le SEUL premier `domaine_restriction_est_intervalle`
(`bo_graphe_NN` + `fini_downward_garde_thm` + `N_existe`) ; une fois ceux-ci mémoïsés le
capstone ne coûte plus que 33 s.  La décharge du bon ordre est donc payante en
HONNÊTETÉ et coûteuse en TEMPS — d'où `_bo_NN` mémoïsé.  Tests marqués `slow`.
⚠️ THÉORIES AUXILIAIRES — « n hypothèses » ≠ « aucune prémisse invisible » : `N.axiome`
rend un théorème à hypothèses VIDES, donc les théories DÉDIÉES échappent au compte
d'hypothèses ET à l'invariant 22 (qui ne certifie que `theorie_ensembles()`).  AUCUNE
théorie n'est créée ici ; toutes sont PRÉEXISTANTES, héritées des briques appelées.
MESURÉ le 2026-07-27 (`outils_ia/verite/axiomes_consommes.dette`, process FRAIS, 1er
appel, DEUX règles `axiome` surveillées) sur le capstone :
  • 32 théories sollicitées = `Ensembles` (les 22 axiomes) + 31 théories DÉDIÉES ;
  • **65 FORMULES étrangères**, pas 31 : Graphe-terme 20, Graphe-induit-sous-ensemble 7,
    Dfam-real-C60 5, Segment-extremite 4, Pullback-seg-card 3, puis 26 noms à 1 formule
    (Dtot-C62, N-collectivise, G-ordre-NN, Intervalle-entiers, D-Knaster-Tarski, Infini(A4),
    la famille Zorn/Zermelo/Bourbaki-Witt/Comp/trichotomie, …) ;
  • dette totale (hypothèses non déchargées ∪ formules étrangères) = **68**.
Ce n'est donc PAS « 31 théories À 1 AXIOME » (chiffre FAUX de la version précédente de cet
en-tête) : cinq théories servent PLUSIEURS formules distinctes, seules 26 en servent une.
Chiffres IDENTIQUES avant et après la décharge du bon ordre (seule la dette bouge, 69 → 68) :
`bo_graphe_NN` ne fait entrer AUCUNE théorie nouvelle — elles étaient déjà toutes consommées
par la chaîne C62.  À comparer aux TROIS de `max_intervalle_vaut_n_entier` seul : c'est le
prix, honnête, du transport au domaine de la fonction globale de C62.

INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, congruence_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import (
    terme_plus_grand, LIANT_TAU, LIANT_MAJORE)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur, est_entier)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_max_intervalle_iii5 import (
    intervalle_zero, ordre_entiers, max_intervalle_vaut_n_entier)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_pont_segment_iii5 import (
    LIANT_POINT, NOM_K, TROU_MAX, NOMS_RESERVES, _t,
    segment_succ_NN, cible_segment_succ_intervalle, segment_succ_est_intervalle)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, bo_graphe_NN)


# ══ LE BON ORDRE DE ℕ — un THÉORÈME, pas un résidu ═════════════════════════════
def bon_ordre_NN_formule():
    """La formule  est_bien_ordonne(R_G≤, ℕ)  telle que la chaîne C62 la produit.

    EXPOSÉE pour que le test puisse asserter qu'elle N'EST PLUS une hypothèse."""
    return E.est_bien_ordonne(_graphe_R(G_ordre_NN()), ensemble_NN())


@lru_cache(maxsize=None)
def _bo_NN():
    """⊢ est_bien_ordonne(R_G≤, ℕ)      [CLOS, 0 hyp — `bo_graphe_NN`, §III.6.1].

    Le résidu « bo » de la chaîne C62 est ICI un théorème : transport de
    `n_bien_ordonne` (forme callable) vers la forme GRAPHE.  ⚠️ PERF : c'est le poste
    dominant du premier appel (cf. en-tête, 545 s pour bo + downward + N_existe ; la
    mesure ISOLÉE de `bo_graphe_NN` n'a PAS été refaite ici) — MÉMOÏSÉ, comme
    `_downward_fini_cardinal`."""
    thm = bo_graphe_NN()
    assert thm.est_clos, "_bo_NN : bo_graphe_NN n'est plus CLOS (0 hyp attendues)"
    assert thm.conclusion == bon_ordre_NN_formule(), \
        "_bo_NN : conclusion ≠ est_bien_ordonne(R_G≤, ℕ) — forme de la chaîne changée ?"
    return thm


# ══ (1) dom( f | seg(ℕ, k+1) ) = [0, k] — le pont TRANSPORTÉ au domaine de C62 ══
def terme_domaine_restriction(V="Uval", k=NOM_K):
    """Le TERME  dom( f | seg(ℕ, k+1) ),  f := ⋃𝔇_tot  la fonction globale de C62."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
        fonction_globale,
    )
    return E.dom(E.restriction(fonction_globale(ensemble_NN(), V), segment_succ_NN(k)))


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.19-19 | PDF p.149  (« l'application de [0, n[ sur f([0, n[) qui coïncide avec f dans [0, n[ » — le domaine de f⁽ⁿ⁾ ; au point n = k+1 ce domaine EST l'intervalle fermé [0,k])
def domaine_restriction_est_intervalle(vh, V="Uval", k=NOM_K, i=LIANT_POINT):
    """🎯 { essais_bien_formes, rule_codomain, k ∈ ℕ } ⊢
           dom( f | seg(ℕ, k+1) ) = [0, k].                              [3 hyps]

    `dom_restriction_seg` (§III.5.8) donne dom(f|seg) = seg sous TROIS résidus C62 ;
    le premier — bo = est_bien_ordonne(R_G≤, ℕ) — est DÉCHARGÉ par `_bo_NN` (CLOS)
    puisqu'on est sur le VRAI ℕ ; le pont `segment_succ_est_intervalle` (1 hyp
    honnête) remplace seg par [0,k].  Ne restent que les DONNÉES DE LA RÈGLE, qui
    ne sont prouvables pour AUCUNE règle en général : essais bien formés, codomaine.
    `vh` est la règle T de C62 (p. ex. `regle_factorielle`)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import (
        dom_restriction_seg,
    )
    vk = _t(k)
    dr = dom_restriction_seg(vh, ensemble_NN(), G_ordre_NN(), V, successeur(vk))
    assert len(dr.hypotheses) == 3, "domaine_restriction_est_intervalle : résidus C62 ≠ 3"
    bo = bon_ordre_NN_formule()
    assert bo in dr.hypotheses, \
        "domaine_restriction_est_intervalle : bo absent des résidus (forme changée ?)"
    dr = N.modus_ponens(_bo_NN(), N.loi_deduction(bo, dr))   # _cut : bo DÉCHARGÉ
    assert len(dr.hypotheses) == 2, \
        "domaine_restriction_est_intervalle : décharge du bon ordre ratée (≠ 2 résidus)"

    res = composer_egalites(dr, segment_succ_est_intervalle(vk, i))
    assert res.conclusion == egal(terme_domaine_restriction(V, vk), intervalle_zero(vk)), \
        "domaine_restriction_est_intervalle : conclusion ≠ dom(f|seg(k+1)) = [0,k]"
    assert res.hypotheses == dr.hypotheses | {appartient(vk, ensemble_NN())}, \
        "domaine_restriction_est_intervalle : hypothèses ≠ 2 résidus C62 + { k ∈ ℕ }"
    assert bo not in res.hypotheses, \
        "domaine_restriction_est_intervalle : le bon ordre a REFLUÉ dans les hypothèses"
    return res


# ══ (2) 🎯🎯 LE CAPSTONE :  M( dom( f | seg(ℕ, k+1) ) ) = k ════════════════════
def cible_max_domaine_restriction(V="Uval", k=NOM_K):
    """ÉNONCÉ-cible (test miroir) :  M( dom( f | seg(ℕ, k+1) ) ) = k."""
    return egal(terme_plus_grand(ordre_entiers, terme_domaine_restriction(V, k),
                                 LIANT_TAU, LIANT_MAJORE), _t(k))


# @livre Ch.III §6.2 Demo.C63 | E III.46 L.28-29 | PDF p.149  (« Soit M(u) la borne supérieure de D(u) dans N » — le terme M appliqué au domaine de la RESTRICTION : au point n = k+1 il DÉNOTE, et vaut k, c.-à-d. le « n − 1 » que C63 lit en f(n−1) L.23 ; lignes RECOMPTÉES sur le PNG, pas recopiées)
def max_domaine_restriction_succ(vh, V="Uval", k=NOM_K, i=LIANT_POINT):
    """🎯🎯 { essais_bien_formes, rule_codomain, k ∈ ℕ } ⊢
              M( dom( f | seg(ℕ, k+1) ) ) = k.                            [3 hyps]

    LE LIVRABLE : c'est CETTE formule que le recâblage de `regle_factorielle`
    consommera pour que `u(M(D u))` se lise `u(k)` au point k+1.  Assemblage : (1)
    donne dom(f|seg(k+1)) = [0,k] ; la congruence de terme (trou FRAIS « wdm ») la
    transporte sous M(·) ; `max_intervalle_vaut_n_entier` donne M([0,k]) = k sous
    { est_entier k }, DÉCHARGÉE par Fini k — tiré de k ∈ ℕ.  Aucune hypothèse
    gratuite : le compte final est EXACTEMENT celui de (1), bon ordre COMPRIS
    (déchargé là-bas, cf. `bon_ordre_NN_formule`)."""
    vk = _t(k)
    dom_eq = domaine_restriction_est_intervalle(vh, V, vk, i)
    Du = dom_eq.conclusion.termes[0]

    # M(dom u) = M([0,k])   (congruence de terme sous le τ de M ; trou FRAIS)
    tpl = terme_plus_grand(ordre_entiers, var(TROU_MAX), LIANT_TAU, LIANT_MAJORE)
    imp = congruence_terme(var(TROU_MAX), intervalle_zero(vk), tpl, TROU_MAX)
    e_max = N.modus_ponens(dom_eq, instancie(N.generalisation(TROU_MAX, imp), Du))

    # M([0,k]) = k   (est_entier k déchargé par Fini k, tiré de k ∈ ℕ)
    fini_k = N.modus_ponens(N.assume(appartient(vk, ensemble_NN())),
                            equivalence_avant(appartenance_NN_instanciee(vk)))
    mx = N.modus_ponens(fini_k, N.loi_deduction(est_entier(vk),
                                                max_intervalle_vaut_n_entier(vk)))
    res = composer_egalites(e_max, mx)

    assert res.conclusion == cible_max_domaine_restriction(V, vk), \
        "max_domaine_restriction_succ : conclusion ≠ M(dom(f|seg(k+1))) = k"
    assert res.hypotheses == dom_eq.hypotheses, \
        "max_domaine_restriction_succ : hypothèses ≠ celles du pont de domaine"
    assert bon_ordre_NN_formule() not in res.hypotheses, \
        "max_domaine_restriction_succ : le bon ordre est REDEVENU une hypothèse"
    assert res.conclusion not in res.hypotheses, "max_domaine_restriction_succ : VACUOUS"
    return res


__all__ = ["LIANT_POINT", "NOM_K", "TROU_MAX", "NOMS_RESERVES",
           "segment_succ_NN",
           "cible_segment_succ_intervalle", "segment_succ_est_intervalle",
           "bon_ordre_NN_formule",
           "terme_domaine_restriction", "domaine_restriction_est_intervalle",
           "cible_max_domaine_restriction", "max_domaine_restriction_succ"]
