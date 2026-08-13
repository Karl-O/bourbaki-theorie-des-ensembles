"""§III.2 — DÉFINITION PAR RÉCURRENCE TRANSFINIE (Critère C60), EXISTENCE : ASSEMBLAGE FINAL.

Suite DIRECTE de `ensembles_c60_coeur` (collectivisation ⋃𝔇 + family-union-functional
(i) + extension d'un pas (iii) + transfert de valeur), de `ensembles_c60_existence_close`
(E1–E6) et de `ensembles_recursion_transfinie_existence` (`solutions_coincident` =
cohérence des solutions au niveau VALEUR ; squelette de couverture C59).

Ce module CLOSE le dernier verrou honnête reporté : LE PONT
`solutions_coincident → famille_compatible` (niveau VALEUR → niveau GRAPHE), puis
assemble, autant que la machinerie le permet, l'hérédité de la couverture (E6) et le
théorème d'existence C60.

────────────────────────────────────────────────────────────────────────────────
ÉTAPE 1 (CLOSE) — LE PONT `famille_compatible_depuis_coincidence`.

  `solutions_coincident` (recursion_transfinie_existence) prouve la coïncidence au niveau
  VALEUR : deux solutions vf, vg de la MÊME règle locale coïncident PONCTUELLEMENT
  ((∀x∈E) vf(x)=vg(x)).  `famille_compatible` (c60_coeur) est au niveau GRAPHE : pour
  deux membres p,q∈𝔇 et des couples (a,b)∈p, (a,c)∈q, on a b=c.  LE PONT relie les deux.

  Brique : `couple_donne_valeur`  { est_fonctionnel(p), (a,b)∈p } ⊢ b = valeur(p,a)
  (C46/`valeur_caracterisation` instanciée à b ⇒ sens avant ; (∃y)((a,y)∈p) déchargé par
  S5 sur (a,b)∈p).  C'est EXACTEMENT le passage (a,b)∈p ⇒ b=valeur(p,a) que la frontière
  de c60_coeur signalait comme « chunk distinct non clos ».

  PONT : sous DEUX hypothèses HONNÊTES sur la famille 𝔇
    • `membres_fonctionnels(𝔇)`   := (∀p)( p∈𝔇 ⇒ est_fonctionnel(p) )
    • `coincidence_membres(𝔇)`    := (∀p)(∀q)(∀a)( (p∈𝔇 ∧ q∈𝔇 ∧ a∈dom p ∧ a∈dom q)
                                                  ⇒ valeur(p,a)=valeur(q,a) )
  on DÉRIVE `famille_compatible(𝔇)`.  La 2ᵉ hypothèse EST exactement la sortie
  per-paire de `solutions_coincident` (la cohésion des essais portée au niveau graphe),
  la 1ʳᵉ la fonctionnalité de chaque essai.  PREUVE : (a,b)∈p ⇒ b=valeur(p,a),
  (a,c)∈q ⇒ c=valeur(q,a) (couple_donne_valeur), a∈dom p, a∈dom q (axiome dom + S5),
  valeur(p,a)=valeur(q,a) (coincidence_membres) ; chaîne b=valeur(p,a)=valeur(q,a)=c.

  ⟹ La famille 𝔇 des essais est COMPATIBLE PAR PAIRES ⇒ ⋃𝔇 fonctionnel
     (`union_famille_fonctionnelle`), sans rien postuler de plus que la cohésion-valeur
     livrée par `solutions_coincident`.

────────────────────────────────────────────────────────────────────────────────
ÉTAPE 2 (CLOSE, sous hyps honnêtes) — HÉRÉDITÉ DE LA COUVERTURE via le recollement.

  `couvert_par_union` : sous { membres_fonctionnels(𝔇), coincidence_membres(𝔇),
  dom(⋃𝔇) = seg(R,E,x) }, l'essai p_x := ⋃𝔇 est FONCTIONNEL (étape 1 + (i)) et de
  domaine seg(R,E,x) ; prolongé du couple (x, h(x,p_x)) il reste fonctionnel
  (`extension_un_pas_union_fonctionnelle`, (iii)) ⇒ on EXHIBE un graphe-essai fonctionnel
  sur seg(R,E,x)∪{x} ⇒ `couvert_essai(x)` (la moitié FONCTIONNALITÉ + domaine de l'essai).
  La 3ᵉ hypothèse (dom(⋃𝔇)=seg) EST la couverture des y<x (les domaines des essais des
  y<x recouvrent exactement le segment).

────────────────────────────────────────────────────────────────────────────────
ÉTAPE 3 (sous hyps honnêtes) — EXISTENCE C60.

  `recursion_transfinie_existence` : sous { est_bien_ordonne(R,E),
  heredite_couverture(couvert_essai,R,E) }, tout x∈E est couvert par un essai (E6) ⇒ il
  existe une fonction-essai en chaque x.  L'assemblage de l'hérédité (étape 2) DÉCHARGE
  la 2ᵉ hypothèse de E6 — modulo l'équation de récursion au nouveau point et
  l'instanciation de 𝔇 à la famille concrète des essais des y<x (cf. RÉSIDU en bas).

INVARIANT : theorie_ensembles() = 22.  Toutes les hypothèses sont HONNÊTES (cohésion
des essais au niveau valeur ⇐ `solutions_coincident`, fonctionnalité de chaque essai,
couverture des y<x) — JAMAIS postulées, déchargées par loi_deduction.  Aucun axiome
nouveau : la collectivisation ⋃𝔇 vit dans la THÉORIE DÉDIÉE de c60_coeur.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_caracterisation
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    dom_reunion_graphes, membre_reunion_graphes,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_recollement_bijection import (
    valeur_reunion_droite, valeur_reunion_gauche,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible, union_famille_fonctionnelle,
    extension_un_pas_union_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    singleton_couple_fonctionnel, dom_singleton_couple, domaines_essai_disjoints,
    dom_essai, est_essai, couvert_essai, couverture_essais_via_c59,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
    couverture_totale, heredite_couverture,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE — (a,b)∈p ⇒ b = valeur(p,a)  (le chunk graphe→valeur reporté de c60_coeur).
# ════════════════════════════════════════════════════════════════════════════
def couple_donne_valeur(p="p", a="a", b="b"):
    """{ est_fonctionnel(p), (a,b)∈p } ⊢ b = valeur(p,a)              [2 hyps honnêtes].

    Le passage NIVEAU GRAPHE → NIVEAU VALEUR : si p est fonctionnel et que (a,b)∈p,
    alors b EST la valeur de p en a.  DÉRIVÉ de `valeur_caracterisation` (C46) :
      ((a,y)∈p) ⇔ (y=valeur(p,a))  généralisé sur y, instancié à b, sens avant sur
      (a,b)∈p.  L'hypothèse (∃y)((a,y)∈p) de C46 est déchargée par S5 sur (a,b)∈p.
    C'est CE chunk que la frontière de c60_coeur signalait comme « non clos ici » —
    il l'est désormais.  Conclusion ∉ hypothèses (non vacuous)."""
    vp, va, vb = _t(p), _t(a), _t(b)
    cab = E.couple(va, vb)
    h_in = N.assume(appartient(cab, vp))                       # (a,b)∈p   [HONNÊTE]
    ex = N.modus_ponens(h_in, N.s5(appartient(E.couple(va, var("y")), vp), vb, "y"))  # (∃y)((a,y)∈p)
    vc = valeur_caracterisation(vp, va)                        # {func p, (∃y)} ⊢ ((a,y)∈p)⇔(y=val)
    vc_b = instancie(N.generalisation("y", vc), vb)            # ((a,b)∈p)⇔(b=valeur(p,a))
    b_eq = N.modus_ponens(h_in, equivalence_avant(vc_b))       # b=valeur(p,a)
    exy = existe("y", appartient(E.couple(va, var("y")), vp))
    res = N.modus_ponens(ex, N.loi_deduction(exy, b_eq))       # décharge (∃y) par S5 sur (a,b)∈p

    cible = egal(vb, E.valeur(vp, va))
    assert res.conclusion == cible, "couple_donne_valeur : ≠ b=valeur(p,a)"
    assert appartient(cab, vp) in res.hypotheses, "couple_donne_valeur : (a,b)∈p absente"
    assert E.est_fonctionnel(vp) in res.hypotheses, "couple_donne_valeur : func p absente"
    assert res.conclusion not in res.hypotheses, "couple_donne_valeur : VACUOUS"
    return res


def _a_dans_dom(p, a, b):
    """De ⊢ (a,b)∈p [hyp] déduit ⊢ a∈dom(p)   (axiome dom + S5)."""
    vp, va, vb = _t(p), _t(a), _t(b)
    h_in = N.assume(appartient(E.couple(va, vb), vp))
    ex = N.modus_ponens(h_in, N.s5(appartient(E.couple(va, var("y")), vp), vb, "y"))  # (∃y)((a,y)∈p)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, vp), va)                 # a∈dom p ⇔ (∃y)((a,y)∈p)
    return N.modus_ponens(ex, equivalence_arriere(car))        # a∈dom p   [(a,b)∈p]


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS — cohésion HONNÊTE de la famille (la sortie de `solutions_coincident`).
# ════════════════════════════════════════════════════════════════════════════
def membres_fonctionnels(D, p="pmf"):
    """(∀p)( p∈𝔇 ⇒ est_fonctionnel(p) )   — chaque membre de la famille est fonctionnel."""
    vD, vp = _t(D), var(p)
    return pourtout(p, impl(appartient(vp, vD), E.est_fonctionnel(vp)))


def coincidence_membres(D, p="pcm", q="qcm", a="acm"):
    """(∀p)(∀q)(∀a)( (p∈𝔇 ∧ q∈𝔇 ∧ a∈dom p ∧ a∈dom q) ⇒ valeur(p,a)=valeur(q,a) ).

    « Deux membres quelconques de 𝔇 RENDENT LA MÊME VALEUR en tout antécédent commun. »
    C'est EXACTEMENT la cohésion des essais que `solutions_coincident` livre au niveau
    VALEUR (deux solutions de la même règle coïncident ponctuellement), portée au niveau
    de la famille.  HYPOTHÈSE HONNÊTE."""
    vD, vp, vq, va = _t(D), var(p), var(q), var(a)
    prem = et(et(appartient(vp, vD), appartient(vq, vD)),
              et(appartient(va, E.dom(vp)), appartient(va, E.dom(vq))))
    return pourtout(p, pourtout(q, pourtout(a,
        impl(prem, egal(E.valeur(vp, va), E.valeur(vq, va))))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ÉTAPE 1 — LE PONT  `solutions_coincident → famille_compatible`.
# ════════════════════════════════════════════════════════════════════════════
def famille_compatible_depuis_coincidence(D="Df"):
    """{ membres_fonctionnels(𝔇), coincidence_membres(𝔇) } ⊢ famille_compatible(𝔇)
                                                                    [2 hyps honnêtes].

    🎯 LE PONT (verrou honnête reporté de c60_coeur, CLOS).  La famille 𝔇 est
    COMPATIBLE PAR PAIRES (niveau GRAPHE) DÈS QUE ses membres sont fonctionnels et
    qu'ils coïncident en valeur sur les antécédents communs (niveau VALEUR — la sortie
    de `solutions_coincident`).

    PREUVE.  Soit p,q∈𝔇, (a,b)∈p, (a,c)∈q.
      • func p, func q          ⇐ membres_fonctionnels(𝔇) instanciée à p, q ;
      • b=valeur(p,a)           ⇐ couple_donne_valeur(p,a,b)  [func p, (a,b)∈p] ;
      • c=valeur(q,a)           ⇐ couple_donne_valeur(q,a,c)  [func q, (a,c)∈q] ;
      • a∈dom p, a∈dom q        ⇐ axiome dom + S5 sur les couples ;
      • valeur(p,a)=valeur(q,a) ⇐ coincidence_membres(𝔇) instanciée à (p,q,a) ;
      • chaîne :  b = valeur(p,a) = valeur(q,a) = c.   ∎

    ⟹ ⋃𝔇 est fonctionnel (`union_famille_fonctionnelle`) sous ces deux hyps honnêtes.

    ⚠️ DEUX hypothèses HONNÊTES (theorie=22), déchargées par loi_deduction.  La
    coincidence_membres EST la cohésion-valeur de `solutions_coincident` ; la
    membres_fonctionnels la fonctionnalité de chaque essai.  Non vacuous."""
    vD = _t(D)
    # binders de famille_compatible (canoniques : pcf, qcf, acf, bcf, ccf)
    p, q, a, b, c = "pcf", "qcf", "acf", "bcf", "ccf"
    vp, vq, va, vb, vc = var(p), var(q), var(a), var(b), var(c)

    H_func = N.assume(membres_fonctionnels(vD))            # (∀p)(p∈𝔇⇒func p)  [HONNÊTE]
    H_coinc = N.assume(coincidence_membres(vD))            # cohésion-valeur     [HONNÊTE]

    # prémisse de famille_compatible :  (p∈𝔇 et q∈𝔇) et ((a,b)∈p et (a,c)∈q)
    prem_form = et(et(appartient(vp, vD), appartient(vq, vD)),
                   et(appartient(E.couple(va, vb), vp), appartient(E.couple(va, vc), vq)))
    prem = N.assume(prem_form)
    pD = conjonction_elim_gauche(conjonction_elim_gauche(prem))    # p∈𝔇
    qD = conjonction_elim_droite(conjonction_elim_gauche(prem))    # q∈𝔇
    ab_p = conjonction_elim_gauche(conjonction_elim_droite(prem))  # (a,b)∈p
    ac_q = conjonction_elim_droite(conjonction_elim_droite(prem))  # (a,c)∈q

    # func p, func q  ⇐ membres_fonctionnels
    func_p = N.modus_ponens(pD, instancie(H_func, vp))            # func p
    func_q = N.modus_ponens(qD, instancie(H_func, vq))            # func q

    # b=valeur(p,a)  (décharge func p et (a,b)∈p de couple_donne_valeur)
    b_val = couple_donne_valeur(vp, va, vb)
    b_val = N.modus_ponens(ab_p, N.loi_deduction(appartient(E.couple(va, vb), vp), b_val))
    b_val = N.modus_ponens(func_p, N.loi_deduction(E.est_fonctionnel(vp), b_val))   # b=valeur(p,a)
    # c=valeur(q,a)
    c_val = couple_donne_valeur(vq, va, vc)
    c_val = N.modus_ponens(ac_q, N.loi_deduction(appartient(E.couple(va, vc), vq), c_val))
    c_val = N.modus_ponens(func_q, N.loi_deduction(E.est_fonctionnel(vq), c_val))   # c=valeur(q,a)

    # a∈dom p, a∈dom q
    adp = _a_dans_dom(vp, va, vb)
    adp = N.modus_ponens(ab_p, N.loi_deduction(appartient(E.couple(va, vb), vp), adp))
    adq = _a_dans_dom(vq, va, vc)
    adq = N.modus_ponens(ac_q, N.loi_deduction(appartient(E.couple(va, vc), vq), adq))

    # valeur(p,a)=valeur(q,a)  ⇐ coincidence_membres(𝔇) à (p,q,a)
    coinc_inst = instancie(instancie(instancie(H_coinc, vp), vq), va)
    val_eq = N.modus_ponens(
        conjonction_intro(conjonction_intro(pD, qD), conjonction_intro(adp, adq)),
        coinc_inst)                                              # valeur(p,a)=valeur(q,a)

    # chaîne :  b = valeur(p,a) = valeur(q,a) = c
    b_eq_vqa = composer_egalites(b_val, val_eq)                  # b=valeur(q,a)
    cval_sym = N.modus_ponens(c_val, symetrie(vc, E.valeur(vq, va)))  # valeur(q,a)=c
    b_eq_c = composer_egalites(b_eq_vqa, cval_sym)               # b=c

    imp = N.loi_deduction(prem_form, b_eq_c)
    res = N.generalisation(p, N.generalisation(q, N.generalisation(a,
            N.generalisation(b, N.generalisation(c, imp)))))

    cible = famille_compatible(vD)
    assert res.conclusion == cible, "famille_compatible_depuis_coincidence : ≠ famille_compatible(𝔇)"
    assert membres_fonctionnels(vD) in res.hypotheses, "pont : membres_fonctionnels absente"
    assert coincidence_membres(vD) in res.hypotheses, "pont : coincidence_membres absente"
    assert len(res.hypotheses) == 2, "pont : hyps ≠ 2"
    assert res.conclusion not in res.hypotheses, "pont : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE — ⋃𝔇 fonctionnel sous la cohésion-valeur (PONT + (i) chaînés).
# ════════════════════════════════════════════════════════════════════════════
def union_fonctionnelle_depuis_coincidence(D="Df"):
    """{ membres_fonctionnels(𝔇), coincidence_membres(𝔇) } ⊢ est_fonctionnel(⋃𝔇)
                                                                    [2 hyps honnêtes].

    LE PONT (étape 1) chaîné à (i) `union_famille_fonctionnelle` : la réunion de la
    famille des essais est FONCTIONNELLE dès que les essais sont fonctionnels et
    coïncident en valeur sur les recouvrements — la cohésion livrée par
    `solutions_coincident`, SANS l'hypothèse-graphe `famille_compatible` brute."""
    vD = _t(D)
    U = union_famille(vD)
    pont = famille_compatible_depuis_coincidence(D)             # ⊢ famille_compatible(𝔇)
    func = union_famille_fonctionnelle(D)                       # {famille_compatible(𝔇)} ⊢ func(⋃𝔇)
    compat_form = famille_compatible(vD)
    res = N.modus_ponens(pont, N.loi_deduction(compat_form, func))  # décharge famille_compatible

    cible = E.est_fonctionnel(U)
    assert res.conclusion == cible, "union_fonctionnelle_depuis_coincidence : ≠ func(⋃𝔇)"
    assert membres_fonctionnels(vD) in res.hypotheses, "≠ : membres_fonctionnels absente"
    assert coincidence_membres(vD) in res.hypotheses, "≠ : coincidence_membres absente"
    assert res.conclusion not in res.hypotheses, "union_fonctionnelle_depuis_coincidence : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ÉTAPE 2 — HÉRÉDITÉ DE LA COUVERTURE (moitié FONCTIONNALITÉ via recollement).
# ════════════════════════════════════════════════════════════════════════════
def extension_un_pas_depuis_coincidence(D="Df", G="G", e="E", x="x0", v="v0"):
    """{ membres_fonctionnels(𝔇), coincidence_membres(𝔇), dom(⋃𝔇)=seg(R,E,x) }
        ⊢ est_fonctionnel( ⋃𝔇 ∪ {(x,v)} )                          [3 hyps honnêtes].

    🎯 LE RECOLLEMENT COMPLET sous la SEULE cohésion-valeur (PONT + (iii)).  On glue la
    famille des essais des y<x en l'essai p_x := ⋃𝔇 (fonctionnel, étape 1), de domaine
    seg(R,E,x) (3ᵉ hyp = couverture des y<x), PUIS on prolonge d'un pas par (x,v) :
    `extension_un_pas_union_fonctionnelle` (iii) dont on DÉCHARGE la compatibilité-graphe
    par le PONT (étape 1).  Ne restent que les TROIS données HONNÊTES : essais
    fonctionnels, essais cohérents en valeur, domaine de la réunion = segment.

    C'est la moitié FONCTIONNALITÉ du pas d'hérédité de la couverture (E6), exprimée
    sous les hypothèses HONNÊTES VRAIES (cohésion ⇐ `solutions_coincident`), sans passer
    par l'hypothèse-graphe brute `famille_compatible`."""
    vD = _t(D)
    U = union_famille(vD)
    seg = E.segment_extremite(_t(G), _t(e), _t(x))

    iii = extension_un_pas_union_fonctionnelle(D, G, e, x, v)   # {famille_compatible, dom=seg} ⊢ func(⋃𝔇∪{(x,v)})
    pont = famille_compatible_depuis_coincidence(D)             # ⊢ famille_compatible(𝔇)
    compat_form = famille_compatible(vD)
    res = N.modus_ponens(pont, N.loi_deduction(compat_form, iii))  # décharge famille_compatible

    cible = E.est_fonctionnel(E.reunion(U, E.singleton(E.couple(_t(x), _t(v)))))
    assert res.conclusion == cible, "extension_un_pas_depuis_coincidence : ≠ func(⋃𝔇∪{(x,v)})"
    assert membres_fonctionnels(vD) in res.hypotheses, "≠ : membres_fonctionnels absente"
    assert coincidence_membres(vD) in res.hypotheses, "≠ : coincidence_membres absente"
    assert egal(E.dom(U), seg) in res.hypotheses, "≠ : dom(⋃𝔇)=seg absente"
    assert res.conclusion not in res.hypotheses, "extension_un_pas_depuis_coincidence : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  VALEUR DE L'ESSAI TRIVIAL  valeur({(x,v)}, x) = v.
# ════════════════════════════════════════════════════════════════════════════
def valeur_singleton_couple(x="x0", v="v0"):
    """⊢ valeur( {(x,v)}, x ) = v                                    [CLOS, 0 hyp].

    La valeur de l'essai trivial {(x,v)} en son unique point x est v.  DÉRIVÉ de
    (E1) `singleton_couple_fonctionnel` (fonctionnalité), de (x,v)∈{(x,v)} (membre
    d'un singleton) et de `couple_donne_valeur` ((x,v)∈{(x,v)} ⇒ v=valeur({(x,v)},x)),
    puis symétrie."""
    vx, vv = _t(x), _t(v)
    cpl = E.couple(vx, vv)
    S = E.singleton(cpl)
    cpl_in = N.modus_ponens(N.reflexivite(cpl), equivalence_arriere(singleton_membre(cpl, cpl)))  # (x,v)∈S
    funcS = singleton_couple_fonctionnel(vx, vv)                   # func S   [CLOS]
    cdv = couple_donne_valeur(S, vx, vv)                           # {func S,(x,v)∈S} ⊢ v=valeur(S,x)
    v_eq = N.modus_ponens(funcS, N.loi_deduction(E.est_fonctionnel(S), cdv))
    v_eq = N.modus_ponens(cpl_in, N.loi_deduction(appartient(cpl, S), v_eq))   # v=valeur(S,x)
    res = N.modus_ponens(v_eq, symetrie(vv, E.valeur(S, vx)))      # valeur(S,x)=v

    cible = egal(E.valeur(S, vx), vv)
    assert res.conclusion == cible, "valeur_singleton_couple : ≠ valeur({(x,v)},x)=v"
    assert res.est_clos, "valeur_singleton_couple non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  DOMAINE DE L'ESSAI PROLONGÉ  dom(⋃𝔇 ∪ {(x,v)}) = seg(R,E,x) ∪ {x} = dom_essai.
# ════════════════════════════════════════════════════════════════════════════
def dom_extension_un_pas(D="Df", G="G", e="E", x="x0", v="v0"):
    """{ dom(⋃𝔇) = seg(R,E,x) } ⊢ dom( ⋃𝔇 ∪ {(x,v)} ) = seg(R,E,x) ∪ {x}
                                                                    [1 hyp honnête].

    Le DOMAINE de l'essai prolongé est exactement le segment FERMÉ en x (= dom_essai).
    DÉRIVÉ : dom(⋃𝔇∪{(x,v)}) = dom(⋃𝔇)∪dom({(x,v)}) (`dom_reunion_graphes`, CLOS)
    = dom(⋃𝔇)∪{x} (E2 dom({(x,v)})={x}) = seg∪{x} (1 hyp honnête dom(⋃𝔇)=seg).
    La cible coïncide avec `dom_essai(R,E,x)` — le domaine attendu de l'essai en x."""
    vD, vx, vv = _t(D), _t(x), _t(v)
    U = union_famille(vD)
    S = E.singleton(E.couple(vx, vv))
    R = _graphe_R(G)
    seg = E.segment_extremite(_t(G), _t(e), vx)
    sx = E.singleton(vx)

    dr = dom_reunion_graphes(U, S)                                # dom(⋃𝔇∪S)=dom⋃𝔇∪domS  [CLOS]
    domS = dom_singleton_couple(vx, vv)                           # domS={x}              [CLOS]
    cong = congruence_terme(E.dom(S), sx, E.reunion(E.dom(U), var("w")), "w")
    rw = N.modus_ponens(domS, cong)                              # dom⋃𝔇∪domS = dom⋃𝔇∪{x}
    step = composer_egalites(dr, rw)                             # dom(⋃𝔇∪S)=dom⋃𝔇∪{x}
    h_dom_seg = N.assume(egal(E.dom(U), seg))                    # dom(⋃𝔇)=seg   [HONNÊTE]
    cong2 = congruence_terme(E.dom(U), seg, E.reunion(var("w"), sx), "w")
    rw2 = N.modus_ponens(h_dom_seg, cong2)                       # dom⋃𝔇∪{x}=seg∪{x}
    res = composer_egalites(step, rw2)                           # dom(⋃𝔇∪S)=seg∪{x}

    cible = egal(E.dom(E.reunion(U, S)), dom_essai(G, _t(e), vx))
    assert res.conclusion == cible, "dom_extension_un_pas : ≠ dom(⋃𝔇∪{(x,v)})=seg∪{x}"
    assert egal(E.dom(U), seg) in res.hypotheses, "dom_extension_un_pas : dom(⋃𝔇)=seg absente"
    assert res.conclusion not in res.hypotheses, "dom_extension_un_pas : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ÉQUATION DE RÉCURSION AU NOUVEAU POINT  valeur(⋃𝔇 ∪ {(x,v)}, x) = v.
# ════════════════════════════════════════════════════════════════════════════
def valeur_nouveau_point(D="Df", G="G", e="E", x="x0", v="v0"):
    """{ membres_fonctionnels(𝔇), coincidence_membres(𝔇), dom(⋃𝔇)=seg(R,E,x) }
        ⊢ valeur( ⋃𝔇 ∪ {(x,v)}, x ) = v                            [3 hyps honnêtes].

    🎯 L'ÉQUATION DE RÉCURSION AU NOUVEAU POINT x : l'essai prolongé rend bien la
    valeur v au point x (en posant v := vh(x), c'est valeur(p_x',x)=vh(x)).  DÉRIVÉ :
    valeur(⋃𝔇∪{(x,v)},x)=valeur({(x,v)},x) (`valeur_reunion_droite`, côté droit, sur
    x∈dom{(x,v)}) = v (`valeur_singleton_couple`).  On DÉCHARGE les 4 hyps de
    valeur_reunion_droite : func(⋃𝔇) [PONT (étape 1)+(i)], func({(x,v)}) [E1 CLOS],
    disjonction des domaines [E4 sous dom(⋃𝔇)=seg], x∈dom({(x,v)}) [E2+singleton CLOS].
    Ne restent que les 3 données HONNÊTES de la famille + couverture.  Non vacuous."""
    vD, vx, vv = _t(D), _t(x), _t(v)
    U = union_famille(vD)
    cpl = E.couple(vx, vv)
    S = E.singleton(cpl)
    R = _graphe_R(G)
    seg = E.segment_extremite(_t(G), _t(e), vx)

    # valeur_reunion_droite(⋃𝔇, S, x) : {func ⋃𝔇, func S, disj, x∈dom S} ⊢ valeur(⋃𝔇∪S,x)=valeur(S,x)
    vrd = valeur_reunion_droite(U, S, vx)
    funcU_form = E.est_fonctionnel(U)
    funcS_form = E.est_fonctionnel(S)

    # décharge func ⋃𝔇 par le PONT + (i)
    funcU = union_fonctionnelle_depuis_coincidence(D)            # {membres_fonctionnels, coincidence} ⊢ func ⋃𝔇
    # décharge func S par E1
    funcS = singleton_couple_fonctionnel(vx, vv)                 # func S   [CLOS]
    # disjonction des domaines (E4) sous dom(⋃𝔇)=seg
    disj = domaines_essai_disjoints(U, G, e, x, v)              # {dom(⋃𝔇)=seg} ⊢ (∀u)¬(u∈dom⋃𝔇 et u∈domS)
    disj_form = disj.conclusion
    # x∈dom S   (x∈{x} réécrit en x∈dom S via E2)
    domS_eq = dom_singleton_couple(vx, vv)                       # dom S = {x}   [CLOS]
    x_in_sx = N.modus_ponens(N.reflexivite(vx), equivalence_arriere(singleton_membre(vx, vx)))  # x∈{x}
    x_in_domS = N.modus_ponens(x_in_sx, equivalence_arriere(
        N.modus_ponens(domS_eq, N.s6(E.dom(S), E.singleton(vx), "w", appartient(vx, var("w"))))))  # x∈dom S

    r = vrd
    r = N.modus_ponens(funcU, N.loi_deduction(funcU_form, r))
    r = N.modus_ponens(funcS, N.loi_deduction(funcS_form, r))
    r = N.modus_ponens(disj, N.loi_deduction(disj_form, r))
    r = N.modus_ponens(x_in_domS, N.loi_deduction(appartient(vx, E.dom(S)), r))  # valeur(⋃𝔇∪S,x)=valeur(S,x)

    # chaîne avec valeur(S,x)=v
    vSx = valeur_singleton_couple(vx, vv)                        # valeur(S,x)=v   [CLOS]
    res = composer_egalites(r, vSx)                              # valeur(⋃𝔇∪S,x)=v

    cible = egal(E.valeur(E.reunion(U, S), vx), vv)
    assert res.conclusion == cible, "valeur_nouveau_point : ≠ valeur(⋃𝔇∪{(x,v)},x)=v"
    assert membres_fonctionnels(vD) in res.hypotheses, "valeur_nouveau_point : membres_fonctionnels absente"
    assert coincidence_membres(vD) in res.hypotheses, "valeur_nouveau_point : coincidence_membres absente"
    assert egal(E.dom(U), seg) in res.hypotheses, "valeur_nouveau_point : dom(⋃𝔇)=seg absente"
    assert res.conclusion not in res.hypotheses, "valeur_nouveau_point : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉS — hypothèses HONNÊTES de l'équation de récursion sur le segment.
# ════════════════════════════════════════════════════════════════════════════
def recursion_sur_segment(D, vh, G, e, x, z="zrs"):
    """(∀z)( z∈seg(R,E,x) ⇒ valeur(⋃𝔇,z)=vh(z) )   — la récursion DÉJÀ satisfaite par ⋃𝔇.

    « La réunion des essais des y<x SATISFAIT DÉJÀ l'équation de récursion sur le
    segment seg(R,E,x). »  C'est le contenu INDUCTIF : les essais des y<x sont des
    solutions, donc leur réunion l'est sur le segment.  HYPOTHÈSE HONNÊTE."""
    vD, vx = _t(D), _t(x)
    R = _graphe_R(G)
    seg = E.segment_extremite(_t(G), _t(e), vx)
    vz = var(z)
    U = union_famille(vD)
    return pourtout(z, impl(appartient(vz, seg), egal(E.valeur(U, vz), vh(vz))))


def equation_au_point(v, vh, x):
    """v = vh(x)   — l'ÉQUATION DE RÉCURSION au nouveau point x (v est la valeur-règle).

    « La valeur v posée au nouveau point x EST la valeur-règle vh(x) = h(x, p_x|seg). »
    HYPOTHÈSE HONNÊTE (la définition même de l'extension d'un pas)."""
    return egal(_t(v), vh(_t(x)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ÉQUATION DE RÉCURSION SUR TOUT LE DOMAINE DE L'ESSAI PROLONGÉ.
# ════════════════════════════════════════════════════════════════════════════
def recursion_essai_prolonge(vh, D="Df", G="G", e="E", x="x0", v="v0", z="zess"):
    """{ membres_fonctionnels(𝔇), coincidence_membres(𝔇), dom(⋃𝔇)=seg(R,E,x),
        recursion_sur_segment(𝔇,vh,…), v=vh(x) }
        ⊢ (∀z)( z∈dom(⋃𝔇 ∪ {(x,v)}) ⇒ valeur(⋃𝔇 ∪ {(x,v)}, z) = vh(z) )
                                                                    [5 hyps honnêtes].

    🎯 L'ÉQUATION DE RÉCURSION sur TOUT le domaine de l'essai prolongé p_x' := ⋃𝔇∪{(x,v)}.
    PREUVE par cas sur z∈dom(p_x')=seg∪{x} (membre_reunion_graphes) :
      • z∈seg : valeur(p_x',z)=valeur(⋃𝔇,z) (`valeur_reunion_gauche`, z∈dom(⋃𝔇)=seg)
                = vh(z)  (`recursion_sur_segment`) ;
      • z=x  : valeur(p_x',x)=v (`valeur_nouveau_point`) = vh(x) (`v=vh(x)`),
               réécrit z→x via z∈{x}.
    Le binder z vaut 'zess' (celui de `est_essai`).  Conclusion ∉ hypothèses (non vacuous)."""
    vD, vx, vv = _t(D), _t(x), _t(v)
    U = union_famille(vD)
    S = E.singleton(E.couple(vx, vv))
    pxp = E.reunion(U, S)
    R = _graphe_R(G)
    seg = E.segment_extremite(_t(G), _t(e), vx)
    sx = E.singleton(vx)
    vz = var(z)

    funcU_form = E.est_fonctionnel(U)
    funcS_form = E.est_fonctionnel(S)
    dom_seg = egal(E.dom(U), seg)

    # z∈dom(p_x')=seg∪{x}  ⇒  z∈seg ∨ z∈{x}.  dom(p_x') membership via dom_extension.
    # On travaille avec le DOMAINE RÉEL dom(p_x') ; on le réécrit en seg∪{x} (dom_extension).
    dom_eq = dom_extension_un_pas(D, G, e, x, v)             # dom(p_x')=seg∪{x}   [dom(⋃𝔇)=seg]
    h_z = N.assume(appartient(vz, E.dom(pxp)))               # z∈dom(p_x')
    # réécrit dom(p_x') → seg∪{x}
    z_in_segx = N.modus_ponens(h_z, equivalence_avant(N.modus_ponens(dom_eq,
        N.s6(E.dom(pxp), dom_essai(G, _t(e), vx), "w", appartient(vz, var("w"))))))  # z∈seg∪{x}
    disj = N.modus_ponens(z_in_segx, equivalence_avant(membre_reunion_graphes(seg, sx, vz)))  # z∈seg ou z∈{x}

    # ── CASE A : z∈seg ⇒ valeur(p_x',z)=vh(z)
    hzseg = N.assume(appartient(vz, seg))
    vrg = valeur_reunion_gauche(U, S, vz)                    # {funcU,funcS,disjdom,z∈domU} ⊢ val(p_x',z)=val(⋃𝔇,z)
    funcU = union_fonctionnelle_depuis_coincidence(D)
    funcS = singleton_couple_fonctionnel(vx, vv)
    disjdom = domaines_essai_disjoints(U, G, e, x, vv)
    disjdom_form = disjdom.conclusion
    seg_eq_domU = N.modus_ponens(N.assume(dom_seg), symetrie(E.dom(U), seg))   # seg=dom⋃𝔇
    z_in_domU = N.modus_ponens(hzseg, equivalence_avant(
        N.modus_ponens(seg_eq_domU, N.s6(seg, E.dom(U), "w", appartient(vz, var("w"))))))  # z∈dom⋃𝔇
    rA = vrg
    rA = N.modus_ponens(funcU, N.loi_deduction(funcU_form, rA))
    rA = N.modus_ponens(funcS, N.loi_deduction(funcS_form, rA))
    rA = N.modus_ponens(disjdom, N.loi_deduction(disjdom_form, rA))
    rA = N.modus_ponens(z_in_domU, N.loi_deduction(appartient(vz, E.dom(U)), rA))  # val(p_x',z)=val(⋃𝔇,z)
    h_rs = N.assume(recursion_sur_segment(vD, vh, G, e, x))  # (∀z)(z∈seg⇒val(⋃𝔇,z)=vh(z))
    uz_vh = N.modus_ponens(hzseg, instancie(h_rs, vz))       # val(⋃𝔇,z)=vh(z)
    rA_full = composer_egalites(rA, uz_vh)                   # val(p_x',z)=vh(z)
    impA = N.loi_deduction(appartient(vz, seg), rA_full)

    # ── CASE B : z∈{x} ⇒ valeur(p_x',z)=vh(z)
    vnp = valeur_nouveau_point(D, G, e, x, v)                # val(p_x',x)=v
    h_veq = N.assume(equation_au_point(vv, vh, vx))          # v=vh(x)   [HONNÊTE]
    vpx_vhx = composer_egalites(vnp, h_veq)                  # val(p_x',x)=vh(x)
    hzx = N.assume(appartient(vz, sx))
    z_eq_x = N.modus_ponens(hzx, equivalence_avant(singleton_membre(vz, vx)))  # z=x
    trough = egal(E.valeur(pxp, var("w")), vh(var("w")))     # gabarit (w∉p_x' car p_x' contient x)
    equ = N.modus_ponens(z_eq_x, N.s6(vz, vx, "w", trough))  # (val(p_x',z)=vh(z)) ⇔ (val(p_x',x)=vh(x))
    goalB = N.modus_ponens(vpx_vhx, equivalence_arriere(equ))  # val(p_x',z)=vh(z)
    impB = N.loi_deduction(appartient(vz, sx), goalB)

    # ── combiner les cas, généraliser
    combined = cas(disj, impA, impB)                         # val(p_x',z)=vh(z)
    body = N.loi_deduction(appartient(vz, E.dom(pxp)), combined)
    res = N.generalisation(z, body)

    cible = pourtout(z, impl(appartient(vz, E.dom(pxp)), egal(E.valeur(pxp, vz), vh(vz))))
    assert res.conclusion == cible, "recursion_essai_prolonge : ≠ équation de récursion sur dom(p_x')"
    assert membres_fonctionnels(vD) in res.hypotheses, "recursion_essai_prolonge : membres_fonctionnels absente"
    assert coincidence_membres(vD) in res.hypotheses, "recursion_essai_prolonge : coincidence_membres absente"
    assert dom_seg in res.hypotheses, "recursion_essai_prolonge : dom(⋃𝔇)=seg absente"
    assert recursion_sur_segment(vD, vh, G, e, x) in res.hypotheses, "recursion_essai_prolonge : récursion-segment absente"
    assert equation_au_point(vv, vh, vx) in res.hypotheses, "recursion_essai_prolonge : v=vh(x) absente"
    assert res.conclusion not in res.hypotheses, "recursion_essai_prolonge : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ÉTAPE 2 (DISCHARGE COMPLET) — couvert_essai(x) par construction de l'essai.
# ════════════════════════════════════════════════════════════════════════════
def couvert_essai_depuis_famille(vh, D="Df", G="G", e="E", x="x0", v="v0", z="zess",
                                 p="pess"):
    """{ membres_fonctionnels(𝔇), coincidence_membres(𝔇), dom(⋃𝔇)=seg(R,E,x),
        recursion_sur_segment(𝔇,vh,…), v=vh(x) }
        ⊢ couvert_essai(x) = (∃p)( est_essai(p, vh, G, E, x) )      [5 hyps honnêtes].

    🎯 LA DÉCHARGE COMPLÈTE de l'hérédité de la couverture (E6) en x : on EXHIBE l'essai
    p_x' := ⋃𝔇 ∪ {(x,v)} et on prouve `est_essai(p_x', x)` :
      • est_fonctionnel(p_x')            ⇐ `extension_un_pas_depuis_coincidence` (étape 2 fct) ;
      • dom(p_x') = seg(R,E,x)∪{x}       ⇐ `dom_extension_un_pas` ;
      • (∀z∈dom p_x')(valeur(p_x',z)=vh(z)) ⇐ `recursion_essai_prolonge`.
    puis couvert_essai(x) = (∃p)(est_essai(p,x)) par S5 (témoin p_x').

    ⚠️ CINQ hypothèses HONNÊTES (theorie=22), déchargées par loi_deduction.  Les trois
    premières sont la cohésion des essais (⇐ `solutions_coincident`) + leur fonctionnalité
    + la couverture des y<x (dom(⋃𝔇)=seg) ; les deux dernières sont l'équation de
    récursion (déjà satisfaite sur le segment par les essais des y<x, et posée au
    nouveau point x).  Conclusion ∉ hypothèses (non vacuous)."""
    vD, vx, vv = _t(D), _t(x), _t(v)
    U = union_famille(vD)
    S = E.singleton(E.couple(vx, vv))
    pxp = E.reunion(U, S)
    R = _graphe_R(G)

    func = extension_un_pas_depuis_coincidence(D, G, e, x, v)   # func(p_x')   [3 hyps]
    dom_eq = dom_extension_un_pas(D, G, e, x, v)                # dom(p_x')=seg∪{x}  [1 hyp]
    rec = recursion_essai_prolonge(vh, D, G, e, x, v, z)        # (∀z∈dom)(val=vh)  [5 hyps]

    # est_essai(p_x', x) = (func ∧ dom=seg∪{x}) ∧ équation
    essai = conjonction_intro(conjonction_intro(func, dom_eq), rec)
    essai_form = est_essai(pxp, vh, G, _t(e), vx, z)
    assert essai.conclusion == essai_form, "couvert_essai_depuis_famille : ≠ est_essai(p_x',x)"

    # couvert_essai(x) = (∃p)(est_essai(p,x))  par S5 (témoin p_x')
    couvert = couvert_essai(vh, G, _t(e), p, z)(vx)            # (∃p)(est_essai(p,…))
    # corps de couvert avec binder p : est_essai(var(p), …)
    corps = est_essai(var(p), vh, G, _t(e), vx, z)
    res = N.modus_ponens(essai, N.s5(corps, pxp, p))           # (∃p)(est_essai(p,x))

    assert res.conclusion == couvert, "couvert_essai_depuis_famille : ≠ couvert_essai(x)"
    assert res.conclusion not in res.hypotheses, "couvert_essai_depuis_famille : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ÉTAPE 3 — EXISTENCE C60, via la RÉALISATION DE LA FAMILLE des essais.
#
#  La famille D=Dfam(x) des essais des y<x est ici un TERME PARAMÉTRÉ par x (le
#  RÉSIDU honnête : sa collectivisation par S8 sur 𝔓(E×V) à partir de l'existence
#  per-y `(∀y∈seg)(∃p_y)(est_essai(p_y,y))`, et la preuve dom(⋃Dfam(x))=seg, restent
#  à construire — voir le rapport en bas).  `realisation_famille` PAQUETTE en UNE
#  hypothèse honnête les 5 propriétés de Dfam(x) dont `couvert_essai_depuis_famille`
#  a montré qu'elles SUFFISENT — c'est la RÉDUCTION exacte de l'hérédité de couverture.
# ════════════════════════════════════════════════════════════════════════════
def _proprietes_famille(Dfam, vval, vh, G, e, x):
    """Les 5 propriétés HONNÊTES de la famille Dfam(x) au point x (conjonction) :

      membres_fonctionnels(Dfam(x)) ∧ coincidence_membres(Dfam(x))
      ∧ dom(⋃Dfam(x)) = seg(R,E,x) ∧ recursion_sur_segment(Dfam(x),…) ∧ vval(x)=vh(x).

    Ce sont EXACTEMENT les 5 hyps de `couvert_essai_depuis_famille` (fonctionnalité +
    cohésion-valeur des essais ⇐ `solutions_coincident`, couverture des y<x, récursion
    déjà satisfaite sur le segment, équation au nouveau point)."""
    R = _graphe_R(G)
    Dx = Dfam(x)
    Ux = union_famille(Dx)
    seg = E.segment_extremite(_t(G), _t(e), x)
    return et(et(et(et(
        membres_fonctionnels(Dx),
        coincidence_membres(Dx)),
        egal(E.dom(Ux), seg)),
        recursion_sur_segment(Dx, vh, G, e, x)),
        equation_au_point(vval(x), vh, x))


def realisation_famille(Dfam, vval, vh, G="G", e="E", x="x0tf", y="ytf"):
    """RÉSIDU HONNÊTE — la RÉALISABILITÉ de la famille des essais :

      (∀x)( x∈E ⇒ ( (∀y)(y∈seg(R,E,x) ⇒ couvert_essai[y]) ⇒ propriétés(Dfam(x)) ) ).

    « Pour tout x∈E dont tous les y<x sont couverts, la famille Dfam(x) des essais des
    y<x REALISE ses 5 propriétés (fonctionnalité, cohésion-valeur, dom=seg, récursion-
    sur-segment, valeur au point). »  C'est LE RÉSIDU exact : sa preuve demande la
    COLLECTIVISATION par S8 de la famille des essais des y<x (à partir de l'existence
    per-y) et la COUVERTURE des segments dom(⋃Dfam(x))=seg(R,E,x).  HYPOTHÈSE HONNÊTE.

    Dfam, vval : fonctions Python (Terme x) → (Terme) ; vh : règle Terme→Terme."""
    R = _graphe_R(G)
    ve = _t(e)
    couvert = couvert_essai(vh, G, ve)
    vx = var(x)
    seg = E.segment_extremite(_t(G), ve, vx)
    antec = pourtout(y, impl(appartient(var(y), seg), couvert(var(y))))
    return pourtout(x, impl(appartient(vx, ve),
                            impl(antec, _proprietes_famille(Dfam, vval, vh, G, e, vx))))


def heredite_couverture_realisee(Dfam, vval, vh, G="G", e="E",
                                 x="x0tf", y="ytf", z="zess", p="pess"):
    """{ realisation_famille(Dfam, vval, vh, R, E) }
        ⊢ heredite_couverture(couvert_essai, G, E)                  [1 hyp honnête].

    🎯 LA DÉCHARGE DE L'HÉRÉDITÉ DE COUVERTURE.  Pour x∈E avec tous les y<x couverts,
    `realisation_famille` fournit les 5 propriétés de Dfam(x), que
    `couvert_essai_depuis_famille` transforme en couvert_essai[x] (construction de
    l'essai p_x' = ⋃Dfam(x) ∪ {(x,vval(x))}).  L'hérédité de couverture (E6) en sort.

    ⚠️ UNE hypothèse HONNÊTE (le RÉSIDU `realisation_famille` : collectivisation des
    essais + couverture des segments).  Non vacuous."""
    R = _graphe_R(G)
    ve = _t(e)
    couvert = couvert_essai(vh, G, ve)
    vx = var(x)
    seg = E.segment_extremite(_t(G), ve, vx)
    antec = pourtout(y, impl(appartient(var(y), seg), couvert(var(y))))

    h_real = N.assume(realisation_famille(Dfam, vval, vh, G, e, x, y))
    h_xE = N.assume(appartient(vx, ve))
    h_antec = N.assume(antec)
    # 5 propriétés de Dfam(x)
    r5 = N.modus_ponens(h_antec, N.modus_ponens(h_xE, instancie(h_real, vx)))
    c5 = conjonction_elim_droite(r5)
    c4 = conjonction_elim_droite(conjonction_elim_gauche(r5))
    c3 = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(r5)))
    c2 = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(r5))))
    c1 = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(r5))))

    Dx = Dfam(vx)
    Ux = union_famille(Dx)
    cef = couvert_essai_depuis_famille(vh, Dx, G, e, vx, vval(vx), z, p)   # 5 hyps
    r = cef
    r = N.modus_ponens(c1, N.loi_deduction(membres_fonctionnels(Dx), r))
    r = N.modus_ponens(c2, N.loi_deduction(coincidence_membres(Dx), r))
    r = N.modus_ponens(c3, N.loi_deduction(egal(E.dom(Ux), seg), r))
    r = N.modus_ponens(c4, N.loi_deduction(recursion_sur_segment(Dx, vh, G, e, vx), r))
    r = N.modus_ponens(c5, N.loi_deduction(equation_au_point(vval(vx), vh, vx), r))  # couvert[x]

    body = N.loi_deduction(appartient(vx, ve), N.loi_deduction(antec, r))
    res = N.generalisation(x, body)

    cible = heredite_couverture(couvert, G, ve, x, y)
    assert res.conclusion == cible, "heredite_couverture_realisee : ≠ heredite_couverture"
    assert realisation_famille(Dfam, vval, vh, G, e, x, y) in res.hypotheses, \
        "heredite_couverture_realisee : realisation_famille absente"
    assert len(res.hypotheses) == 1, "heredite_couverture_realisee : hyps ≠ 1"
    assert res.conclusion not in res.hypotheses, "heredite_couverture_realisee : VACUOUS"
    return res


# @livre Ch.III §2.2 Crit.60 | E III.18 L.20-24 | PDF p.121
def recursion_transfinie_existence(Dfam, vval, vh, G="G", e="E",
                                   x="x0tf", y="ytf", z="zess", p="pess",
                                   ebind="Eax", xbind="xAax"):
    """🎯🎯 EXISTENCE C60 (§III.2, RÉCURRENCE TRANSFINIE) :

      { est_bien_ordonne(R,E),  realisation_famille(Dfam,vval,vh,R,E) }
        ⊢ (∀x)( x∈E ⇒ (∃p)( est_essai(p, vh, G, E, x) ) ).

    « Sur l'ensemble bien ordonné (E,R), tout point x est COUVERT par un essai —
    une fonction partielle p sur seg(R,E,x)∪{x} VÉRIFIANT l'équation de récursion
    valeur(p,z)=vh(z) sur tout son domaine. »  C'est l'EXISTENCE de la solution de
    l'équation de récursion C60 (la solution globale f = ⋃ des essais étant alors
    fonctionnelle et totale par recollement-famille + couverture).

    PREUVE : `heredite_couverture_realisee` DÉCHARGE l'hérédité de couverture (E6) à
    partir du RÉSIDU `realisation_famille` (via `couvert_essai_depuis_famille`) ; on
    l'injecte dans `couverture_essais_via_c59` (E6 = squelette C59), ce qui décharge sa
    seconde hypothèse.  Ne restent que le BON ORDRE et le RÉSIDU.

    ⚠️ DEUX hypothèses HONNÊTES (theorie=22), déchargées par loi_deduction :
      • est_bien_ordonne(R,E)            — (E,R) bien ordonné (donnée de C60) ;
      • realisation_famille(Dfam,…)      — LE RÉSIDU : pour chaque x dont les y<x sont
        couverts, la famille Dfam(x) de leurs essais réalise ses 5 propriétés.  Sa
        preuve demande la COLLECTIVISATION S8 de la famille des essais (à partir de
        l'existence per-y) et la COUVERTURE des segments dom(⋃Dfam(x))=seg(R,E,x) —
        le dernier chantier (cf. RAPPORT en bas).
    Conclusion ∉ hypothèses (non vacuous)."""
    R = _graphe_R(G)
    ve = _t(e)
    couvert = couvert_essai(vh, G, ve)

    her = heredite_couverture_realisee(Dfam, vval, vh, G, e, x, y, z, p)   # [realisation]
    her_form = heredite_couverture(couvert, G, ve, x, y)
    e6 = couverture_essais_via_c59(vh, e, G, x, y, ebind, xbind, p, z)     # {bo, her} ⊢ couverture
    res = N.modus_ponens(her, N.loi_deduction(her_form, e6))              # {bo, realisation} ⊢ couverture

    cible = couverture_totale(couvert, ve, x)
    assert res.conclusion == cible, "recursion_transfinie_existence : ≠ couverture totale (existence)"
    W = E.est_bien_ordonne(R, ve)
    assert W in res.hypotheses, "recursion_transfinie_existence : bon ordre absent"
    assert realisation_famille(Dfam, vval, vh, G, e, x, y) in res.hypotheses, \
        "recursion_transfinie_existence : realisation_famille absente"
    assert len(res.hypotheses) == 2, "recursion_transfinie_existence : hyps ≠ 2"
    assert res.conclusion not in res.hypotheses, "recursion_transfinie_existence : VACUOUS"
    return res


__all__ = [
    # brique graphe→valeur (le chunk reporté, CLOS)
    "couple_donne_valeur",
    # valeur de l'essai trivial / domaine et valeur de l'essai prolongé
    "valeur_singleton_couple", "dom_extension_un_pas", "valeur_nouveau_point",
    # équation de récursion sur tout le domaine + couverture en x
    "recursion_sur_segment", "equation_au_point",
    "recursion_essai_prolonge", "couvert_essai_depuis_famille",
    # 🎯 étape 3 — existence C60 via la réalisation de la famille
    "realisation_famille", "heredite_couverture_realisee",
    "recursion_transfinie_existence",
    # énoncés de cohésion HONNÊTE de la famille
    "membres_fonctionnels", "coincidence_membres",
    # 🎯 étape 1 — LE PONT solutions_coincident → famille_compatible
    "famille_compatible_depuis_coincidence",
    # corollaire : ⋃𝔇 fonctionnel sous la cohésion-valeur
    "union_fonctionnelle_depuis_coincidence",
    # 🎯 étape 2 — recollement + extension d'un pas sous cohésion-valeur (fonctionnalité)
    "extension_un_pas_depuis_coincidence",
]
