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

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_caracterisation

from bourbaki.ordre.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.ensembles_c60_coeur import (
    union_famille, famille_compatible, union_famille_fonctionnelle,
    extension_un_pas_union_fonctionnelle,
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
    seg = E.segment_extremite(_graphe_R(G), _t(e), _t(x))

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


__all__ = [
    # brique graphe→valeur (le chunk reporté, CLOS)
    "couple_donne_valeur",
    # énoncés de cohésion HONNÊTE de la famille
    "membres_fonctionnels", "coincidence_membres",
    # 🎯 étape 1 — LE PONT solutions_coincident → famille_compatible
    "famille_compatible_depuis_coincidence",
    # corollaire : ⋃𝔇 fonctionnel sous la cohésion-valeur
    "union_fonctionnelle_depuis_coincidence",
    # 🎯 étape 2 — recollement + extension d'un pas sous cohésion-valeur (fonctionnalité)
    "extension_un_pas_depuis_coincidence",
]
