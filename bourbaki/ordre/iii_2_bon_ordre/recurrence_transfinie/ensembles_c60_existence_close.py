"""§III.2 — DÉFINITION PAR RÉCURRENCE TRANSFINIE (Critère C60) : EXISTENCE, suite.

Suite DIRECTE de `ensembles_recursion_transfinie_existence` (la moitié EXISTENCE de
C60, partielle) et de `ensembles_recurrence_transfinie` (C59 induction transfinie
CLOS + C60-UNICITÉ).  Ce module pousse la moitié EXISTENCE plus loin en CLOSANT les
briques CONSTRUCTIVES du « prolongement d'un pas » (le cœur reporté) et en
INSTANCIANT la couverture-via-C59 sur le prédicat CONCRET d'existence d'un essai.

────────────────────────────────────────────────────────────────────────────────
RAPPEL DU CADRE (faithful Bourbaki E.III.2, Critère C60).

Soit (E,R) bien ordonné et une « règle » h.  C60 affirme l'existence d'une UNIQUE
fonction f sur E vérifiant l'ÉQUATION DE RÉCURSION  (∀x∈E) f(x) = h(x, f|seg(R,E,x)).

Construction de Bourbaki : f = ⋃ des « essais » (fonctions partielles sur les
segments initiaux).  Chaque essai est défini sur seg(R,E,x)∪{x} et vérifie l'équation
de récursion sur son domaine.  Pour prouver que f est TOTALE, on montre par C59-
induction que tout x∈E est COUVERT (= appartient au domaine d'un essai).  Le pas
d'hérédité (PROLONGEMENT d'un essai-sur-seg en un essai-sur-seg∪{x}) est le CŒUR.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST CLOS ICI (theorie=22 intangible ; tout est DÉRIVÉ, rien n'est postulé).

  (E1) `singleton_couple_fonctionnel`  ⊢ est_fonctionnel({(x,v)})   [CLOS, 0 hyp].
        Le graphe-essai TRIVIAL en un point (le pas atomique de l'extension) est
        fonctionnel.  Cœur : un seul couple ⇒ injectivité du couple ⇒ v=z.

  (E2) `dom_singleton_couple`  ⊢ dom({(x,v)}) = {x}                  [CLOS, 0 hyp].
        Le domaine d'un essai trivial en x est exactement {x}.

  (E3) `point_hors_segment`  ⊢ ¬( x ∈ seg(R,E,x) )                   [CLOS, 0 hyp].
        Un point n'est PAS dans son propre segment initial ]←,x[ (seg exclut x).
        C'est CE QUI rend les domaines de l'essai-sur-seg et de l'essai-trivial-en-x
        DISJOINTS — la condition même du recollement.

  (E4) `domaines_essai_disjoints`  { dom(p)=seg(R,E,x) }
        ⊢ (∀u)¬( u∈dom(p) ∧ u∈dom({(x,v)}) )                        [1 hyp honnête].
        DISJONCTION des domaines (essai partiel p sur le segment vs essai trivial en
        x), DÉRIVÉE de (E2)+(E3).  Hypothèse HONNÊTE : dom(p)=seg(R,E,x) (p EST un
        essai sur le segment).

  (E5) `extension_un_pas_fonctionnelle`  { est_fonctionnel(p), dom(p)=seg(R,E,x) }
        ⊢ est_fonctionnel( p ∪ {(x,v)} )                            [2 hyps honnêtes].
        🎯 LE PROLONGEMENT D'UN PAS, moitié FONCTIONNALITÉ : prolonger un essai
        fonctionnel p (sur seg) par le couple (x,v) donne un graphe FONCTIONNEL.
        DÉRIVÉ de (E1)+(E4) via `reunion_graphes_fonctionnelle` (infra recollement) :
        on DÉCHARGE deux des trois hypothèses du pivot (la fonctionnalité du
        singleton et la disjonction), il ne reste QUE les deux données honnêtes de
        l'essai partiel.  C'est la moitié constructive (fonctionnalité) du pas
        d'hérédité de la couverture.

  (E6) `couverture_essais_via_c59`  (couverture-via-C59 sur le prédicat CONCRET)
        { est_bien_ordonne(R,E), heredite(couvert_essai,…) }
        ⊢ (∀x∈E)(∃p)( est_essai(p,x) )                              [2 hyps honnêtes].
        🎯 COUVERTURE par des essais RÉELS : on INSTANCIE le squelette C59
        `couverture_transfinie` sur le prédicat CONCRET
            couvert_essai(x) := (∃p)( est_fonctionnel(p)
                                      ∧ dom(p)=seg(R,E,x)∪{x}
                                      ∧ (∀z∈dom p)(vp(z)=vh(z)) ).
        À comparer au prédicat SYMBOLIQUE `x∈Couv` du module antérieur : ici le
        prédicat de couverture EST l'existence d'un essai vérifiant l'équation de
        récursion sur son domaine.  La seconde hypothèse (hérédité de la couverture
        = le PROLONGEMENT D'UN PAS COMPLET) reste honnête — c'est la FRONTIÈRE.

────────────────────────────────────────────────────────────────────────────────
LA FRONTIÈRE (reportée, honnêtement — voir le rapport en bas).

  Le pas d'hérédité COMPLET de (E6) — « si tout y<x est couvert, alors x est
  couvert » — demande, à partir de la FAMILLE des essais sur les segments des y<x :
    (i)  GLUER cette famille en un essai p_x sur seg(R,E,x) (recollement d'une
         famille NON binaire ; les essais coïncident par C60-unicité solutions_coincident) ;
    (ii) PROLONGER p_x d'un pas en posant v := h(x, p_x) — la moitié FONCTIONNALITÉ
         de ce prolongement EST close ici (E5) ; reste l'équation de récursion sur
         le nouveau point et la COLLECTIVISATION de la famille des essais (S8 sur
         𝔓(E×V)) pour pouvoir quantifier dessus.
  C'est le recollement d'une FAMILLE (non binaire) + la collectivisation des essais :
  le gros chantier annoncé.  (E5) en clôt le pas ATOMIQUE (fonctionnalité) ; (E6) en
  clôt le SQUELETTE C59.  Ne reste que le gluing-de-famille + l'équation-au-point.

INVARIANT : theorie_ensembles() = 22.  Les hypothèses (bon ordre, p essai, hérédité)
sont HONNÊTES, déchargées par loi_deduction — les données mêmes du Critère C60.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout, existe,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, antecedent_consequent,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    singleton_membre, couple_egal_implique_composantes,
)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    reunion_graphes_fonctionnelle,
)

from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recursion_transfinie_existence import (
    couverture_transfinie, couverture_totale, heredite_couverture,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  (E1) — FONCTIONNALITÉ DU GRAPHE-ESSAI TRIVIAL  {(x,v)}.
# ════════════════════════════════════════════════════════════════════════════
def singleton_couple_fonctionnel(x="x0", v="v0"):
    """⊢ est_fonctionnel( {(x,v)} )                                  [CLOS, 0 hyp].

    Le graphe à un seul couple (x,v) est fonctionnel : si (u,w) et (u,s) sont dans
    {(x,v)}, alors tous deux ÉGAUX à (x,v) (membre d'un singleton), donc w=v=s par
    INJECTIVITÉ DU COUPLE (`couple_egal_implique_composantes`).  C'est le pas ATOMIQUE
    de l'extension d'un essai (l'essai trivial en un nouveau point)."""
    vx, vv = _t(x), _t(v)
    cpl0 = E.couple(vx, vv)
    S = E.singleton(cpl0)
    u, w, z = var("u"), var("v"), var("z")     # binders de est_fonctionnel (u,v,z)
    cuw, cuz = E.couple(u, w), E.couple(u, z)

    hyp = N.assume(et(appartient(cuw, S), appartient(cuz, S)))
    in_uw = conjonction_elim_gauche(hyp)
    in_uz = conjonction_elim_droite(hyp)
    eq_uw = N.modus_ponens(in_uw, equivalence_avant(singleton_membre(cuw, cpl0)))  # (u,w)=(x,v)
    eq_uz = N.modus_ponens(in_uz, equivalence_avant(singleton_membre(cuz, cpl0)))  # (u,z)=(x,v)
    w_eq_v = conjonction_elim_droite(
        N.modus_ponens(eq_uw, couple_egal_implique_composantes(u, w, vx, vv)))     # w=v
    z_eq_v = conjonction_elim_droite(
        N.modus_ponens(eq_uz, couple_egal_implique_composantes(u, z, vx, vv)))     # z=v
    v_eq_z = composer_egalites(w_eq_v, N.modus_ponens(z_eq_v, symetrie(z, vv)))    # w=z (v binder)

    body = N.loi_deduction(et(appartient(cuw, S), appartient(cuz, S)), v_eq_z)
    res = N.generalisation("u", N.generalisation("v", N.generalisation("z", body)))

    assert res.conclusion == E.est_fonctionnel(S), "singleton_couple_fonctionnel : ≠ est_fonctionnel({(x,v)})"
    assert res.est_clos, "singleton_couple_fonctionnel non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (E2) — DOMAINE DU GRAPHE-ESSAI TRIVIAL  dom({(x,v)}) = {x}.
# ════════════════════════════════════════════════════════════════════════════
def dom_singleton_couple(x="x0", v="v0", z="z"):
    """⊢ dom( {(x,v)} ) = {x}                                        [CLOS, 0 hyp].

    Double inclusion (membership) + extensionnalité A1.
      z∈dom{(x,v)} ⇔ (∃y)((z,y)∈{(x,v)}) ⇔ (z,y)=(x,v) ⇒ z=x ⇔ z∈{x}  ;
      réciproquement z=x ⇒ (z,v)∈{(x,v)} ⇒ z∈dom.  Le domaine d'un essai trivial en
      x est exactement {x} (utile pour la disjonction des domaines)."""
    from bourbaki.logique.i_1_termes_relations.formule import inclus
    vx, vv = _t(x), _t(v)
    cpl0 = E.couple(vx, vv)
    S = E.singleton(cpl0)
    dS, sx = E.dom(S), E.singleton(vx)
    vz, vy = var(z), var("y")

    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, S), vz)              # z∈dom S ⇔ (∃y)((z,y)∈S)

    # ── inclus(dom S, {x}) :  z∈dom S ⇒ z∈{x} ────────────────────────────────
    hz = N.assume(appartient(vz, dS))
    exy = N.modus_ponens(hz, equivalence_avant(car))
    hzy = N.assume(appartient(E.couple(vz, vy), S))
    eqzy = N.modus_ponens(hzy, equivalence_avant(singleton_membre(E.couple(vz, vy), cpl0)))
    z_eq_x = conjonction_elim_gauche(
        N.modus_ponens(eqzy, couple_egal_implique_composantes(vz, vy, vx, vv)))     # z=x
    z_in_sx = N.modus_ponens(z_eq_x, equivalence_arriere(singleton_membre(vz, vx)))  # z∈{x}
    body1 = N.loi_deduction(appartient(E.couple(vz, vy), S), z_in_sx)
    z_in_sx_f = N.modus_ponens(exy, existe_elimination(body1, "y"))
    incl1 = N.generalisation(z, N.loi_deduction(appartient(vz, dS), z_in_sx_f))

    # ── inclus({x}, dom S) :  z∈{x} ⇒ z∈dom S ────────────────────────────────
    hz2 = N.assume(appartient(vz, sx))
    z_eq_x2 = N.modus_ponens(hz2, equivalence_avant(singleton_membre(vz, vx)))       # z=x
    x_eq_z = N.modus_ponens(z_eq_x2, symetrie(vz, vx))                               # x=z
    cpl0_in_S = N.modus_ponens(N.reflexivite(cpl0),
                               equivalence_arriere(singleton_membre(cpl0, cpl0)))     # (x,v)∈S
    congr = N.modus_ponens(x_eq_z, N.s6(vx, vz, "w", appartient(E.couple(var("w"), vv), S)))
    zv_in_S = N.modus_ponens(cpl0_in_S, equivalence_avant(congr))                    # (z,v)∈S
    exy2 = N.modus_ponens(zv_in_S, N.s5(appartient(E.couple(vz, var("y")), S), vv, "y"))
    z_in_dS = N.modus_ponens(exy2, equivalence_arriere(car))
    incl2 = N.generalisation(z, N.loi_deduction(appartient(vz, sx), z_in_dS))

    res = N.modus_ponens(conjonction_intro(incl1, incl2), extensionnalite_appliquee(dS, sx))
    assert res.conclusion == egal(dS, sx), "dom_singleton_couple : ≠ dom({(x,v)})={x}"
    assert res.est_clos, "dom_singleton_couple non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (E3) — UN POINT N'EST PAS DANS SON PROPRE SEGMENT  ¬( x ∈ seg(R,E,x) ).
# ════════════════════════════════════════════════════════════════════════════
def point_hors_segment(G="G", e="E", x="x0"):
    """⊢ ¬( x ∈ seg(R,E,x) )                                         [CLOS, 0 hyp].

    seg(R,E,x) = ]←,x[ = { y∈E | y≤x et y≠x } EXCLUT x : si x∈seg(R,E,x) alors x≠x,
    contredisant la réflexivité.  C'est EXACTEMENT ce qui rend les domaines de
    l'essai-sur-seg et de l'essai-trivial-en-x DISJOINTS.  R = relation portée par G."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    seg = E.segment_extremite(R, ve, vx)

    th = E.theorie_segment_extremite(R)
    ax = N.axiome(th, E.axiome_segment_extremite(R))
    seg_membre = instancie(instancie(instancie(ax, ve), vx), vx)   # x∈seg ⇔ ((x∈E et x≤x) et x≠x)

    cible = non(appartient(vx, seg))
    h = N.assume(appartient(vx, seg))
    corps = N.modus_ponens(h, equivalence_avant(seg_membre))
    x_ne_x = conjonction_elim_droite(corps)                        # x≠x = ¬(x=x)
    refl = N.reflexivite(vx)                                       # x=x
    inner = N.modus_ponens(refl, N.modus_ponens(x_ne_x, N.s2(non(egal(vx, vx)), cible)))
    imp = N.loi_deduction(appartient(vx, seg), inner)              # (x∈seg) ⇒ ¬(x∈seg)
    _, notP = antecedent_consequent(imp.conclusion)
    res = N.modus_ponens(imp, N.s1(notP))                          # ¬(x∈seg)

    assert res.conclusion == cible, "point_hors_segment : ≠ ¬(x∈seg(R,E,x))"
    assert res.est_clos, "point_hors_segment non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (E4) — DISJONCTION DES DOMAINES  dom(p) ⊥ dom({(x,v)}).
# ════════════════════════════════════════════════════════════════════════════
def domaines_essai_disjoints(p="p", G="G", e="E", x="x0", v="v0", u="u"):
    """{ dom(p) = seg(R,E,x) } ⊢ (∀u)¬( u∈dom(p) ∧ u∈dom({(x,v)}) )  [1 hyp honnête].

    DISJONCTION des domaines : l'essai partiel p (sur le segment) et l'essai trivial
    en x n'ont AUCUN antécédent commun.  DÉRIVÉ de (E2) dom({(x,v)})={x} et (E3)
    x∉seg : si u∈dom(p)=seg et u∈dom({(x,v)})={x} alors u=x∈seg — impossible (E3).
    Forme EXACTEMENT celle attendue par `reunion_graphes_fonctionnelle` (liant u).
    Hypothèse HONNÊTE : dom(p)=seg(R,E,x) (p EST un essai sur le segment)."""
    R = _graphe_R(G)
    vp, ve, vx, vv, vu = _t(p), _t(e), _t(x), _t(v), _t(u)
    seg = E.segment_extremite(R, ve, vx)
    cpl0 = E.couple(vx, vv)
    S = E.singleton(cpl0)
    domp, domS = E.dom(vp), E.dom(S)

    h_dom_eq = N.assume(egal(domp, seg))                            # dom(p)=seg  [HONNÊTE]
    domS_eq_sx = dom_singleton_couple(vx, vv)                       # dom({(x,v)})={x}  [E2, CLOS]
    x_notin_seg = point_hors_segment(G, ve, vx)                     # ¬(x∈seg)         [E3, CLOS]
    sx = E.singleton(vx)

    cuble_neg = non(et(appartient(vu, domp), appartient(vu, domS)))
    hconj = N.assume(et(appartient(vu, domp), appartient(vu, domS)))
    u_in_domp = conjonction_elim_gauche(hconj)                      # u∈dom p
    u_in_domS = conjonction_elim_droite(hconj)                      # u∈dom({(x,v)})

    # u∈dom p ⇒ u∈seg  (réécriture dom p = seg)
    u_in_seg = N.modus_ponens(u_in_domp,
        equivalence_avant(N.modus_ponens(h_dom_eq, N.s6(domp, seg, "w", appartient(vu, var("w"))))))
    # u∈dom({(x,v)}) ⇒ u∈{x}  (réécriture dom = {x}), puis u=x
    u_in_sx = N.modus_ponens(u_in_domS,
        equivalence_avant(N.modus_ponens(domS_eq_sx, N.s6(domS, sx, "w", appartient(vu, var("w"))))))
    u_eq_x = N.modus_ponens(u_in_sx, equivalence_avant(singleton_membre(vu, vx)))   # u=x
    # x∈seg  (réécriture u→x dans u∈seg)  contredit ¬(x∈seg)
    x_in_seg = N.modus_ponens(u_in_seg,
        equivalence_avant(N.modus_ponens(u_eq_x, N.s6(vu, vx, "w", appartient(var("w"), seg)))))
    ex = N.modus_ponens(x_in_seg,
        N.modus_ponens(x_notin_seg, N.s2(non(appartient(vx, seg)), cuble_neg)))
    imp = N.loi_deduction(et(appartient(vu, domp), appartient(vu, domS)), ex)
    _, notP = antecedent_consequent(imp.conclusion)
    disj_u = N.modus_ponens(imp, N.s1(notP))                        # ¬(u∈dom p et u∈dom S)
    res = N.generalisation(u, disj_u)

    cible = pourtout(u, non(et(appartient(vu, domp), appartient(vu, domS))))
    assert res.conclusion == cible, "domaines_essai_disjoints : conclusion inattendue"
    assert res.conclusion not in res.hypotheses, "domaines_essai_disjoints : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (E5) — 🎯 PROLONGEMENT D'UN PAS, moitié FONCTIONNALITÉ.
#  est_fonctionnel( p ∪ {(x,v)} )  given { est_fonctionnel(p), dom(p)=seg(R,E,x) }.
# ════════════════════════════════════════════════════════════════════════════
def extension_un_pas_fonctionnelle(p="p", G="G", e="E", x="x0", v="v0"):
    """{ est_fonctionnel(p), dom(p) = seg(R,E,x) } ⊢ est_fonctionnel( p ∪ {(x,v)} )
                                                                    [2 hyps honnêtes].

    🎯 LE PROLONGEMENT D'UN PAS (moitié FONCTIONNALITÉ).  Prolonger un essai
    fonctionnel p (défini sur le segment seg(R,E,x)) par le nouveau couple (x,v) donne
    un graphe FONCTIONNEL.  DÉRIVÉ de `reunion_graphes_fonctionnelle` (pivot recollement
    R25) dont on DÉCHARGE deux des trois hypothèses :
      • est_fonctionnel({(x,v)})            ⇐ (E1) singleton_couple_fonctionnel [CLOS] ;
      • (∀u)¬(u∈dom p ∧ u∈dom({(x,v)}))     ⇐ (E4) domaines_essai_disjoints [dom p=seg].
    Il ne reste QUE les deux données HONNÊTES de l'essai partiel : p fonctionnel, et
    dom(p)=seg(R,E,x).  C'est la moitié constructive (fonctionnalité) du pas
    d'hérédité de la couverture (E6).  Conclusion ∉ hypothèses (non vacuous)."""
    vp, ve, vx, vv = _t(p), _t(e), _t(x), _t(v)
    S = E.singleton(E.couple(vx, vv))

    pivot = reunion_graphes_fonctionnelle(vp, S)    # {func p, func S, disj} ⊢ func(p∪S)
    func_S = singleton_couple_fonctionnel(vx, vv)   # est_fonctionnel(S)            [CLOS]
    disj = domaines_essai_disjoints(p, G, ve, vx, vv)   # disjonction               [dom p=seg]

    # formes EXACTES attendues par le pivot
    f_p = E.est_fonctionnel(vp)
    f_S = E.est_fonctionnel(S)
    disj_form = disj.conclusion

    # décharge func(S) puis la disjonction dans le pivot (modus ponens via loi_deduction)
    step1 = N.modus_ponens(func_S, N.loi_deduction(f_S, pivot))     # {func p, disj} ⊢ func(p∪S)
    step2 = N.modus_ponens(disj, N.loi_deduction(disj_form, step1)) # {func p, dom p=seg} ⊢ func(p∪S)

    cible = E.est_fonctionnel(E.reunion(vp, S))
    assert step2.conclusion == cible, "extension_un_pas_fonctionnelle : ≠ est_fonctionnel(p∪{(x,v)})"
    # hypothèses honnêtes attendues : func(p) et dom(p)=seg
    seg = E.segment_extremite(_graphe_R(G), ve, vx)
    assert f_p in step2.hypotheses, "extension_un_pas_fonctionnelle : func(p) absente"
    assert egal(E.dom(vp), seg) in step2.hypotheses, "extension_un_pas_fonctionnelle : dom p=seg absente"
    assert step2.conclusion not in step2.hypotheses, "extension_un_pas_fonctionnelle : VACUOUS"
    return step2


# ════════════════════════════════════════════════════════════════════════════
#  (E6) — 🎯 COUVERTURE-VIA-C59 sur le prédicat CONCRET d'existence d'un essai.
# ════════════════════════════════════════════════════════════════════════════
def dom_essai(R, e, x):
    """Le DOMAINE d'un essai en x : seg(R,E,x) ∪ {x}  (le segment fermé en x)."""
    return E.reunion(E.segment_extremite(R, _t(e), _t(x)), E.singleton(_t(x)))


def est_essai(p, vh, R, e, x, z="zess"):
    """Prédicat « p est un ESSAI en x » (fonction partielle solution sur seg∪{x}) :

        est_fonctionnel(p)  ∧  dom(p) = seg(R,E,x)∪{x}
        ∧  (∀z)( z∈dom(p) ⇒ valeur(p,z) = vh(z) ).

    p : Terme (le graphe-essai) ; vh : Terme→Terme (valeur-règle, qui ne lit p que via
    sa restriction au segment).  L'équation de récursion vaut sur TOUT le domaine de p."""
    vp = _t(p)
    vz = var(z)
    eq = pourtout(z, impl(appartient(vz, E.dom(vp)), egal(E.valeur(vp, vz), vh(vz))))
    return et(et(E.est_fonctionnel(vp), egal(E.dom(vp), dom_essai(R, e, x))), eq)


def couvert_essai(vh, R, e, p="pess", z="zess"):
    """Prédicat de COUVERTURE CONCRET  couvert(x) := (∃p)( est_essai(p,x) )  (Terme→Formule).

    « x est couvert » = il EXISTE un essai (fonction partielle solution) défini sur
    seg(R,E,x)∪{x}.  C'est le prédicat sur lequel on fait l'induction C59 (E6) — bien
    plus FIDÈLE que le prédicat symbolique `x∈Couv` du module antérieur."""
    return lambda x: existe(p, est_essai(var(p), vh, R, e, x, z))


def couverture_essais_via_c59(vh, e="E", G="G", x0="x0tf", y="ytf",
                              ebind="Eax", xbind="xAax", p="pess", z="zess"):
    """⊢ { est_bien_ordonne(R,E),  heredite_couverture(couvert_essai,R,E) }
         ⊢ (∀x)( x∈E ⇒ (∃p)( est_essai(p,x) ) )            [ COUVERTURE PAR ESSAIS ].

    🎯 INSTANCIATION du squelette C59 `couverture_transfinie` sur le prédicat CONCRET
    `couvert_essai` (= il existe un essai sur seg∪{x}).  La couverture devient
    « tout point de E est dans le domaine d'un essai vérifiant l'équation de récursion
    sur son domaine » — la totalité de la solution f=⋃essais.

    ⚠️ DEUX HYPOTHÈSES HONNÊTES (jamais postulées ; theorie=22), déchargées par
    loi_deduction :
      • est_bien_ordonne(R,E)                      — (E,R) bien ordonné (donnée C60) ;
      • heredite_couverture(couvert_essai,R,E)     — le PROLONGEMENT D'UN PAS COMPLET
        (glue la famille des essais sur les y<x + extension d'un pas) — FRONTIÈRE.
        Sa moitié FONCTIONNALITÉ est close (E5) ; reste le gluing-de-famille +
        l'équation-au-nouveau-point + la collectivisation des essais.
    Conclusion (couverture par essais) ∉ hypothèses (non vacuous)."""
    R = _graphe_R(G)
    ve = _t(e)
    couvert = couvert_essai(vh, R, ve, p, z)
    res = couverture_transfinie(couvert, e, G, x0, y, ebind, xbind)  # 2 hyps honnêtes

    cible = couverture_totale(couvert, ve, x0)
    assert res.conclusion == cible, "couverture_essais_via_c59 : conclusion ≠ couverture totale"
    assert len(res.hypotheses) == 2, "couverture_essais_via_c59 : hyps ≠ 2"
    W = E.est_bien_ordonne(R, ve)
    her = heredite_couverture(couvert, R, ve, x0, y)
    assert W in res.hypotheses and her in res.hypotheses, "couverture_essais_via_c59 : hyps inattendues"
    assert res.conclusion not in res.hypotheses, "couverture_essais_via_c59 : VACUOUS"
    return res


__all__ = [
    # briques CONSTRUCTIVES du prolongement d'un pas (CLOSES)
    "singleton_couple_fonctionnel",   # (E1) 0 hyp
    "dom_singleton_couple",           # (E2) 0 hyp
    "point_hors_segment",             # (E3) 0 hyp
    "domaines_essai_disjoints",       # (E4) 1 hyp honnête
    "extension_un_pas_fonctionnelle", # (E5) 2 hyps honnêtes  🎯 prolongement (fonctionnalité)
    # couverture-via-C59 sur le prédicat CONCRET d'essai
    "dom_essai", "est_essai", "couvert_essai",
    "couverture_essais_via_c59",      # (E6) 2 hyps honnêtes  🎯 couverture par essais réels
]
