"""§III.5 — PROPOSITION 4 (E.III.37), parties PROPRES : SURJECTIVITÉ de la
translation x ↦ a+x de [0,b] sur [a,a+b] (et l'antécédent u = y−a ∈ [0,b]).

Complète la Prop 4 §III.5 : bien-définie + mono-large + mono-stricte + injective
(toutes MERGED ailleurs) ; ICI on ferme la SURJECTIVITÉ.

    prop4_surjective :
        ⊢ ( est_entier(a) et est_entier(b) et y∈[a,a+b] ) ⇒
              (∃u)( u∈[0,b]  et  a+u = y ).
        (Tout y de [a,a+b] est atteint, par u = y−a = Card(τc(y=a+c)).)

ROUTE
  • EXISTENCE CARDINALE du complément (renforcée) — `existe_complement_somme_cardinal` :
        ( card a et card b et a≤b ) ⇒ (∃c)( card c et b = a+c ).
    De `existe_complement_somme` (∃c)b=a+c, on réalise le témoin w0 := diff_somme(b,a)
    (b = a+w0), puis a+w0 = a+Card(w0) (`somme_cardinale_bien_definie`, via Eq(a,a) et
    Eq(w0,Card w0)) ; Card(w0) EST un cardinal ⇒ c := Card(w0) témoigne avec la garde
    `est_cardinal(c)`.  (Le τ-témoin brut n'est pas prouvablement un cardinal ; on le
    REMPLACE par son cardinal, qui donne la MÊME somme.)
  • ANNULATION ADDITIVE DE L'ORDRE (a fini) — `additive_order_cancel` :
        ( est_entier(a) et card u et card v et a+u ≤ a+v ) ⇒ u ≤ v.
    Comparabilité u≤v ou v≤u ; si v≤u alors a+v≤a+u (mono-large) donc a+u=a+v
    (antisymétrie, a+u/a+v cardinaux) ⇒ u=v (injectivité) ⇒ u≤v (réflexivité).
  • SURJECTIVITÉ : y∈[a,a+b] ⇒ (a≤y, y≤a+b, card y).  Existence cardinale appliquée à
    (a,y) (sous a≤y) donne card u et y=a+u ; donc a+u=y, et u≤b par annulation de
    a+u≤a+b (réécrit y≤a+b) ; 0≤u (zero_inf_egal) ⇒ u∈[0,b].  S5 ⇒ (∃u)(u∈[0,b] et a+u=y).

⚠️ theorie_ensembles() = 22.  0 hyp.  Rien postulé.  N'édite aucun fichier déposé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, ou, existe, appartient,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere, cas,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, equipotent,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_entier, est_fini, ZERO
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire, somme_disjointe,
)

# briques closes réutilisées
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    existe_complement_somme, diff_somme,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_somme_equipotence import (
    somme_cardinale_bien_definie,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    card_est_un_cardinal, fini_implique_cardinal,
)
from bourbaki.cardinaux.iii_4_ordinal_cardinal.equipotence_retrait.ensembles_equipotence_retrait import equipotence_reflexive_pour
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_total_general, inf_egal_antisymetrique_card,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop4_strict_iii5 import (
    prop4_translation_injective,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_prop4_iii5 import (
    prop4_translation_croissante, _mem_int_t, _intervalle_borne_sup_t,
    _zero_inf_egal_card,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  Eq(T, Card T)  pour un TERME T quelconque (généralise equipotent_son_cardinal)
# ════════════════════════════════════════════════════════════════════════════
def _eq_son_cardinal_t(t):
    """⊢ Eq(T, Card T)   pour un TERME T (instance close de equipotent_son_cardinal)."""
    vt = _t(t)
    gen = N.generalisation("X", equipotent_son_cardinal("X"))   # (∀X) Eq(X, Card X)
    return instancie(gen, vt)


# ════════════════════════════════════════════════════════════════════════════
#  a + w = a + Card(w)   (la somme ne dépend que du cardinal de w)
# ════════════════════════════════════════════════════════════════════════════
def _somme_card_droite(va, vw):
    """⊢ somme_cardinale_binaire(a, w) = somme_cardinale_binaire(a, Card w).

    somme_cardinale_bien_definie(A:=a, B:=w, A1:=a, B1:=Card w) :
        (Eq(a,a) et Eq(w,Card w)) ⇒ Card(a⊔w) = Card(a⊔Card w),
    or Card(a⊔w) = a+w et Card(a⊔Card w) = a+Card w (déf de + binaire)."""
    va, vw = _t(va), _t(vw)
    cw = cardinal(vw)
    # bien-définition sur NOMS frais puis instanciation aux TERMES (capture-safe)
    base = somme_cardinale_bien_definie("Asc", "Bsc", "A1sc", "B1sc")
    gen = N.generalisation("Asc", N.generalisation("Bsc",
        N.generalisation("A1sc", N.generalisation("B1sc", base))))
    inst = instancie(instancie(instancie(instancie(gen, va), vw), va), cw)
    # inst : (Eq(a,a) et Eq(w,Card w)) ⇒ a+w = a+Card w
    eq_aa = equipotence_reflexive_pour(va)               # Eq(a,a)
    eq_w = _eq_son_cardinal_t(vw)                        # Eq(w, Card w)
    res = N.modus_ponens(conjonction_intro(eq_aa, eq_w), inst)   # a+w = a+Card w
    cible = egal(somme_cardinale_binaire(va, vw), somme_cardinale_binaire(va, cw))
    assert res.conclusion == cible, "_somme_card_droite : conclusion inattendue"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  EXISTENCE CARDINALE renforcée :
#     ( card a et card b et a≤b ) ⇒ (∃c)( card c et b = a+c )
# ════════════════════════════════════════════════════════════════════════════
def existe_complement_somme_cardinal_enonce(a="aP4s", b="bP4s", c="cP4s"):
    va, vb = _t(a), _t(b)
    return impl(et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(va, vb)),
                existe(c, et(est_cardinal(var(c)),
                             egal(vb, somme_cardinale_binaire(va, var(c))))))


def existe_complement_somme_cardinal(a="aP4s", b="bP4s", c="cP4s"):
    """⊢ ( card a et card b et a≤b ) ⇒ (∃c)( card c et b = a+c ).   (CLOS, 0 hyp.)

    existe_complement_somme : (∃c) b=a+c ; témoin w0:=diff_somme(b,a) (b=a+w0) ;
    a+w0 = a+Card(w0) (_somme_card_droite) ⇒ b = a+Card(w0) ; Card(w0) cardinal ⇒
    c:=Card(w0) témoigne avec la garde est_cardinal(c) (S5)."""
    va, vb = _t(a), _t(b)
    w0 = diff_somme(vb, va, c)                            # τc(b = a+c)
    cw0 = cardinal(w0)
    body0 = egal(vb, somme_cardinale_binaire(va, var(c)))  # b = a + c

    ante = et(et(est_cardinal(va), est_cardinal(vb)), inf_egal_card(va, vb))
    h = N.assume(ante)

    exists = N.modus_ponens(h, existe_complement_somme(a, b, c))   # (∃c) b = a+c
    realise = N.modus_ponens(exists, N.existe_temoin(body0, c))    # b = a + w0
    # a+w0 = a+Card(w0)
    somme_eq = _somme_card_droite(va, w0)                # a+w0 = a+Card(w0)
    b_eq_aCw0 = composer_egalites(realise, somme_eq)     # b = a + Card(w0)
    # Card(w0) est un cardinal
    card_cw0 = card_est_un_cardinal(w0, est_cardinal(cw0).lieur)   # est_cardinal(Card w0)
    # témoin c := Card(w0) : (card c et b = a+c)
    body = et(est_cardinal(var(c)), egal(vb, somme_cardinale_binaire(va, var(c))))
    conj = conjonction_intro(card_cw0, b_eq_aCw0)        # card(Card w0) et b = a+Card w0
    ex = N.modus_ponens(conj, N.s5(body, cw0, c))        # (∃c)(card c et b = a+c)
    res = N.loi_deduction(ante, ex)
    assert res.conclusion == existe_complement_somme_cardinal_enonce(a, b, c), \
        "existe_complement_somme_cardinal : conclusion inattendue"
    assert res.est_clos and not res.hypotheses, "existe_complement_somme_cardinal : non close !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ANNULATION ADDITIVE DE L'ORDRE (a fini) :
#     ( est_entier a et card u et card v et a+u ≤ a+v ) ⇒ u ≤ v
# ════════════════════════════════════════════════════════════════════════════
def _card_somme(va, vu):
    """⊢ est_cardinal( somme_cardinale_binaire(a, u) )   (= Card(a⊔u))."""
    va, vu = _t(va), _t(vu)
    aXu = somme_disjointe(va, vu)
    return card_est_un_cardinal(aXu, est_cardinal(somme_cardinale_binaire(va, vu)).lieur)


def additive_order_cancel_enonce(a="aoc", u="uoc", v="voc"):
    va, vu, vv = _t(a), _t(u), _t(v)
    au = somme_cardinale_binaire(va, vu)
    av = somme_cardinale_binaire(va, vv)
    return impl(et(et(et(est_entier(va), est_cardinal(vu)), est_cardinal(vv)),
                   inf_egal_card(au, av)),
                inf_egal_card(vu, vv))


def additive_order_cancel(a="aoc", u="uoc", v="voc"):
    """⊢ ( est_entier a et card u et card v et a+u ≤ a+v ) ⇒ u ≤ v.   (CLOS, 0 hyp.)

    Comparabilité (u≤v ou v≤u).  Branche u≤v : conclusion.  Branche v≤u : mono-large
    (prop4_translation_croissante) donne a+v≤a+u ; avec a+u≤a+v et a+u,a+v cardinaux,
    antisymétrie ⇒ a+u=a+v ; injectivité (prop4_translation_injective) ⇒ u=v ;
    réflexivité ⇒ u≤v."""
    va, vu, vv = _t(a), _t(u), _t(v)
    au = somme_cardinale_binaire(va, vu)
    av = somme_cardinale_binaire(va, vv)

    ante = et(et(et(est_entier(va), est_cardinal(vu)), est_cardinal(vv)),
              inf_egal_card(au, av))
    h = N.assume(ante)
    h_ent = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))  # est_entier a
    h_cu = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))   # card u
    h_cv = conjonction_elim_droite(conjonction_elim_gauche(h))    # card v
    h_le = conjonction_elim_droite(h)                            # a+u ≤ a+v

    # comparabilité u≤v ou v≤u
    total = instancie(instancie(inf_egal_total_general("X", "Y"), vu), vv)   # u≤v ou v≤u
    # branche u≤v : direct
    branch_uv = N.loi_deduction(inf_egal_card(vu, vv), N.assume(inf_egal_card(vu, vv)))
    # branche v≤u
    h_vu = N.assume(inf_egal_card(vv, vu))                       # v ≤ u
    croiss = prop4_translation_croissante(a="acocP4", x="xcocP4", x2="xpcocP4")
    croiss_g = N.generalisation("acocP4", N.generalisation("xcocP4",
        N.generalisation("xpcocP4", croiss)))
    croiss_inst = instancie(instancie(instancie(croiss_g, va), vv), vu)  # (v≤u)⇒(a+v≤a+u)
    av_le_au = N.modus_ponens(h_vu, croiss_inst)               # a+v ≤ a+u
    # antisymétrie : (a+u≤a+v et a+v≤a+u et card(a+u) et card(a+v)) ⇒ a+u=a+v
    card_au = _card_somme(va, vu)                              # est_cardinal(a+u)
    card_av = _card_somme(va, vv)                              # est_cardinal(a+v)
    anti = instancie(instancie(inf_egal_antisymetrique_card("a", "b"), au), av)
    au_eq_av = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(h_le, av_le_au), card_au), card_av), anti)   # a+u = a+v
    # injectivité : (est_entier a et card u et card v) ⇒ (a+u=a+v ⇒ u=v)
    inj = prop4_translation_injective(a="aiP4", x="xiP4", xp="xpiP4")
    inj_g = N.generalisation("aiP4", N.generalisation("xiP4",
        N.generalisation("xpiP4", inj)))
    inj_inst = instancie(instancie(instancie(inj_g, va), vu), vv)
    inj_impl = N.modus_ponens(conjonction_intro(conjonction_intro(h_ent, h_cu), h_cv),
                              inj_inst)                         # (a+u=a+v)⇒(u=v)
    u_eq_v = N.modus_ponens(au_eq_av, inj_impl)               # u = v
    # u=v ⇒ u≤v : réflexivité u≤u puis Leibniz u↦v sur la droite
    refl_u = instancie(N.generalisation("X", inf_egal_reflexif("X")), vu)   # u ≤ u
    u_le_v = N.modus_ponens(refl_u, equivalence_avant(N.modus_ponens(
        u_eq_v, N.s6(vu, vv, "w", inf_egal_card(vu, var("w"))))))   # u ≤ v
    branch_vu = N.loi_deduction(inf_egal_card(vv, vu), u_le_v)

    le = cas(total, branch_uv, branch_vu)                     # u ≤ v
    res = N.loi_deduction(ante, le)
    assert res.conclusion == additive_order_cancel_enonce(a, u, v), \
        "additive_order_cancel : conclusion inattendue"
    assert res.est_clos and not res.hypotheses, "additive_order_cancel : non close !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 SURJECTIVITÉ de la translation x ↦ a+x : [0,b] → [a,a+b]
# ════════════════════════════════════════════════════════════════════════════
def prop4_surjective_enonce(a="aP4surj", b="bP4surj", y="yP4surj", u="uP4surj"):
    va, vb, vy = _t(a), _t(b), _t(y)
    ab = somme_cardinale_binaire(va, vb)
    seg_dom = E.intervalle_entiers(ZERO, vb)
    return impl(et(et(est_entier(va), est_entier(vb)),
                   appartient(vy, E.intervalle_entiers(va, ab))),
                existe(u, et(appartient(var(u), seg_dom),
                             egal(somme_cardinale_binaire(va, var(u)), vy))))


def prop4_surjective(a="aP4surj", b="bP4surj", y="yP4surj", u="uP4surj"):
    """🎯 ⊢ ( est_entier a et est_entier b et y∈[a,a+b] ) ⇒
              (∃u)( u∈[0,b] et a+u = y ).   (CLOS, 0 hyp — SURJECTIVITÉ, Prop. 4 §III.5.)

    y∈[a,a+b] ⇒ (y card, a≤y, y≤a+b).  Existence cardinale du complément (a,y) sous a≤y :
    (∃c)(card c et y=a+c) ; témoin u (card u, y=a+u) ⇒ a+u=y.  u≤b par annulation
    additive de a+u≤a+b (réécrit y≤a+b via a+u=y).  0≤u (zero_inf_egal) ⇒ u∈[0,b].
    S5 ⇒ (∃u)(u∈[0,b] et a+u=y)."""
    va, vb, vy = _t(a), _t(b), _t(y)
    ab = somme_cardinale_binaire(va, vb)
    seg_codom = E.intervalle_entiers(va, ab)
    seg_dom = E.intervalle_entiers(ZERO, vb)

    ante = et(et(est_entier(va), est_entier(vb)), appartient(vy, seg_codom))
    h = N.assume(ante)
    h_enta = conjonction_elim_gauche(conjonction_elim_gauche(h))   # est_entier a
    h_entb = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_entier b
    h_in = conjonction_elim_droite(h)                             # y ∈ [a,a+b]

    card_a = N.modus_ponens(h_enta, fini_implique_cardinal(va))   # est_cardinal a
    card_b = N.modus_ponens(h_entb, fini_implique_cardinal(vb))   # est_cardinal b

    # corps de y∈[a,a+b] : (y card, a≤y, y≤a+b)
    corps = N.modus_ponens(h_in, equivalence_avant(_mem_int_t(va, ab, vy)))
    card_y = conjonction_elim_gauche(conjonction_elim_gauche(corps))  # est_cardinal y
    a_le_y = conjonction_elim_droite(conjonction_elim_gauche(corps)) # a ≤ y
    y_le_ab = conjonction_elim_droite(corps)                        # y ≤ a+b

    # existence cardinale du complément (a, y) sous (card a et card y et a≤y)
    cc = "cP4surjc"
    ecsc = existe_complement_somme_cardinal(a, y, cc)            # (card a et card y et a≤y)⇒(∃c)(card c et y=a+c)
    exists = N.modus_ponens(conjonction_intro(conjonction_intro(card_a, card_y), a_le_y), ecsc)

    # réaliser le témoin u := τc( card c et y=a+c ) (τ canonique du corps RENFORCÉ,
    # qui PORTE est_cardinal — ce n'est donc PAS diff_somme, dont le corps diffère).
    from bourbaki.logique.i_1_termes_relations.formule import tau
    body = et(est_cardinal(var(cc)), egal(vy, somme_cardinale_binaire(va, var(cc))))
    wu = tau(cc, body)                                          # u = τc(card c et y=a+c)
    realise = N.modus_ponens(exists, N.existe_temoin(body, cc)) # (card u et y = a+u)
    card_u = conjonction_elim_gauche(realise)                   # est_cardinal u
    y_eq_au = conjonction_elim_droite(realise)                  # y = a + u
    au = somme_cardinale_binaire(va, wu)                        # a+u
    au_eq_y = N.modus_ponens(y_eq_au, symetrie(vy, au))        # a+u = y

    # u ≤ b : a+u ≤ a+b (réécrit y≤a+b via y=a+u) puis annulation additive
    au_le_ab = N.modus_ponens(y_le_ab, equivalence_avant(N.modus_ponens(
        y_eq_au, N.s6(vy, au, "w", inf_egal_card(var("w"), ab)))))   # a+u ≤ a+b
    aoc = additive_order_cancel("aocP4s", "uocP4s", "vocP4s")
    aoc_g = N.generalisation("aocP4s", N.generalisation("uocP4s",
        N.generalisation("vocP4s", aoc)))
    aoc_inst = instancie(instancie(instancie(aoc_g, va), wu), vb)
    # aoc_inst : (est_entier a et card u et card b et a+u≤a+b) ⇒ u≤b
    u_le_b = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(h_enta, card_u), card_b), au_le_ab), aoc_inst)  # u ≤ b

    # 0 ≤ u
    zero_le_u = _zero_inf_egal_card(wu)                        # 0 ≤ u

    # u ∈ [0,b]  via (card u, 0≤u, u≤b)
    corps_u = conjonction_intro(conjonction_intro(card_u, zero_le_u), u_le_b)
    u_in = N.modus_ponens(corps_u, equivalence_arriere(_mem_int_t(ZERO, vb, wu)))  # u∈[0,b]

    # (∃u)(u∈[0,b] et a+u=y)  via S5 sur le témoin wu
    body_final = et(appartient(var(u), seg_dom),
                    egal(somme_cardinale_binaire(va, var(u)), vy))
    conj_final = conjonction_intro(u_in, au_eq_y)             # u∈[0,b] et a+u=y
    ex = N.modus_ponens(conj_final, N.s5(body_final, wu, u))  # (∃u)(u∈[0,b] et a+u=y)
    res = N.loi_deduction(ante, ex)
    assert res.conclusion == prop4_surjective_enonce(a, b, y, u), \
        "prop4_surjective : conclusion inattendue"
    assert res.est_clos and not res.hypotheses, "prop4_surjective : non close !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PROP 4 ASSEMBLÉE : x↦a+x est un ISOMORPHISME D'ORDRE de [0,b] sur [a,a+b]
#
#  Bundle des QUATRE propriétés établies (sous (est_entier a et est_entier b)) :
#    (1) bien-définie  : x∈[0,b] ⇒ a+x∈[a,a+b]
#    (2) strictement croissante : (card x, card x') ⇒ (x<x' ⇒ a+x<a+x')
#    (3) injective     : (card x, card x') ⇒ (a+x=a+x' ⇒ x=x')
#    (4) surjective    : y∈[a,a+b] ⇒ (∃u)(u∈[0,b] et a+u=y)
#  (énoncé combinatoire de l'iso d'ordre, sans réifier l'application — chacune des
#   quatre composantes est un théorème CLOS ré-employé.)
# ════════════════════════════════════════════════════════════════════════════
def _strict_card(a, x, xp):
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_strict_card
    va, vx, vxp = _t(a), _t(x), _t(xp)
    return impl(inf_strict_card(vx, vxp),
                inf_strict_card(somme_cardinale_binaire(va, vx),
                                somme_cardinale_binaire(va, vxp)))


def prop4_ordre_iso_enonce(a="aP4iso", b="bP4iso", x="xP4iso", xp="xpP4iso",
                           y="yP4iso", u="uP4iso"):
    va, vb, vx, vxp, vy = _t(a), _t(b), _t(x), _t(xp), _t(y)
    ab = somme_cardinale_binaire(va, vb)
    seg_dom = E.intervalle_entiers(ZERO, vb)
    bd = impl(appartient(vx, seg_dom),
              appartient(somme_cardinale_binaire(va, vx), E.intervalle_entiers(va, ab)))
    cards = et(est_cardinal(vx), est_cardinal(vxp))
    st = impl(cards, _strict_card(va, vx, vxp))
    inj = impl(cards, impl(egal(somme_cardinale_binaire(va, vx),
                                somme_cardinale_binaire(va, vxp)), egal(vx, vxp)))
    surj = impl(appartient(vy, E.intervalle_entiers(va, ab)),
                existe(u, et(appartient(var(u), seg_dom),
                             egal(somme_cardinale_binaire(va, var(u)), vy))))
    return impl(et(est_entier(va), est_entier(vb)),
                et(et(et(bd, st), inj), surj))


def prop4_ordre_iso(a="aP4iso", b="bP4iso", x="xP4iso", xp="xpP4iso",
                    y="yP4iso", u="uP4iso"):
    """🎯 ⊢ ( est_entier a et est_entier b ) ⇒
              ( (x∈[0,b] ⇒ a+x∈[a,a+b])
                et ((card x et card x') ⇒ (x<x' ⇒ a+x<a+x'))
                et ((card x et card x') ⇒ (a+x=a+x' ⇒ x=x'))
                et (y∈[a,a+b] ⇒ (∃u)(u∈[0,b] et a+u=y)) ).
       (CLOS, 0 hyp — Prop. 4 §III.5 : x↦a+x ISOMORPHISME D'ORDRE [0,b]→[a,a+b].)

    Conjonction des quatre composantes CLOSES : bien-définie, strictement croissante,
    injective, surjective, ré-employées sous la garde uniforme (est_entier a et
    est_entier b).  (est_cardinal a déchargée par fini_implique_cardinal pour la
    bien-définition.)  Énoncé combinatoire — l'application n'est pas réifiée."""
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_prop4_iii5 import prop4_translation_bien_definie
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop4_strict_iii5 import prop4_translation_stricte
    va, vb, vx, vxp, vy = _t(a), _t(b), _t(x), _t(xp), _t(y)
    ab = somme_cardinale_binaire(va, vb)
    seg_dom = E.intervalle_entiers(ZERO, vb)

    ante = et(est_entier(va), est_entier(vb))
    h = N.assume(ante)
    h_enta = conjonction_elim_gauche(h)
    h_entb = conjonction_elim_droite(h)
    card_a = N.modus_ponens(h_enta, fini_implique_cardinal(va))   # est_cardinal a

    # (1) bien-définie : (card a et x∈[0,b]) ⇒ a+x∈[a,a+b] ; on décharge card a
    bd_thm = prop4_translation_bien_definie(a, b, x)
    h_xin = N.assume(appartient(vx, seg_dom))
    ax_in = N.modus_ponens(conjonction_intro(card_a, h_xin), bd_thm)
    bd = N.loi_deduction(appartient(vx, seg_dom), ax_in)         # x∈[0,b] ⇒ a+x∈[a,a+b]

    # (2) strictement croissante : (est_entier a et card x et card x') ⇒ (x<x'⇒a+x<a+x')
    st_thm = prop4_translation_stricte(a, x, xp)
    cards = et(est_cardinal(vx), est_cardinal(vxp))
    h_cards = N.assume(cards)
    st_inner = N.modus_ponens(conjonction_intro(conjonction_intro(
        h_enta, conjonction_elim_gauche(h_cards)), conjonction_elim_droite(h_cards)), st_thm)
    st = N.loi_deduction(cards, st_inner)                        # (card x et card x') ⇒ (x<x'⇒a+x<a+x')

    # (3) injective : même garde
    inj_thm = prop4_translation_injective(a, x, xp)
    h_cards2 = N.assume(cards)
    inj_inner = N.modus_ponens(conjonction_intro(conjonction_intro(
        h_enta, conjonction_elim_gauche(h_cards2)), conjonction_elim_droite(h_cards2)), inj_thm)
    inj = N.loi_deduction(cards, inj_inner)

    # (4) surjective : (est_entier a et est_entier b et y∈[a,a+b]) ⇒ (∃u)…
    surj_thm = prop4_surjective(a, b, y, u)
    h_yin = N.assume(appartient(vy, E.intervalle_entiers(va, ab)))
    ex = N.modus_ponens(conjonction_intro(conjonction_intro(h_enta, h_entb), h_yin), surj_thm)
    surj = N.loi_deduction(appartient(vy, E.intervalle_entiers(va, ab)), ex)

    conj = conjonction_intro(conjonction_intro(conjonction_intro(bd, st), inj), surj)
    res = N.loi_deduction(ante, conj)
    assert res.conclusion == prop4_ordre_iso_enonce(a, b, x, xp, y, u), \
        "prop4_ordre_iso : conclusion inattendue"
    assert res.est_clos and not res.hypotheses, "prop4_ordre_iso : non close !"
    return res


__all__ = [
    "existe_complement_somme_cardinal", "existe_complement_somme_cardinal_enonce",
    "additive_order_cancel", "additive_order_cancel_enonce",
    "prop4_surjective", "prop4_surjective_enonce",
    "prop4_ordre_iso", "prop4_ordre_iso_enonce",
]
