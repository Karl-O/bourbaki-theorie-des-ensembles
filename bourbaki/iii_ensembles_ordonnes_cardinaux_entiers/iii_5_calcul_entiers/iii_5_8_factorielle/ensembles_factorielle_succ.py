"""§III.5.8 — CAS SUCCESSEUR, briques (3A) :  T_fac(u) évalué côté u≠∅, seg⊂E,
dom(f|seg)=seg.

Vers f(n+1)=(n+1)·f(n) (E III.41 L.30-32) : au point m, la forme du livre donne
f(m)=T_fac(u) avec u=f|seg(m) ; si u≠∅ le τ s'évalue sur le SECOND disjoint :

  • `t_fac_en_non_vide(T, u, thm_nonvide)`  Γ ⊢ T(u) = (card(dom u)+1)·u(dom u)
      [Γ = hyps de thm_nonvide ⊢ u≠∅ ; garde-disjonction en ordre INVERSE
       (_ou_commute_gd), puis S7 + S5/existe_temoin]
  • `seg_inclus_e`                 ⊢ seg(R,E,x) ⊂ E                    [CLOS]
  • `dom_restriction_seg`   { bo, ebf, rc } ⊢ dom(f|seg(x)) = seg(x)
      [seg⊂E CLOS + dom(f)=E (3 résidus C62) + restriction_dom_sous_inclusion]

NB — recâblage du 2 août 2026 : la règle porte désormais le M(D u) RÉEL
(`terme_plus_grand`, §III.1.7) et le facteur Déf.2 `card(dom u)` ; l'ancienne
forme-fallback prev = u(D u) est morte.  La chaîne conclut f(succ n) = (succ n)·u(n) ;
le seul écart restant vers la phrase du livre est valeur(u,n) vs valeur(f,n)
(accord de la restriction sur son domaine — brique suivante).
INVARIANT : theorie_ensembles() = 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, equivalence_avant,
    equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
    _garde_disjonction, _ou_commute_gd,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import restriction_dom_sous_inclusion
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import membre_segment
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import dom_fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_zero import _et_parts


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  Γ ⊢ T(u) = (card(dom u)+1)·u(dom u)   pour Γ ⊢ u≠∅  (évaluation du τ, cas succ).
# ════════════════════════════════════════════════════════════════════════════
def t_fac_en_non_vide(T, u, thm_nonvide):
    """Γ ⊢ T(u) = produit( successeur(card(dom u)), valeur(u, dom u) )
                                                       [Γ = hypothèses de thm_nonvide].

    T(u) = τy( (u=∅ ∧ y=1) ∨ (u≠∅ ∧ y=Sval) ).  thm_nonvide ⊢ ¬(u=∅) sert DEUX fois
    (garde vraie du disjoint droit ET réfutation de la garde gauche) ; la disjonction
    est en ordre inverse ⇒ `_garde_disjonction` sur l'ordre commuté + `_ou_commute_gd` ;
    S7 puis S5+existe_temoin évaluent le τ à Sval."""
    u = _t(u)
    Tu = T(u)                                                    # τy(cond)
    cond = Tu.args[0]
    gauche, droite = cond.sous[0], cond.sous[1]
    P0, R0 = _et_parts(gauche)                                   # u=∅ ; y=1
    Q1, R1 = _et_parts(droite)                                   # ¬(u=∅) ; y=Sval
    assert P0 == egal(u, E.VIDE), "t_fac_en_non_vide : garde gauche ≠ u=∅"
    assert Q1 == thm_nonvide.conclusion, "t_fac_en_non_vide : thm_nonvide ≠ ¬(u=∅)"
    vy = var(Tu.lieur)
    Sval = R1.termes[1]                                          # le terme (…)·(…)

    # ordre inverse : ((u≠∅ ∧ y=Sval) ∨ (u=∅ ∧ y=1)) ⇔ (y=Sval), puis commute
    gd = _garde_disjonction(thm_nonvide, thm_nonvide, R1, R0)
    chain = _ou_commute_gd(gd, cond)                             # cond ⇔ (y=Sval)
    gen = N.generalisation(Tu.lieur, chain)
    tau_eq = N.modus_ponens(gen, N.s7(cond, R1, Tu.lieur))       # τ(cond)=τ(y=Sval)
    tau_val = N.modus_ponens(
        N.modus_ponens(N.reflexivite(Sval), N.s5(egal(vy, Sval), Sval, Tu.lieur)),
        N.existe_temoin(egal(vy, Sval), Tu.lieur))               # τ(y=Sval)=Sval
    res = composer_egalites(tau_eq, tau_val)

    assert res.conclusion == egal(Tu, Sval), "t_fac_en_non_vide : ≠ T(u)=Sval"
    assert set(res.hypotheses) == set(thm_nonvide.hypotheses), \
        "t_fac_en_non_vide : hypothèses ≠ celles de thm_nonvide"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ⊢ seg(R,E,x) ⊂ E   [CLOS]  — tout membre du segment est dans E.
# ════════════════════════════════════════════════════════════════════════════
def seg_inclus_e(e="Enat", G="Gle", x="zfgl"):
    """⊢ seg(R,E,x) ⊂ E   (x nom OU terme)                             [CLOS, 0 hyp]."""
    R = _graphe_R(G)
    ve, vx, vz = _t(e), _t(x), var("z")
    seg = E.segment_extremite(_t(G), ve, vx)

    h = N.assume(appartient(vz, seg))
    car = N.modus_ponens(h, equivalence_avant(membre_segment(G, e, vx, vz)))
    zE = conjonction_elim_gauche(conjonction_elim_gauche(car))   # z∈E
    res = N.generalisation("z", N.loi_deduction(appartient(vz, seg), zE))

    assert res.conclusion == inclus(seg, ve), "seg_inclus_e : ≠ seg⊂E"
    assert res.est_clos, "seg_inclus_e : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  { bo, ebf, rc } ⊢ dom( f|seg(x) ) = seg(x)   — le domaine de u est le segment.
# ════════════════════════════════════════════════════════════════════════════
def dom_restriction_seg(vh, e="Enat", G="Gle", V="Uval", x="zfgl"):
    """{ bo, essais_bien_formes, rule_codomain } ⊢ dom(f|seg(x)) = seg(x).

    seg⊂E [CLOS] transporté le long de dom(f)=E [3 résidus C62] donne seg⊂dom f ;
    `restriction_dom_sous_inclusion` (CLOS) conclut.  x : nom OU terme."""
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, vx)

    sub = seg_inclus_e(e, G, x)                                  # seg⊂E   [CLOS]
    domE = dom_fonction_globale(vh, e, G, V)                     # dom f=E [3 hyps]
    e_eq = N.modus_ponens(domE, symetrie(E.dom(f), ve))          # E = dom f
    equivF = N.modus_ponens(e_eq, N.s6(ve, E.dom(f), "wde", inclus(seg, var("wde"))))
    sub_dom = N.modus_ponens(sub, equivalence_avant(equivF))     # seg ⊂ dom f
    res = N.modus_ponens(sub_dom, restriction_dom_sous_inclusion(f, seg))

    assert res.conclusion == egal(E.dom(E.restriction(f, seg)), seg), \
        "dom_restriction_seg : ≠ dom(f|seg)=seg"
    assert len(res.hypotheses) == 3, "dom_restriction_seg : hyps ≠ 3"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  Γ ⊢ f|seg(m) ≠ ∅   — le témoin (0, f(0)) habite la restriction.
# ════════════════════════════════════════════════════════════════════════════
def _rebuild_restr_t(F, A, z, a, b, thm_corps):
    """De ⊢ ((z=(a,b) ∧ a∈A) ∧ (a,b)∈F) [thm_corps, a,b TERMES] déduit ⊢ z∈F|A."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements.ensembles_restrictions import _inst_restriction
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, existe
    F, A, z, a, b = _t(F), _t(A), _t(z), _t(a), _t(b)
    vp, vq = var("p"), var("q")
    corps_pq = et(et(egal(z, E.couple(vp, vq)), appartient(vp, A)),
                  appartient(E.couple(vp, vq), F))
    corps_aq = et(et(egal(z, E.couple(a, vq)), appartient(a, A)),
                  appartient(E.couple(a, vq), F))
    ex_q = N.modus_ponens(thm_corps, N.s5(corps_aq, b, "q"))
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", corps_pq), a, "p"))
    return N.modus_ponens(ex_pq, equivalence_arriere(_inst_restriction(F, A, z)))


def u_non_vide(vh, e="Enat", G="Gle", V="Uval", n="nfsc"):
    """{ ZERO∈E, ZERO∈seg(succ n), bo, ebf, rc } ⊢ ¬( f|seg(succ n) = ∅ ).

    ZERO∈dom f (dom f=E, 3 résidus) donne un couple (0,y)∈f [AXIOME_DOM] ; avec
    ZERO∈seg(succ n) il se REBUILD dans la restriction ⇒ (∃z)(z∈u) ⇒ u≠∅."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, non
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, successeur
    R = _graphe_R(G)
    ve, vn = _t(e), var(n)
    m = successeur(vn)
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, m)
    u = E.restriction(f, seg)

    h_0E = N.assume(appartient(ZERO, ve))                        # ZERO∈E      [HONNÊTE]
    h_0s = N.assume(appartient(ZERO, seg))                       # ZERO∈seg(m) [HONNÊTE]
    domE = dom_fonction_globale(vh, e, G, V)                     # dom f=E [3 résidus]
    e_eq = N.modus_ponens(domE, symetrie(E.dom(f), ve))          # E=dom f
    eqF = N.modus_ponens(e_eq, N.s6(ve, E.dom(f), "wde", appartient(ZERO, var("wde"))))
    z0_dom = N.modus_ponens(h_0E, equivalence_avant(eqF))        # ZERO∈dom f
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax_dom, f), ZERO)
    exy = N.modus_ponens(z0_dom, equivalence_avant(car))         # (∃y)((0,y)∈f)

    vy = var("y")
    cpl = E.couple(ZERO, vy)
    h_y = N.assume(appartient(cpl, f))
    wit = conjonction_intro(conjonction_intro(N.reflexivite(cpl), h_0s), h_y)
    z_in_u = _rebuild_restr_t(f, seg, cpl, ZERO, vy, wit)        # (0,y)∈u
    exz = N.modus_ponens(z_in_u, N.s5(appartient(var("z"), u), cpl, "z"))   # (∃z)(z∈u)
    nv_car = instancie(N.generalisation("A", non_vide_ssi_element("A")), u)
    res = N.modus_ponens(exz, equivalence_arriere(nv_car))       # ¬(u=∅)
    res = N.modus_ponens(exy, existe_elimination(
        N.loi_deduction(appartient(cpl, f), res), "y"))

    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import non as _non
    assert res.conclusion == _non(egal(u, E.VIDE)), "u_non_vide : ≠ ¬(u=∅)"
    assert len(res.hypotheses) == 5, "u_non_vide : hyps ≠ 5"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 f(succ n) = (succ succ n) · u([0,n])   — LE CAS SUCCESSEUR (forme-fallback).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« (n+1)! = n!(n+1) » — le cas successeur ; depuis le recâblage du 2 août la règle porte M(D u) réel et le facteur Déf.2 ; reste u(n) vs f(n))
def factorielle_succ_fallback(e="Enat", G="Gle", V="Vfac62", n="nfsc"):
    """🎯🎯 { bo, ebf, rc, essais_restriction(T_Z,T_Z), succ n∈E, seg(succ n)=[0,n],
             ZERO∈E, ZERO∈seg(succ n), est_entier(n) } ⊢
        valeur(f, succ n) = produit( successeur(n), valeur(u, n) )
    où u = f|seg(succ n) et T_Z = regle_factorielle(zcard="Z") (liant cardinal
    canonique, raccordable à prop5 — légitime depuis le fix subst).
    C'EST « f(n+1) = (n+1)·u(n) » : le facteur du livre, le point PRÉDÉCESSEUR réel.
    (Nom « fallback » historique — l'écart fallback est MORT le 2 août ; l'écart
    restant vers la phrase du livre est valeur(u,n) vs valeur(f,n).)

    ⚠️ zcard="Z" est FORCÉ, ne PAS le paramétrer : l'étape (5) réécrit
    `cardinal([0,n], z="Z")` par `prop5_intervalle_zero`, qui écrit Card au liant
    CANONIQUE de `cardinal` (`def cardinal(X, z="Z")`).  Toute autre valeur fait
    échouer l'assert « Sval inattendu » de l'étape (3).
    ⚠️ CONSÉQUENCE, mesurée le 26 juil. : ce théorème n'est PAS recollable avec
    `factorielle_zero()` À SES DÉFAUTS (zcard="Zfac62") — 2 hypothèses partagées
    seulement, union 13 au lieu de 10.  Les jeux d'hypothèses sont pourtant
    α-ÉQUIVALENTS (mesuré) : le désaccord porte sur le NOM d'un τ-liant, que le noyau
    n'identifie pas.  C'est `factorielle_zero` qu'il faut appeler avec zcard="Z".  Cf.
    `ensembles_factorielle_existence_vrai.factorielle_caracterisation`, qui JOINT les
    deux moitiés en la phrase du livre (E III.41 L.30-32).

    Chaîne : forme du livre en succ n → τ évalué côté u≠∅ (`t_fac_en_non_vide`) →
    dom u→seg (`dom_restriction_seg`) → seg→[0,n] [donnée d'ordre] →
    Card([0,n])=succ n [prop5, CLOS] → M([0,n])=n [`max_intervalle_vaut_n_entier`,
    MÊME hypothèse est_entier(n) que prop5 : l'étape est gratuite]."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, successeur
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_equation_restriction import equation_restriction_fonction
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_prop4_iii5 import prop5_intervalle_zero
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_max_intervalle_iii5 import max_intervalle_vaut_n_entier
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import terme_plus_grand
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import congruence_terme

    R = _graphe_R(G)
    ve, vn = _t(e), var(n)
    m = successeur(vn)
    T = regle_factorielle(zcard="Z")
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, m)
    u = E.restriction(f, seg)
    I0n = E.intervalle_entiers(ZERO, vn)

    def _rewrite(eq_thm, gauche, droite, template, hole):
        """De ⊢ gauche=droite : ⊢ template{gauche} = template{droite} (trou clos)."""
        imp = congruence_terme(var(hole), droite, template, hole)
        return N.modus_ponens(eq_thm, instancie(N.generalisation(hole, imp), gauche))

    # (1) forme du livre en m : f(m) = T(u)
    eqres = equation_restriction_fonction(T, T, e, G, V)
    h_mE = N.assume(appartient(m, ve))                           # succ n∈E   [HONNÊTE]
    eqm = N.modus_ponens(h_mE, instancie(eqres, m))              # f(m)=T(u)

    # (2) τ évalué côté u≠∅
    nv = u_non_vide(T, e, G, V, n)                               # ¬(u=∅) [5 hyps]
    tnv = t_fac_en_non_vide(T, u, nv)                            # T(u)=succ(card(dom u))·u(dom u)
    Sval = tnv.conclusion.termes[1]

    # (3) dom u → seg   (trou TRIPLE : le cardinal + les 2 occurrences sous le τ de M)
    dr = dom_restriction_seg(T, e, G, V, m)                      # dom u = seg [3 résidus]
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
    _M = lambda A: terme_plus_grand(inf_egal_card, A, "m", "x")  # le M de la règle
    tpl3 = produit_cardinal_binaire(cardinal(var("wdu"), z="Z"),
                                    E.valeur(u, _M(var("wdu"))))
    assert Sval == produit_cardinal_binaire(cardinal(E.dom(u), z="Z"),
                                            E.valeur(u, _M(E.dom(u)))), \
        "factorielle_succ_fallback : Sval inattendu (forme de la règle ?)"
    e3 = _rewrite(dr, E.dom(u), seg, tpl3, "wdu")                # Sval = …(seg)…

    # (4) seg → [0,n]   (donnée d'ordre, trou triple)
    h_seg = N.assume(egal(seg, I0n))                             # seg(m)=[0,n] [HONNÊTE]
    tpl4 = produit_cardinal_binaire(cardinal(var("wsi"), z="Z"),
                                    E.valeur(u, _M(var("wsi"))))
    e4 = _rewrite(h_seg, seg, I0n, tpl4, "wsi")                  # …(seg)… = …([0,n])…

    # (5) Card([0,n]) = succ n   (prop5, CLOS ; hyp est_entier(n))
    p5 = prop5_intervalle_zero(vn)
    h_ent = N.assume(p5.conclusion.sous[0].sous[0])              # est_entier(n) [HONNÊTE]
    card_eq = N.modus_ponens(h_ent, p5)                          # Card([0,n]) = succ n
    tpl5 = produit_cardinal_binaire(var("wcp"), E.valeur(u, _M(I0n)))
    e5 = _rewrite(card_eq, cardinal(I0n, z="Z"), successeur(vn), tpl5, "wcp")

    # (6) M([0,n]) = n   (max_intervalle_vaut_n_entier — MÊME hypothèse est_entier(n))
    mx = max_intervalle_vaut_n_entier(vn)                        # M([0,n]) = n [1 hyp]
    tpl6 = produit_cardinal_binaire(successeur(vn), E.valeur(u, var("wmx")))
    e6 = _rewrite(mx, _M(I0n), vn, tpl6, "wmx")                  # …M([0,n])… = …n…

    # chaîne complète
    res = composer_egalites(composer_egalites(composer_egalites(composer_egalites(
        composer_egalites(eqm, tnv), e3), e4), e5), e6)

    cible = egal(E.valeur(f, m),
                 produit_cardinal_binaire(successeur(vn), E.valeur(u, vn)))
    assert res.conclusion == cible, "factorielle_succ_fallback : ≠ cible"
    assert len(res.hypotheses) == 9, "factorielle_succ_fallback : hyps ≠ 9"
    assert res.conclusion not in res.hypotheses, "factorielle_succ_fallback : VACUOUS"
    return res


__all__ = ["t_fac_en_non_vide", "seg_inclus_e", "dom_restriction_seg",
           "u_non_vide", "factorielle_succ_fallback"]
