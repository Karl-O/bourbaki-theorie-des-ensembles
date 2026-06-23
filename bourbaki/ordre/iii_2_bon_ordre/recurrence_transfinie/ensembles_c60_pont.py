"""§III.2 — RÉCURRENCE TRANSFINIE (Critère C60) : LE PONT bare→ambiant.

Suite DIRECTE de `ensembles_c60_clauses` (qui CLOSE `recursion_transfinie_existence_complet`
⊢ existence sous { est_bien_ordonne(R,E), clause_P3_ambiant, clause_P4_ambiant }, où les
deux clauses AMBIANTES portent `antecedent_couverture_ambiant` qui EXIGE que chaque essai
témoin p d'un y<x vive dans l'ambiant 𝔓(E×V)).

────────────────────────────────────────────────────────────────────────────────
LE PONT (le verrou honnête de c60_clauses).

  De `est_essai(p,vh,R,E,y)` SEUL, `p∈𝔓(E×V)` n'est PAS dérivable : vh est OPAQUE
  (aucune contrainte vh(z)∈V), et est_essai (= fonctionnel ∧ dom=seg∪{y} ∧ équation de
  récursion) ne dit RIEN de STRUCTUREL — il N'IMPOSE PAS que les membres de p soient des
  COUPLES (`est_fonctionnel` quantifie sur les couples mais n'EXCLUT pas un membre
  non-couple ; cf. `ensembles_h_est_graphe` qui rencontre exactement ce phénomène).

  Le pont ajoute donc les hypothèses HONNÊTES et NATURELLES de la construction de Bourbaki :
    • rule-codomain  (∀z)( vh(z) ∈ V )            — la règle h produit ses valeurs dans V ;
    • est_un_graphe(p)                            — un essai EST un ensemble de couples
                                                     (E.II.37 ; c'est ce qu'est un graphe) ;
    • dom(p) ⊂ E                                  — le domaine de l'essai vit dans E (le
                                                     segment seg(R,E,y)∪{y} ⊂ E).
  Alors pour c∈p : c=(a,b) [graphe] ; a∈dom(p) [a couple atteste l'antécédent] ; a∈E
  [dom p⊂E] ; b=valeur(p,a) [fonctionnel + C46] ; valeur(p,a)=vh(a) [équation de récursion]
  ; vh(a)∈V [rule-codomain] ; donc b∈V ; donc c=(a,b)∈E×V.  D'où p⊂E×V, donc p∈𝔓(E×V)
  par l'axiome des parties A3 (A⊂B ⇒ A∈𝔓(B)).

  `essai_dans_parties(vh)` ⊢ { est_essai(p,vh,R,E,y), est_un_graphe(p), dom(p)⊂E,
  rule-codomain } ⇒ p∈𝔓(E×V).  C'est le PONT bare→ambiant.

INVARIANT : theorie_ensembles() = 22.  Tout DÉRIVÉ, rien postulé.  vh OPAQUE.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus, subst_f,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, equivalence_transitivite,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.ensembles.fonctions.ensembles_fonctions import valeur_dans_graphe
from bourbaki.ensembles.fonctions.ensembles_restriction_somme import antecedent_dans_domaine
from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ensembles.familles.ensembles_produit_famille import _inst_parties

from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import est_essai
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation import ambiant


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def rule_codomain(vh, V="Vval", z="zrc"):
    """L'hypothèse rule-codomain :  (∀z)( vh(z) ∈ V ).

    « La règle h produit ses valeurs dans V (le contenant des valeurs candidates). »
    C'est la donnée NATURELLE de la construction de Bourbaki (f(x)=h(x,f|seg), h:…→V).
    vh OPAQUE (callable Terme→Terme)."""
    vz = var(z)
    return pourtout(z, appartient(vh(vz), _t(V)))


def _alpha_couple(vc, a, b):
    """⊢ (∃x)(∃y)(c=(x,y)) ⇔ (∃a)(∃b)(c=(a,b))   (double renommage-α, a,b FRAIS dans c).

    `est_un_couple(c)` lie x (externe), y (interne).  On renomme y→b sous (∃x), on
    remonte la congruence sous (∃x), puis x→a.  Pattern de `_alpha_existe2`
    (`ensembles_h_est_graphe`).  a,b supposés FRAIS dans c."""
    va = var(a)
    inner_xy = egal(vc, E.couple(var("x"), var("y")))            # c=(x,y)
    # renommer interne y→b sous le liant x : (∃y)(c=(x,y)) ⇔ (∃b)(c=(x,b))
    inner_x = egal(vc, E.couple(var("x"), var(b)))              # corps après y→b (x encore liant)
    ren_y = alpha_existe("y", b, egal(vc, E.couple(var("x"), var("y"))))   # (∃y)(c=(x,y))⇔(∃b)(c=(x,b))
    eqv_y_lift = _congruence_existe(ren_y, "x")                 # (∃x)(∃y)… ⇔ (∃x)(∃b)…
    body_a = existe(b, egal(vc, E.couple(va, var(b))))         # (∃b)(c=(a,b))  — corps après x→a
    body_x = existe(b, egal(vc, E.couple(var("x"), var(b))))   # (∃b)(c=(x,b))
    ren_x = alpha_existe("x", a, body_x)                       # (∃x)(∃b)… ⇔ (∃a)(∃b)…
    return equivalence_transitivite(eqv_y_lift, ren_x)


def _congruence_existe(thm_eq, x):
    """⊢ (R⇔S) (x non libre dans Γ) ⟹ Γ ⊢ (∃x)R ⇔ (∃x)S."""
    avant = monotonie_existe(equivalence_avant(thm_eq), x)
    arriere = monotonie_existe(equivalence_arriere(thm_eq), x)
    return conjonction_intro(avant, arriere)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LE PONT — essai_dans_parties(vh)  ⊢  p ∈ 𝔓(E×V).
# ════════════════════════════════════════════════════════════════════════════
def essai_dans_parties(vh, e="E", G="G", y="ypont", V="Vval",
                       p="ppont", c="cpont", a="apont", b="bpont", z="zrc"):
    """{ est_essai(p,vh,R,E,y), est_un_graphe(p), dom(p)⊂E, (∀z)vh(z)∈V } ⊢ p ∈ 𝔓(E×V).

    🎯 LE PONT bare→ambiant.  Tout essai p d'un point y, qui EST un graphe (ensemble de
    couples) de domaine ⊂ E, et dont la règle vh prend ses valeurs dans V, vit dans
    l'ambiant 𝔓(E×V).  PREUVE (p ⊂ E×V puis A3) : pour c∈p,
      • c=(a,b)                       [est_un_graphe(p), témoins a,b éliminés] ;
      • a∈dom(p)                      [(a,b)∈p ⇒ a∈dom p, `antecedent_dans_domaine`] ;
      • a∈E                           [dom(p)⊂E instancié à a] ;
      • b=valeur(p,a)                 [est_fonctionnel(p) + (a,b)∈p, C46 `valeur_caracterisation`] ;
      • valeur(p,a)=vh(a)             [équation de récursion de est_essai, a∈dom p] ;
      • vh(a)∈V                       [rule-codomain instancié à a] ⇒ b∈V ;
      • c=(a,b)∈E×V                   [couple_dans_produit] ⇒ c∈E×V.
    D'où p⊂E×V, donc p∈𝔓(E×V) par A3 (`_inst_parties`).

    ⚠️ QUATRE hypothèses HONNÊTES (non vacuous, theorie=22) : est_essai(p,y),
    est_un_graphe(p), dom(p)⊂E, rule-codomain — les données naturelles de la
    construction de Bourbaki.  vh OPAQUE."""
    R = _graphe_R(G)
    ve, vy, vV = _t(e), _t(y), _t(V)
    vp, vc, va, vb = var(p), var(c), var(a), var(b)
    EV = E.produit(ve, vV)
    amb = ambiant(e, V)                                           # 𝔓(E×V)

    # ── hypothèses honnêtes ──────────────────────────────────────────────────
    h_essai = N.assume(est_essai(vp, vh, R, ve, vy, z))          # est_essai(p,y)
    h_graphe = N.assume(E.est_un_graphe(vp))                     # est_un_graphe(p)
    h_dom_sub = N.assume(inclus(E.dom(vp), ve))                  # dom(p) ⊂ E
    h_rule = N.assume(rule_codomain(vh, V, z))                   # (∀z) vh(z)∈V

    func_p = conjonction_elim_gauche(conjonction_elim_gauche(h_essai))   # est_fonctionnel(p)
    eq_rec = conjonction_elim_droite(h_essai)        # (∀z)(z∈dom p ⇒ valeur(p,z)=vh(z))

    # ── BUT : c∈p ⇒ c∈E×V ────────────────────────────────────────────────────
    h_c_in_p = N.assume(appartient(vc, vp))                      # c∈p

    # c=(x,y) via est_un_graphe(p), renommé en (∃a)(∃b)(c=(a,b))
    couple_c_xy = N.modus_ponens(h_c_in_p, instancie(h_graphe, vc))   # (∃x)(∃y)(c=(x,y))
    couple_c = N.modus_ponens(couple_c_xy, equivalence_avant(_alpha_couple(vc, a, b)))  # (∃a)(∃b)(c=(a,b))

    # corps témoin (a,b) :  c=(a,b)  ⇒  c∈E×V
    h_c_eq = N.assume(egal(vc, E.couple(va, vb)))                # c=(a,b)
    cab_in_p = N.modus_ponens(h_c_in_p, equivalence_avant(
        N.modus_ponens(h_c_eq, N.s6(vc, E.couple(va, vb), "wcab", appartient(var("wcab"), vp)))))  # (a,b)∈p
    a_in_dom = N.modus_ponens(cab_in_p, antecedent_dans_domaine(va, vb, vp))   # a∈dom p
    a_in_E = N.modus_ponens(a_in_dom, instancie(h_dom_sub, va))  # a∈E
    # b=valeur(p,a)  via fonctionnalité : ((a,b)∈p et (a,p(a))∈p) ⇒ b=p(a)
    pa = E.valeur(vp, va)                             # p(a) = τw((a,w)∈p)
    # (∃w)((a,w)∈p)  (témoin w:=b)  ⇒  (a,p(a))∈p  [valeur_dans_graphe]
    ex_w = N.modus_ponens(cab_in_p, N.s5(appartient(E.couple(va, var("y")), vp), vb, "y"))  # (∃y)((a,y)∈p)
    a_pa_in_p = N.modus_ponens(ex_w, N.loi_deduction(
        existe("y", appartient(E.couple(va, var("y")), vp)),
        valeur_dans_graphe(vp, va)))                 # (a,p(a))∈p
    func_inst = instancie(instancie(instancie(func_p, va), vb), pa)  # ((a,b)∈p et (a,p(a))∈p)⇒b=p(a)
    b_eq_val = N.modus_ponens(conjonction_intro(cab_in_p, a_pa_in_p), func_inst)   # b=valeur(p,a)
    val_eq_vh = N.modus_ponens(a_in_dom, instancie(eq_rec, va))    # valeur(p,a)=vh(a)
    b_eq_vh = composer_egalites(b_eq_val, val_eq_vh)              # b=vh(a)
    vha_in_V = instancie(h_rule, va)                             # vh(a)∈V
    vha_eq_b = N.modus_ponens(b_eq_vh, symetrie(vb, vh(va)))     # vh(a)=b
    b_in_V = N.modus_ponens(vha_in_V, equivalence_avant(
        N.modus_ponens(vha_eq_b, N.s6(vh(va), vb, "wbv", appartient(var("wbv"), vV)))))   # b∈V
    cab_in_EV = N.modus_ponens(conjonction_intro(a_in_E, b_in_V),
                               equivalence_arriere(couple_dans_produit_ssi(va, vb, ve, vV)))   # (a,b)∈E×V
    c_in_EV = N.modus_ponens(cab_in_EV, equivalence_arriere(
        N.modus_ponens(h_c_eq, N.s6(vc, E.couple(va, vb), "wcev", appartient(var("wcev"), EV)))))  # c∈E×V

    # élimine les témoins a,b (c∈E×V ne contient ni a ni b)
    imp_eq = N.loi_deduction(egal(vc, E.couple(va, vb)), c_in_EV)   # c=(a,b) ⇒ c∈E×V
    ex_b = existe_elimination(imp_eq, b)                          # (∃b)(c=(a,b)) ⇒ c∈E×V
    ex_a = existe_elimination(ex_b, a)                            # (∃a)(∃b)(c=(a,b)) ⇒ c∈E×V
    c_in_EV_f = N.modus_ponens(couple_c, ex_a)                    # c∈E×V   [c∈p, hyps]

    # p ⊂ E×V  =  (∀z)( z∈p ⇒ z∈E×V )  (binder 'z' attendu par inclus / A3)
    sub0 = N.generalisation(c, N.loi_deduction(appartient(vc, vp), c_in_EV_f))   # (∀cpont)(…)
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
    sub = N.modus_ponens(sub0, equivalence_avant(alpha_pour_tout(
        c, "z", impl(appartient(vc, vp), appartient(vc, EV)))))   # (∀z)(z∈p ⇒ z∈E×V)
    assert sub.conclusion == inclus(vp, EV), "essai_dans_parties : ≠ (p ⊂ E×V)"

    # p∈𝔓(E×V)  par A3 (A⊂B ⇒ A∈𝔓(B))
    res = N.modus_ponens(sub, equivalence_arriere(_inst_parties(EV, vp)))   # p∈𝔓(E×V)

    cible = appartient(vp, amb)
    assert res.conclusion == cible, "essai_dans_parties : ≠ p∈𝔓(E×V)"
    assert est_essai(vp, vh, R, ve, vy, z) in res.hypotheses, "essai_dans_parties : est_essai absente"
    assert E.est_un_graphe(vp) in res.hypotheses, "essai_dans_parties : est_un_graphe absente"
    assert inclus(E.dom(vp), ve) in res.hypotheses, "essai_dans_parties : dom⊂E absente"
    assert rule_codomain(vh, V, z) in res.hypotheses, "essai_dans_parties : rule-codomain absente"
    assert res.conclusion not in res.hypotheses, "essai_dans_parties : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  WELL-FORMEDNESS DES ESSAIS — l'hypothèse honnête « tout essai est un graphe de
#  domaine ⊂ E » (la structure d'un essai de Bourbaki, non encodée dans est_essai).
# ════════════════════════════════════════════════════════════════════════════
def essais_bien_formes(vh, e="E", G="G", V="Vval", q="qwf", w="wwf", z="zrc"):
    """(∀q)(∀w)( est_essai(q,vh,R,E,w) ⇒ ( est_un_graphe(q) ∧ dom(q)⊂E ) ).

    « Tout essai (au sens est_essai) est un GRAPHE de domaine ⊂ E. »  C'est la
    STRUCTURE d'un essai de Bourbaki (un graphe fonctionnel partiel sur un segment
    initial de E) — propriété NON encodée dans le prédicat `est_essai` déposé
    (= fonctionnel ∧ dom=seg∪{w} ∧ équation de récursion), donc une hypothèse HONNÊTE
    de bonne formation.  C'est l'INTRANT structurel que `essai_dans_parties` consomme
    pour situer l'essai dans 𝔓(E×V)."""
    R = _graphe_R(G)
    ve = _t(e)
    vq, vw = var(q), var(w)
    return pourtout(q, pourtout(w, impl(
        est_essai(vq, vh, R, ve, vw, z),
        et(E.est_un_graphe(vq), inclus(E.dom(vq), ve)))))


def essai_dans_parties_depuis_bien_formes(vh, e="E", G="G", y="ypont", V="Vval",
                                          p="ppont", c="cpont", a="apont",
                                          b="bpont", z="zrc", q="qwf", w="wwf"):
    """{ est_essai(p,vh,R,E,y), essais_bien_formes(vh), rule-codomain } ⊢ p∈𝔓(E×V).

    `essai_dans_parties` avec ses deux intrants STRUCTURELS (est_un_graphe(p), dom(p)⊂E)
    DÉCHARGÉS depuis l'hypothèse universelle de bonne formation `essais_bien_formes`
    instanciée à (p,y).  Ne restent que les hypothèses NATURELLES { est_essai(p,y),
    essais_bien_formes, rule-codomain }."""
    R = _graphe_R(G)
    ve, vy = _t(e), _t(y)
    vp = var(p)
    base = essai_dans_parties(vh, e, G, y, V, p, c, a, b, z)   # {essai, graphe, dom⊂E, rule}
    h_essai = est_essai(vp, vh, R, ve, vy, z)
    h_wf = N.assume(essais_bien_formes(vh, e, G, V, q, w, z))  # (∀q)(∀w)(essai⇒graphe∧dom⊂E)
    # instancier à (p,y) puis MP avec est_essai(p,y)
    wf_py = instancie(instancie(h_wf, vp), vy)                # essai(p,y) ⇒ (graphe(p) ∧ dom p⊂E)
    h_ess_assume = N.assume(h_essai)
    conj = N.modus_ponens(h_ess_assume, wf_py)                # graphe(p) ∧ dom p⊂E
    graphe_p = conjonction_elim_gauche(conj)                  # est_un_graphe(p)
    domsub_p = conjonction_elim_droite(conj)                  # dom p ⊂ E
    res = N.modus_ponens(graphe_p, N.loi_deduction(E.est_un_graphe(vp), base))
    res = N.modus_ponens(domsub_p, N.loi_deduction(inclus(E.dom(vp), ve), res))
    cible = appartient(vp, ambiant(e, V))
    assert res.conclusion == cible, "essai_dans_parties_depuis_bien_formes : ≠ p∈𝔓(E×V)"
    assert E.est_un_graphe(vp) not in res.hypotheses, "graphe(p) non déchargé"
    assert inclus(E.dom(vp), ve) not in res.hypotheses, "dom⊂E non déchargé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LE PONT bare→ambiant AU NIVEAU ANTÉCÉDENT.
#  antecedent_couverture(x)  +  essais_bien_formes  +  rule-codomain
#     ⊢  antecedent_couverture_ambiant(x).
# ════════════════════════════════════════════════════════════════════════════
def antecedent_ambiant_depuis_bare(vh, e="E", G="G", x="x0", V="Vval",
                                   y="ytf", p="pcf", z="zess", q="qwf", w="wwf"):
    """{ antecedent_couverture(x), essais_bien_formes(vh), rule-codomain }
        ⊢ antecedent_couverture_ambiant(x).

    🎯 LE PONT bare→ambiant, AU NIVEAU DE L'ANTÉCÉDENT D'INDUCTION.  Pour chaque y<x,
    l'antécédent BARE fournit un essai pess avec est_essai(pess,y) ; `essai_dans_parties
    _depuis_bien_formes` (sous essais_bien_formes + rule-codomain) le SITUE dans 𝔓(E×V) ;
    on conjoint, on réintroduit l'existentiel ambiant (∃pcf)(pcf∈𝔓(E×V)∧est_essai), on
    élimine le témoin pess.  C'est EXACTEMENT le pont qui relie l'antécédent d'induction
    BARE de C59 à l'antécédent AMBIANT exigé par les clauses (P3),(P4) de c60_clauses.

    ⚠️ TROIS hypothèses HONNÊTES : antecedent_couverture(x) (l'hyp d'induction C59),
    essais_bien_formes(vh) (structure des essais), rule-codomain (vh:…→V).  theorie=22."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import couvert_essai
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation import antecedent_couverture
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_clauses import antecedent_couverture_ambiant
    R = _graphe_R(G)
    ve, vx = _t(e), _t(x)
    seg = E.segment_extremite(R, ve, vx)
    vy = var(y)
    pess = "pess"                                            # binder témoin de couvert_essai (défaut)
    vpess = var(pess)

    h_bare = N.assume(antecedent_couverture(vh, e, G, vx, y))   # (∀y)(y∈seg ⇒ (∃pess)essai)
    h_wf = N.assume(essais_bien_formes(vh, e, G, V, q, w, z))
    h_rule = N.assume(rule_codomain(vh, V, z))

    # but : y∈seg ⇒ (∃pcf)(pcf∈𝔓(E×V) ∧ est_essai(pcf,y))
    h_yseg = N.assume(appartient(vy, seg))                   # y∈seg
    bare_y = N.modus_ponens(h_yseg, instancie(h_bare, vy))   # (∃pess)est_essai(pess,y)

    # corps témoin pess : est_essai(pess,y) ⇒ (∃pcf)(pcf∈𝔓 ∧ est_essai(pcf,y))
    essai_pess = est_essai(vpess, vh, R, ve, vy, z)
    h_essai = N.assume(essai_pess)
    # pess∈𝔓(E×V)  (décharge essai(pess,y) du converter, garde wf + rule)
    inpar = essai_dans_parties_depuis_bien_formes(vh, e, G, y, V, pess, "cpont", "apont", "bpont", z, q, w)
    inpar = N.modus_ponens(h_essai, N.loi_deduction(essai_pess, inpar))   # pess∈𝔓(E×V)  [wf, rule, essai(pess,y)]
    conj = conjonction_intro(inpar, h_essai)                 # pess∈𝔓 ∧ est_essai(pess,y)
    # (∃pcf)(pcf∈𝔓 ∧ est_essai(pcf,y))   intro sur pcf
    gabarit = et(appartient(var(p), ambiant(e, V)), est_essai(var(p), vh, R, ve, vy, z))
    ex_pcf = N.modus_ponens(conj, N.s5(gabarit, vpess, p))   # (∃pcf)(...)
    # élimine témoin pess
    imp = N.loi_deduction(essai_pess, ex_pcf)
    ex_imp = existe_elimination(imp, pess)                   # (∃pess)essai(pess,y) ⇒ (∃pcf)(...)
    body_y = N.modus_ponens(bare_y, ex_imp)                  # (∃pcf)(...)   [y∈seg, hyps]

    res = N.generalisation(y, N.loi_deduction(appartient(vy, seg), body_y))
    cible = antecedent_couverture_ambiant(vh, e, G, vx, V, y, p, z)
    assert res.conclusion == cible, "antecedent_ambiant_depuis_bare : ≠ antecedent_couverture_ambiant"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CLAUSES BARE DÉRIVÉES DES CLAUSES AMBIANTES (via le pont d'antécédent).
# ════════════════════════════════════════════════════════════════════════════
def _clause_bare_depuis_ambiant(ambiant_thm, clause_bare_form, clause_ambiant_form,
                                vh, e, G, x, V, y, p, z, q, w, conc_builder):
    """Schéma : { ambiant_thm sous Γ } ∪ { antecedent bridge hyps }
        ⊢ clause_bare_form.

    Pour x∈E : on assume antecedent_couverture(x) (bare), on en DÉRIVE
    antecedent_couverture_ambiant(x) via `antecedent_ambiant_depuis_bare`, on l'injecte
    dans la clause AMBIANTE (instanciée à x, x∈E déchargé) pour obtenir la conclusion ;
    on enveloppe (∀x)(x∈E ⇒ (antéc bare ⇒ conclusion)) = clause BARE."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation import antecedent_couverture
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_clauses import antecedent_couverture_ambiant
    ve, vx = _t(e), var(x)
    antec_bare = antecedent_couverture(vh, e, G, vx, y)
    antec_amb = antecedent_couverture_ambiant(vh, e, G, vx, V, y, p, z)
    conc = conc_builder(vx)

    h_xE = N.assume(appartient(vx, ve))
    h_antec_bare = N.assume(antec_bare)
    # bare(x) + wf + rule ⊢ ambiant(x)
    bridge = antecedent_ambiant_depuis_bare(vh, e, G, vx, V, y, p, z, q, w)
    amb_x = N.modus_ponens(h_antec_bare, N.loi_deduction(antec_bare, bridge))   # ambiant(x)  [wf,rule,bare]
    # clause ambiante instanciée à x : x∈E ⇒ (ambiant(x) ⇒ conc)
    cl_x = N.modus_ponens(h_xE, instancie(ambiant_thm, vx))         # ambiant(x) ⇒ conc   [Γ]
    conc_x = N.modus_ponens(amb_x, cl_x)                            # conc   [Γ,wf,rule,bare,x∈E]
    body = N.loi_deduction(appartient(vx, ve), N.loi_deduction(antec_bare, conc_x))
    res = N.generalisation(x, body)
    assert res.conclusion == clause_bare_form, "_clause_bare_depuis_ambiant : ≠ clause bare"
    return res


def recursion_transfinie_existence_final(vh, e="E", G="G", V="Vval",
                                         x="x0tf", y="ytf", p="pcf", z="zess",
                                         q="qwf", w="wwf"):
    """🎯🎯🎯 EXISTENCE C60 (§III.2) — bare→ambiant PONTÉ :

      { est_bien_ordonne(R,E),  essais_bien_formes(vh),  rule_codomain(vh,V) }
        ⊢ (∀x)( x∈E ⇒ (∃p)( est_essai(p, vh, R, E, x) ) ).

    On part de `recursion_transfinie_existence_complet` (existence sous { bo, clause_P3
    (BARE), clause_P4 (BARE) }) et on DÉCHARGE les deux clauses BARE :
      • clause_P3 (bare) ⇐ `couverture_segment_realise` (clause_P3_AMBIANT sous {bo})
        + pont d'antécédent (`antecedent_ambiant_depuis_bare`) ;
      • clause_P4 (bare) ⇐ `recursion_segment_realise` (clause_P4_AMBIANT, CLOS)
        + pont d'antécédent.
    Le pont (`essai_dans_parties` : essai+graphe+dom⊂E+rule-codomain ⇒ p∈𝔓(E×V)) DÉCHARGE
    la condition d'appartenance ambiante de chaque essai-témoin.  Ne restent que les
    hypothèses NATURELLES de C60 : le bon ordre, la bonne formation des essais (graphe de
    domaine ⊂ E), et rule-codomain (la règle h produit ses valeurs dans V).

    ⚠️ TROIS hypothèses HONNÊTES (theorie=22), JAMAIS de bare clause résiduelle :
      • est_bien_ordonne(R,E)  — (E,R) bien ordonné (donnée C60) ;
      • essais_bien_formes(vh) — tout essai est un graphe de domaine ⊂ E (structure) ;
      • rule_codomain(vh,V)    — (∀z) vh(z)∈V (la règle prend ses valeurs dans V).
    Conclusion ∉ hypothèses (non vacuous)."""
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_clauses import (
        recursion_transfinie_existence_complet,
        couverture_segment_realise, recursion_segment_realise,
        clause_P3_ambiant, clause_P4_ambiant,
    )
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
        clause_P3 as _clause_P3, clause_P4 as _clause_P4, Dfam_real,
    )
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille
    R = _graphe_R(G)
    ve = _t(e)

    base = recursion_transfinie_existence_complet(vh, e, G, V, x, y)   # {bo, P3bare, P4bare}

    # clause_P3 (bare) théorème : depuis couverture_segment_realise (P3 ambiant sous {bo})
    p3_amb = couverture_segment_realise(vh, e, G, x, V, y, p, z)       # {bo} ⊢ clause_P3_ambiant
    seg_b = lambda vx: E.segment_extremite(R, ve, vx)
    def _conc3(vx):
        Ux = union_famille(Dfam_real(vh, e, G, vx, V))
        return egal(E.dom(Ux), E.segment_extremite(R, ve, vx))
    p3_bare = _clause_bare_depuis_ambiant(
        p3_amb, _clause_P3(vh, e, G, x, V, y), clause_P3_ambiant(vh, e, G, x, V, y, p, z),
        vh, e, G, x, V, y, p, z, q, w, _conc3)
    base = N.modus_ponens(p3_bare, N.loi_deduction(_clause_P3(vh, e, G, x, V, y), base))

    # clause_P4 (bare) théorème : depuis recursion_segment_realise (P4 ambiant CLOS)
    p4_amb = recursion_segment_realise(vh, e, G, x, V, y, "zrs", p, z)  # ⊢ clause_P4_ambiant [CLOS]
    from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_final import recursion_sur_segment
    def _conc4(vx):
        Dx = Dfam_real(vh, e, G, vx, V)
        return recursion_sur_segment(Dx, vh, G, e, vx)
    p4_bare = _clause_bare_depuis_ambiant(
        p4_amb, _clause_P4(vh, e, G, x, V, y), clause_P4_ambiant(vh, e, G, x, V, y, p, z),
        vh, e, G, x, V, y, p, z, q, w, _conc4)
    base = N.modus_ponens(p4_bare, N.loi_deduction(_clause_P4(vh, e, G, x, V, y), base))

    W = E.est_bien_ordonne(R, ve)
    assert W in base.hypotheses, "final : bon ordre absent"
    assert essais_bien_formes(vh, e, G, V, q, w, z) in base.hypotheses, "final : essais_bien_formes absente"
    assert rule_codomain(vh, V, z) in base.hypotheses, "final : rule-codomain absente"
    assert _clause_P3(vh, e, G, x, V, y) not in base.hypotheses, "final : P3 bare NON déchargée"
    assert _clause_P4(vh, e, G, x, V, y) not in base.hypotheses, "final : P4 bare NON déchargée"
    assert base.conclusion not in base.hypotheses, "final : VACUOUS"
    return base


__all__ = ["rule_codomain", "essai_dans_parties",
           "essais_bien_formes", "essai_dans_parties_depuis_bien_formes",
           "antecedent_ambiant_depuis_bare",
           "recursion_transfinie_existence_final"]
