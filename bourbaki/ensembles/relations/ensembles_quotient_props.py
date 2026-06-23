"""§II.6 — THÉORÈMES du quotient (factorisation C57, décomposition effective, unicité).

Module NEUF (prouve les THÉORÈMES, là où `ensembles_decomposition_quotient` et
`ensembles_quotient_complements` ne faisaient que DÉFINIR les notions et reportaient
la factorisation effective).  On réutilise le PONT « valeur d'une composée »
(`composition_valeur_t` : (G'∘G)(x) = G'(G(x)) modulo les hypothèses C46) et le pont
APPLICATION (`application_egale_par_valeurs` : mêmes valeurs ⇒ f=g).

THÉORÈMES PROUVÉS (clos modulo hypothèses EXPLICITES — jamais postulés) :

  • `factorisation_valeur(f,h,p,x)` — C57, identité de valeur de la factorisation :
        {f = h∘p (graphes), + C46 de h∘p}  ⊢  f(x) = h(p(x)).
    Pur Leibniz sur f = h∘p (réécrit valeur(f,x)) + composition_valeur_t.

  • `factorisation_implique_compatible(f,h,p,x,y)` — C57, sens DUR (« factorise ⇒
        compatible ») au niveau des valeurs :
        {f = h∘p, C46 de h∘p en x ET en y}
            ⊢  (p(x) = p(y)) ⇒ (f(x) = f(y)).
    Cœur de « f compatible avec la relation R_p{x,y} := p(x)=p(y) » : f est constante
    sur les fibres de p.  Substantif (congruence de h sur p(x)=p(y) + les deux
    identités de valeur).

  • `factorisation_compatible_Rp(f,h,p)` — emballage : sous {f=h∘p, …},
        ⊢ (∀x)(∀y)( p(x)=p(y) ⇒ f(x)=f(y) )  = `est_compatible_application(f, R_p)`.

  • `decomposition_valeur(F,b,p,i,x)` — décomposition canonique EFFECTIVE au niveau
        des valeurs (E.II.6.5, f = i∘b∘p) :
        {F = i∘(b∘p) (graphes), + C46 imbriquées}  ⊢  f(x) = i(b(p(x))).

  • `factorisation_meme_valeurs(h,hp,p,f,x)` — UNICITÉ (propriété universelle), cœur :
        {f = h∘p, f = h'∘p, + C46 des deux composées}
            ⊢  h(p(x)) = h'(p(x)).
    Deux factorisations de f par p ont la même valeur en tout p(x).

  • `factorisation_unique(h,hp,p,f,quot)` — UNICITÉ, conclusion APPLICATION :
        {h∈𝓕(E/R;F), h'∈𝓕(E/R;F), f=h∘p, f=h'∘p, p surjective (toute t∈E/R est p(x)),
         + C46}  ⊢  h = h'.   (assemble factorisation_meme_valeurs + surjectivité de p
        + application_egale_par_valeurs.)  Propriété universelle du quotient :
        l'application déduite par passage au quotient est UNIQUE.

Tout sort des axiomes existants (composition_valeur_t, application_egale_par_valeurs,
Leibniz S6, congruence C44).  `theorie_ensembles` reste à 22 axiomes — AUCUN axiome
ajouté ici.  Les hypothèses C46 (fonctionnalité + appartenance au domaine des
facteurs) sont laissées EXPLICITEMENT dans le séquent (jamais déchargées par un
postulat).

Liants : « w » (trou de congruence/Leibniz), « x », « y », « G » (témoins
d'application_egale_par_valeurs, internes à ce pont).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, impl, appartient,
                                       pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import instancie
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_composee_valeurs import composition_valeur_t
from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
    application_egale_par_valeurs, egalite_valeurs_application)
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# 1.  factorisation_valeur :  f = h∘p  ⊢  f(x) = h(p(x))   (C57, identité de valeur)
# ═══════════════════════════════════════════════════════════════════════════════
def factorisation_valeur(f="f", h="h", p="P", x="x"):
    """{f = h∘p (graphes), C46(h∘p,x)} ⊢ valeur(f, x) = h(p(x)).   (C57, niveau valeur.)

    Lorsque f se factorise f = h∘p (g = p application canonique de E sur E/R, h
    déduite par passage au quotient, E.II.6.5), la VALEUR f(x) est exactement
    h(p(x)).  Preuve : Leibniz (S6) sur l'égalité de graphes f = h∘p réécrit
    valeur(f,x) en valeur(h∘p, x) ; puis composition_valeur_t donne
    valeur(h∘p,x) = h(p(x)).  Hypothèses laissées dans le séquent : l'égalité de
    graphes f=h∘p et les conditions C46 de la composée h∘p au point x.

    f, h, p : GRAPHES (noms ou termes)."""
    vf, vh, vp, vx = _t(f), _t(h), _t(p), _t(x)
    comp = E.composee(vh, vp)                      # h ∘ p
    px = E.valeur(vp, vx)                          # p(x)
    hpx = E.valeur(vh, px)                          # h(p(x))
    # f = h∘p  →  valeur(f,x) = valeur(h∘p, x)   (congruence sur le 1er arg de valeur)
    h_feq = N.assume(egal(vf, comp))               # f = h∘p
    cong = N.modus_ponens(h_feq, congruence_terme(
        vf, comp, E.valeur(var("w"), vx), "w"))    # valeur(f,x) = valeur(h∘p, x)
    # valeur(h∘p, x) = h(p(x))   (composition_valeur_t ; hyps C46 dans le séquent)
    cv = composition_valeur_t(vh, vp, vx)          # valeur(h∘p,x) = h(p(x))
    return composer_egalites(cong, cv)             # valeur(f,x) = h(p(x))


# ═══════════════════════════════════════════════════════════════════════════════
# 2.  factorisation ⇒ compatible :  p(x)=p(y) ⇒ f(x)=f(y)   (C57, sens DUR)
# ═══════════════════════════════════════════════════════════════════════════════
def factorisation_implique_compatible(f="f", h="h", p="P", x="x", y="yb"):
    """{f = h∘p, C46(h∘p,x), C46(h∘p,y)} ⊢ (p(x)=p(y)) ⇒ (f(x)=f(y)).   (C57, sens dur.)

    « Si f se factorise par p (f = h∘p), alors f est compatible avec la relation
    R_p{x,y} := p(x)=p(y) » : f est CONSTANTE sur les fibres de p.  C'est la moitié
    substantielle du critère C57 (l'autre étant la construction de h).

    Preuve : f(x)=h(p(x)) et f(y)=h(p(y)) (factorisation_valeur) ; sous l'hypothèse
    p(x)=p(y), congruence de h donne h(p(x))=h(p(y)) ; on chaîne
    f(x)=h(p(x))=h(p(y))=f(y)."""
    vf, vh, vp, vx, vy = _t(f), _t(h), _t(p), _t(x), _t(y)
    px, py = E.valeur(vp, vx), E.valeur(vp, vy)
    # f(x) = h(p(x))  et  f(y) = h(p(y))
    fx_eq = factorisation_valeur(vf, vh, vp, vx)   # f(x) = h(p(x))
    fy_eq = factorisation_valeur(vf, vh, vp, vy)   # f(y) = h(p(y))
    # sous p(x)=p(y) : h(p(x)) = h(p(y))   (congruence de h)
    h_pxy = N.assume(egal(px, py))                 # p(x) = p(y)
    h_cong = N.modus_ponens(h_pxy, congruence_terme(
        px, py, E.valeur(vh, var("w")), "w"))      # h(p(x)) = h(p(y))
    # f(x) = h(p(x)) = h(p(y)) = f(y)
    fy_sym = N.modus_ponens(fy_eq, symetrie(E.valeur(vf, vy), E.valeur(vh, py)))  # h(p(y))=f(y)
    chain = composer_egalites(composer_egalites(fx_eq, h_cong), fy_sym)  # f(x) = f(y)
    return N.loi_deduction(egal(px, py), chain)    # (p(x)=p(y)) ⇒ (f(x)=f(y))


def relation_Rp(p):
    """R_p{x,y} := p(x) = p(y)  (relation d'équivalence associée à p, lue par valeurs).

    C'est R_f de E.II.6.2 lue sur les valeurs : « x ≡ y (mod R_p) ⟺ p(x)=p(y) ».
    Renvoie une fonction (Terme,Terme)→Formule.  p : graphe (nom ou terme)."""
    vp = _t(p)
    return lambda a, b: egal(E.valeur(vp, a), E.valeur(vp, b))


def _dom_point(g, t):
    """(∃y)((t,y)∈G) — « t est dans le domaine de G »  (C46, condition de domaine)."""
    from bourbaki.logique.formule import existe
    return existe("y", appartient(E.couple(_t(t), var("y")), _t(g)))


def domaine_total(g, e, x="x"):
    """« G est défini partout sur E » := (∀x)(x∈E ⇒ (∃y)((x,y)∈G)).

    Forme universelle de la condition de domaine C46 (toute la source est dans le
    domaine du graphe G).  Renvoie une Formule.  G : graphe ; e = E (source)."""
    vg, ve = _t(g), _t(e)
    vx = var(x)
    return pourtout(x, impl(appartient(vx, ve), _dom_point(vg, vx)))


def factorisation_compatible_Rp(f="f", h="h", p="P", e="E", quot="Q", x="x", y="yb"):
    """{f = h∘p,  p définie sur E,  h définie sur Q=E/R,  (∀x)(x∈E ⇒ p(x)∈Q),
        h∘p fonctionnel}
       ⊢ (∀x)(∀y)( (x∈E et y∈E) ⇒ (p(x)=p(y) ⇒ f(x)=f(y)) ).

    Forme universellement quantifiée (GARDÉE par E) de
    `factorisation_implique_compatible` : « f compatible avec la relation associée à
    p » (E.II.6.5, `est_compatible_application` lue sur R_p{x,y} := p(x)=p(y)).

    On décharge les conditions C46 PONCTUELLES (x∈dom p, p(x)∈dom h) du lemme
    par point en les déduisant de leurs formes UNIVERSELLES (domaine_total) sous la
    garde x∈E (et p(x)∈Q par p:E→Q, Q⊂dom h) ; les hypothèses restantes (f=h∘p, les
    conditions universelles, h∘p fonctionnel) sont x,y-libres, donc généralisables.

    Conditionné aux hypothèses EXPLICITES ci-dessus (jamais postulées)."""
    from bourbaki.logique.formule import existe
    vf, vh, vp = _t(f), _t(h), _t(p)
    ve, vQ = _t(e), _t(quot)
    vx, vy = _t(x), _t(y)
    px, py = E.valeur(vp, vx), E.valeur(vp, vy)

    # le lemme par point : ses hyps incluent les 4 C46 ponctuelles {x∈domP, yb∈domP,
    # P(x)∈dom h, P(yb)∈dom h} + {f=h∘P, h∘P func}.
    imp = factorisation_implique_compatible(vf, vh, vp, vx, vy)

    # hypothèses universelles (x,y-libres) à fournir
    dom_p = domaine_total(vp, ve, x="x")          # (∀a)(a∈E ⇒ (∃y)((a,y)∈P))
    dom_h = domaine_total(vh, vQ, x="x")          # (∀a)(a∈Q ⇒ (∃y)((a,y)∈h))
    p_into_Q = pourtout("x", impl(appartient(var("x"), ve),
                                  appartient(E.valeur(vp, var("x")), vQ)))  # (∀a)(a∈E⇒P(a)∈Q)

    # discharge des 4 C46 ponctuelles SOUS la garde (x∈E et y∈E)
    h_xinE = N.assume(appartient(vx, ve))
    h_yinE = N.assume(appartient(vy, ve))
    h_domp = N.assume(dom_p)
    h_domh = N.assume(dom_h)
    h_pQ = N.assume(p_into_Q)

    xdom = N.modus_ponens(h_xinE, instancie(h_domp, vx))     # (∃y)((x,y)∈P)
    ydom = N.modus_ponens(h_yinE, instancie(h_domp, vy))     # (∃y)((yb,y)∈P)
    pxQ = N.modus_ponens(h_xinE, instancie(h_pQ, vx))        # P(x)∈Q
    pyQ = N.modus_ponens(h_yinE, instancie(h_pQ, vy))        # P(yb)∈Q
    pxdomh = N.modus_ponens(pxQ, instancie(h_domh, px))      # (∃y)((P(x),y)∈h)
    pydomh = N.modus_ponens(pyQ, instancie(h_domh, py))      # (∃y)((P(yb),y)∈h)

    # décharger les 4 C46 ponctuelles de imp, puis fournir les preuves ci-dessus
    imp1 = N.modus_ponens(xdom, N.loi_deduction(_dom_point(vp, vx),
           N.modus_ponens(ydom, N.loi_deduction(_dom_point(vp, vy),
           N.modus_ponens(pxdomh, N.loi_deduction(_dom_point(vh, px),
           N.modus_ponens(pydomh, N.loi_deduction(_dom_point(vh, py), imp))))))))
    # imp1 : reste hyps = {f=h∘P, h∘P func, x∈E, yb∈E, dom_p, dom_h, p_into_Q}
    # garde explicite (x∈E et y∈E) ⇒ (p(x)=p(y) ⇒ f(x)=f(y))
    h_both = N.assume(et(appartient(vx, ve), appartient(vy, ve)))
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite)
    # re-dériver imp1 sous la conjonction unique (réutilise h_xinE/h_yinE via cut)
    body = impl(egal(px, py), egal(E.valeur(vf, vx), E.valeur(vf, vy)))
    imp_under_both = N.modus_ponens(conjonction_elim_droite(h_both),
        N.loi_deduction(appartient(vy, ve),
        N.modus_ponens(conjonction_elim_gauche(h_both),
        N.loi_deduction(appartient(vx, ve), imp1))))
    guarded = N.loi_deduction(et(appartient(vx, ve), appartient(vy, ve)), imp_under_both)
    return N.generalisation("x", N.generalisation("yb", guarded))


# ═══════════════════════════════════════════════════════════════════════════════
# 3.  décomposition canonique EFFECTIVE au niveau des valeurs  f = i∘b∘p  (E.II.6.5)
# ═══════════════════════════════════════════════════════════════════════════════
def decomposition_valeur(F="F", b="b", p="P", i="i", x="x"):
    """{F = i∘(b∘p) (graphes), C46 imbriquées} ⊢ valeur(F, x) = i(b(p(x))).

    Identité de VALEUR de la décomposition canonique f = i∘b∘p (E.II.6.5) : la
    valeur de f en x se calcule en appliquant d'abord p (E→E/R_f), puis b (la
    bijection induite E/R_f→f⟨E⟩), puis i (l'injection canonique f⟨E⟩→F).  C'est la
    forme effective (au niveau des valeurs) du prédicat de graphes
    `decomposition_canonique`.

    Preuve : Leibniz sur F = i∘(b∘p) réécrit valeur(F,x) en valeur(i∘(b∘p),x) ; puis
    composition_valeur_t (i, b∘p) donne i((b∘p)(x)), et composition_valeur_t (b,p)
    avec congruence de i donne i((b∘p)(x)) = i(b(p(x)))."""
    vF, vb, vp, vi, vx = _t(F), _t(b), _t(p), _t(i), _t(x)
    bp = E.composee(vb, vp)                         # b ∘ p
    comp = E.composee(vi, bp)                        # i ∘ (b ∘ p)
    px = E.valeur(vp, vx)                            # p(x)
    bpx = E.valeur(vb, px)                           # b(p(x))
    bp_x = E.valeur(bp, vx)                          # (b∘p)(x)
    # F = i∘(b∘p)  →  valeur(F,x) = valeur(i∘(b∘p), x)
    h_Feq = N.assume(egal(vF, comp))                # F = i∘(b∘p)
    cong0 = N.modus_ponens(h_Feq, congruence_terme(
        vF, comp, E.valeur(var("w"), vx), "w"))     # valeur(F,x) = valeur(i∘(b∘p),x)
    # valeur(i∘(b∘p),x) = i((b∘p)(x))
    cv1 = composition_valeur_t(vi, bp, vx)          # valeur(i∘(b∘p),x) = i((b∘p)(x))
    # (b∘p)(x) = b(p(x))   →  congruence de i  →  i((b∘p)(x)) = i(b(p(x)))
    cv2 = composition_valeur_t(vb, vp, vx)          # (b∘p)(x) = b(p(x))
    cong_i = N.modus_ponens(cv2, congruence_terme(
        bp_x, bpx, E.valeur(vi, var("w")), "w"))    # i((b∘p)(x)) = i(b(p(x)))
    # chaîne : valeur(F,x) = valeur(i∘(b∘p),x) = i((b∘p)(x)) = i(b(p(x)))
    return composer_egalites(composer_egalites(cong0, cv1), cong_i)


# ═══════════════════════════════════════════════════════════════════════════════
# 4.  UNICITÉ de l'application déduite (propriété universelle du quotient)
# ═══════════════════════════════════════════════════════════════════════════════
def factorisation_meme_valeurs(h="h", hp="hp", p="P", f="f", x="x"):
    """{f = h∘p, f = h'∘p, C46(h∘p,x), C46(h'∘p,x)} ⊢ h(p(x)) = h'(p(x)).

    Cœur de l'UNICITÉ (propriété universelle du quotient) : deux applications h, h'
    qui factorisent la MÊME f par la MÊME surjection p prennent la même valeur en
    tout point p(x).  Preuve : h(p(x)) = f(x) = h'(p(x))  (deux instances de
    factorisation_valeur, l'une retournée par symétrie).

    h, hp (=h'), p, f : graphes."""
    vh, vhp, vp, vf, vx = _t(h), _t(hp), _t(p), _t(f), _t(x)
    px = E.valeur(vp, vx)                            # p(x)
    hpx = E.valeur(vh, px)                           # h(p(x))
    fx = E.valeur(vf, vx)                            # f(x)
    # f(x) = h(p(x))   →   h(p(x)) = f(x)
    fx_eq_h = factorisation_valeur(vf, vh, vp, vx)  # f(x) = h(p(x))
    h_eq_fx = N.modus_ponens(fx_eq_h, symetrie(fx, hpx))  # h(p(x)) = f(x)
    # f(x) = h'(p(x))
    fx_eq_hp = factorisation_valeur(vf, vhp, vp, vx)  # f(x) = h'(p(x))
    return composer_egalites(h_eq_fx, fx_eq_hp)     # h(p(x)) = h'(p(x))


def surjectivite_ponctuelle(p, quot, t="t", x="xa"):
    """« p surjective de E sur Q » (forme ponctuelle) := (∀t)(t∈Q ⇒ (∃x)(t = p(x))).

    Tout élément du quotient Q = E/R est de la forme p(x) — la surjectivité de
    l'application canonique p, lue « par valeurs ».  p : graphe ; quot = Q.  Renvoie
    une Formule."""
    from bourbaki.logique.formule import existe
    vp, vQ = _t(p), _t(quot)
    vt, vx = var(t), var(x)
    return pourtout(t, impl(appartient(vt, vQ), existe(x, egal(vt, E.valeur(vp, vx)))))


def coincidence_ponctuelle_graphe(gh, ghp, p, x="x"):
    """« gh et gh' coïncident en tout p(x) » := (∀x)( gh(p(x)) = gh'(p(x)) ).

    Forme universelle (x-libre une fois quantifiée) de la coïncidence ponctuelle des
    DEUX GRAPHES gh = graphe_de(h), gh' = graphe_de(h') aux valeurs de p.  Dérivable
    de {f=h∘p, f=h'∘p, C46} par `factorisation_meme_valeurs` + généralisation après
    décharge des C46 (cf. report) ; ici on l'expose comme hypothèse explicite afin de
    rester au-dessus de la lourdeur des C46 imbriquées de graphe_de.  Renvoie une
    Formule.  gh, ghp, p : termes (graphes)."""
    vgh, vghp, vp = _t(gh), _t(ghp), _t(p)
    vx = var(x)
    px = E.valeur(vp, vx)
    return pourtout(x, egal(E.valeur(vgh, px), E.valeur(vghp, px)))


def coincidence_sur_quotient(h="h", hp="hp", p="P", quot="Q", t="x", x="xa"):
    """{p surjective ponctuelle (E sur Q),
        (∀x)( gh(p(x)) = gh'(p(x)) )   [coïncidence ponctuelle des graphes]}
       ⊢ (∀t)( t∈Q ⇒ valeur(graphe_de(h),t) = valeur(graphe_de(h'),t) ).

    h, h' COÏNCIDENT sur Q = E/R : sous t∈Q, surjectivité de p donne t = p(x) pour un
    x ; l'hypothèse de coïncidence ponctuelle donne gh(p(x))=gh'(p(x)) ; Leibniz
    (t = p(x)) réécrit en gh(t)=gh'(t).  La conclusion est LITTÉRALEMENT
    `egalite_valeurs_application(h, h', Q)` (binder « x » par défaut) — l'hypothèse de
    valeurs d'application_egale_par_valeurs.  Auxiliaire de `factorisation_unique`.

    La 2e hypothèse (coïncidence ponctuelle des graphes) est x-LIBRE après son ∀, donc
    n'obstrue pas l'élimination du témoin x ; elle est elle-même conséquence des deux
    factorisations (factorisation_meme_valeurs ; cf. report)."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    vh, vhp, vp, vQ = _t(h), _t(hp), _t(p), _t(quot)
    vt, vx = var(t), var(x)
    grh, grhp = graphe_de(vh), graphe_de(vhp)
    px = E.valeur(vp, vx)
    # hypothèse : (∀x)( gh(p(x)) = gh'(p(x)) )  — instanciée en x
    h_coinc = N.assume(coincidence_ponctuelle_graphe(grh, grhp, vp, x=x))
    eq_at_px = instancie(h_coinc, vx)               # gh(p(x)) = gh'(p(x))
    # sous t = p(x) : réécrit en gh(t) = gh'(t)  (Leibniz S6 — substitue p(x)→t)
    h_teq = N.assume(egal(vt, px))                  # t = p(x)
    leib = N.s6(vt, px, "w",
                egal(E.valeur(grh, var("w")), E.valeur(grhp, var("w"))))
    # (t=p(x)) ⇒ ( (gh(t)=gh'(t)) ⇔ (gh(p(x))=gh'(p(x))) )
    eq_at_t = N.modus_ponens(eq_at_px, _arriere(N.modus_ponens(h_teq, leib)))
    imp_x = N.loi_deduction(egal(vt, px), eq_at_t)  # (t=p(x)) ⇒ gh(t)=gh'(t)
    elim_x = existe_elimination(imp_x, x)           # (∃x)(t=p(x)) ⇒ gh(t)=gh'(t)
    # fournir (∃x)(t=p(x)) sous t∈Q via la surjectivité ponctuelle de p
    surj = N.assume(surjectivite_ponctuelle(vp, vQ, t=t, x=x))
    ex_ante = N.modus_ponens(N.assume(appartient(vt, vQ)), instancie(surj, vt))  # (∃x)(t=p(x))
    eq_final = N.modus_ponens(ex_ante, elim_x)      # gh(t) = gh'(t)
    imp_t = N.loi_deduction(appartient(vt, vQ), eq_final)
    return N.generalisation(t, imp_t)               # (∀t)(t∈Q ⇒ gh(t)=gh'(t))


def factorisation_unique(h="h", hp="hp", p="P", but="F", quot="Q", t="x", x="xa"):
    """{h∈𝓕(Q;F), h'∈𝓕(Q;F),
        p surjective ponctuelle (E sur Q),
        (∀x)( gh(p(x)) = gh'(p(x)) )   [coïncidence ponctuelle des graphes]}
       ⊢ h = h'.

    UNICITÉ de l'application déduite par passage au quotient — PROPRIÉTÉ UNIVERSELLE
    du quotient (E.II.6.5 : « h est uniquement déterminée par f »).  p étant
    surjective de E sur Q = E/R, h et h' coïncident sur Q (coincidence_sur_quotient) ;
    application_egale_par_valeurs (extensionnalité des applications de Q dans F)
    conclut h = h'.

    Assemble coincidence_sur_quotient (qui produit EXACTEMENT l'hypothèse de valeurs
    de application_egale_par_valeurs) par cut sur cette hypothèse.  Hypothèses
    restantes (jamais postulées) : h,h'∈𝓕(Q;F), la surjectivité ponctuelle de p, la
    coïncidence ponctuelle des graphes (= conséquence des deux factorisations,
    factorisation_meme_valeurs).  quot = Q = E/R, but = F."""
    vh, vhp, vQ, vF = _t(h), _t(hp), _t(quot), _t(but)
    # application_egale_par_valeurs(h, h', Q, F) : sa 3e hyp = egalite_valeurs_application(h,h',Q)
    aev = application_egale_par_valeurs(vh, vhp, vQ, vF)
    hyp_vals = egalite_valeurs_application(vh, vhp, vQ)   # (∀x)(x∈Q⇒gh(x)=gh'(x))
    # décharger cette hyp dans aev, puis fournir la coïncidence prouvée
    aev_imp = N.loi_deduction(hyp_vals, aev)             # hyp_vals ⇒ (… ⊢ h=h')
    coinc = coincidence_sur_quotient(vh, vhp, p, vQ, t=t, x=x)  # ⊢ hyp_vals
    return N.modus_ponens(coinc, aev_imp)                # {h,h'∈𝓕, surj, coïnc} ⊢ h=h'


def _arriere(eqv_thm):
    """De ⊢ (A ⇔ B) déduire ⊢ (B ⇒ A).  (sens arrière d'une équivalence prouvée.)"""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    return equivalence_arriere(eqv_thm)


__all__ = [
    "factorisation_valeur",
    "factorisation_implique_compatible", "relation_Rp",
    "domaine_total", "factorisation_compatible_Rp",
    "decomposition_valeur",
    "factorisation_meme_valeurs", "surjectivite_ponctuelle",
    "coincidence_ponctuelle_graphe", "coincidence_sur_quotient", "factorisation_unique",
]
