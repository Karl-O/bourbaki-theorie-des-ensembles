"""§II.5.2 — PONT GÉNÉRAL au niveau APPLICATION : « f(x) au sens Bourbaki ».

Une APPLICATION f = ((G,E),F) ∈ 𝓕(E;F) est le TRIPLE (graphe fonctionnel, source,
but) (E.II.5.2).  La valeur f(x) « au sens de Bourbaki » est G(x), CALCULÉE sur le
GRAPHE G = graphe_de(f) = pr₁(pr₁ f), PAS sur le triple f (valeur(f,x) sur le triple
serait du garbage).  Ce module EMBALLE le pont graphe (`valeur_dans_codomaine` /
`graphe_egal_par_valeurs`) au niveau application, pour TOUTE la suite (Prop 9/10/13…) :

  • valeur_application_dans_but(f,E,F,x) : {f∈𝓕(E;F), x∈E}
        ⊢ valeur(graphe_de(f), x) ∈ F.
    (« l'image d'un point de la source par une application est dans le but ».)

  • application_egale_par_valeurs(f,g,E,F) :
        {f∈𝓕(E;F), g∈𝓕(E;F), (∀x)(x∈E ⇒ valeur(graphe_de(f),x)=valeur(graphe_de(g),x))}
        ⊢ f = g.
    (extensionnalité des applications de E dans F : mêmes valeurs ⇒ égales.)

Ce sont les versions APPLICATION (réutilisables) du pont graphe.  AUCUN axiome
ajouté (theorie_ensembles inchangée) : tout sort des axiomes de DÉFINITION
`axiome_applications` / `axiome_exposant` (membership, E.II.5.2), du pont graphe
`valeur_dans_codomaine`, de l'extensionnalité fonctionnelle `graphe_egal_par_valeurs`,
de `graphe_de_triple`, et de la substitution de Leibniz (S6).  Rien n'est postulé.

Mécanique commune : sous le TÉMOIN G de l'existentielle d'axiome_applications
(f = ((G,E),F), G ∈ F^E), `graphe_de_triple` donne graphe_de(((G,E),F)) = G, donc
(congruence, f = ((G,E),F)) graphe_de(f) = G ; et `axiome_exposant` donne G ⊂ E×F et
dom G = E.  La conclusion (∈ F, resp. f = g) ne mentionne pas G, donc
`existe_elimination` décharge proprement le témoin.

Liants : témoin existentiel « G » (≠ x,y des machineries graphe-terme et de valeur ;
exactement le liant des axiomes axiome_applications / axiome_exposant).  Trou de
congruence « w ».
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, appartient,
                                       existe, pourtout, inclus, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.arithmetique.fondations.ensembles_graphe_de import (
    graphe_de, graphe_de_triple)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_valeur_codomaine import valeur_dans_codomaine
from bourbaki.ensembles.fonctions.ii_3_general.ensembles_extensionnalite import graphe_egal_par_valeurs


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _conjoints_application(vf, vE, vF, vG):
    """{f∈𝓕(E;F)} ⊢ (f = ((G,E),F) et G ∈ F^E)  pour le TÉMOIN G.

    Instancie axiome_applications(E,F) en f : f∈𝓕(E;F) ⇔ (∃G)(f=((G,E),F) et G∈F^E).
    Renvoie le corps existentiel sous le témoin G (assume(body)) — l'appelant
    enchaîne sous ce témoin puis décharge par existe_elimination."""
    triple = E.couple(E.couple(vG, vE), vF)             # ((G, E), F)
    body = et(egal(vf, triple), appartient(vG, E.exposant(vE, vF)))
    return body


def _graphe_de_f_egal_G(vf, vE, vF, vG, h_f_eq_triple):
    """{f = ((G,E),F)} ⊢ graphe_de(f) = G.

    graphe_de_triple : graphe_de(((G,E),F)) = G.  Congruence (trou « w ») transporte
    f = ((G,E),F) en graphe_de(f) = graphe_de(((G,E),F)) ; on compose."""
    triple = E.couple(E.couple(vG, vE), vF)             # ((G, E), F)
    # graphe_de(f) = graphe_de(((G,E),F))   (congruence sur f → triple)
    cong = N.modus_ponens(
        h_f_eq_triple,
        congruence_terme(vf, triple, graphe_de(var("w"))))   # graphe_de(f)=graphe_de(triple)
    triple_graphe = graphe_de_triple(vG, vE, vF)        # graphe_de(((G,E),F)) = G
    return composer_egalites(cong, triple_graphe)       # graphe_de(f) = G


def _exposant_conjoints(vG, vE, vF, h_G_in_exp):
    """{G ∈ F^E} ⊢ (G ⊂ E×F, est_fonctionnel(G), dom G = E).

    Instancie axiome_exposant(E,F) en G : G∈F^E ⇔ ((G⊂E×F et G fonct) et dom G=E)."""
    ax = N.axiome(E.theorie_exposant(vE, vF), E.axiome_exposant(vE, vF))
    car = instancie(ax, vG)            # G∈F^E ⇔ ((G⊂E×F et G fonct) et dom G=E)
    corps = N.modus_ponens(h_G_in_exp, equivalence_avant(car))
    incl = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # G ⊂ E×F
    func = conjonction_elim_droite(conjonction_elim_gauche(corps))   # est_fonctionnel(G)
    domeq = conjonction_elim_droite(corps)                          # dom G = E
    return incl, func, domeq


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  valeur_application_dans_but :  f(x) = G(x) ∈ F
# ═══════════════════════════════════════════════════════════════════════════════
def valeur_application_dans_but(f="f", e="E", but="F", x="x"):
    """{f ∈ 𝓕(E;F), x ∈ E} ⊢ valeur(graphe_de(f), x) ∈ F.

    « f(x) au sens de Bourbaki (= G(x)) est dans le but F. »  Sous le témoin G de
    axiome_applications (f=((G,E),F), G∈F^E) : graphe_de(f)=G (graphe_de_triple +
    congruence) et G⊂E×F, dom G=E (axiome_exposant) ; valeur_dans_codomaine donne
    G(x)∈F, réécrit en valeur(graphe_de(f),x)∈F par Leibniz (graphe_de(f)=G).  La
    conclusion ne mentionne pas G : existe_elimination décharge le témoin."""
    vf, vE, vF, vx = _t(f), _t(e), _t(but), _t(x)
    vG = var("G")
    gr_f = graphe_de(vf)                                # graphe_de(f) = pr₁(pr₁ f)

    # axiome_applications(E,F) en f : f∈𝓕(E;F) ⇔ (∃G)(f=((G,E),F) et G∈F^E)
    ax_app = N.axiome(E.theorie_applications(vE, vF), E.axiome_applications(vE, vF))
    app_car = instancie(ax_app, vf)
    body = _conjoints_application(vf, vE, vF, vG)       # f=((G,E),F) et G∈F^E

    # ── sous le témoin G : conclure valeur(graphe_de(f),x) ∈ F ──────────────────
    hb = N.assume(body)
    h_f_eq_triple = conjonction_elim_gauche(hb)         # f = ((G,E),F)
    h_G_in_exp = conjonction_elim_droite(hb)            # G ∈ F^E

    gr_eq_G = _graphe_de_f_egal_G(vf, vE, vF, vG, h_f_eq_triple)   # graphe_de(f) = G
    incl, func, domeq = _exposant_conjoints(vG, vE, vF, h_G_in_exp)  # G⊂E×F, …, dom G=E

    # valeur_dans_codomaine(G,E,F,x) : {G⊂E×F, dom G=E, x∈E} ⊢ G(x) ∈ F
    vdc = valeur_dans_codomaine(vG, vE, vF, vx)
    # décharger ses 3 hypothèses puis les fournir par les théorèmes Γ-portés
    vdc_imp = N.loi_deduction(
        inclus(vG, E.produit(vE, vF)),
        N.loi_deduction(
            egal(E.dom(vG), vE),
            N.loi_deduction(appartient(vx, vE), vdc)))   # G⊂E×F ⇒ (dom G=E ⇒ (x∈E ⇒ G(x)∈F))
    h_x = N.assume(appartient(vx, vE))                   # x ∈ E
    Gx_in_F = N.modus_ponens(h_x, N.modus_ponens(
        domeq, N.modus_ponens(incl, vdc_imp)))           # valeur(G,x) ∈ F

    # réécrire valeur(G,x) → valeur(graphe_de(f),x)  via graphe_de(f)=G (Leibniz S6)
    G_eq_gr = N.modus_ponens(gr_eq_G, symetrie(gr_f, vG))   # G = graphe_de(f)
    leib = N.s6(vG, gr_f, "w", appartient(E.valeur(var("w"), vx), vF))
    # (G=graphe_de(f)) ⇒ (valeur(G,x)∈F ⇔ valeur(graphe_de(f),x)∈F)
    grx_in_F = N.modus_ponens(Gx_in_F, equivalence_avant(
        N.modus_ponens(G_eq_gr, leib)))                  # valeur(graphe_de(f),x) ∈ F

    # décharger le corps, éliminer le témoin G (conclusion sans G), puis MP
    imp_body = N.loi_deduction(body, grx_in_F)           # body ⇒ valeur(gr f,x)∈F
    elim_G = existe_elimination(imp_body, "G")           # (∃G)body ⇒ valeur(gr f,x)∈F
    ex_G = N.modus_ponens(N.assume(appartient(vf, E.applications(vE, vF))),
                          equivalence_avant(app_car))     # (∃G)body   [sous f∈𝓕(E;F)]
    return N.modus_ponens(ex_G, elim_G)   # {f∈𝓕(E;F), x∈E} ⊢ valeur(graphe_de(f),x)∈F


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  application_egale_par_valeurs :  mêmes valeurs ⇒ f = g
# ═══════════════════════════════════════════════════════════════════════════════
def egalite_valeurs_application(f, g, e, x="x"):
    """(∀x)(x ∈ E ⇒ valeur(graphe_de(f),x) = valeur(graphe_de(g),x)).

    Hypothèse « mêmes valeurs sur E » des applications f, g (au sens Bourbaki)."""
    vf, vg, vE, vx = _t(f), _t(g), _t(e), var(x)
    return pourtout(x, impl(appartient(vx, vE),
                            egal(E.valeur(graphe_de(vf), vx),
                                 E.valeur(graphe_de(vg), vx))))


def _inclus_produit_est_graphe(vG, vE, vF):
    """{ G ⊂ E×F } ⊢ est_un_graphe(G).   (z∈G ⇒ z∈E×F ⇒ z=(p,q) est un couple.)

    Inline (autonome, AUCUNE dépendance au fichier Prop 9 en cours d'édition) :
    z∈G ⊂ E×F ⇒ z∈E×F ⇒ (∃p)(∃q)(z=(p,q) et …) [AXIOME_PRODUIT, binders p,q] ⇒ z=(p,q)
    ⇒ (∃x)(∃y)(z=(x,y)) = est_un_couple(z) (témoins x:=p, y:=q ; binders x,y de
    est_un_couple).  ∃-élim de p,q (la conclusion est_un_couple(z) ne contient pas p,q)."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import _instance_produit
    vz = var("z")
    h_incl = N.assume(inclus(vG, E.produit(vE, vF)))   # G⊂E×F = (∀z)(z∈G⇒z∈E×F)
    z_in_prod_imp = instancie(h_incl, vz)              # z∈G ⇒ z∈E×F
    car = _instance_produit(vE, vF, vz)                # z∈E×F ⇔ (∃p)(∃q)(z=(p,q) et …)
    body = et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vE)),
              appartient(var("q"), vF))
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    inner_xy = egal(vz, E.couple(var("x"), var("y")))            # z=(x,y)
    body_py = subst_f(var("p"), "x", inner_xy)                   # (p|x)(z=(x,y)) = z=(p,y)
    ex_y = N.modus_ponens(z_pq, N.s5(body_py, var("q"), "y"))    # (∃y)(z=(p,y))
    ex_xy = N.modus_ponens(ex_y, N.s5(existe("y", inner_xy), var("p"), "x"))  # (∃x)(∃y)(z=(x,y))
    couple_z = existe_elimination(existe_elimination(
        N.loi_deduction(body, ex_xy), "q"), "p")       # (∃p)(∃q)(…) ⇒ est_un_couple(z)
    z_in = N.assume(appartient(vz, vG))
    in_prod = N.modus_ponens(z_in, z_in_prod_imp)      # z∈E×F
    ex_body = N.modus_ponens(in_prod, equivalence_avant(car))  # (∃p)(∃q)(z=(p,q) et…)
    couple = N.modus_ponens(ex_body, couple_z)         # est_un_couple(z)
    return N.generalisation("z", N.loi_deduction(appartient(vz, vG), couple))  # est_un_graphe(G)


def _conjoints_graphe(vG, vE, vF, h_G_in_exp):
    """{G ∈ F^E} ⊢ (est_fonctionnel(G), est_un_graphe(G), dom G = E).

    Les trois prémisses de graphe_egal_par_valeurs côté G.  est_un_graphe(G) sort de
    G ⊂ E×F : tout élément d'un produit est un couple (_inclus_produit_est_graphe)."""
    incl, func, domeq = _exposant_conjoints(vG, vE, vF, h_G_in_exp)
    # _inclus_produit_est_graphe : {G⊂E×F} ⊢ est_un_graphe(G) ; on décharge l'assume
    # interne puis on fournit incl (théorème Γ-porté G⊂E×F).
    graphe_imp = N.loi_deduction(inclus(vG, E.produit(vE, vF)),
                                 _inclus_produit_est_graphe(vG, vE, vF))   # G⊂E×F ⇒ est_un_graphe(G)
    graphe = N.modus_ponens(incl, graphe_imp)          # est_un_graphe(G)
    return func, graphe, domeq


def application_egale_par_valeurs(f="f", g="g", e="E", but="F"):
    """{f ∈ 𝓕(E;F), g ∈ 𝓕(E;F),
        (∀x)(x∈E ⇒ valeur(graphe_de(f),x)=valeur(graphe_de(g),x))} ⊢ f = g.

    Extensionnalité des applications de E dans F (E.II.5.2).  Sous les témoins Gf, Gg
    (graphe_de(f)=Gf, graphe_de(g)=Gg, tous deux fonctionnels, graphes, de domaine E
    par axiome_exposant) : l'hypothèse des valeurs, réécrite sur Gf,Gg, alimente
    graphe_egal_par_valeurs ⇒ Gf=Gg ; donc f=((Gf,E),F)=((Gg,E),F)=g (congruence).
    La conclusion f=g ne mentionne ni Gf ni Gg : existe_elimination décharge."""
    vf, vg, vE, vF = _t(f), _t(g), _t(e), _t(but)
    vGf, vGg = var("Gf"), var("Gg")
    gr_f, gr_g = graphe_de(vf), graphe_de(vg)
    h_vals = N.assume(egalite_valeurs_application(vf, vg, vE))   # (∀x)(x∈E⇒f(x)=g(x))

    # axiome_applications avec le binder existentiel ADÉQUAT de chaque côté (Gf / Gg)
    # pour que les corps existentiels (∃Gf)…, (∃Gg)… s'accordent avec body_f/body_g.
    ax_app_f = N.axiome(E.theorie_applications(vE, vF, g="Gf"),
                        E.axiome_applications(vE, vF, g="Gf"))
    ax_app_g = N.axiome(E.theorie_applications(vE, vF, g="Gg"),
                        E.axiome_applications(vE, vF, g="Gg"))
    app_car_f = instancie(ax_app_f, vf)   # f∈𝓕 ⇔ (∃Gf)(f=((Gf,E),F) et Gf∈F^E)
    app_car_g = instancie(ax_app_g, vg)   # g∈𝓕 ⇔ (∃Gg)(g=((Gg,E),F) et Gg∈F^E)
    body_f = _conjoints_application(vf, vE, vF, vGf)    # f=((Gf,E),F) et Gf∈F^E
    body_g = _conjoints_application(vg, vE, vF, vGg)    # g=((Gg,E),F) et Gg∈F^E

    # ── sous les deux témoins Gf, Gg : conclure f = g ───────────────────────────
    hbf = N.assume(body_f)
    hbg = N.assume(body_g)
    h_f_eq_triple = conjonction_elim_gauche(hbf)        # f = ((Gf,E),F)
    h_g_eq_triple = conjonction_elim_gauche(hbg)        # g = ((Gg,E),F)
    h_Gf_in_exp = conjonction_elim_droite(hbf)          # Gf ∈ F^E
    h_Gg_in_exp = conjonction_elim_droite(hbg)          # Gg ∈ F^E

    grf_eq_Gf = _graphe_de_f_egal_G(vf, vE, vF, vGf, h_f_eq_triple)   # graphe_de(f)=Gf
    grg_eq_Gg = _graphe_de_f_egal_G(vg, vE, vF, vGg, h_g_eq_triple)   # graphe_de(g)=Gg

    func_f, graphe_f, dom_f = _conjoints_graphe(vGf, vE, vF, h_Gf_in_exp)
    func_g, graphe_g, dom_g = _conjoints_graphe(vGg, vE, vF, h_Gg_in_exp)

    # dom Gf = dom Gg   (dom Gf = E = dom Gg)
    dom_eq = composer_egalites(dom_f, N.modus_ponens(dom_g, symetrie(E.dom(vGg), vE)))

    # (∀x)(x∈dom Gf ⇒ Gf(x)=Gg(x))   à partir de h_vals réécrit Gf→graphe_de(f), Gg→…
    val_eq = _valeurs_sur_graphes(vf, vg, vGf, vGg, vE, grf_eq_Gf, grg_eq_Gg,
                                  dom_f, h_vals)

    # graphe_egal_par_valeurs : (Gf fonct et Gg fonct et Gf graphe et Gg graphe
    #   et dom Gf=dom Gg et (∀x)(x∈dom Gf⇒Gf(x)=Gg(x))) ⇒ Gf=Gg
    gev = graphe_egal_par_valeurs(vGf, vGg)
    hyp_conj = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(func_f, func_g), graphe_f), graphe_g), dom_eq), val_eq)
    Gf_eq_Gg = N.modus_ponens(hyp_conj, gev)            # Gf = Gg

    # f = ((Gf,E),F) = ((Gg,E),F) = g   (congruence sur le coin Gf→Gg, trou « w »)
    triple_f = E.couple(E.couple(vGf, vE), vF)
    triple_eq = N.modus_ponens(Gf_eq_Gg,
        congruence_terme(vGf, vGg, E.couple(E.couple(var("w"), vE), vF)))  # ((Gf,E),F)=((Gg,E),F)
    g_eq_triple_g = N.modus_ponens(h_g_eq_triple,
        symetrie(vg, E.couple(E.couple(vGg, vE), vF)))   # ((Gg,E),F) = g
    f_eq_tripleGg = composer_egalites(h_f_eq_triple, triple_eq)   # f = ((Gg,E),F)
    f_eq_g = composer_egalites(f_eq_tripleGg, g_eq_triple_g)      # f = g

    # éliminer les deux témoins (conclusion f=g sans Gf,Gg), puis MP×2
    imp_g = N.loi_deduction(body_g, f_eq_g)              # body_g ⇒ f=g   [sous f∈𝓕, body_f, h_vals]
    elim_g = existe_elimination(imp_g, "Gg")            # (∃Gg)body_g ⇒ f=g
    ex_Gg = N.modus_ponens(N.assume(appartient(vg, E.applications(vE, vF))),
                           equivalence_avant(app_car_g))  # (∃Gg)body_g   [sous g∈𝓕]
    f_eq_g_no_Gg = N.modus_ponens(ex_Gg, elim_g)        # f=g   [sous f∈𝓕, body_f, g∈𝓕, h_vals]
    imp_f = N.loi_deduction(body_f, f_eq_g_no_Gg)       # body_f ⇒ f=g
    elim_f = existe_elimination(imp_f, "Gf")           # (∃Gf)body_f ⇒ f=g
    ex_Gf = N.modus_ponens(N.assume(appartient(vf, E.applications(vE, vF))),
                           equivalence_avant(app_car_f))  # (∃Gf)body_f   [sous f∈𝓕]
    return N.modus_ponens(ex_Gf, elim_f)
    # {f∈𝓕(E;F), g∈𝓕(E;F), (∀x)(x∈E⇒f(x)=g(x))} ⊢ f = g


def _valeurs_sur_graphes(vf, vg, vGf, vGg, vE, grf_eq_Gf, grg_eq_Gg, dom_f, h_vals):
    """{(∀x)(x∈E⇒f(x)=g(x)), graphe_de(f)=Gf, graphe_de(g)=Gg, dom Gf=E}
       ⊢ (∀x)(x∈dom Gf ⇒ Gf(x)=Gg(x)).

    Sous x∈dom Gf : dom Gf=E donne x∈E (Leibniz), d'où valeur(graphe_de f,x)=
    valeur(graphe_de g,x) (h_vals) ; réécrit graphe_de(f)→Gf et graphe_de(g)→Gg
    (Leibniz S6) en Gf(x)=Gg(x)."""
    vx = var("x")
    gr_f, gr_g = graphe_de(vf), graphe_de(vg)
    h_xdom = N.assume(appartient(vx, E.dom(vGf)))       # x ∈ dom Gf
    # x∈dom Gf et dom Gf=E ⇒ x∈E  (Leibniz S6 sur 2ᵉ arg de ∈)
    leib_dom = N.s6(E.dom(vGf), vE, "w", appartient(vx, var("w")))
    x_in_E = N.modus_ponens(h_xdom, equivalence_avant(N.modus_ponens(dom_f, leib_dom)))
    # f(x)=g(x)  i.e. valeur(graphe_de f,x)=valeur(graphe_de g,x)
    fx_eq_gx = N.modus_ponens(x_in_E, instancie(h_vals, vx))
    # réécrire graphe_de(f)→Gf (1ᵉʳ membre) puis graphe_de(g)→Gg (2ᵉ membre)
    leib_f = N.s6(gr_f, vGf, "w",
                  egal(E.valeur(var("w"), vx), E.valeur(gr_g, vx)))
    step1 = N.modus_ponens(fx_eq_gx, equivalence_avant(
        N.modus_ponens(grf_eq_Gf, leib_f)))             # Gf(x)=valeur(graphe_de g,x)
    leib_g = N.s6(gr_g, vGg, "w",
                  egal(E.valeur(vGf, vx), E.valeur(var("w"), vx)))
    gfx_eq_ggx = N.modus_ponens(step1, equivalence_avant(
        N.modus_ponens(grg_eq_Gg, leib_g)))             # Gf(x)=Gg(x)
    imp = N.loi_deduction(appartient(vx, E.dom(vGf)), gfx_eq_ggx)
    return N.generalisation("x", imp)                   # (∀x)(x∈dom Gf ⇒ Gf(x)=Gg(x))


__all__ = ["valeur_application_dans_but", "application_egale_par_valeurs",
           "egalite_valeurs_application"]
