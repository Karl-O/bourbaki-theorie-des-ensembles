"""§II.3.8 Théorème 1 / identités de composition au niveau des VALEURS.

S'appuie sur le verrou « valeur d'une composée » composition_valeur :
    ⊢ (g∘f)(x) = g(f(x))   sous {F,G fonctionnels, x∈dom F, f(x)∈dom G}.

On en déduit ici les identités de composition au niveau des valeurs qui étaient
reportées au round 1 :

  • `composition_valeur_t` : version « TERMES » de composition_valeur — accepte des
        termes composés (p.ex. H∘G) comme facteurs. Conclusion ⊢ (tG∘tF)(x)=tG(tF(x))
        avec, en hypothèses, « tG∘tF fonctionnel » et l'existence des correspondants
        (les conditions C46) — sans recourir à la Proposition 6 (qui n'est énoncée
        que pour des graphes-fonctions « lettres »).

  • `associativite_valeur` : ⊢ ((h∘g)∘f)(x) = (h∘(g∘f))(x)
        (les deux membres valent h(g(f(x)))) — contenu « valeurs » de
        l'associativité de la composition (préalable au Théorème 1 a/b).

Les compositions r∘r' / s∘s' du Théorème 1 a-f, et Prop. 9, restent reportées
(cf. rapport) : elles exigent en plus le pont surjectivité↔image.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, existe, appartient, impl
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, equivalence_arriere,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites, congruence_terme, symetrie
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_dans_graphe, valeur_caracterisation
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composee_intro
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus, et as _et
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import est_application
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import membre_image
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee import image_composee
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_correspondances import image_croissante


def _cut(thm, preuve_hyp):
    """Décharge de `thm` l'hypothèse H = preuve_hyp.conclusion (règle de coupure)."""
    H = preuve_hyp.conclusion
    return N.modus_ponens(preuve_hyp, N.loi_deduction(H, thm))


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _symetrie_thm(thm_eq):
    """De Γ⊢(T=U) déduire Γ⊢(U=T)."""
    t, u = thm_eq.conclusion.termes
    return N.modus_ponens(thm_eq, symetrie(t, u))


# @livre Ch.II §3.8 Lem.- | E II.19 L.27-37 | PDF p.70
# @livre Ch.II §3.8 Demo.- | E II.19 L.26-26 | PDF p.70  (démonstration de composition_valeur_t)
def composition_valeur_t(tG, tF, tx):
    """⊢ (tG∘tF)(x) = tG(tF(x))   (version TERMES de composition_valeur).

    tG, tF, tx : termes (ou noms). Hypothèses laissées dans le séquent :
      tF fonctionnel-au-point (∃y)(x,y)∈tF, (∃y)(f(x),y)∈tG, et tG∘tF fonctionnel.
    On n'invoque PAS la Proposition 6 (réservée aux fonctions-lettres) : la
    fonctionnalité de la composée reste une hypothèse explicite."""
    vG, vF, vx, vy = _t(tG), _t(tF), _t(tx), var("y")
    comp = E.composee(vG, vF)
    fx = E.valeur(vF, vx)
    gfx = E.valeur(vG, fx)                              # g(f(x))
    gof = E.valeur(comp, vx)                            # (g∘f)(x)
    in_comp = composee_intro(vG, vF, vx, gfx, fx,       # (x, g(f(x))) ∈ G∘F  [hyps domaines]
                             valeur_dans_graphe(vF, vx), valeur_dans_graphe(vG, fx))
    vc = valeur_caracterisation(comp, vx)              # ((x,y)∈comp ⇔ y=(g∘f)(x)) [hyps comp func/dom]
    vc_gfx = instancie(N.generalisation("y", vc), gfx)
    eq = N.modus_ponens(in_comp, equivalence_avant(vc_gfx))   # g(f(x)) = (g∘f)(x)
    # cut de l'hypothèse de domaine « (∃y)(x,y)∈comp » (dérivée de in_comp)
    comp_dom = N.modus_ponens(in_comp, N.s5(appartient(E.couple(vx, vy), comp), gfx, "y"))
    eq1 = N.modus_ponens(comp_dom, N.loi_deduction(
        existe("y", appartient(E.couple(vx, vy), comp)), eq))
    return N.modus_ponens(eq1, symetrie(gfx, gof))      # (g∘f)(x) = g(f(x))


# @livre Ch.II §3.3 Prop.4 | E II.12 L.5-6 | PDF p.63
def composee_associee_droite_valeur(h="H", g="G", f="F", x="x"):
    """⊢ (h∘(g∘f))(x) = h(g(f(x))).   (réduction « à droite » au niveau des valeurs.)

    Point x simple (sans nesting) : composition_valeur_t deux fois + congruence
    sous h(·). Sert de demi-associativité ; l'identité complète
    ((h∘g)∘f)(x)=(h∘(g∘f))(x) est REPORTÉE (cf. rapport) car le membre gauche
    exige composition_valeur en un point qui est lui-même une valeur τy(...),
    ce qui déclenche la capture du liant « y » dans valeur_caracterisation."""
    vH, vG, vF, vx = var(h), var(g), var(f), var(x)
    GF = E.composee(vG, vF)
    fx = E.valeur(vF, vx)
    Gfx = E.valeur(vG, fx)                               # g(f(x))
    R1 = composition_valeur_t(vH, GF, vx)               # (h∘(g∘f))(x) = h((g∘f)(x))
    R2 = composition_valeur_t(vG, vF, vx)               # (g∘f)(x) = g(f(x))
    cong = N.modus_ponens(R2, congruence_terme(         # h((g∘f)(x)) = h(g(f(x)))
        E.valeur(GF, vx), Gfx, E.valeur(vH, var("w")), "w"))
    return composer_egalites(R1, cong)                  # (h∘(g∘f))(x) = h(g(f(x)))


# @livre Ch.II §3.8 Def.11 | E II.18 L.37-39 | PDF p.69
def retraction_compose_valeur(r="R", f="F", a="A", x="x"):
    """{est_retraction(R,F,A), F func, R func, x∈domF, f(x)∈domR} ⊢ (x∈A) ⇒ ((r∘f)(x) = x).

    Relie la définition matricielle r∘f = Id_A (E II.18, Déf. 11 : (∀x∈A) r(f(x))=x)
    au niveau « composée » : (r∘f)(x) = r(f(x)) (composition_valeur) puis r(f(x))=x
    (instance de est_retraction). Donc (r∘f)(x)=x sur A — l'identité d'application
    Id_A lue sur les valeurs."""
    vR, vF, vA, vx = var(r), var(f), var(a), var(x)
    comp = E.composee(vR, vF)
    fx = E.valeur(vF, vx)
    rfx = E.valeur(vR, fx)                               # r(f(x))
    rof = E.valeur(comp, vx)                             # (r∘f)(x)
    # (r∘f)(x) = r(f(x))   (composition_valeur ; hyps fonctionnels/domaines)
    cv = composition_valeur_t(vR, vF, vx)               # (r∘f)(x) = r(f(x))
    # r(f(x)) = x   à partir de est_retraction(R,F,A) sous x∈A
    hret = N.assume(E.est_retraction(vR, vF, vA))       # (∀x)(x∈A ⇒ r(f(x))=x)
    inst = instancie(hret, vx)                          # x∈A ⇒ r(f(x))=x
    hxa = N.assume(appartient(vx, vA))
    eq_rfx_x = N.modus_ponens(hxa, inst)                # {ret, x∈A} ⊢ r(f(x))=x
    chained = composer_egalites(cv, eq_rfx_x)           # (r∘f)(x) = x
    return N.loi_deduction(appartient(vx, vA), chained)  # (x∈A) ⇒ (r∘f)(x)=x


# @livre Ch.II §3.8 Def.11 | E II.18-19 (dual de retraction_compose_valeur) | PDF p.69
def section_compose_valeur(s="S", f="F", b="B", x="u"):
    """{est_section(S,F,B), F∘S func, u∈domS, s(u)∈domF} ⊢ (u∈B) ⇒ ((f∘s)(u) = u).

    Dual EXACT de `retraction_compose_valeur` : relie la définition matricielle
    f∘s = Id_B (E II.18, Déf. 11 : (∀y∈B) f(s(y))=y) au niveau « composée » :
    (f∘s)(u) = f(s(u)) (composition_valeur) puis f(s(u))=u (instance de est_section).
    Donc (f∘s)(u)=u sur B — l'identité Id_B lue sur les valeurs.  Point « u » ≠ « y »
    (liant interne de valeur et liant de est_section) pour éviter la capture."""
    vS, vF, vB, vx = var(s), var(f), var(b), var(x)
    comp = E.composee(vF, vS)                            # F∘S
    su = E.valeur(vS, vx)                                # s(u)
    fsu = E.valeur(vF, su)                               # f(s(u))
    fos = E.valeur(comp, vx)                             # (f∘s)(u)
    # (f∘s)(u) = f(s(u))   (composition_valeur ; hyps fonctionnels/domaines)
    cv = composition_valeur_t(vF, vS, vx)               # (f∘s)(u) = f(s(u))
    # f(s(u)) = u   à partir de est_section(S,F,B) sous u∈B
    # liant « u » (=point) ≠ « y » : sinon valeur(S,y)=τy((y,y)∈S) se self-capture
    hsec = N.assume(E.est_section(vS, vF, vB, y=x))     # (∀u)(u∈B ⇒ f(s(u))=u)
    inst = instancie(hsec, vx)                          # u∈B ⇒ f(s(u))=u
    hub = N.assume(appartient(vx, vB))
    eq_fsu_u = N.modus_ponens(hub, inst)                # {sec, u∈B} ⊢ f(s(u))=u
    chained = composer_egalites(cv, eq_fsu_u)           # (f∘s)(u) = u
    return N.loi_deduction(appartient(vx, vB), chained)  # (u∈B) ⇒ (f∘s)(u)=u


def cible_section_compose_valeur(s="S", f="F", b="B", x="u"):
    """Conclusion attendue : (u∈B) ⇒ ((f∘s)(u) = u)  [(f∘s)(u) lu comme UN graphe]."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    vS, vF, vB, vx = var(s), var(f), var(b), var(x)
    fos = E.valeur(E.composee(vF, vS), vx)
    return impl(appartient(vx, vB), egal(fos, vx))


def enonce_composee_valeur_app(g="G", f="F", e="E", fp="Fp", gp="Gp", x="u"):
    vG, vF, vE, vu = var(g), var(f), var(e), var(x)
    fu = E.valeur(vF, vu)
    gof = E.valeur(E.composee(vG, vF), vu)
    return impl(appartient(vu, vE), egal(gof, E.valeur(vG, fu)))


# @livre Ch.II §3.8 Prop.- | E II.19 L.27-37 | PDF p.70  (composée-valeur, version APPLICATION)
def composee_valeur_app(g="G", f="F", e="E", fp="Fp", gp="Gp", x="u"):
    """⊢ {est_application(F,E,Fp), est_application(G,Fp,Gp)}  (u∈E) ⇒ ((g∘f)(u) = g(f(u))).

    Version « application » de composition_valeur : les 3 hypothèses de POINT de
    composition_valeur_t (u∈domF, f(u)∈domG, G∘F fonctionnel) sont DÉCHARGÉES depuis
    est_application, si bien que l'énoncé ne porte QUE les deux hypothèses
    d'application (universelles) — donc généralisable sur u (clé pour les converses
    de facteur, n°79).  Décharge :
      · (c) G∘F fonctionnel  ← composee_fonctionnelle(G,F) [F,G fonctionnels ex application] ;
      · (a) (∃y)(u,y)∈F      ← u∈E ∧ domF=E ⇒ u∈domF (Leibniz S6) ⇒ ∃ (AXIOME_DOM) ;
      · (b) (∃y)(f(u),y)∈G   ← (u,f(u))∈F [valeur_dans_graphe] ∧ F⊂E×Fp ⇒ f(u)∈Fp=domG ⇒ ∃."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_7_composee_fonctions.ensembles_fonctions_composee import composee_fonctionnelle
    vG, vF, vE, vFp, vGp, vu = var(g), var(f), var(e), var(fp), var(gp), var(x)
    fu = E.valeur(vF, vu)

    hF = N.assume(est_application(vF, vE, vFp))
    hG = N.assume(est_application(vG, vFp, vGp))
    F_func = conjonction_elim_gauche(conjonction_elim_gauche(hF))   # est_fonctionnel(F)
    domF_eq = conjonction_elim_droite(conjonction_elim_gauche(hF))  # dom F = E
    F_incl = conjonction_elim_droite(hF)                            # F ⊂ E×Fp
    G_func = conjonction_elim_gauche(conjonction_elim_gauche(hG))   # est_fonctionnel(G)
    domG_eq = conjonction_elim_droite(conjonction_elim_gauche(hG))  # dom G = Fp
    hu = N.assume(appartient(vu, vE))                               # u∈E

    dom_ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    # (c) G∘F fonctionnel
    comp_func = N.modus_ponens(conjonction_intro(F_func, G_func), composee_fonctionnelle(g, f))
    # (a) (∃y)(u,y)∈F
    membre_domF = instancie(instancie(dom_ax, vF), vu)             # (u∈domF)⇔(∃y)(u,y)∈F
    s6_domF = N.s6(E.dom(vF), vE, "w", appartient(vu, var("w")))   # (domF=E)⇒((u∈domF)⇔(u∈E))
    u_in_domF = N.modus_ponens(hu, equivalence_arriere(N.modus_ponens(domF_eq, s6_domF)))
    hyp_a = N.modus_ponens(u_in_domF, equivalence_avant(membre_domF))            # (∃y)(u,y)∈F
    # (b) (∃y)(f(u),y)∈G
    uf_in_F = _cut(valeur_dans_graphe(vF, vu), hyp_a)             # (u,f(u))∈F
    uf_in_prod = N.modus_ponens(uf_in_F, instancie(F_incl, E.couple(vu, fu)))    # (u,f(u))∈E×Fp
    fu_in_Fp = conjonction_elim_droite(N.modus_ponens(
        uf_in_prod, equivalence_avant(couple_dans_produit_ssi(vu, fu, vE, vFp)))) # f(u)∈Fp
    membre_domG = instancie(instancie(dom_ax, vG), fu)            # (f(u)∈domG)⇔(∃y)(f(u),y)∈G
    s6_domG = N.s6(E.dom(vG), vFp, "w", appartient(fu, var("w"))) # (domG=Fp)⇒((f(u)∈domG)⇔(f(u)∈Fp))
    fu_in_domG = N.modus_ponens(fu_in_Fp, equivalence_arriere(N.modus_ponens(domG_eq, s6_domG)))
    hyp_b = N.modus_ponens(fu_in_domG, equivalence_avant(membre_domG))           # (∃y)(f(u),y)∈G

    cv = composition_valeur_t(vG, vF, vu)                         # (g∘f)(u)=g(f(u)), 3 hyps
    cv = _cut(cv, hyp_b)
    cv = _cut(cv, comp_func)
    cv = _cut(cv, hyp_a)                                          # 3 hyps de point déchargées
    res = N.loi_deduction(appartient(vu, vE), cv)                # (u∈E)⇒((g∘f)(u)=g(f(u)))
    assert res.conclusion == enonce_composee_valeur_app(g, f, e, fp, gp, x), \
        "composee_valeur_app : conclusion ≠ énoncé attendu"
    return res


# @livre Ch.II §3.4 Prop.- | E II.14 L.4-7 | PDF p.65  (image d'une application ⊂ son but)
def image_incluse_arrivee(f="F", e="E", b="B"):
    """⊢ {est_application(F,E,B)}  f⟨E⟩ ⊂ B.   (l'image d'une application tombe dans son but.)

    z∈f⟨E⟩ ⇒ (∃x)(x∈E et (x,z)∈F) [membre_image] ; sous le témoin (x,z)∈F⊂E×B
    [est_application] donne (x,z)∈E×B, donc z∈B [couple_dans_produit_ssi]."""
    vF, vE, vB, vz, vx = var(f), var(e), var(b), var("z"), var("x")
    hF = N.assume(est_application(vF, vE, vB))
    F_incl = conjonction_elim_droite(hF)                         # F ⊂ E×B
    hz = N.assume(appartient(vz, E.image(vF, vE)))               # z ∈ f⟨E⟩
    ex = N.modus_ponens(hz, equivalence_avant(membre_image(vF, vE, vz)))  # (∃x)(x∈E et (x,z)∈F)
    body = _et(appartient(vx, vE), appartient(E.couple(vx, vz), vF))
    hb = N.assume(body)
    xz_prod = N.modus_ponens(conjonction_elim_droite(hb),
                             instancie(F_incl, E.couple(vx, vz)))         # (x,z)∈E×B
    zB = conjonction_elim_droite(N.modus_ponens(
        xz_prod, equivalence_avant(couple_dans_produit_ssi(vx, vz, vE, vB))))  # z∈B
    zB_final = N.modus_ponens(ex, existe_elimination(N.loi_deduction(body, zB), "x"))  # z∈B
    res = N.generalisation("z", N.loi_deduction(appartient(vz, E.image(vF, vE)), zB_final))
    assert res.conclusion == inclus(E.image(vF, vE), vB), \
        "image_incluse_arrivee : conclusion ≠ énoncé attendu"
    return res


def enonce_injective_facteur_droit(g="G", f="F", e="E", fp="Fp", gp="Gp"):
    vG, vF, vE = var(g), var(f), var(e)
    comp = E.composee(vG, vF)
    return impl(E.injective_dans(comp, vE), E.injective_dans(vF, vE))


# @livre Ch.R §2 Prop.- | E.R.10 item 12 (converse de facteur : G∘F injective ⇒ F injective) | PDF p.313
def injective_facteur_droit(g="G", f="F", e="E", fp="Fp", gp="Gp"):
    """⊢ {est_application(F,E,Fp), est_application(G,Fp,Gp)}  injective_dans(G∘F,E) ⇒ injective_dans(F,E).

    Converse de facteur DROIT : si la composée g∘f est injective sur E, alors le
    facteur intérieur f l'est aussi.  Preuve : f(u)=f(u') ⇒ g(f(u))=g(f(u'))
    [congruence_terme sous g] ⇒ (g∘f)(u)=(g∘f)(u') [composee_valeur_app aux deux
    points] ⇒ u=u' [injective_dans(g∘f,E)].  Généralisation licite : composee_valeur_app
    ne laisse que des hyps d'application (sans u/u')."""
    vG, vF, vE, vFp, vGp = var(g), var(f), var(e), var(fp), var(gp)
    comp = E.composee(vG, vF)
    u, up = var("u"), var("up")
    inj_comp = N.assume(E.injective_dans(comp, vE))
    inst = instancie(instancie(inj_comp, u), up)     # (u∈E∧u'∈E∧(g∘f)(u)=(g∘f)(u'))⇒u=u'

    h = N.assume(E.et(E.et(appartient(u, vE), appartient(up, vE)),
                      egal(E.valeur(vF, u), E.valeur(vF, up))))       # u∈E∧u'∈E∧f(u)=f(u')
    uE = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upE = conjonction_elim_droite(conjonction_elim_gauche(h))
    fu_eq = conjonction_elim_droite(h)                               # f(u)=f(u')
    g_cong = N.modus_ponens(fu_eq, congruence_terme(                 # g(f(u))=g(f(u'))
        E.valeur(vF, u), E.valeur(vF, up), E.valeur(vG, var("w")), "w"))
    cvu = N.modus_ponens(uE, composee_valeur_app(g, f, e, fp, gp, "u"))    # (g∘f)(u)=g(f(u))
    cvup = N.modus_ponens(upE, composee_valeur_app(g, f, e, fp, gp, "up")) # (g∘f)(u')=g(f(u'))
    comp_eq = composer_egalites(composer_egalites(cvu, g_cong), _symetrie_thm(cvup))  # (g∘f)(u)=(g∘f)(u')
    ante = conjonction_intro(conjonction_intro(uE, upE), comp_eq)
    uu = N.modus_ponens(ante, inst)                                  # u=u'
    imp = N.loi_deduction(h.conclusion, uu)
    gen = N.generalisation("u", N.generalisation("up", imp))         # injective_dans(F,E)
    res = N.loi_deduction(E.injective_dans(comp, vE), gen)
    assert res.conclusion == enonce_injective_facteur_droit(g, f, e, fp, gp), \
        "injective_facteur_droit : conclusion ≠ énoncé attendu"
    return res


def enonce_surjective_facteur_gauche(f="F", g="G", e="E", fs="Fs"):
    vf, vg, vE, vFs = var(f), var(g), var(e), var(fs)
    comp = E.composee(vf, vg)
    return impl(E.est_surjective(comp, vFs, vFs), E.est_surjective(vf, vE, vFs))


# @livre Ch.R §2 Prop.- | E.R.10 item 12 (converse de facteur : f∘g surjective ⇒ f surjective) | PDF p.313
def surjective_facteur_gauche(f="F", g="G", e="E", fs="Fs"):
    """⊢ {est_application(F,E,Fs), est_application(G,Fs,E)}  est_surjective(F∘G,Fs,Fs) ⇒ est_surjective(F,E,Fs).

    Converse de facteur GAUCHE : si la composée f∘g est surjective sur Fs, le facteur
    extérieur f l'est aussi.  Preuve par double inclusion de f⟨E⟩ et Fs :
      · f⟨E⟩ ⊂ Fs                    [image_incluse_arrivee] ;
      · Fs = (f∘g)⟨Fs⟩ [surj] = f⟨g⟨Fs⟩⟩ [image_composee] ⊂ f⟨E⟩
        [g⟨Fs⟩⊂E (image_incluse_arrivee) + image_croissante] ;
    d'où f⟨E⟩ = Fs [extensionnalite_appliquee], i.e. f surjective."""
    vf, vg, vE, vFs = var(f), var(g), var(e), var(fs)
    comp = E.composee(vf, vg)
    imgfE = E.image(vf, vE)                    # f⟨E⟩
    imggFs = E.image(vg, vFs)                  # g⟨Fs⟩
    fg_Fs = E.image(vf, imggFs)                # f⟨g⟨Fs⟩⟩

    hsurj = N.assume(E.est_surjective(comp, vFs, vFs))   # (f∘g)⟨Fs⟩ = Fs

    incl_fE_Fs = image_incluse_arrivee(f, e, fs)          # {est_app(F,E,Fs)} f⟨E⟩⊂Fs
    incl_gFs_E = image_incluse_arrivee(g, fs, e)          # {est_app(G,Fs,E)} g⟨Fs⟩⊂E

    imgcomp = image_composee(f, g, fs)                    # (f∘g)⟨Fs⟩ = f⟨g⟨Fs⟩⟩   [CLOS]
    croiss = instancie(instancie(N.generalisation("X", N.generalisation("Y",
                image_croissante(f, "X", "Y"))), imggFs), vE)   # (g⟨Fs⟩⊂E)⇒(f⟨g⟨Fs⟩⟩⊂f⟨E⟩)
    fg_sub_fE = N.modus_ponens(incl_gFs_E, croiss)        # f⟨g⟨Fs⟩⟩ ⊂ f⟨E⟩

    Fs_eq_comp = N.modus_ponens(hsurj, symetrie(E.image(comp, vFs), vFs))  # Fs = (f∘g)⟨Fs⟩
    Fs_eq_fgFs = composer_egalites(Fs_eq_comp, imgcomp)                    # Fs = f⟨g⟨Fs⟩⟩
    s6 = N.s6(vFs, fg_Fs, "w", inclus(var("w"), imgfE))  # (Fs=f⟨g⟨Fs⟩⟩)⇒((Fs⊂f⟨E⟩)⇔(f⟨g⟨Fs⟩⟩⊂f⟨E⟩))
    Fs_sub_fE = N.modus_ponens(fg_sub_fE, equivalence_arriere(N.modus_ponens(Fs_eq_fgFs, s6)))  # Fs⊂f⟨E⟩

    ext = extensionnalite_appliquee(imgfE, vFs)          # (f⟨E⟩⊂Fs et Fs⊂f⟨E⟩)⇒f⟨E⟩=Fs
    eq = N.modus_ponens(conjonction_intro(incl_fE_Fs, Fs_sub_fE), ext)    # f⟨E⟩=Fs = est_surjective(f,E,Fs)
    res = N.loi_deduction(E.est_surjective(comp, vFs, vFs), eq)
    assert res.conclusion == enonce_surjective_facteur_gauche(f, g, e, fs), \
        "surjective_facteur_gauche : conclusion ≠ énoncé attendu"
    return res


__all__ = ["composition_valeur_t", "composee_associee_droite_valeur",
           "retraction_compose_valeur", "section_compose_valeur",
           "cible_section_compose_valeur",
           "enonce_composee_valeur_app", "composee_valeur_app",
           "image_incluse_arrivee",
           "enonce_injective_facteur_droit", "injective_facteur_droit",
           "enonce_surjective_facteur_gauche", "surjective_facteur_gauche"]
