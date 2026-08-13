"""§II.5.5 / §III.3.3 — ADJONCTION D'INDICE : la BIJECTION et le CARDINAL (T1b-(2)).

Suite de ..._adjonction (Φ, P1-P3, hypothèses) et ..._adjonction_briques.  Ici :
  P6 adjonction_injective    {H2}         ⊢ injective_dans(Φ, ∏_{I∪{j}})
  P4/P5 adjonction_image     {H1, H3}     ⊢ image(Φ, ∏_{I∪{j}}) = (∏_I) × u_j
  P7 adjonction_bijection    {H1, H2, H3} ⊢ est_bijection_de(Φ, ∏_{I∪{j}}, ∏_I × u_j)
     eq_produit_adjonction   {H1, H2, H3} ⊢ Eq( ∏_{I∪{j}} , (∏_I) × u_j )
     produit_cardinal_adjonction {…}      ⊢ Card(∏_{I∪{j}}) = Card((∏_I) × u_j)
        — dont le membre droit EST, terme à terme, produit_cardinal_binaire(∏_I, u_j).

INJECTIVITÉ : Φ(F)=Φ(F') ⇒ (F|I, F(j)) = (F'|I, F'(j)) ⇒ pr_ι(F)=pr_ι(F') pour tout
ι∈I∪{j} (sur I via restriction_valeur, en j par le pont α-τ) ⇒ F=F' (extensionnalité
du produit, sous H2).  SURJECTIVITÉ : l'antécédent de (G,x) est le prolongement
G∪{(j,x)} (briques) dont la restriction à I redonne G (graphe_egal_par_valeurs,
sous H3) et la valeur en j redonne x.  H1/H2/H3 : cf. ensembles_produit_adjonction.
Rien postulé ; theorie_ensembles() = 22 ; noyau/subst intouchés.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, appartient, existe, inclus, subst_t, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a, syllogisme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie, cas)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre, couple_egal_implique_composantes)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    graphe_egal_par_valeurs)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_extensionnalite_produit import (
    extensionnalite_produit)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    restriction_dom_sous_inclusion, restriction_valeur, _restriction_fonctionnelle_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de, equipotent, cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    _prop1_direct_t, produit_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
    _membre_produit_egal_couple_ab, _membre_produit_pr1_ab, _membre_produit_pr2_ab,
    _couple_dans_produit_t)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import (
    _t, _dech, XB, VC, indices_adjoints, produit_total, produit_cible,
    terme_adjonction, graphe_adjonction, valeur_y_egal_c, i_dans_union,
    j_dans_union, inclusion_I_union, adjonction_fonctionnelle, adjonction_domaine,
    adjonction_valeur, hypothese_indice_neuf, hypothese_graphes_total,
    hypothese_graphes_partiel, _car_union, _corps_membre, _leibniz_membre,
    _leibniz_membre_arriere)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    restriction_dans_produit, restriction_est_graphe, valeur_reunion_gauche,
    valeur_reunion_point, prolongement_un_point_dans_produit)


# ── P6 : INJECTIVITÉ  {H2} ⊢ injective_dans(Φ, ∏_{I∪{j}}) ─────────────────────
def adjonction_injective(u="uq", i="Iq", j="jq"):
    """{H2} ⊢ injective_dans(Φ, ∏_{I∪{j}}).

    Φ(F)=Φ(F') donne F|I=F'|I et F(j)[c]=F'(j)[c] (composantes du couple) ; d'où
    pr_ι(F)=pr_ι(F') pour tout ι∈I∪{j} (sur I : F(ι)=(F|I)(ι), en j : pont α-τ) ;
    l'extensionnalité du produit (sous H2 pour « graphes ») conclut F=F'.
    LIANTS : preuve sur points EXOTIQUES Fa/Fb (la machinerie restriction_valeur
    généralise la lettre « u ») puis ∀-clôture + ré-instanciation en u/up pour la
    forme EXACTE de injective_dans (liants u/up figés par est_bijection_de)."""
    vI, vj, vu, vup = _t(i), _t(j), var("Fa"), var("Fb")
    A, union = produit_total(u, i, j), indices_adjoints(i, j)
    Phi, T = graphe_adjonction(u, i, j), terme_adjonction(i, j)
    h2 = N.assume(hypothese_graphes_total(u, i, j))
    hyp = et(et(appartient(vu, A), appartient(vup, A)),
             egal(E.valeur(Phi, vu), E.valeur(Phi, vup)))
    h = N.assume(hyp)
    uin = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upin = conjonction_elim_droite(conjonction_elim_gauche(h))
    val_eq = conjonction_elim_droite(h)
    # T[Fa] = Φ(Fa) = Φ(Fb) = T[Fb]  puis composantes
    av_u = _dech(adjonction_valeur("Fa", u, i, j), uin)
    av_up = _dech(adjonction_valeur("Fb", u, i, j), upin)
    Tu = subst_t(vu, XB, T)
    eq_T = composer_egalites(composer_egalites(
        N.modus_ponens(av_u, symetrie(E.valeur(Phi, vu), Tu)), val_eq), av_up)
    ru, cu = E.restriction(vu, vI), E.valeur(vu, vj, b=VC)
    rup, cup = E.restriction(vup, vI), E.valeur(vup, vj, b=VC)
    comps = N.modus_ponens(eq_T, couple_egal_implique_composantes(ru, cu, rup, cup))
    restr_eq = conjonction_elim_gauche(comps)                   # Fa|I = Fb|I
    valc_eq = conjonction_elim_droite(comps)                    # Fa(j)[c] = Fb(j)[c]
    _, func_u, domeq_u, _ = _corps_membre(uin, u, union, vu)
    _, func_up, domeq_up, _ = _corps_membre(upin, u, union, vup)
    # (∀i)(i∈I∪{j} ⇒ Fa(i) = Fb(i))   — par cas i∈I / i∈{j}
    vi = var("i")
    hi = N.assume(appartient(vi, union))
    disj_i = N.modus_ponens(hi, equivalence_avant(_car_union(i, j, vi)))
    #   i∈I : Fa(i) = (Fa|I)(i) = (Fb|I)(i) = Fb(i)
    hiI = N.assume(appartient(vi, vI))
    i_un = _dech(i_dans_union(i, j, vi), hiI)
    def _rv(vpt, func_pt, domeq_pt):
        i_dom = _leibniz_membre_arriere(i_un, domeq_pt, vi)
        return _dech(restriction_valeur(vpt, vI, vi), func_pt, hiI, i_dom)
    rv_u, rv_up = _rv(vu, func_u, domeq_u), _rv(vup, func_up, domeq_up)
    mid = N.modus_ponens(restr_eq, congruence_terme(ru, rup, E.valeur(var("w"), vi)))
    chainA = composer_egalites(composer_egalites(
        N.modus_ponens(rv_u, symetrie(E.valeur(ru, vi), E.valeur(vu, vi))), mid), rv_up)
    brA = N.loi_deduction(appartient(vi, vI), chainA)
    #   i∈{j} : Fa(j) = Fa(j)[c] = Fb(j)[c] = Fb(j), transporté en i par i=j
    hiJ = N.assume(appartient(vi, E.singleton(vj)))
    i_eq_j = N.modus_ponens(hiJ, equivalence_avant(singleton_membre(vi, vj)))
    chainJ = composer_egalites(composer_egalites(valeur_y_egal_c(vu, vj), valc_eq),
        N.modus_ponens(valeur_y_egal_c(vup, vj), symetrie(E.valeur(vup, vj), cup)))
    transport = N.modus_ponens(N.modus_ponens(i_eq_j, symetrie(vi, vj)),
        N.s6(vj, vi, "w", egal(E.valeur(vu, var("w")), E.valeur(vup, var("w")))))
    brB = N.loi_deduction(appartient(vi, E.singleton(vj)),
                          N.modus_ponens(chainJ, equivalence_avant(transport)))
    proj_eq = N.generalisation("i", N.loi_deduction(appartient(vi, union),
                                                    cas(disj_i, brA, brB)))
    # extensionnalité du produit (les « est_un_graphe » viennent de H2)
    gr_u = N.modus_ponens(uin, instancie(h2, vu))
    gr_up = N.modus_ponens(upin, instancie(h2, vup))
    ext = extensionnalite_produit(_t(u), union, vu, vup, "i")
    conj = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        uin, upin), gr_u), gr_up), proj_eq)
    u_eq_up = N.modus_ponens(conj, ext)
    # ∀-clôture sur Fa/Fb puis ré-instanciation en u/up (forme exacte injective_dans)
    gen_ex = N.generalisation("Fa", N.generalisation("Fb", N.loi_deduction(hyp, u_eq_up)))
    inst = instancie(instancie(gen_ex, var("u")), var("up"))
    res = N.generalisation("u", N.generalisation("up", inst))
    assert res.conclusion == E.injective_dans(Phi, A), "P6 : forme"
    assert res.hypotheses == frozenset({hypothese_graphes_total(u, i, j)}), "P6 : hyps"
    return res


# ── P4/P5 : IMAGE  {H1, H3} ⊢ image(Φ, ∏_{I∪{j}}) = (∏_I) × u_j ───────────────
def adjonction_image(u="uq", i="Iq", j="jq"):
    """{H1, H3} ⊢ image(Φ, ∏_{I∪{j}}) = (∏_I) × u_j.

    ⊂ (P4) : s=T[t]=(t|I, t(j)[c]) avec t|I ∈ ∏_I (restriction_dans_produit) et
    t(j)∈u_j (membership en j∈I∪{j}).  ⊃ (P5, surjectivité) : l'antécédent de s
    est t₀ := pr₁s ∪ {(j, pr₂s)} — t₀∈∏ (prolongement, sous H1), t₀|I = pr₁s
    (graphe_egal_par_valeurs, sous H3), t₀(j) = pr₂s.  Élément « s » (≠ liants
    z/x/y des machineries), α-renommé en « z » pour l'extension finale."""
    vI, vj = _t(i), _t(j)
    A, B, union = produit_total(u, i, j), produit_cible(u, i, j), indices_adjoints(i, j)
    Phi, T = graphe_adjonction(u, i, j), terme_adjonction(i, j)
    prodI = E.produit_famille(_t(u), vI)
    famj = E.valeur_famille(_t(u), vj)
    vs, vt = var("s"), var("t")
    # caractérisation de l'image (AXIOME_IMAGE, liant ∃ renommé x→t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, Phi), A), vs)
    ren = alpha_existe("x", "t", et(appartient(var("x"), A),
                                    appartient(E.couple(var("x"), vs), Phi)))
    img_car = equivalence_transitivite(img_car0, ren)   # s∈Φ⟨A⟩ ⇔ (∃t)(t∈A et (t,s)∈Φ)
    bodyR = et(appartient(vt, A), appartient(E.couple(vt, vs), Phi))
    # ── P4 (⊂) : sous (t∈A et (t,s)∈Φ), s = T[t] ∈ ∏_I × u_j ──────────────────
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)
    cpl_in = conjonction_elim_droite(hbR)
    mem = membre_graphe_terme(A, T, "t", "s", XB, "yb")      # ((t,s)∈Φ) ⇔ (t∈A et s=T[t])
    s_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))
    Tt = subst_t(vt, XB, T)
    assert Tt == E.couple(E.restriction(vt, vI), E.valeur(vt, vj, b=VC)), "P4 : T[t]"
    rdp = _dech(restriction_dans_produit(vt, u, i, j), t_in)
    _, _, _, vals_t = _corps_membre(t_in, u, union, vt)
    tj_in = N.modus_ponens(j_dans_union(i, j), instancie(vals_t, vj))   # t(j) ∈ u_j
    leib_c = N.modus_ponens(valeur_y_egal_c(vt, vj),
        N.s6(E.valeur(vt, vj), E.valeur(vt, vj, b=VC), "w", appartient(var("w"), famj)))
    tjc_in = N.modus_ponens(tj_in, equivalence_avant(leib_c))           # t(j)[c] ∈ u_j
    cpl_T = N.modus_ponens(conjonction_intro(rdp, tjc_in),
        _couple_dans_produit_t(E.restriction(vt, vI), E.valeur(vt, vj, b=VC), prodI, famj))
    s_in_B = N.modus_ponens(cpl_T, equivalence_arriere(N.modus_ponens(
        s_eq_Tt, N.s6(vs, Tt, "w", appartient(var("w"), B)))))
    fwd = existe_elimination(N.loi_deduction(bodyR, s_in_B), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)   # s∈Φ⟨A⟩ ⇒ s∈B
    # ── P5 (⊃) : sous s∈B, l'antécédent t₀ = pr₁s ∪ {(j, pr₂s)} ───────────────
    Gz, xz = E.pr1(vs, "a", "b"), E.pr2(vs, "a", "b")
    G_in = _membre_produit_pr1_ab(prodI, famj, vs)           # {s∈B} ⊢ pr₁s ∈ ∏_I
    x_in = _membre_produit_pr2_ab(prodI, famj, vs)           # {s∈B} ⊢ pr₂s ∈ u_j
    s_rec = _membre_produit_egal_couple_ab(prodI, famj, vs)  # {s∈B} ⊢ s = (pr₁s, pr₂s)
    S = E.singleton(E.couple(vj, xz))
    t0 = E.reunion(Gz, S)
    restr = E.restriction(t0, vI)
    t0_in = _dech(prolongement_un_point_dans_produit(Gz, xz, u, i, j), G_in, x_in)
    _, func_t0, domeq_t0, _ = _corps_membre(t0_in, u, union, t0)
    _, func_G, domeq_G, _ = _corps_membre(G_in, u, vI, Gz)
    # (α) t₀|I = pr₁s  par extensionnalité fonctionnelle (6 prémisses de gev)
    c_func_r = N.modus_ponens(func_t0, _restriction_fonctionnelle_terme(t0, vI))
    c_gr_r = restriction_est_graphe(t0, vI)                             # CLOS
    h3 = N.assume(hypothese_graphes_partiel(u, i, j))
    c_gr_G = N.modus_ponens(G_in, instancie(h3, Gz))                    # sous H3
    leib_i = N.modus_ponens(domeq_t0, N.s6(E.dom(t0), union, "w", inclus(vI, var("w"))))
    incl_dom = N.modus_ponens(inclusion_I_union(i, j), equivalence_arriere(leib_i))
    dom_restr = N.modus_ponens(incl_dom, restriction_dom_sous_inclusion(t0, vI))
    dom_eq = composer_egalites(dom_restr, N.modus_ponens(domeq_G, symetrie(E.dom(Gz), vI)))
    vx = var("x")
    hx = N.assume(appartient(vx, E.dom(restr)))
    x_I = _leibniz_membre(hx, dom_restr, vx)                            # x∈I
    x_un = _dech(i_dans_union(i, j, vx), x_I)
    x_domt0 = _leibniz_membre_arriere(x_un, domeq_t0, vx)               # x∈dom t₀
    x_domG = _leibniz_membre_arriere(x_I, domeq_G, vx)                  # x∈dom pr₁s
    rv = _dech(restriction_valeur(t0, vI, vx), func_t0, x_I, x_domt0)
    vrg = _dech(valeur_reunion_gauche(Gz, S, vx), func_t0, x_domG)
    val_eq = N.generalisation("x", N.loi_deduction(appartient(vx, E.dom(restr)),
                                                   composer_egalites(rv, vrg)))
    conj_gev = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(c_func_r, func_G), c_gr_r), c_gr_G), dom_eq), val_eq)
    restr_eq_G = N.modus_ponens(conj_gev, graphe_egal_par_valeurs(restr, Gz))
    G_eq_restr = N.modus_ponens(restr_eq_G, symetrie(restr, Gz))        # pr₁s = t₀|I
    # (β) s = T[t₀] = (t₀|I, t₀(j)[c])
    Tt0 = subst_t(t0, XB, T)
    assert Tt0 == E.couple(restr, E.valeur(t0, vj, b=VC)), "P5 : T[t₀]"
    c1 = N.modus_ponens(G_eq_restr, congruence_terme(Gz, restr, E.couple(var("w"), xz)))
    vrp = _dech(valeur_reunion_point(Gz, vj, xz), func_t0)
    x_eq_c = composer_egalites(N.modus_ponens(vrp, symetrie(E.valeur(t0, vj), xz)),
                               valeur_y_egal_c(t0, vj))                 # pr₂s = t₀(j)[c]
    c2 = N.modus_ponens(x_eq_c, congruence_terme(xz, E.valeur(t0, vj, b=VC),
                                                 E.couple(restr, var("w"))))
    s_eq_T = composer_egalites(s_rec, composer_egalites(c1, c2))        # s = T[t₀]
    # (γ) (t₀, s) ∈ Φ  (axiome C54, témoins Fq:=t₀, yb:=s)
    ax_P = N.axiome(E.theorie_graphe_terme(A, T, XB, "yb", "zz"),
                    E.axiome_graphe_terme(A, T, XB, "yb", "zz"))
    cpl_ts = E.couple(t0, vs)
    car_ts = instancie(ax_P, cpl_ts)
    gbody = et(et(egal(cpl_ts, E.couple(var(XB), var("yb"))), appartient(var(XB), A)),
               egal(var("yb"), T))
    wit = conjonction_intro(conjonction_intro(N.reflexivite(cpl_ts), t0_in), s_eq_T)
    ex_yb = N.modus_ponens(wit, N.s5(subst_f(t0, XB, gbody), vs, "yb"))
    ex_F = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody), t0, XB))
    cpl_in_Phi = N.modus_ponens(ex_F, equivalence_arriere(car_ts))      # (t₀,s)∈Φ
    ex_t = N.modus_ponens(conjonction_intro(t0_in, cpl_in_Phi), N.s5(bodyR, t0, "t"))
    in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))         # s∈Φ⟨A⟩
    bwd_full = N.loi_deduction(appartient(vs, B), in_img)
    # ── double inclusion → extension (élément « s » α-renommé en « z ») ───────
    equiv_s = conjonction_intro(fwd_full, bwd_full)          # s∈Φ⟨A⟩ ⇔ s∈B  {H1, H3}
    equiv_z = instancie(N.generalisation("s", equiv_s), var("z"))
    char_img = N.generalisation("z", equiv_z)
    zB = appartient(var("z"), B)
    self_B = N.generalisation("z", conjonction_intro(a_implique_a(zB), a_implique_a(zB)))
    res = egalite_par_extension(char_img, self_B, E.image(Phi, A), B, "z")
    assert res.conclusion == egal(E.image(Phi, A), B), "P4/P5 : forme"
    assert res.hypotheses == frozenset({hypothese_indice_neuf(i, j),
                                        hypothese_graphes_partiel(u, i, j)}), "P4/P5 : hyps"
    return res


# ── P7 : BIJECTION, ÉQUIPOTENCE, CARDINAL ─────────────────────────────────────
def adjonction_bijection(u="uq", i="Iq", j="jq"):
    """{H1, H2, H3} ⊢ est_bijection_de(Φ, ∏_{I∪{j}}, (∏_I) × u_j).   (P7, cœur.)"""
    A, B = produit_total(u, i, j), produit_cible(u, i, j)
    res = conjonction_intro(
        conjonction_intro(adjonction_fonctionnelle(u, i, j), adjonction_domaine(u, i, j)),
        conjonction_intro(adjonction_injective(u, i, j), adjonction_image(u, i, j)))
    assert res.conclusion == est_bijection_de(graphe_adjonction(u, i, j), A, B), "P7 : forme"
    assert res.hypotheses == frozenset({
        hypothese_indice_neuf(i, j), hypothese_graphes_total(u, i, j),
        hypothese_graphes_partiel(u, i, j)}), "P7 : hyps"
    return res


def eq_produit_adjonction(u="uq", i="Iq", j="jq"):
    """{H1, H2, H3} ⊢ Eq( ∏_{ι∈I∪{j}} u_ι , (∏_{ι∈I} u_ι) × u_j ).   (P7, S5.)"""
    A, B = produit_total(u, i, j), produit_cible(u, i, j)
    bij = adjonction_bijection(u, i, j)
    res = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), A, B),
                                   graphe_adjonction(u, i, j), "F"))
    assert res.conclusion == equipotent(A, B), "Eq : forme"
    return res


#   (associativité des produits, cas « partition de I∪{j} en (I, {j}) » de la Rem. 1,
#    le facteur ∏_{{j}} étant identifié à u_j ; forme CARDINALE via Prop. 1 III.3.1 —
#    infra de la récursion du produit fini indexé, chantier T1b.)
# @livre Ch.II §5.5 Prop.7 | E II.35 L.2-6 | PDF p.86
# @livre Ch.II §5.5 Rem.1 | E II.35 L.15-22 | PDF p.86
def produit_cardinal_adjonction(u="uq", i="Iq", j="jq"):
    """{H1, H2, H3} ⊢ Card(∏_{ι∈I∪{j}} u_ι) = Card((∏_{ι∈I} u_ι) × u_j).

    FORME CARDINALE : le membre droit est LITTÉRALEMENT le terme
    produit_cardinal_binaire(∏_I u, u_j) = Card(∏_I × u_j) (Déf. 3, E.III.3.3) —
    aucune invariance supplémentaire du produit binaire n'est requise (asserté)."""
    A, B = produit_total(u, i, j), produit_cible(u, i, j)
    eq = eq_produit_adjonction(u, i, j)
    res = N.modus_ponens(eq, _prop1_direct_t(A, B))
    assert res.conclusion == egal(cardinal(A), cardinal(B)), "Card : forme"
    assert cardinal(B) == produit_cardinal_binaire(
        E.produit_famille(_t(u), _t(i)), E.valeur_famille(_t(u), _t(j))), \
        "Card : le RHS n'est pas produit_cardinal_binaire(∏_I, u_j)"
    assert res.hypotheses == frozenset({
        hypothese_indice_neuf(i, j), hypothese_graphes_total(u, i, j),
        hypothese_graphes_partiel(u, i, j)}), "Card : hyps"
    return res


__all__ = ["adjonction_injective", "adjonction_image", "adjonction_bijection",
           "eq_produit_adjonction", "produit_cardinal_adjonction"]
