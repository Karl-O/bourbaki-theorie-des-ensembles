"""§III.3.5 — MONOTONIE de l'EXPONENTIATION cardinale en l'EXPOSANT, INCONDITIONNELLE.

On DÉCHARGE l'hypothèse de support de `exposant_monotone_exposant_conditionnel`
(`ensembles_arith_cardinale_props_exposant_monotone`) en CONSTRUISANT l'injection
d'espaces de fonctions

    (C ≤ D  et  A ≠ ∅)  ⇒  𝓕(C;A) ≤ 𝓕(D;A)         [support_monotone_exposant]

puis, par le transport (0) :

    (c ≤ d  et  a ≠ 0)  ⇒  (a^c ≤ a^d)              [exposant_monotone_exposant]

a^c = exposant_cardinal_binaire(a,c) = Card(𝓕(c;a)) ; le « a ≠ 0 » est la condition
de Bourbaki (E.III.3.5) : une valeur-défaut a₀∈A est nécessaire pour PROLONGER une
application définie sur C↪D au domaine D tout entier.

CONSTRUCTION (en DEUX paliers chaînés par transitivité de ≤) :

  Palier 1  (κ : C ↪ D injection  ⇒  bijection C → κ⟨C⟩) :
      κ est une bijection de C sur son image κ⟨C⟩ (les 4 conjoints de
      est_bijection_de(κ,C,κ⟨C⟩) sont ceux de est_injection_de(κ,C,D) sauf
      l'image, qui devient κ⟨C⟩=κ⟨C⟩ trivialement).  κ⁻¹ : κ⟨C⟩ → C bijection
      (reciproque_est_bijection).  Le BUILDER GÉNÉRIQUE du module d'invariance
      `injection_via_pointmap(C, κ⟨C⟩, κ⁻¹)`  (pré-composition g ↦ g∘κ⁻¹) donne
          𝓕(C;A) ≤ 𝓕(κ⟨C⟩;A).

  Palier 2  (PROLONGEMENT par valeur-défaut a₀∈A le long de S ⊆ D) :
      `support_extension_domaine(S,D,a0)`  ⊢  𝓕(S;A) ≤ 𝓕(D;A)   {S⊆D, a₀∈A}.
      À g∈𝓕(S;A) on associe ĝ = graphe_de(g) ∪ R  où  R = { (d,a₀) | d∈D∖S }
      (constante a₀ sur le complément).  Domaines DISJOINTS (S et D∖S), donc
      RECOLLEMENT fonctionnel (reunion_graphes_fonctionnelle) de domaine
      dom g ∪ (D∖S) = S ∪ (D∖S) = D ; ĝ ⊂ D×A (g(s)∈A par le PONT ; a₀∈A) ;
      injectivité : ĝ₁=ĝ₂ coïncident sur S (valeur_reunion_gauche) ⇒ g₁=g₂
      (application_egale_par_valeurs).

  Avec S := κ⟨C⟩ ⊆ D, la transitivité de ≤ chaîne Paliers 1+2 :
      𝓕(C;A) ≤ 𝓕(κ⟨C⟩;A) ≤ 𝓕(D;A).

theorie_ensembles INCHANGÉE (22) ; aucun fichier existant modifié.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, ou, impl,
                     appartient, existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie,
    cas)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, est_bijection_de, inf_egal_card, equipotent)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, paires):
    out = thm
    for hyp_formule, preuve in paires:
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_formule, out))
    return out


# ═══════════════════════════════════════════════════════════════════════════════
#  PALIER 1 :  κ : C ↪ D injection  ⇒  𝓕(C;A) ≤ 𝓕(κ⟨C⟩;A).
# ═══════════════════════════════════════════════════════════════════════════════
def inj_donne_bij_image(kappa="kappa", c="C", d="D"):
    """{ est_injection_de(κ,C,D) } ⊢ est_bijection_de(κ, C, κ⟨C⟩).

    Une injection est une bijection sur son image : fonctionnel, dom κ=C, κ injective
    sont les trois premiers conjoints de est_injection_de ; la surjectivité sur κ⟨C⟩
    est image(κ,C)=κ⟨C⟩ (RÉFLEXIVITÉ)."""
    vk, vc, vd = _t(kappa), _t(c), _t(d)
    imgC = E.image(vk, vc)
    h_inj = N.assume(est_injection_de(vk, vc, vd))
    # est_injection_de = (((fonct et dom=C) et injective_dans) et image⊂D)
    func_dom = conjonction_elim_gauche(conjonction_elim_gauche(h_inj))   # (fonct et dom κ=C)
    inj_dans = conjonction_elim_droite(conjonction_elim_gauche(h_inj))   # injective_dans(κ,C)
    surj = N.reflexivite(imgC)                                           # image(κ,C)=κ⟨C⟩
    bijec = conjonction_intro(inj_dans, surj)                            # est_bijective(κ,C,κ⟨C⟩)
    return conjonction_intro(func_dom, bijec)                            # est_bijection_de(κ,C,κ⟨C⟩)


def support_le_image(kappa="kappa", c="C", d="D"):
    """{ est_injection_de(κ,C,D) } ⊢ inf_egal_card(𝓕(C;A), 𝓕(κ⟨C⟩;A)).

    κ⁻¹ : κ⟨C⟩ → C bijection (reciproque_est_bijection sur la bijection C→κ⟨C⟩) ;
    le BUILDER d'invariance injection_via_pointmap(C, κ⟨C⟩, κ⁻¹) (pré-composition
    g↦g∘κ⁻¹) donne 𝓕(C;A) ≤ 𝓕(κ⟨C⟩;A)."""
    from bourbaki.cardinaux.ensembles_eq_exposant_invariant import injection_via_pointmap
    from bourbaki.cardinaux.ensembles_bijection import reciproque_est_bijection
    vk, vc, vd = _t(kappa), _t(c), _t(d)
    imgC = E.image(vk, vc)
    Kinv = E.reciproque(vk)
    # bijection C→κ⟨C⟩
    bij_img = inj_donne_bij_image(vk, vc, vd)                            # bij(κ,C,κ⟨C⟩)
    # κ⁻¹ bijection κ⟨C⟩→C  (reciproque_est_bijection sur la bijection κ:C→κ⟨C⟩)
    rb = reciproque_est_bijection("F", "X", "Y")                        # bij(F,X,Y) ⇒ bij(F⁻¹,Y,X)
    rb = instancie(instancie(instancie(N.generalisation("F",
        N.generalisation("X", N.generalisation("Y", rb))), vk), vc), imgC)
    bij_inv = N.modus_ponens(bij_img, rb)                              # bij(κ⁻¹, κ⟨C⟩, C)
    # injection_via_pointmap(S=C, T=κ⟨C⟩, m=κ⁻¹) : {bij(κ⁻¹,κ⟨C⟩,C)} ⊢ 𝓕(C;A)≤𝓕(κ⟨C⟩;A)
    base = injection_via_pointmap(vc, imgC, Kinv)
    return _cut(base, [(est_bijection_de(Kinv, imgC, vc), bij_inv)])


# ═══════════════════════════════════════════════════════════════════════════════
#  PALIER 2 :  PROLONGEMENT par valeur-défaut a₀  le long de  S ⊆ D.
#    R       := { (d, a₀) | d ∈ D∖S }   (graphe constant a₀ sur le complément)
#    ĝ       := graphe_de(g) ∪ R         (recollement, domaines S et D∖S disjoints)
#    Ψ(g)    := ((ĝ, D), A)
#    W       := graphe_terme( 𝓕(S;A) , Ψ(g) , «g» )
# ═══════════════════════════════════════════════════════════════════════════════
_RPT = "d"          # point courant du graphe-terme R  (∈ D∖S)
_POINT = "g"        # point courant du graphe-terme externe W


def _compl(s, d):
    """D∖S."""
    return E.difference(_t(d), _t(s))


def R_terme(a0, s, d):
    """R := graphe_terme(D∖S, a₀, «d») = { (d, a₀) | d∈D∖S }  (constante a₀)."""
    return E.graphe_terme(_compl(s, d), _t(a0), _RPT)


def R_fonctionnel(a0, s, d):
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    return graphe_terme_fonctionnel(_compl(s, d), _t(a0), _RPT, "y")


def R_domaine(a0, s, d):
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
    return graphe_terme_domaine(_compl(s, d), _t(a0), _RPT, "y", "z")


def _R_inclus(a0, s, d, a):
    """{ a₀ ∈ A } ⊢ R ⊂ D×A.

    z∈R ⇒ z=(d,y), d∈D∖S, y=a₀ ; d∈D∖S ⇒ d∈D (difference⊂D) ; a₀∈A ⇒ y∈A ; (d,y)∈D×A."""
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    va0, vs, vd, va = _t(a0), _t(s), _t(d), _t(a)
    DmS = _compl(vs, vd)
    R = R_terme(va0, vs, vd)
    DA = E.produit(vd, va)
    vdp, vy, vz = var(_RPT), var("y"), var("z")

    from bourbaki.cardinaux.ensembles_eq_exposant_invariant import _membre_graphe_terme_z
    h_a0 = N.assume(appartient(va0, va))                       # a₀∈A
    # z∈R ⇔ (∃d)(∃y)(z=(d,y) et d∈D∖S et y=a₀)
    car = _membre_graphe_terme_z(DmS, va0, _RPT, "z", "y")
    body = et(et(egal(vz, E.couple(vdp, vy)), appartient(vdp, DmS)), egal(vy, va0))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(d,y)
    d_in = conjonction_elim_droite(conjonction_elim_gauche(hb))   # d∈D∖S
    y_eq = conjonction_elim_droite(hb)                            # y=a₀
    # d∈D  (difference ⊂ D)
    ax_diff = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    diff_car = instancie(instancie(instancie(ax_diff, vd), vs), vdp)  # d∈D∖S ⇔ (d∈D et ¬(d∈S))
    d_in_D = conjonction_elim_gauche(N.modus_ponens(d_in, equivalence_avant(diff_car)))
    # y∈A  (y=a₀, a₀∈A)
    y_in_A = N.modus_ponens(h_a0, equivalence_arriere(N.modus_ponens(
        y_eq, N.s6(vy, va0, "w", appartient(var("w"), va)))))     # y∈A
    dy_in_prod = N.modus_ponens(conjonction_intro(d_in_D, y_in_A),
        equivalence_arriere(couple_dans_produit_ssi(vdp, vy, vd, va)))   # (d,y)∈D×A
    z_in_prod = N.modus_ponens(dy_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(vdp, vy), "w", appartient(var("w"), DA)))))  # z∈D×A
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_prod), "y"), _RPT)
    h_z = N.assume(appartient(vz, R))
    ex = N.modus_ponens(h_z, equivalence_avant(car))
    z_in_DA = N.modus_ponens(ex, ex_imp)
    return N.generalisation("z", N.loi_deduction(appartient(vz, R), z_in_DA))   # R⊂D×A


# ── disjonction des domaines :  (∀u)¬(u∈S et u∈D∖S) ──────────────────────────
def _disj_S_complement(s, d, u="u"):
    """⊢ (∀u)¬(u∈S et u∈D∖S).   (S et son complément D∖S sont disjoints : u∈D∖S
    contient ¬(u∈S), contradictoire avec u∈S.)"""
    vs, vd = _t(s), _t(d)
    vu = var(u)
    DmS = _compl(vs, vd)
    ax_diff = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    diff_car = instancie(instancie(instancie(ax_diff, vd), vs), vu)   # u∈D∖S ⇔ (u∈D et ¬(u∈S))
    conj = et(appartient(vu, vs), appartient(vu, DmS))
    h = N.assume(conj)
    u_in_S = conjonction_elim_gauche(h)                              # u∈S
    u_in_diff = conjonction_elim_droite(h)                          # u∈D∖S
    n_u_in_S = conjonction_elim_droite(N.modus_ponens(u_in_diff, equivalence_avant(diff_car)))  # ¬(u∈S)
    # sous conj : (u∈S) et ¬(u∈S)  ⇒  ¬conj  ((u∈S)⇒¬conj via s2 sur ¬(u∈S), puis MP)
    nconj = non(conj)
    p_imp_nconj = N.modus_ponens(n_u_in_S, N.s2(non(appartient(vu, vs)), nconj))  # (u∈S) ⇒ ¬conj
    derive_nconj = N.modus_ponens(u_in_S, p_imp_nconj)             # ¬conj   [sous conj]
    imp2 = N.loi_deduction(conj, derive_nconj)                     # conj ⇒ ¬conj = (¬conj ∨ ¬conj)
    neg = N.modus_ponens(imp2, N.s1(nconj))                        # ¬conj   (S1 : (¬c∨¬c)⇒¬c)
    return N.generalisation(u, neg)


# ── le recollement ĝ = graphe_de(g) ∪ R  et ses propriétés structurelles ──────
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de


def _ghat(g, a0, s, d):
    """ĝ := graphe_de(g) ∪ R."""
    return E.reunion(graphe_de(_t(g)), R_terme(a0, s, d))


def _struct_g(vg, vs, va):
    """{ g ∈ 𝓕(S;A) } ⊢ (graphe_de(g)⊂S×A, est_fonctionnel(graphe_de g), dom graphe_de(g)=S).

    Décompose g∈𝓕(S;A) (témoin G éliminé) en les 3 faits structurels du graphe."""
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
        _exposant_conjoints, _graphe_de_f_egal_G)
    vG = var("G")
    triple_g = E.couple(E.couple(vG, vs), va)
    body = et(egal(vg, triple_g), appartient(vG, E.exposant(vs, va)))
    grg = graphe_de(vg)

    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)
    G_in_exp = conjonction_elim_droite(hb)
    g_incl, g_func, g_dom = _exposant_conjoints(vG, vs, va, G_in_exp)
    gr_eq = _graphe_de_f_egal_G(vg, vs, va, vG, f_eq)            # graphe_de(g)=G
    incl = N.modus_ponens(g_incl, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", inclus(var("w"), E.produit(vs, va))))))
    func = N.modus_ponens(g_func, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", E.est_fonctionnel(var("w"))))))
    dom = N.modus_ponens(g_dom, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", egal(E.dom(var("w")), vs)))))
    # décharger le corps + éliminer le témoin via axiome_applications
    def discharge(thm):
        inner = existe_elimination(N.loi_deduction(body, thm), "G")
        ax = N.axiome(E.theorie_applications(vs, va, "t", "G"),
                      E.axiome_applications(vs, va, "t", "G"))
        car = instancie(ax, vg)
        h_app = N.assume(appartient(vg, E.applications(vs, va)))
        ex_body = N.modus_ponens(h_app, equivalence_avant(car))
        return N.modus_ponens(ex_body, inner)
    return discharge(incl), discharge(func), discharge(dom)


def _ghat_disjonction(vg, vs, va0, vd):
    """{ dom graphe_de(g)=S } ⊢ (∀u)¬(u∈dom graphe_de(g) et u∈dom R).

    Réécrit la disjonction S/(D∖S) (=_disj_S_complement) : S → dom graphe_de(g)
    (dom grg=S) et D∖S → dom R (R_domaine)."""
    grg = graphe_de(vg)
    DmS = _compl(vs, vd)
    domR = E.dom(R_terme(va0, vs, vd))
    vu = var("u")
    base = _disj_S_complement(vs, vd, "u")          # (∀u)¬(u∈S et u∈D∖S)
    base_u = instancie(base, vu)                    # ¬(u∈S et u∈D∖S)
    # S = dom grg
    h_dom = N.assume(egal(E.dom(grg), vs))
    s_eq_dom = N.modus_ponens(h_dom, symetrie(E.dom(grg), vs))    # S = dom grg
    # D∖S = dom R   (R_domaine : dom R = D∖S, symétrisé)
    dr = R_domaine(va0, vs, vd)                     # dom R = D∖S
    DmS_eq_domR = N.modus_ponens(dr, symetrie(domR, DmS))        # D∖S = dom R
    # réécrire S → dom grg  (membre gauche)
    ctx_left = non(et(appartient(vu, var("w")), appartient(vu, DmS)))
    step1 = N.modus_ponens(base_u, equivalence_avant(N.modus_ponens(s_eq_dom,
        N.s6(vs, E.dom(grg), "w", ctx_left))))      # ¬(u∈dom grg et u∈D∖S)
    # réécrire D∖S → dom R  (membre droit)
    ctx_right = non(et(appartient(vu, E.dom(grg)), appartient(vu, var("w"))))
    step2 = N.modus_ponens(step1, equivalence_avant(N.modus_ponens(DmS_eq_domR,
        N.s6(DmS, domR, "w", ctx_right))))          # ¬(u∈dom grg et u∈dom R)
    return N.generalisation("u", step2)


# ── S ∪ (D∖S) = D  sous S⊆D ────────────────────────────────────────────────────
def _S_union_compl_D(s, d):
    """{ S⊆D } ⊢ S ∪ (D∖S) = D.

    z∈S∪(D∖S) ⇔ (z∈S ou (z∈D et ¬z∈S)) ; ⇒ : z∈S⇒z∈D (S⊆D), sinon z∈D directement ;
    ⇐ : z∈D ; soit z∈S (gauche), soit ¬z∈S et alors z∈D∖S (droite)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    vs, vd = _t(s), _t(d)
    DmS = _compl(vs, vd)
    U = E.reunion(vs, DmS)
    vz = var("z")
    zS, zD = appartient(vz, vs), appartient(vz, vd)
    h_sub = N.assume(inclus(vs, vd))                       # (∀z)(z∈S⇒z∈D)
    sub_z = instancie(h_sub, vz)                          # z∈S ⇒ z∈D
    ax_un = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    car_un = instancie(instancie(instancie(ax_un, vs), DmS), vz)   # z∈U ⇔ (z∈S ou z∈D∖S)
    ax_diff = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    car_diff = instancie(instancie(instancie(ax_diff, vd), vs), vz)  # z∈D∖S ⇔ (z∈D et ¬z∈S)

    # ── ⇒ : z∈U ⇒ z∈D ───────────────────────────────────────────────────────────
    hL = N.assume(appartient(vz, U))
    disj = N.modus_ponens(hL, equivalence_avant(car_un))   # z∈S ou z∈D∖S
    brS = N.loi_deduction(zS, N.modus_ponens(N.assume(zS), sub_z))   # z∈S ⇒ z∈D
    h_diff = N.assume(appartient(vz, DmS))
    zD_fromdiff = conjonction_elim_gauche(N.modus_ponens(h_diff, equivalence_avant(car_diff)))
    brD = N.loi_deduction(appartient(vz, DmS), zD_fromdiff)  # z∈D∖S ⇒ z∈D
    zD_L = cas(disj, brS, brD)                            # z∈D
    fwd = N.generalisation("z", N.loi_deduction(appartient(vz, U), zD_L))   # U⊂D

    # ── ⇐ : z∈D ⇒ z∈U  (tertium : z∈S ou ¬z∈S) ─────────────────────────────────
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import tiers_exclu
    zDmS = appartient(vz, DmS)
    hR = N.assume(zD)
    tnd = tiers_exclu(zS)                                  # z∈S ou ¬z∈S
    # z∈S ⇒ z∈U  (injection gauche)
    inU_fromS = N.loi_deduction(zS, N.modus_ponens(N.modus_ponens(N.assume(zS),
        N.s2(zS, zDmS)), equivalence_arriere(car_un)))    # z∈S ⇒ z∈U
    # ¬z∈S ⇒ z∈U  (z∈D∖S via car_diff, puis injection droite : (z∈D∖S)⇒(z∈S ou z∈D∖S))
    h_nS = N.assume(non(zS))
    z_in_diff = N.modus_ponens(conjonction_intro(hR, h_nS), equivalence_arriere(car_diff))  # z∈D∖S
    diff_to_disj = N.modus_ponens(N.modus_ponens(z_in_diff, N.s2(zDmS, zS)),
                                  N.s3(zDmS, zS))          # z∈S ou z∈D∖S
    inU_fromnS = N.loi_deduction(non(zS),
        N.modus_ponens(diff_to_disj, equivalence_arriere(car_un)))   # ¬z∈S ⇒ z∈U
    zU_R = cas(tnd, inU_fromS, inU_fromnS)                # z∈U  (sous z∈D)
    bwd = N.generalisation("z", N.loi_deduction(zD, zU_R))   # D⊂U
    ext = extensionnalite_appliquee(U, vd)
    return N.modus_ponens(conjonction_intro(fwd, bwd), ext)   # S∪(D∖S)=D


# ── ĝ : fonctionnel, dom = D, ĝ ⊂ D×A  (sous {g∈𝓕(S;A), S⊆D, a₀∈A}) ───────────
def _ghat_fonctionnel(vg, va0, vs, vd, va):
    """{ g∈𝓕(S;A), a₀∈A } ⊢ est_fonctionnel(ĝ).   (recollement de graphes
    fonctionnels à domaines disjoints.)"""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import reunion_graphes_fonctionnelle
    grg = R_graphes_g = graphe_de(vg)
    R = R_terme(va0, vs, vd)
    _incl, g_func, g_dom = _struct_g(vg, vs, va)          # graphe_de(g) fonctionnel, dom=S
    r_func = R_fonctionnel(va0, vs, vd)                   # R fonctionnel
    disj = _ghat_disjonction(vg, vs, va0, vd)            # (∀u)¬(u∈dom grg et u∈dom R)  [dom grg=S]
    disj = _cut(disj, [(egal(E.dom(grg), vs), g_dom)])   # décharge dom grg=S
    base = reunion_graphes_fonctionnelle(grg, R)         # {func grg, func R, disj} ⊢ func(grg∪R)
    disj_form = pourtout("u", non(et(appartient(var("u"), E.dom(grg)),
                                     appartient(var("u"), E.dom(R)))))
    return _cut(base, [(E.est_fonctionnel(grg), g_func),
                       (E.est_fonctionnel(R), r_func),
                       (disj_form, disj)])


def _ghat_domaine(vg, va0, vs, vd, va):
    """{ g∈𝓕(S;A), S⊆D } ⊢ dom(ĝ) = D.

    dom(grg∪R)=dom grg ∪ dom R (dom_reunion_graphes) = S ∪ (D∖S) (dom grg=S, dom R=D∖S)
    = D (_S_union_compl_D, sous S⊆D)."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import dom_reunion_graphes
    grg = graphe_de(vg)
    R = R_terme(va0, vs, vd)
    DmS = _compl(vs, vd)
    _incl, _func, g_dom = _struct_g(vg, vs, va)          # dom grg=S
    r_dom = R_domaine(va0, vs, vd)                       # dom R=D∖S
    domGuH = E.dom(E.reunion(grg, R))
    dom_un = dom_reunion_graphes(grg, R)                 # dom(grg∪R)=dom grg ∪ dom R
    # réécrire dom grg→S  (Leibniz sur le 1ᵉʳ membre de la réunion-image)
    step1 = N.modus_ponens(dom_un, equivalence_avant(N.modus_ponens(g_dom,
        N.s6(E.dom(grg), vs, "w", egal(domGuH, E.reunion(var("w"), E.dom(R)))))))   # =S∪dom R
    # réécrire dom R→D∖S
    step2 = N.modus_ponens(step1, equivalence_avant(N.modus_ponens(r_dom,
        N.s6(E.dom(R), DmS, "w", egal(domGuH, E.reunion(vs, var("w")))))))          # =S∪(D∖S)
    # S∪(D∖S)=D  (sous S⊆D) ; chaîner
    su = _S_union_compl_D(vs, vd)                        # S∪(D∖S)=D
    return composer_egalites(step2, su)                  # dom(grg∪R)=D


def _produit_mono_gauche(s, d, a):
    """{ S⊆D } ⊢ S×A ⊂ D×A.   (produit_inclusion_facile avec A⊂A réflexif.)"""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import produit_inclusion_facile
    vs, vd, va = _t(s), _t(d), _t(a)
    # produit_inclusion_facile : ((S⊂D) et (A⊂A)) ⇒ S×A⊂D×A
    pif = produit_inclusion_facile("A", "B", "Ap", "Bp")
    pif = instancie(instancie(instancie(instancie(N.generalisation("A",
        N.generalisation("B", N.generalisation("Ap", N.generalisation("Bp", pif)))),
        vd), va), vs), va)                              # ((S⊂D) et (A⊂A)) ⇒ S×A⊂D×A
    refl_AA = _inclus_reflexif(va)                      # A⊂A
    h_sub = N.assume(inclus(vs, vd))
    return N.modus_ponens(conjonction_intro(h_sub, refl_AA), pif)   # S×A⊂D×A  [S⊆D]


def _inclus_reflexif(a):
    """⊢ A ⊂ A."""
    va = _t(a)
    vz = var("z")
    return N.generalisation("z", N.loi_deduction(appartient(vz, va), N.assume(appartient(vz, va))))


def _ghat_inclus(vg, va0, vs, vd, va):
    """{ g∈𝓕(S;A), S⊆D, a₀∈A } ⊢ ĝ ⊂ D×A.

    z∈grg∪R ⇒ z∈grg (⊂S×A⊂D×A) ou z∈R (⊂D×A)."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import membre_reunion_graphes
    grg = graphe_de(vg)
    R = R_terme(va0, vs, vd)
    GuH = E.reunion(grg, R)
    DA = E.produit(vd, va)
    vz = var("z")
    g_incl, _func, _dom = _struct_g(vg, vs, va)          # grg⊂S×A
    sa_da = _produit_mono_gauche(vs, vd, va)            # S×A⊂D×A  [S⊆D]
    grg_inDA = N.generalisation("z", N.loi_deduction(appartient(vz, grg),
        N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, grg)), instancie(g_incl, vz)),
                       instancie(sa_da, vz))))           # grg⊂D×A  [g∈𝓕,S⊆D]
    r_incl = _R_inclus(va0, vs, vd, va)                 # R⊂D×A  [a₀∈A]
    car = membre_reunion_graphes(grg, R, vz)            # z∈grg∪R ⇔ (z∈grg ou z∈R)
    h_z = N.assume(appartient(vz, GuH))
    disj = N.modus_ponens(h_z, equivalence_avant(car))  # z∈grg ou z∈R
    brG = N.loi_deduction(appartient(vz, grg),
        N.modus_ponens(N.assume(appartient(vz, grg)), instancie(grg_inDA, vz)))
    brR = N.loi_deduction(appartient(vz, R),
        N.modus_ponens(N.assume(appartient(vz, R)), instancie(r_incl, vz)))
    z_inDA = cas(disj, brG, brR)
    return N.generalisation("z", N.loi_deduction(appartient(vz, GuH), z_inDA))   # ĝ⊂D×A


# ── ((ĝ,D),A) ∈ 𝓕(D;A)  (BIEN-DÉFINITION) ────────────────────────────────────
def triple_ghat_dans_applications(vg, va0, vs, vd, va):
    """{ g∈𝓕(S;A), S⊆D, a₀∈A } ⊢ ((ĝ,D),A) ∈ 𝓕(D;A)."""
    from bourbaki.cardinaux.ensembles_eq_exposant_invariant import (
        _dans_exposant, _triple_dans_applications)
    RG = _ghat(vg, va0, vs, vd)
    in_exp = _dans_exposant(va, vd, RG,
        _ghat_inclus(vg, va0, vs, vd, va),
        _ghat_fonctionnel(vg, va0, vs, vd, va),
        _ghat_domaine(vg, va0, vs, vd, va))
    return _triple_dans_applications(va, vd, RG, in_exp)


__all__ = ["support_monotone_exposant", "exposant_monotone_exposant"]


# ═══════════════════════════════════════════════════════════════════════════════
#  INJECTIVITÉ de Ψ  :  ĝ₁ = ĝ₂  ⇒  g₁ = g₂.
#    ĝᵢ coïncide avec graphe_de(gᵢ) sur S (valeur_reunion_gauche) ; ĝ₁=ĝ₂ ⇒
#    ∀s∈S g₁(s)=g₂(s) ⇒ (application_egale_par_valeurs) g₁=g₂.
# ═══════════════════════════════════════════════════════════════════════════════
def _ghat_coincide_S(vg, va0, vs, vd, va, s_nom):
    """{ g∈𝓕(S;A), a₀∈A, s∈S } ⊢ valeur(ĝ, s) = valeur(graphe_de g, s)  (binder «y»).

    valeur_reunion_gauche(grg, R, s) sous {func grg, func R, disj, s∈dom grg} ; déchargé
    par _struct_g (func, dom grg=S ⇒ s∈dom grg de s∈S) et R_fonctionnel et la disjonction."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import valeur_reunion_gauche
    grg = graphe_de(vg)
    R = R_terme(va0, vs, vd)
    vs_pt = var(s_nom)
    _incl, g_func, g_dom = _struct_g(vg, vs, va)
    r_func = R_fonctionnel(va0, vs, vd)
    disj = _cut(_ghat_disjonction(vg, vs, va0, vd), [(egal(E.dom(grg), vs), g_dom)])
    disj_form = pourtout("u", non(et(appartient(var("u"), E.dom(grg)),
                                     appartient(var("u"), E.dom(R)))))
    # s∈dom grg  (de s∈S et dom grg=S)
    h_s = N.assume(appartient(vs_pt, vs))
    s_in_domgrg = N.modus_ponens(h_s, equivalence_avant(N.modus_ponens(
        N.modus_ponens(g_dom, symetrie(E.dom(grg), vs)),
        N.s6(vs, E.dom(grg), "w", appartient(vs_pt, var("w"))))))   # s∈dom grg
    vr = valeur_reunion_gauche(grg, R, vs_pt)   # {func grg, func R, disj, s∈dom grg}⊢ val(ĝ,s)=val(grg,s)
    return _cut(vr, [(E.est_fonctionnel(grg), g_func),
                     (E.est_fonctionnel(R), r_func),
                     (disj_form, disj),
                     (appartient(vs_pt, E.dom(grg)), s_in_domgrg)])


def _g_egalite_valeurs_ext(vg1, vg2, va0, vs, vd, va):
    """{ g₁,g₂∈𝓕(S;A), a₀∈A, ĝ₁=ĝ₂ }
       ⊢ (∀x)(x∈S ⇒ valeur(graphe_de g₁,x)=valeur(graphe_de g₂,x)).

    val(ĝ₁,s)=val(grg₁,s), val(ĝ₂,s)=val(grg₂,s) (_ghat_coincide_S) ; ĝ₁=ĝ₂ ⇒
    val(ĝ₁,s)=val(ĝ₂,s) (congruence) ; donc val(grg₁,s)=val(grg₂,s)."""
    g1hat = _ghat(vg1, va0, vs, vd)
    g2hat = _ghat(vg2, va0, vs, vd)
    grg1, grg2 = graphe_de(vg1), graphe_de(vg2)
    vs_pt = var("s")
    # val(ĝ₁,s)=val(grg₁,s) , val(ĝ₂,s)=val(grg₂,s)
    co1 = _ghat_coincide_S(vg1, va0, vs, vd, va, "s")   # {g₁∈𝓕,a₀∈A,s∈S}
    co2 = _ghat_coincide_S(vg2, va0, vs, vd, va, "s")   # {g₂∈𝓕,a₀∈A,s∈S}
    g1hat_s = E.valeur(g1hat, vs_pt)
    g2hat_s = E.valeur(g2hat, vs_pt)
    grg1_s = E.valeur(grg1, vs_pt)
    grg2_s = E.valeur(grg2, vs_pt)
    # ĝ₁=ĝ₂ ⇒ val(ĝ₁,s)=val(ĝ₂,s)
    h_eq = N.assume(egal(g1hat, g2hat))
    ghat_s_eq = N.modus_ponens(h_eq, congruence_terme(g1hat, g2hat, E.valeur(var("w"), vs_pt)))
    # val(grg₁,s) = val(ĝ₁,s) = val(ĝ₂,s) = val(grg₂,s)
    grg1_eq_g1hat = N.modus_ponens(co1, symetrie(g1hat_s, grg1_s))   # val(grg₁,s)=val(ĝ₁,s)
    chain = composer_egalites(composer_egalites(grg1_eq_g1hat, ghat_s_eq), co2)  # val(grg₁,s)=val(grg₂,s)
    imp = N.loi_deduction(appartient(vs_pt, vs), chain)
    raw = N.generalisation("s", imp)
    inst = instancie(raw, var("x"))
    return N.generalisation("x", inst)


def psi_injective_sous_appartenance(g1, g2, va0, vs, vd, va):
    """{ g₁,g₂∈𝓕(S;A), a₀∈A, ĝ₁=ĝ₂ } ⊢ g₁ = g₂."""
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
        application_egale_par_valeurs, egalite_valeurs_application)
    vg1, vg2 = _t(g1), _t(g2)
    eva = _g_egalite_valeurs_ext(vg1, vg2, va0, vs, vd, va)
    base = application_egale_par_valeurs(vg1, vg2, vs, va)
    target_eva = egalite_valeurs_application(vg1, vg2, vs)
    assert eva.conclusion == target_eva, "egalite_valeurs ext != attendu"
    return _cut(base, [(target_eva, eva)])


# ═══════════════════════════════════════════════════════════════════════════════
#  L'INJECTION  Ψ : 𝓕(S;A) ↪ 𝓕(D;A),  témoin W = graphe de Ψ (graphe_terme).
#    Ψ(g) := ((ĝ,D),A),  W := graphe_terme( 𝓕(S;A) , Ψ(g) , «g» ).
# ═══════════════════════════════════════════════════════════════════════════════
def _source_ext(s, a):
    return E.applications(_t(s), _t(a))


def _but_ext(d, a):
    return E.applications(_t(d), _t(a))


def _psi_valeur(g, va0, vs, vd, va):
    """Ψ(g) := ((ĝ,D),A)."""
    return E.couple(E.couple(_ghat(g, va0, vs, vd), _t(vd)), _t(va))


def W_psi(va0, vs, vd, va):
    return E.graphe_terme(_source_ext(vs, va), _psi_valeur(var(_POINT), va0, vs, vd, va), _POINT)


def W_psi_fonctionnel(va0, vs, vd, va):
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    return graphe_terme_fonctionnel(_source_ext(vs, va), _psi_valeur(var(_POINT), va0, vs, vd, va), _POINT, "y")


def W_psi_domaine(va0, vs, vd, va):
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_domaine
    return graphe_terme_domaine(_source_ext(vs, va), _psi_valeur(var(_POINT), va0, vs, vd, va), _POINT, "y", "z")


def W_psi_valeur(point_nom, va0, vs, vd, va):
    """{g ∈ 𝓕(S;A)} ⊢ W(g) = Ψ(g)."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_valeur
    return graphe_terme_valeur(_source_ext(vs, va), _psi_valeur(var(_POINT), va0, vs, vd, va),
                               point_nom, _POINT, "y")


def _psi_cod_en_point(va0, vs, vd, va, vg, g_in_thm):
    """{g∈𝓕(S;A), S⊆D, a₀∈A} ⊢ Ψ(g) ∈ 𝓕(D;A)."""
    base = triple_ghat_dans_applications(var(_POINT), va0, vs, vd, va)   # {pt∈𝓕(S;A),S⊆D,a₀∈A}
    base_imp = N.loi_deduction(appartient(var(_POINT), _source_ext(vs, va)), base)
    gen = N.generalisation(_POINT, base_imp)
    inst = instancie(gen, vg)
    return N.modus_ponens(g_in_thm, inst)


def W_psi_image_incluse(va0, vs, vd, va):
    """{ S⊆D, a₀∈A } ⊢ image(W, 𝓕(S;A)) ⊂ 𝓕(D;A).   (BIEN-DÉFINITION.)"""
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
    dom = _source_ext(vs, va)
    cod = _but_ext(vd, va)
    W = W_psi(va0, vs, vd, va)
    PSI = _psi_valeur(var(_POINT), va0, vs, vd, va)
    vz, vk = var("z"), var("t")

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), dom), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), dom), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "t", inner)
    img_car = equivalence_transitivite(img0, ren)

    mem = membre_graphe_terme(dom, PSI, "t", "z", _POINT, "y")
    Psi_t = subst_t(vk, _POINT, PSI)
    body = et(appartient(vk, dom), appartient(E.couple(vk, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)
    tz_in = conjonction_elim_droite(hb)
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))
    z_eq = conjonction_elim_droite(cond)
    psi_t_in = _psi_cod_en_point(va0, vs, vd, va, vk, t_in)
    z_in_cod = N.modus_ponens(psi_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Psi_t, "w", appartient(var("w"), cod)))))
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), "t")
    h_z = N.assume(appartient(vz, E.image(W, dom)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))
    z_in = N.modus_ponens(ex, ex_imp)
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, dom)), z_in))


def _psi_egal_donne_ghat(vg1, vg2, va0, vs, vd, va):
    """{ Ψ(g₁)=Ψ(g₂) } ⊢ ĝ₁=ĝ₂."""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    g1hat, g2hat = _ghat(vg1, va0, vs, vd), _ghat(vg2, va0, vs, vd)
    L1, L2 = _psi_valeur(vg1, va0, vs, vd, va), _psi_valeur(vg2, va0, vs, vd, va)
    inner1, inner2 = E.couple(g1hat, vd), E.couple(g2hat, vd)
    h = N.assume(egal(L1, L2))
    comp1 = N.modus_ponens(h, couple_egal_implique_composantes(inner1, va, inner2, va))
    inner_eq = conjonction_elim_gauche(comp1)
    comp2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(g1hat, vd, g2hat, vd))
    return conjonction_elim_gauche(comp2)


def W_psi_injective(va0, vs, vd, va):
    """{ a₀∈A, S⊆D } ⊢ injective_dans(W, 𝓕(S;A))."""
    dom = _source_ext(vs, va)
    Wt = W_psi(va0, vs, vd, va)
    vg1, vg2 = var("g1"), var("g2")
    L1, L2 = _psi_valeur(vg1, va0, vs, vd, va), _psi_valeur(vg2, va0, vs, vd, va)
    g1hat, g2hat = _ghat(vg1, va0, vs, vd), _ghat(vg2, va0, vs, vd)

    hyp = et(et(appartient(vg1, dom), appartient(vg2, dom)),
             egal(E.valeur(Wt, vg1), E.valeur(Wt, vg2)))
    h = N.assume(hyp)
    g1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    g2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)
    Wg1 = _cut(W_psi_valeur("g1", va0, vs, vd, va), [(appartient(vg1, dom), g1_in)])
    Wg2 = _cut(W_psi_valeur("g2", va0, vs, vd, va), [(appartient(vg2, dom), g2_in)])
    psi_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wg1, symetrie(E.valeur(Wt, vg1), L1)), W_eq), Wg2)   # Ψ(g₁)=Ψ(g₂)
    ghat_eq = _cut(_psi_egal_donne_ghat(vg1, vg2, va0, vs, vd, va), [(egal(L1, L2), psi_eq)])
    g_eq = psi_injective_sous_appartenance("g1", "g2", va0, vs, vd, va)
    g_eq = _cut(g_eq, [(appartient(vg1, dom), g1_in),
                       (appartient(vg2, dom), g2_in),
                       (egal(g1hat, g2hat), ghat_eq)])
    inner = N.loi_deduction(hyp, g_eq)
    raw = N.generalisation("g1", N.generalisation("g2", inner))
    inst = instancie(instancie(raw, var("u")), var("up"))
    return N.generalisation("u", N.generalisation("up", inst))


def W_psi_est_injection(va0, vs, vd, va):
    """{ a₀∈A, S⊆D } ⊢ est_injection_de(W, 𝓕(S;A), 𝓕(D;A))."""
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_psi_fonctionnel(va0, vs, vd, va), W_psi_domaine(va0, vs, vd, va)),
        W_psi_injective(va0, vs, vd, va)), W_psi_image_incluse(va0, vs, vd, va))


def support_extension_domaine(s="S", d="D", a0="a0", a="A"):
    """{ S⊆D, a₀∈A } ⊢ inf_egal_card(𝓕(S;A), 𝓕(D;A))."""
    vs, vd, va0, va = _t(s), _t(d), _t(a0), _t(a)
    dom = _source_ext(vs, va)
    cod = _but_ext(vd, va)
    Wt = W_psi(va0, vs, vd, va)
    inj = W_psi_est_injection(va0, vs, vd, va)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), dom, cod), Wt, "F"))


# ═══════════════════════════════════════════════════════════════════════════════
#  CHAÎNE Paliers 1+2  ⇒  support_monotone_exposant.
# ═══════════════════════════════════════════════════════════════════════════════
def _support_sous_kappa_a0(vc, vd, va, vk, va0):
    """{ est_injection_de(κ,C,D), a₀∈A } ⊢ inf_egal_card(𝓕(C;A), 𝓕(D;A)).

    Palier 1 (κ⁻¹ pré-comp) : 𝓕(C;A) ≤ 𝓕(κ⟨C⟩;A) ; Palier 2 (prolongement, S:=κ⟨C⟩
    avec κ⟨C⟩⊆D du 4ᵉ conjoint de l'injection) : 𝓕(κ⟨C⟩;A) ≤ 𝓕(D;A) ; transitivité."""
    from bourbaki.cardinaux.ensembles_cardinaux_ordre import inf_egal_transitive
    imgC = E.image(vk, vc)
    FCA = E.applications(vc, va)
    FimgA = E.applications(imgC, va)
    FDA = E.applications(vd, va)
    # Palier 1
    p1 = support_le_image(vk, vc, vd)                 # {inj(κ,C,D)} ⊢ 𝓕(C;A)≤𝓕(κ⟨C⟩;A)
    # κ⟨C⟩⊆D  (4ᵉ conjoint de est_injection_de)
    h_inj = N.assume(est_injection_de(vk, vc, vd))
    img_incl = conjonction_elim_droite(h_inj)         # image(κ,C)⊆D
    # Palier 2 : support_extension_domaine(S=κ⟨C⟩, D, a0, A) sous {κ⟨C⟩⊆D, a0∈A}
    p2 = support_extension_domaine(imgC, vd, va0, va)  # {κ⟨C⟩⊆D, a0∈A} ⊢ 𝓕(κ⟨C⟩;A)≤𝓕(D;A)
    p2 = _cut(p2, [(inclus(imgC, vd), img_incl)])     # {inj(κ,C,D), a0∈A} ⊢ 𝓕(κ⟨C⟩;A)≤𝓕(D;A)
    # transitivité : (𝓕(C;A)≤𝓕(κ⟨C⟩;A) et 𝓕(κ⟨C⟩;A)≤𝓕(D;A)) ⇒ 𝓕(C;A)≤𝓕(D;A)
    trans = inf_egal_transitive("F", "G", "X", "Y", "Z")
    trans = instancie(instancie(instancie(N.generalisation("X", N.generalisation("Y",
        N.generalisation("Z", trans))), FCA), FimgA), FDA)   # version TERME
    return N.modus_ponens(conjonction_intro(p1, p2), trans)   # 𝓕(C;A)≤𝓕(D;A)


def support_monotone_exposant(c="C", d="D", a="A"):
    """⊢ (C ≤ D  et  A ≠ ∅)  ⇒  (𝓕(C;A) ≤ 𝓕(D;A)).   (INCONDITIONNEL.)

    Décharge le témoin κ de C≤D=(∃F)inj(F,C,D) et le témoin a₀∈A de A≠∅
    (non_vide_ssi_element)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    vc, vd, va = _t(c), _t(d), _t(a)
    vk, va0 = var("kappa"), var("a0")
    inj_body = est_injection_de(vk, vc, vd)
    a0_body = appartient(va0, va)
    base = _support_sous_kappa_a0(vc, vd, va, vk, va0)   # {inj(κ,C,D), a0∈A} ⊢ 𝓕(C;A)≤𝓕(D;A)
    # décharger a0 : (∃a0)(a0∈A) ⇒ 𝓕(C;A)≤𝓕(D;A)
    imp_a0 = existe_elimination(N.loi_deduction(a0_body, base), "a0")   # (∃a0)(a0∈A) ⇒ … [inj]
    # A≠∅ ⇒ (∃z)(z∈A) ; α-renommer z→a0
    nve = non_vide_ssi_element(va)                      # ¬(A=∅) ⇔ (∃z)(z∈A)
    ex_z = N.modus_ponens(N.assume(non(egal(va, E.VIDE))), equivalence_avant(nve))  # (∃z)(z∈A)
    ren = alpha_existe("z", "a0", appartient(var("z"), va))   # (∃z)(z∈A) ⇔ (∃a0)(a0∈A)
    ex_a0 = N.modus_ponens(ex_z, equivalence_avant(ren))      # (∃a0)(a0∈A)  [A≠∅]
    concl_inj = N.modus_ponens(ex_a0, imp_a0)               # 𝓕(C;A)≤𝓕(D;A)  [inj, A≠∅]
    # décharger κ : (∃κ)inj(κ,C,D)=C≤D ⇒ …
    imp_k = existe_elimination(N.loi_deduction(inj_body, concl_inj), "kappa")  # C≤D ⇒ … [A≠∅]
    le_cd = inf_egal_card(vc, vd)                       # (∃F)inj(F,C,D)
    ren_k = alpha_existe("kappa", "F", est_injection_de(vk, vc, vd))  # (∃κ)inj ⇔ (∃F)inj
    concl_cd = N.modus_ponens(N.modus_ponens(N.assume(le_cd),
        equivalence_arriere(ren_k)), imp_k)             # 𝓕(C;A)≤𝓕(D;A)  [C≤D, A≠∅]
    # rassembler en (C≤D et A≠∅) ⇒ …
    hyp = et(le_cd, non(egal(va, E.VIDE)))
    h = N.assume(hyp)
    concl = _cut(concl_cd, [(le_cd, conjonction_elim_gauche(h)),
                            (non(egal(va, E.VIDE)), conjonction_elim_droite(h))])
    return N.loi_deduction(hyp, concl)                  # (C≤D et A≠∅) ⇒ 𝓕(C;A)≤𝓕(D;A)


# ═══════════════════════════════════════════════════════════════════════════════
#  FINAL — monotonie en l'EXPOSANT au niveau des CARDINAUX (INCONDITIONNEL) :
#      (c ≤ d  et  a ≠ 0)  ⇒  (a^c ≤ a^d),   a^c := exposant_cardinal_binaire(a,c)
#                                                  = Card(𝓕(c;a)).
#  Le « a ≠ 0 » est ¬(a=∅) : la valeur-défaut a₀∈a impose a non vide (cas Bourbaki
#  a ≠ 0 ; ici a joue le rôle du BUT A de l'exponentiation a^c=Card 𝓕(c;a)).
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_monotone_exposant(a="a", c="c", d="d"):
    """⊢ (c ≤ d  et  a ≠ 0)  ⇒  (a^c ≤ a^d).   (a^c = exposant_cardinal_binaire(a,c)
    = Card(𝓕(c;a)) ; a ≠ 0 := ¬(a=∅).)   INCONDITIONNEL, AUCUNE hyp de support.

    Chaîne (cf. exposant_monotone_base) :
      support_monotone_exposant(c,d,a) : (c≤d et a≠∅) ⇒ (𝓕(c;a) ≤ 𝓕(d;a))
      inf_egal_transporte_cardinal     : (𝓕(c;a)≤𝓕(d;a)) ⇒ (Card 𝓕(c;a) ≤ Card 𝓕(d;a))
    et Card 𝓕(c;a) = exposant_cardinal_binaire(a,c) (DÉFINITION 4)."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale_props_exposant_monotone import (
        inf_egal_transporte_cardinal)
    va, vc, vd = _t(a), _t(c), _t(d)
    Fca = E.applications(vc, va)             # 𝓕(c;a)
    Fda = E.applications(vd, va)             # 𝓕(d;a)
    # support sur NOMS FRAIS (C,D,A ≠ binders internes), généralisé puis instancié aux TERMES
    sm = support_monotone_exposant("C", "D", "A")   # (C≤D et A≠∅) ⇒ (𝓕(C;A)≤𝓕(D;A))
    sm_gen = N.generalisation("C", N.generalisation("D", N.generalisation("A", sm)))
    sm_t = instancie(instancie(instancie(sm_gen, vc), vd), va)  # (c≤d et a≠∅) ⇒ (𝓕(c;a)≤𝓕(d;a))
    # transport (0) instancié aux supports
    transp_all = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))
    transp = instancie(instancie(transp_all, Fca), Fda)  # (𝓕(c;a)≤𝓕(d;a)) ⇒ (a^c ≤ a^d)
    # chaîne sous (c≤d et a≠0)
    hyp = et(inf_egal_card(vc, vd), non(egal(va, E.VIDE)))
    h = N.assume(hyp)
    sup = N.modus_ponens(h, sm_t)                  # 𝓕(c;a)≤𝓕(d;a)
    exp_le = N.modus_ponens(sup, transp)           # a^c ≤ a^d
    return N.loi_deduction(hyp, exp_le)
