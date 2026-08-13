"""§II.4.8 — LE RECOLLEMENT INDEXÉ : E ≅ ⊔_{y∈F} f⁻¹⟨{y}⟩  (P5-P7 de S3, la 🎯).

Suite de ensembles_somme_indexee (P0), ensembles_fibres_famille (P1-P2) et
ensembles_decomposition_fibres (P3-P4).  Ici :
  P6 decomposition_injective                ⊢ injective_dans(Φ, E)        [CLOS]
  P4/P5 decomposition_image {Hf1,Hf2,Hf3,HF} ⊢ image(Φ, E) = ⊔(Xfib, F)
  P7 decomposition_bijection {…}            ⊢ est_bijection_de(Φ, E, ⊔)
     eq_decomposition_fibres {…}            ⊢ Eq( E , somme_famille(Xfib, F) ) 🎯
     card_decomposition_fibres {…}          ⊢ Card(E) = Card(⊔(Xfib, F))
        — dont le RHS EST, terme à terme, somme_cardinale(Xfib, F) (asserté).

INJECTIVITÉ (bien plus courte que T1b-2 : PAS d'extensionnalité) : Φ(u)=Φ(u')
⇒ (u, f(u)[c]) = (u', f(u')[c]) ⇒ u=u' par PREMIÈRE composante (Prop. 1 couples).
SURJECTIVITÉ : s ∈ ⊔ se décompose (axiome-somme + produit-singleton) en
s=(u, i), u ∈ fibre(i) ; alors (u,i)∈f (image réciproque + réciproque +
singleton), donc u ∈ dom f = E et i = f(u) (C46), d'où s = T[u] et (u,s)∈Φ.

HYPOTHÈSES HONNÊTES (exactement 4, cf. ensembles_fibres_famille) :
  Hf1 func f · Hf2 dom f=E · Hf3 (∀x∈E)f(x)∈F · HF pont fam↔valeur (mur T1c).
Rien postulé ; noyau/subst intouchés ; theorie_ensembles()==22 (asserté en test).
LIANTS EXOTIQUES locaux : sfb (élément de ⊔), tfb (liant image), ufb
(antécédent), ifb (indice ∃ renommé), wfb1 (témoin img. réciproque), wfb (trous
Leibniz/congruence), bfb/zfb (liants C54), uaf/ubf (points P6).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, appartient, existe, subst_t, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a, syllogisme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    egalite_par_extension)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre, couple_egal_implique_composantes)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_caracterisation)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    membre_graphe_terme)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    _membre_produit_singleton)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_indexee import (
    membre_somme_famille)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    _t, _dech, fibre, famille_fibres, somme_fibres, hypothese_fonctionnelle,
    hypothese_domaine, hypothese_valeurs, hypothese_pont_fam, fam_fibre_egale)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_decomposition_fibres import (
    XB, VC, terme_marquage, graphe_marquage, valeur_y_egal_cfb,
    marquage_fonctionnel, marquage_domaine, marquage_valeur, marque_dans_somme)


# ── P6 : INJECTIVITÉ  ⊢ injective_dans(Φ, E)  [CLOS] ─────────────────────────
def decomposition_injective(f="ffb", e="Efb"):
    """P6 ⊢ injective_dans(Φ, E)                                        [CLOS].

    Φ(uaf)=Φ(ubf) donne (uaf, f(uaf)[c]) = (ubf, f(ubf)[c]) (P3c des deux côtés)
    puis uaf=ubf par PREMIÈRE composante (Prop. 1).  Preuve sur points EXOTIQUES
    uaf/ubf, puis ∀-clôture + ré-instanciation en u/up (liants figés de
    injective_dans) — motif exact de T1b-2 P6, sans extensionnalité."""
    ve = _t(e)
    Phi, T = graphe_marquage(f, e), terme_marquage(f)
    vu, vup = var("uaf"), var("ubf")
    fca = E.valeur(_t(f), vu, b=VC)
    fcb = E.valeur(_t(f), vup, b=VC)
    hyp = et(et(appartient(vu, ve), appartient(vup, ve)),
             egal(E.valeur(Phi, vu), E.valeur(Phi, vup)))
    h = N.assume(hyp)
    uin = conjonction_elim_gauche(conjonction_elim_gauche(h))
    upin = conjonction_elim_droite(conjonction_elim_gauche(h))
    val_eq = conjonction_elim_droite(h)
    av_u = _dech(marquage_valeur("uaf", f, e), uin)         # Φ(uaf) = T[uaf]
    av_up = _dech(marquage_valeur("ubf", f, e), upin)       # Φ(ubf) = T[ubf]
    Tua = subst_t(vu, XB, T)
    eq_T = composer_egalites(composer_egalites(
        N.modus_ponens(av_u, symetrie(E.valeur(Phi, vu), Tua)), val_eq), av_up)
    comps = N.modus_ponens(eq_T,
        couple_egal_implique_composantes(vu, fca, vup, fcb))
    u_eq = conjonction_elim_gauche(comps)                   # uaf = ubf
    gen_ex = N.generalisation("uaf", N.generalisation("ubf",
        N.loi_deduction(hyp, u_eq)))
    inst = instancie(instancie(gen_ex, var("u")), var("up"))
    res = N.generalisation("u", N.generalisation("up", inst))
    assert res.conclusion == E.injective_dans(Phi, ve), "P6 : forme"
    assert res.est_clos, "P6 : non clos"
    return res


# ── P4/P5 : IMAGE  {Hf1, Hf2, Hf3, HF} ⊢ image(Φ, E) = ⊔(Xfib, F) ────────────
# @livre Ch.II §4.8 Rem.- | E II.30 L.11-14 | PDF p.81
#   (le marquage atteint TOUTE la somme : l'antécédent de (u, i) est u lui-même,
#    qui est dans la fibre de i donc dans E, avec f(u)=i.)
def decomposition_image(f="ffb", e="Efb", b="Ffb"):
    """P4/P5 {Hf1, Hf2, Hf3, HF} ⊢ image(Φ, E) = ⊔_{y∈F} f⁻¹⟨{y}⟩.

    ⊂ (P4) : s=T[t]=(t, f(t)[c]) avec t∈E tombe dans la somme (marque_dans_somme).
    ⊃ (P5, surjectivité) : s∈⊔ ⇒ s=(u,i), u∈fibre(i) ⇒ (u,i)∈f ⇒ u∈dom f=E,
    i=f(u) (C46) ⇒ s=T[u] et (u,s)∈Φ (axiome C54, témoins xfb:=u, bfb:=s).
    Élément « sfb », α-renommé en « z » pour l'extension finale (motif T1b-2)."""
    vf, ve, vb = _t(f), _t(e), _t(b)
    X = famille_fibres(f, b)
    Phi, T = graphe_marquage(f, e), terme_marquage(f)
    S = somme_fibres(f, b)
    vs, vt, vu, vi = var("sfb"), var("tfb"), var("ufb"), var("ifb")

    # caractérisation de l'image (AXIOME_IMAGE, liant ∃ renommé x→tfb)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, Phi), ve), vs)
    ren = alpha_existe("x", "tfb", et(appartient(var("x"), ve),
                                      appartient(E.couple(var("x"), vs), Phi)))
    img_car = equivalence_transitivite(img_car0, ren)   # s∈Φ⟨E⟩ ⇔ (∃tfb)(tfb∈E et (tfb,s)∈Φ)
    corpsR = et(appartient(vt, ve), appartient(E.couple(vt, vs), Phi))

    # ── P4 (⊂) : sous (t∈E et (t,s)∈Φ), s = T[t] ∈ ⊔ ──────────────────────────
    hbR = N.assume(corpsR)
    t_in = conjonction_elim_gauche(hbR)
    cpl_in = conjonction_elim_droite(hbR)
    mem = membre_graphe_terme(ve, T, "tfb", "sfb", XB, "bfb")  # ((t,s)∈Φ) ⇔ (t∈E et s=T[t])
    s_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem)))
    Tt = subst_t(vt, XB, T)
    mds = _dech(marque_dans_somme("tfb", f, e, b), t_in)       # T[t] ∈ ⊔
    leib_s = N.modus_ponens(s_eq_Tt, N.s6(vs, Tt, "wfb", appartient(var("wfb"), S)))
    s_in_S = N.modus_ponens(mds, equivalence_arriere(leib_s))  # s ∈ ⊔
    fwd = existe_elimination(N.loi_deduction(corpsR, s_in_S), "tfb")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)     # s∈Φ⟨E⟩ ⇒ s∈⊔

    # ── P5 (⊃) : sous s∈⊔, l'antécédent est u (s=(u,i), u∈fibre(i)) ───────────
    corps_i = et(appartient(var("i"), vb),
                 appartient(vs, E.produit(E.valeur_famille(X, var("i")),
                                          E.singleton(var("i")))))
    som_car = equivalence_transitivite(membre_somme_famille(X, vb, vs),
                                       alpha_existe("i", "ifb", corps_i))
    corps_ifb = subst_f(vi, "i", corps_i)              # (ifb∈F et s∈fam(X,ifb)×{ifb})
    hb = N.assume(corps_ifb)
    i_in = conjonction_elim_gauche(hb)                 # ifb ∈ F
    prod_in = conjonction_elim_droite(hb)              # s ∈ fam(X,ifb)×{ifb}
    # fam(X, ifb) = fibre(ifb)  (P1c) puis transport de s (trou wfb)
    fam_eq = fam_fibre_egale(i_in, vi, f, b)
    leib_f = N.modus_ponens(fam_eq, N.s6(E.valeur_famille(X, vi), fibre(f, vi),
        "wfb", appartient(vs, E.produit(var("wfb"), E.singleton(vi)))))
    prod_in2 = N.modus_ponens(prod_in, equivalence_avant(leib_f))  # s ∈ fibre(ifb)×{ifb}
    mps = _membre_produit_singleton(fibre(f, vi), vi, vs, "ufb")
    ex_u = N.modus_ponens(prod_in2, equivalence_avant(mps))    # (∃ufb)(ufb∈fibre et s=(ufb,ifb))
    inner = et(appartient(vu, fibre(f, vi)), egal(vs, E.couple(vu, vi)))
    hi = N.assume(inner)
    u_in_fib = conjonction_elim_gauche(hi)
    s_eq_cpl = conjonction_elim_droite(hi)
    # (u, ifb) ∈ f  (image réciproque + réciproque + singleton, témoin wfb1)
    mir0 = instancie(instancie(instancie(ax_img, E.reciproque(vf)),
                               E.singleton(vi)), vu)
    ren_w = alpha_existe("x", "wfb1", et(appartient(var("x"), E.singleton(vi)),
        appartient(E.couple(var("x"), vu), E.reciproque(vf))))
    mir = equivalence_transitivite(mir0, ren_w)
    ex_w = N.modus_ponens(u_in_fib, equivalence_avant(mir))
    corpsW = et(appartient(var("wfb1"), E.singleton(vi)),
                appartient(E.couple(var("wfb1"), vu), E.reciproque(vf)))
    hw = N.assume(corpsW)
    w_eq_i = N.modus_ponens(conjonction_elim_gauche(hw),
        equivalence_avant(singleton_membre(var("wfb1"), vi)))  # wfb1 = ifb
    uw_in_f = N.modus_ponens(conjonction_elim_droite(hw),
        equivalence_avant(couple_reciproque(vf, var("wfb1"), vu)))  # (u,wfb1)∈f
    tr = N.modus_ponens(w_eq_i, N.s6(var("wfb1"), vi, "wfb",
        appartient(E.couple(vu, var("wfb")), vf)))
    ui_in_f0 = N.modus_ponens(uw_in_f, equivalence_avant(tr))  # (u, ifb)∈f
    ui_in_f = N.modus_ponens(ex_w,
        existe_elimination(N.loi_deduction(corpsW, ui_in_f0), "wfb1"))
    # u ∈ dom f = E
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vf), vu)
    ex_y = N.modus_ponens(ui_in_f,
        N.s5(appartient(E.couple(vu, var("y")), vf), vi, "y"))  # (∃y)((u,y)∈f)
    u_in_dom = N.modus_ponens(ex_y, equivalence_arriere(dom_car))
    h2 = N.assume(hypothese_domaine(f, e))
    leib_dom = N.modus_ponens(h2, N.s6(E.dom(vf), ve, "wfb",
                                       appartient(vu, var("wfb"))))
    u_in_E = N.modus_ponens(u_in_dom, equivalence_avant(leib_dom))  # u ∈ E
    # i = f(u)  (C46, y ∀-clos puis instancié en ifb ; « func f » = Hf1 reste)
    vc = _dech(valeur_caracterisation(vf, vu), ex_y)
    vc_i = instancie(N.generalisation("y", vc), vi)    # ((u,ifb)∈f) ⇔ (ifb=f(u))
    i_eq_fu = N.modus_ponens(ui_in_f, equivalence_avant(vc_i))  # ifb = f(u)
    # s = (u, ifb) = (u, f(u)) = (u, f(u)[c]) = T[u]
    fu, fuc = E.valeur(vf, vu), E.valeur(vf, vu, b=VC)
    Tu = subst_t(vu, XB, T)
    assert Tu == E.couple(vu, fuc), "P5 : T[u] ≠ (u, f(u)[c])"
    c1 = N.modus_ponens(i_eq_fu,
        congruence_terme(vi, fu, E.couple(vu, var("wfb")), "wfb"))
    c2 = N.modus_ponens(valeur_y_egal_cfb(f, vu),
        congruence_terme(fu, fuc, E.couple(vu, var("wfb")), "wfb"))
    s_eq_T = composer_egalites(s_eq_cpl, composer_egalites(c1, c2))   # s = T[u]
    # (u, s) ∈ Φ  (axiome C54, témoins xfb:=u, bfb:=s)
    ax_P = N.axiome(E.theorie_graphe_terme(ve, T, XB, "bfb", "zfb"),
                    E.axiome_graphe_terme(ve, T, XB, "bfb", "zfb"))
    cpl_us = E.couple(vu, vs)
    car_us = instancie(ax_P, cpl_us)
    gcorps = et(et(egal(cpl_us, E.couple(var(XB), var("bfb"))),
                   appartient(var(XB), ve)), egal(var("bfb"), T))
    wit = conjonction_intro(conjonction_intro(N.reflexivite(cpl_us), u_in_E), s_eq_T)
    ex_b = N.modus_ponens(wit, N.s5(subst_f(vu, XB, gcorps), vs, "bfb"))
    ex_F = N.modus_ponens(ex_b, N.s5(existe("bfb", gcorps), vu, XB))
    cpl_in_Phi = N.modus_ponens(ex_F, equivalence_arriere(car_us))    # (u,s)∈Φ
    # s ∈ Φ⟨E⟩ puis décharges des trois ∃ (ufb, ifb) et de s∈⊔
    ex_t = N.modus_ponens(conjonction_intro(u_in_E, cpl_in_Phi),
                          N.s5(corpsR, vu, "tfb"))
    in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))       # s∈Φ⟨E⟩
    in_img = N.modus_ponens(ex_u,
        existe_elimination(N.loi_deduction(inner, in_img), "ufb"))
    imp_i = existe_elimination(N.loi_deduction(corps_ifb, in_img), "ifb")
    hs = N.assume(appartient(vs, S))
    ex_i = N.modus_ponens(hs, equivalence_avant(som_car))
    bwd_full = N.loi_deduction(appartient(vs, S), N.modus_ponens(ex_i, imp_i))

    # ── double inclusion → extension (élément « sfb » α-renommé en « z ») ─────
    equiv_s = conjonction_intro(fwd_full, bwd_full)    # s∈Φ⟨E⟩ ⇔ s∈⊔
    equiv_z = instancie(N.generalisation("sfb", equiv_s), var("z"))
    char_img = N.generalisation("z", equiv_z)
    zS = appartient(var("z"), S)
    self_S = N.generalisation("z", conjonction_intro(a_implique_a(zS), a_implique_a(zS)))
    res = egalite_par_extension(char_img, self_S, E.image(Phi, ve), S, "z")
    assert res.conclusion == egal(E.image(Phi, ve), S), "P4/P5 : forme"
    assert res.hypotheses == frozenset({
        hypothese_fonctionnelle(f), hypothese_domaine(f, e),
        hypothese_valeurs(f, e, b), hypothese_pont_fam(f, b)}), "P4/P5 : hyps"
    return res


# ── P7 : BIJECTION, ÉQUIPOTENCE, CARDINAL ─────────────────────────────────────
def decomposition_bijection(f="ffb", e="Efb", b="Ffb"):
    """P7 {Hf1, Hf2, Hf3, HF} ⊢ est_bijection_de(Φ, E, ⊔_{y∈F} f⁻¹⟨{y}⟩)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_bijection_de)
    res = conjonction_intro(
        conjonction_intro(marquage_fonctionnel(f, e), marquage_domaine(f, e)),
        conjonction_intro(decomposition_injective(f, e),
                          decomposition_image(f, e, b)))
    assert res.conclusion == est_bijection_de(graphe_marquage(f, e), _t(e),
                                              somme_fibres(f, b)), "P7 : forme"
    assert res.hypotheses == frozenset({
        hypothese_fonctionnelle(f), hypothese_domaine(f, e),
        hypothese_valeurs(f, e, b), hypothese_pont_fam(f, b)}), "P7 : hyps"
    return res


# @livre Ch.II §4.8 Rem.- | E II.30 L.11-14 | PDF p.81
#   (« Par abus de langage, on dit qu'un ensemble E est somme d'une famille
#    d'ensembles (X_ι)_{ι∈I} lorsqu'il existe une bijection de E sur la somme de
#    cette famille définie par la déf. 8 » — ICI : E EST somme de la famille de
#    ses fibres par f, le témoin étant le marquage x ↦ (x, f(x)).  C'est le
#    RECOLLEMENT INDEXÉ, socle des bergers (Prop.9 §III.5.5) et de Prop.4/5b.)
def eq_decomposition_fibres(f="ffb", e="Efb", b="Ffb"):
    """🎯 {Hf1, Hf2, Hf3, HF} ⊢ Eq( E , somme_famille(Xfib, F) ).   (S5, F frais.)"""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_bijection_de, equipotent)
    ve, S = _t(e), somme_fibres(f, b)
    bij = decomposition_bijection(f, e, b)
    res = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), ve, S),
                                   graphe_marquage(f, e), "F"))
    assert res.conclusion == equipotent(ve, S), "Eq : forme"
    assert len(res.hypotheses) == 4, "Eq : nb hyps"
    return res


# @livre Ch.III §3.3 Def.3 | E III.25 L.45-48 | PDF p.128
#   (le RHS est LITTÉRALEMENT ∑_{y∈F} du terme somme_cardinale — la forme
#    cardinale du recollement indexé, l'entrée des bergers.)
def card_decomposition_fibres(f="ffb", e="Efb", b="Ffb"):
    """{Hf1, Hf2, Hf3, HF} ⊢ Card(E) = Card(⊔(Xfib, F)) = somme_cardinale(Xfib, F)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal, somme_cardinale)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        _prop1_direct_t)
    ve, S = _t(e), somme_fibres(f, b)
    res = N.modus_ponens(eq_decomposition_fibres(f, e, b), _prop1_direct_t(ve, S))
    assert res.conclusion == egal(cardinal(ve), cardinal(S)), "Card : forme"
    assert cardinal(S) == somme_cardinale(famille_fibres(f, b), _t(b)), \
        "Card : le RHS n'est pas somme_cardinale(Xfib, F)"
    assert len(res.hypotheses) == 4, "Card : nb hyps"
    return res


__all__ = ["decomposition_injective", "decomposition_image",
           "decomposition_bijection", "eq_decomposition_fibres",
           "card_decomposition_fibres"]
