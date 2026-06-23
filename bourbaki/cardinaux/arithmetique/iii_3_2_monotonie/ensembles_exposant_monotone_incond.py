"""§III.3.5 — MONOTONIE DE L'EXPONENTIATION cardinale, INCONDITIONNELLE.

On DÉCHARGE ici les hypothèses de support des énoncés conditionnels
(`ensembles_arith_cardinale_props_exposant_monotone`) en CONSTRUISANT les
injections d'espaces de fonctions.

M1 — monotonie en la BASE :
    (A ≤ B)  ⇒  𝓕(C;A) ≤ 𝓕(C;B)      [post-composition par ι : A↪B]
puis, par le transport (0) et l'énoncé conditionnel :
    `exposant_monotone_base`  ⊢  (a ≤ b) ⇒ (a^c ≤ b^c).

CONSTRUCTION (M1).  Soit ι le graphe-témoin d'une injection A↪B (est_injection_de
(ι,A,B), 2ᵉ conjoint dom ι=A, 3ᵉ injective_dans(ι,A), 4ᵉ image(ι,A)⊂B).  À
g∈𝓕(C;A) on associe l'application Φ(g)=((K_g,C),B) où

    K_g := { (c, ι(g(c))) | c∈C }   (post-composée ι∘g, niveau GRAPHE)

avec g(c)=valeur(graphe_de(g),c,«r») et ι(g(c))=valeur(ι,g(c),«s»).
  • bien-définition : g(c)∈A (PONT valeur_dans_codomaine sur graphe_de(g)⊂C×A),
    ι(g(c))∈B (image(ι,A)⊂B ; ι(g(c))∈image(ι,A) car (g(c),ι(g(c)))∈ι) ⇒ K_g⊂C×B
    ⇒ K_g∈B^C ⇒ ((K_g,C),B)∈𝓕(C;B).
  • injectivité : K_g₁=K_g₂ ⇒ ∀c∈C ι(g₁(c))=ι(g₂(c)) ; g₁(c),g₂(c)∈A et ι injective
    (injective_dans) ⇒ ∀c∈C g₁(c)=g₂(c) ⇒ (application_egale_par_valeurs) g₁=g₂.

UNE seule injection (on conclut ≤, pas Eq : pas de Cantor-Bernstein).

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

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card, equipotent)
from bourbaki.cardinaux.arithmetique.fondations.ensembles_graphe_de import (
    graphe_de, graphe_de_triple)

# helpers réutilisés du module d'invariance (versions capture-safe à binder paramétré)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import (
    _couple_valeur_q, _valeur_codomaine_q, _membre_graphe_terme_z,
    _membre_produit, _cut, _dans_exposant, _triple_dans_applications)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── liants sûrs ───────────────────────────────────────────────────────────────
_PT = "c"          # point courant du graphe-terme K_g
_VBO = "r"         # liant τ de g(c)        = valeur(graphe_de g, c, «r»)
_VBI = "s"         # liant τ de ι(g(c))     = valeur(ι, g(c), «s»)
_POINT = "g"       # point courant du graphe-terme externe W


# ═══════════════════════════════════════════════════════════════════════════════
#  K_g  et ses propriétés structurelles.
#    g(c)    := valeur(graphe_de(g), c, «r»)
#    ι(g(c)) := valeur(ι, g(c), «s»)
#    K_g     := graphe_terme(C, ι(g(c)), «c»)
# ═══════════════════════════════════════════════════════════════════════════════
def _g_de_c(g):
    """g(c) = valeur(graphe_de g, c, «r»)  (point c = _PT)."""
    return E.valeur(graphe_de(_t(g)), var(_PT), _VBO)


def _val_K(g, iota):
    """ι(g(c)) = valeur(ι, g(c), «s»)."""
    return E.valeur(_t(iota), _g_de_c(g), _VBI)


def K_g(g, c, iota):
    """K_g := { (c, ι(g(c))) | c∈C }  (graphe-terme, niveau GRAPHE)."""
    return E.graphe_terme(_t(c), _val_K(g, iota), _PT)


def K_g_fonctionnelle(g, c, iota):
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    return graphe_terme_fonctionnel(_t(c), _val_K(g, iota), _PT, "y")


def K_g_domaine(g, c, iota):
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_domaine
    return graphe_terme_domaine(_t(c), _val_K(g, iota), _PT, "y", "z")


# ═══════════════════════════════════════════════════════════════════════════════
#  ι(a) ∈ B   pour a∈A   (ι : A→B injection ⇒ image(ι,A)⊂B et (a,ι(a))∈ι).
# ═══════════════════════════════════════════════════════════════════════════════
def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G).   (AXIOME_IMAGE, liant interne « x »)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, _t(g)), _t(xset)), _t(y))


def _iota_val_dans_B(iota, va, vb, point, binder=_VBI):
    """{ est_injection_de(ι,A,B), point ∈ A } ⊢ ι(point) ∈ B,  ι(point)=valeur(ι,point,binder).

    (point,ι(point))∈ι via _couple_valeur_q (dom ι=A décharge via injection) ; témoin
    point∈A ⇒ ι(point)∈image(ι,A) ; image(ι,A)⊂B ⇒ ι(point)∈B.  Le point d'évaluation
    doit éviter le liant interne « x » de AXIOME_IMAGE."""
    viota, vp = _t(iota), _t(point)
    ip = E.valeur(viota, vp, binder)                    # ι(point)
    h_inj = N.assume(est_injection_de(viota, va, vb))
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_gauche(h_inj)))                # dom ι = A
    img_incl = conjonction_elim_droite(h_inj)           # image(ι,A) ⊂ B
    # (point,ι(point))∈ι  (décharger dom ι=A)
    cpl = _cut(_couple_valeur_q(viota, va, vp, binder),
               [(egal(E.dom(viota), va), dom_eq)])      # (point,ι(point))∈ι
    # ι(point)∈image(ι,A)
    ii = _inst_image(viota, va, ip)                     # ι(point)∈ι⟨A⟩ ⇔ (∃x)(x∈A et (x,ι(point))∈ι)
    h_pt = N.assume(appartient(vp, va))                 # point∈A
    body = et(appartient(var("x"), va), appartient(E.couple(var("x"), ip), viota))
    ex = N.modus_ponens(conjonction_intro(h_pt, cpl), N.s5(body, vp, "x"))
    in_img = N.modus_ponens(ex, equivalence_arriere(ii))  # ι(point)∈image(ι,A)
    # image(ι,A)⊂B ⇒ ι(point)∈B
    return N.modus_ponens(in_img, instancie(img_incl, ip))   # ι(point)∈B


# ═══════════════════════════════════════════════════════════════════════════════
#  BIEN-DÉFINITION :  K_g ⊂ C×B  sous { graphe_de(g)⊂C×A, dom graphe_de(g)=C,
#                                       est_injection_de(ι,A,B) }.
# ═══════════════════════════════════════════════════════════════════════════════
def _K_g_inclus(vg, va, vb, vc, viota):
    G = graphe_de(vg)
    K = K_g(vg, vc, viota)
    T = _val_K(vg, viota)                            # ι(g(c))  (point c)
    CB = E.produit(vc, vb)                           # C×B
    vc_pt, vy, vz = var(_PT), var("y"), var("z")
    gc = _g_de_c(vg)                                 # g(c)

    hyp_incl = N.assume(inclus(G, E.produit(vc, va)))   # G ⊂ C×A
    hyp_dom = N.assume(egal(E.dom(G), vc))              # dom G = C

    car = _membre_graphe_terme_z(vc, T, _PT, "z", "y")  # z∈K_g ⇔ (∃c)(∃y)(z=(c,y) et c∈C et y=T)
    body = et(et(egal(vz, E.couple(vc_pt, vy)), appartient(vc_pt, vc)), egal(vy, T))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(c,y)
    cC = conjonction_elim_droite(conjonction_elim_gauche(hb))     # c∈C
    y_eq_T = conjonction_elim_droite(hb)                          # y=ι(g(c))
    # g(c)∈A  (PONT valeur_dans_codomaine sur G au point c)
    gc_in_A = _cut(_valeur_codomaine_q(G, vc, va, vc_pt, _VBO), [
        (inclus(G, E.produit(vc, va)), hyp_incl),
        (egal(E.dom(G), vc), hyp_dom),
        (appartient(vc_pt, vc), cC)])                # g(c)∈A
    # ι(g(c))∈B   (injection)
    T_in_B = _cut(_iota_val_dans_B(viota, va, vb, gc, _VBI),
                  [(appartient(gc, va), gc_in_A)])   # ι(g(c))∈B
    y_in_B = N.modus_ponens(T_in_B, equivalence_arriere(N.modus_ponens(
        y_eq_T, N.s6(vy, T, "w", appartient(var("w"), vb)))))     # y∈B
    cy_in_prod = N.modus_ponens(conjonction_intro(cC, y_in_B),
        equivalence_arriere(_membre_produit(vc_pt, vy, vc, vb)))   # (c,y)∈C×B
    z_in_prod = N.modus_ponens(cy_in_prod, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(vc_pt, vy), "w", appartient(var("w"), CB)))))  # z∈C×B
    ex_imp = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_in_prod), "y"), _PT)              # (∃c)(∃y)body ⇒ z∈C×B
    h_z = N.assume(appartient(vz, K))
    ex = N.modus_ponens(h_z, equivalence_avant(car))             # (∃c)(∃y)body
    z_in_CB = N.modus_ponens(ex, ex_imp)                         # z∈C×B
    imp_z = N.loi_deduction(appartient(vz, K), z_in_CB)          # z∈K_g ⇒ z∈C×B
    return N.generalisation("z", imp_z)                         # K_g ⊂ C×B


# ═══════════════════════════════════════════════════════════════════════════════
#  ((K_g,C),B) ∈ 𝓕(C;B).
# ═══════════════════════════════════════════════════════════════════════════════
def triple_K_dans_applications(g, a, b, c, iota):
    """{ graphe_de(g)⊂C×A, dom graphe_de(g)=C, est_injection_de(ι,A,B) }
       ⊢ ((K_g,C),B) ∈ 𝓕(C;B)."""
    vg, va, vb, vc, viota = _t(g), _t(a), _t(b), _t(c), _t(iota)
    RG = K_g(vg, vc, viota)
    in_exp = _dans_exposant(vb, vc, RG,
        _K_g_inclus(vg, va, vb, vc, viota),
        K_g_fonctionnelle(vg, vc, viota),
        K_g_domaine(vg, vc, viota))
    return _triple_dans_applications(vb, vc, RG, in_exp)


def triple_K_sous_appartenance(g, a, b, c, iota):
    """{ g ∈ 𝓕(C;A), est_injection_de(ι,A,B) } ⊢ ((K_g,C),B) ∈ 𝓕(C;B).

    Décharge les hyps structurelles sur graphe_de(g) via g∈𝓕(C;A) (témoin G éliminé)."""
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
        _exposant_conjoints, _graphe_de_f_egal_G)
    vg, va, vb, vc, viota = _t(g), _t(a), _t(b), _t(c), _t(iota)
    vG = var("G")
    triple_g = E.couple(E.couple(vG, vc), va)             # ((G,C),A)
    body = et(egal(vg, triple_g), appartient(vG, E.exposant(vc, va)))

    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)                    # g=((G,C),A)
    G_in_exp = conjonction_elim_droite(hb)                # G∈A^C
    g_incl, _g_func, g_dom = _exposant_conjoints(vG, vc, va, G_in_exp)
    gr_eq = _graphe_de_f_egal_G(vg, vc, va, vG, f_eq)     # graphe_de(g)=G
    grg = graphe_de(vg)
    incl_grg = N.modus_ponens(g_incl, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", inclus(var("w"), E.produit(vc, va))))))   # gr(g)⊂C×A
    dom_grg = N.modus_ponens(g_dom, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(grg, vG, "w", egal(E.dom(var("w")), vc)))))             # dom gr(g)=C
    base = triple_K_dans_applications(vg, va, vb, vc, viota)
    base = _cut(base, [(inclus(grg, E.produit(vc, va)), incl_grg),
                       (egal(E.dom(grg), vc), dom_grg)])
    inner = existe_elimination(N.loi_deduction(body, base), "G")
    ax = N.axiome(E.theorie_applications(vc, va, "t", "G"),
                  E.axiome_applications(vc, va, "t", "G"))
    car = instancie(ax, vg)                               # g∈𝓕(C;A) ⇔ (∃G)body
    h_app = N.assume(appartient(vg, E.applications(vc, va)))
    ex_body = N.modus_ponens(h_app, equivalence_avant(car))
    return N.modus_ponens(ex_body, inner)                 # ((K_g,C),B)∈𝓕(C;B)


# ═══════════════════════════════════════════════════════════════════════════════
#  L'INJECTION  Φ : 𝓕(C;A) ↪ 𝓕(C;B),  témoin W = graphe de Φ (graphe_terme).
#    Φ(g) := ((K_g,C),B),  W := graphe_terme(𝓕(C;A), Φ(g), «g»).
# ═══════════════════════════════════════════════════════════════════════════════
def _source(a, c):
    """𝓕(C;A)   (source de Φ)."""
    return E.applications(_t(c), _t(a))


def _but_(b, c):
    """𝓕(C;B)   (but de Φ)."""
    return E.applications(_t(c), _t(b))


def _phi_valeur(g, b, c, iota):
    """Φ(g) := ((K_g,C),B)."""
    return E.couple(E.couple(K_g(g, c, iota), _t(c)), _t(b))


def W_phi(a, b, c, iota):
    """W := graphe_terme( 𝓕(C;A) , Φ(g) , «g» )."""
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    return E.graphe_terme(_source(va, vc), _phi_valeur(var(_POINT), vb, vc, viota), _POINT)


def W_phi_fonctionnel(a, b, c, iota):
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    return graphe_terme_fonctionnel(_source(va, vc), _phi_valeur(var(_POINT), vb, vc, viota), _POINT, "y")


def W_phi_domaine(a, b, c, iota):
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_domaine
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    return graphe_terme_domaine(_source(va, vc), _phi_valeur(var(_POINT), vb, vc, viota), _POINT, "y", "z")


def W_phi_valeur(point_nom, a, b, c, iota):
    """{g ∈ 𝓕(C;A)} ⊢ W(g) = Φ(g).   (point d'évaluation = NOM.)"""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur
    if not isinstance(point_nom, str):
        raise ValueError("W_phi_valeur : point = NOM")
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    return graphe_terme_valeur(_source(va, vc), _phi_valeur(var(_POINT), vb, vc, viota),
                               point_nom, _POINT, "y")


def _phi_cod_en_point(va, vb, vc, viota, vg, g_in_thm):
    """{g∈𝓕(C;A), inj} ⊢ Φ(g) ∈ 𝓕(C;B)  (instanciation-terme au point g)."""
    base = triple_K_sous_appartenance(var(_POINT), va, vb, vc, viota)
    base_imp = N.loi_deduction(appartient(var(_POINT), _source(va, vc)), base)
    gen = N.generalisation(_POINT, base_imp)
    inst = instancie(gen, vg)
    return N.modus_ponens(g_in_thm, inst)


def W_phi_image_incluse(a, b, c, iota):
    """{ est_injection_de(ι,A,B) } ⊢ image(W, 𝓕(C;A)) ⊂ 𝓕(C;B).   (BIEN-DÉFINITION.)"""
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    dom = _source(va, vc)
    cod = _but_(vb, vc)
    W = W_phi(va, vb, vc, viota)
    PHI = _phi_valeur(var(_POINT), vb, vc, viota)            # Φ(g), point g
    vz = var("z")
    from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img0 = instancie(instancie(instancie(ax_img, W), dom), vz)
    impl_LtoEX = img0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), dom), appartient(E.couple(var(nom), vz), W))
    ren = alpha_existe(nom, "t", inner)
    img_car = equivalence_transitivite(img0, ren)

    mem = membre_graphe_terme(dom, PHI, "t", "z", _POINT, "y")
    vk = var("t")
    Phi_t = subst_t(vk, _POINT, PHI)                        # Φ(t)
    body = et(appartient(vk, dom), appartient(E.couple(vk, vz), W))
    hb = N.assume(body)
    t_in = conjonction_elim_gauche(hb)
    tz_in = conjonction_elim_droite(hb)
    cond = N.modus_ponens(tz_in, equivalence_avant(mem))
    z_eq = conjonction_elim_droite(cond)                    # z=Φ(t)
    phi_t_in = _phi_cod_en_point(va, vb, vc, viota, vk, t_in)  # Φ(t)∈cod  [inj]
    z_in_cod = N.modus_ponens(phi_t_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, Phi_t, "w", appartient(var("w"), cod)))))   # z∈cod
    ex_imp = existe_elimination(N.loi_deduction(body, z_in_cod), "t")
    h_z = N.assume(appartient(vz, E.image(W, dom)))
    ex = N.modus_ponens(h_z, equivalence_avant(img_car))
    z_in = N.modus_ponens(ex, ex_imp)
    return N.generalisation("z", N.loi_deduction(appartient(vz, E.image(W, dom)), z_in))


# ═══════════════════════════════════════════════════════════════════════════════
#  INJECTIVITÉ de Φ  :  K_g₁ = K_g₂  ⇒  g₁ = g₂.
#    K_g₁=K_g₂ ⇒ (∀c∈C) ι(g₁(c))=ι(g₂(c))  (graphe_terme_valeur) ;  g₁(c),g₂(c)∈A
#    et ι injective ⇒ g₁(c)=g₂(c) ;  application_egale_par_valeurs ⇒ g₁=g₂.
# ═══════════════════════════════════════════════════════════════════════════════
def _Kg_valeur_egal(g, c, iota, c_nom):
    """{ u∈C } ⊢ K_g(u) = ι(g(u)),   point u_nom NOM."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur
    vc = _t(c)
    return graphe_terme_valeur(vc, _val_K(g, iota), c_nom, _PT, "y")


def _iota_de_gc(viota, vg, vc_pt):
    """ι(g(c)) = valeur(ι, valeur(graphe_de g, c, «r»), «s»)   (au point c nommé)."""
    gc = E.valeur(graphe_de(vg), vc_pt, _VBO)
    return E.valeur(viota, gc, _VBI)


def _gc_at(vg, vc_pt, binder=_VBO):
    """g(c) = valeur(graphe_de g, c, binder)  (point c nommé)."""
    return E.valeur(graphe_de(vg), vc_pt, binder)


def _g_values_at_c(vg1, vg2, va, vb, vc, viota, c_nom):
    """{ g₁,g₂∈𝓕(C;A), est_injection_de(ι,A,B), K_g₁=K_g₂, c∈C }
       ⊢ valeur(graphe_de g₁, c, «r») = valeur(graphe_de g₂, c, «r»)  (point c=NOM).

    K_gᵢ(c)=ι(gᵢ(c)) (graphe_terme_valeur, c∈C) ; K_g₁=K_g₂ ⇒ ι(g₁(c))=ι(g₂(c)) ;
    g₁(c),g₂(c)∈A (PONT) ; ι injective ⇒ g₁(c)=g₂(c)."""
    vc_pt = var(c_nom)
    Kg1, Kg2 = K_g(vg1, vc, viota), K_g(vg2, vc, viota)
    g1c, g2c = _gc_at(vg1, vc_pt), _gc_at(vg2, vc_pt)         # g₁(c),g₂(c)  binder «r»
    i_g1c, i_g2c = _iota_de_gc(viota, vg1, vc_pt), _iota_de_gc(viota, vg2, vc_pt)  # ι(gᵢ(c))
    h_cC = N.assume(appartient(vc_pt, vc))                   # c∈C
    # K_gᵢ(c)=ι(gᵢ(c))
    Kg1c = _cut(_Kg_valeur_egal(vg1, vc, viota, c_nom), [(appartient(vc_pt, vc), h_cC)])
    Kg2c = _cut(_Kg_valeur_egal(vg2, vc, viota, c_nom), [(appartient(vc_pt, vc), h_cC)])
    # K_g₁=K_g₂ ⇒ K_g₁(c)=K_g₂(c)
    h_Keq = N.assume(egal(Kg1, Kg2))
    Kc_eq = N.modus_ponens(h_Keq, congruence_terme(Kg1, Kg2, E.valeur(var("w"), vc_pt, "y")))
    # ι(g₁(c)) = K_g₁(c) = K_g₂(c) = ι(g₂(c))
    i_g1c_eq_Kg1c = N.modus_ponens(Kg1c, symetrie(E.valeur(Kg1, vc_pt, "y"), i_g1c))
    igc_eq = composer_egalites(composer_egalites(i_g1c_eq_Kg1c, Kc_eq), Kg2c)   # ι(g₁(c))=ι(g₂(c))
    # g₁(c),g₂(c)∈A   (PONT valeur_dans_codomaine ; déchargé via g∈𝓕(C;A))
    g1c_in_A = _gc_dans_A(vg1, va, vc, vc_pt)
    g2c_in_A = _gc_dans_A(vg2, va, vc, vc_pt)
    # ι injective : (g₁(c)∈A et g₂(c)∈A et ι(g₁(c))=ι(g₂(c))) ⇒ g₁(c)=g₂(c)
    # rebind ι(gᵢ(c)) du binder «s» (interne K_g) vers «y» (binder défaut de injective_dans)
    reb1 = N.alpha_tau(appartient(E.couple(g1c, var(_VBI)), viota), _VBI, "y")  # ι(g₁(c))[s]=ι(g₁(c))[y]
    reb2 = N.alpha_tau(appartient(E.couple(g2c, var(_VBI)), viota), _VBI, "y")
    i_g1c_y = E.valeur(viota, g1c, "y")
    i_g2c_y = E.valeur(viota, g2c, "y")
    # ι(g₁(c))[y] = ι(g₁(c))[s] = ι(g₂(c))[s] = ι(g₂(c))[y]
    i_g1c_y_eq_s = N.modus_ponens(reb1, symetrie(i_g1c, i_g1c_y))   # ι(g₁(c))[y]=ι(g₁(c))[s]
    igc_eq_y = composer_egalites(composer_egalites(i_g1c_y_eq_s, igc_eq), reb2)  # ι(g₁(c))[y]=ι(g₂(c))[y]
    h_inj = N.assume(est_injection_de(viota, va, vb))
    inj_dans = conjonction_elim_droite(conjonction_elim_gauche(h_inj))   # injective_dans(ι,A) = (∀u)(∀up)corps
    inj_inst = instancie(instancie(inj_dans, g1c), g2c)      # (g₁(c)∈A et g₂(c)∈A et ι(g₁(c))[y]=ι(g₂(c))[y])⇒g₁(c)=g₂(c)
    return N.modus_ponens(conjonction_intro(conjonction_intro(g1c_in_A, g2c_in_A), igc_eq_y),
                          inj_inst)                          # g₁(c)=g₂(c)


def _inj_corps(viota, va):
    """Le corps (∀-libéré sur u,up) de injective_dans(ι,A) :
       ((u∈A et u'∈A et ι(u)=ι(u')) ⇒ u=u'),  binder valeur défaut «y»."""
    vu, vup = var("u"), var("up")
    return impl(et(et(appartient(vu, va), appartient(vup, va)),
                   egal(E.valeur(viota, vu), E.valeur(viota, vup))),
                egal(vu, vup))


def _gc_dans_A(vg, va, vc, vc_pt):
    """{ g∈𝓕(C;A), c∈C } ⊢ valeur(graphe_de g, c, «r») ∈ A.

    décharge graphe_de(g)⊂C×A, dom graphe_de(g)=C via g∈𝓕(C;A) (témoin G), puis PONT."""
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
        _exposant_conjoints, _graphe_de_f_egal_G)
    G = graphe_de(vg)
    gc = E.valeur(G, vc_pt, _VBO)
    vG = var("G")
    triple_g = E.couple(E.couple(vG, vc), va)
    body = et(egal(vg, triple_g), appartient(vG, E.exposant(vc, va)))
    hb = N.assume(body)
    f_eq = conjonction_elim_gauche(hb)
    G_in_exp = conjonction_elim_droite(hb)
    g_incl, _g_func, g_dom = _exposant_conjoints(vG, vc, va, G_in_exp)
    gr_eq = _graphe_de_f_egal_G(vg, vc, va, vG, f_eq)
    incl_grg = N.modus_ponens(g_incl, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(G, vG, "w", inclus(var("w"), E.produit(vc, va))))))
    dom_grg = N.modus_ponens(g_dom, equivalence_arriere(N.modus_ponens(gr_eq,
        N.s6(G, vG, "w", egal(E.dom(var("w")), vc)))))
    h_cC = N.assume(appartient(vc_pt, vc))
    pont = _valeur_codomaine_q(G, vc, va, vc_pt, _VBO)       # {G⊂C×A,dom G=C,c∈C}⊢g(c)∈A
    pont = _cut(pont, [(inclus(G, E.produit(vc, va)), incl_grg),
                       (egal(E.dom(G), vc), dom_grg),
                       (appartient(vc_pt, vc), h_cC)])        # g(c)∈A  [body, c∈C]
    inner = existe_elimination(N.loi_deduction(body, pont), "G")
    ax = N.axiome(E.theorie_applications(vc, va, "t", "G"),
                  E.axiome_applications(vc, va, "t", "G"))
    car = instancie(ax, vg)
    h_app = N.assume(appartient(vg, E.applications(vc, va)))
    ex_body = N.modus_ponens(h_app, equivalence_avant(car))
    return N.modus_ponens(ex_body, inner)                    # g(c)∈A  [g∈𝓕(C;A), c∈C]


def _g_egalite_valeurs(vg1, vg2, va, vb, vc, viota):
    """{ g₁,g₂∈𝓕(C;A), inj, K_g₁=K_g₂ }
       ⊢ (∀x)(x∈C ⇒ valeur(graphe_de g₁,x,«y»)=valeur(graphe_de g₂,x,«y»))."""
    vc_pt = var("e")
    pt = _g_values_at_c(vg1, vg2, va, vb, vc, viota, "e")    # g₁(e)[r]=g₂(e)[r]
    # rebind r→y des deux côtés
    reb1 = N.alpha_tau(appartient(E.couple(vc_pt, var(_VBO)), graphe_de(vg1)), _VBO, "y")
    reb2 = N.alpha_tau(appartient(E.couple(vc_pt, var(_VBO)), graphe_de(vg2)), _VBO, "y")
    g1r, g1y = _gc_at(vg1, vc_pt, _VBO), E.valeur(graphe_de(vg1), vc_pt, "y")
    g2r, g2y = _gc_at(vg2, vc_pt, _VBO), E.valeur(graphe_de(vg2), vc_pt, "y")
    g1y_eq_r = N.modus_ponens(reb1, symetrie(g1r, g1y))      # g₁(s)[y]=g₁(s)[r]
    pt_y = composer_egalites(composer_egalites(g1y_eq_r, pt), reb2)   # g₁(s)[y]=g₂(s)[y]
    pt_y = N.loi_deduction(appartient(vc_pt, vc), pt_y)
    raw = N.generalisation("e", pt_y)
    inst = instancie(raw, var("x"))
    return N.generalisation("x", inst)


def phi_injective_sous_appartenance(g1, g2, a, b, c, iota):
    """{ g₁,g₂∈𝓕(C;A), inj, K_g₁=K_g₂ } ⊢ g₁ = g₂."""
    from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
        application_egale_par_valeurs, egalite_valeurs_application)
    vg1, vg2, va, vb, vc, viota = _t(g1), _t(g2), _t(a), _t(b), _t(c), _t(iota)
    eva = _g_egalite_valeurs(vg1, vg2, va, vb, vc, viota)
    base = application_egale_par_valeurs(vg1, vg2, vc, va)   # {g₁∈𝓕,g₂∈𝓕,(∀x)…}⊢g₁=g₂
    target_eva = egalite_valeurs_application(vg1, vg2, vc)
    assert eva.conclusion == target_eva, "egalite_valeurs ≠ attendu"
    return _cut(base, [(target_eva, eva)])


def _phi_egal_donne_K(vg1, vg2, vb, vc, viota):
    """{ Φ(g₁)=Φ(g₂) } ⊢ K_g₁=K_g₂."""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
    Kg1, Kg2 = K_g(vg1, vc, viota), K_g(vg2, vc, viota)
    L1, L2 = _phi_valeur(vg1, vb, vc, viota), _phi_valeur(vg2, vb, vc, viota)
    inner1, inner2 = E.couple(Kg1, vc), E.couple(Kg2, vc)
    h = N.assume(egal(L1, L2))                               # ((Kg₁,C),B)=((Kg₂,C),B)
    comp1 = N.modus_ponens(h, couple_egal_implique_composantes(inner1, vb, inner2, vb))
    inner_eq = conjonction_elim_gauche(comp1)               # (Kg₁,C)=(Kg₂,C)
    comp2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(Kg1, vc, Kg2, vc))
    return conjonction_elim_gauche(comp2)                   # Kg₁=Kg₂


def W_phi_injective(a, b, c, iota):
    """{ est_injection_de(ι,A,B) } ⊢ injective_dans(W, 𝓕(C;A))."""
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    dom = _source(va, vc)
    Wt = W_phi(va, vb, vc, viota)
    vg1, vg2 = var("g1"), var("g2")
    L1, L2 = _phi_valeur(vg1, vb, vc, viota), _phi_valeur(vg2, vb, vc, viota)
    Kg1, Kg2 = K_g(vg1, vc, viota), K_g(vg2, vc, viota)

    hyp = et(et(appartient(vg1, dom), appartient(vg2, dom)),
             egal(E.valeur(Wt, vg1), E.valeur(Wt, vg2)))
    h = N.assume(hyp)
    g1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    g2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                       # W(g₁)=W(g₂)
    Wg1 = _cut(W_phi_valeur("g1", va, vb, vc, viota), [(appartient(vg1, dom), g1_in)])
    Wg2 = _cut(W_phi_valeur("g2", va, vb, vc, viota), [(appartient(vg2, dom), g2_in)])
    phi_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wg1, symetrie(E.valeur(Wt, vg1), L1)), W_eq), Wg2)   # Φ(g₁)=Φ(g₂)
    K_eq = _cut(_phi_egal_donne_K(vg1, vg2, vb, vc, viota), [(egal(L1, L2), phi_eq)])
    g_eq = phi_injective_sous_appartenance("g1", "g2", va, vb, vc, viota)
    g_eq = _cut(g_eq, [(appartient(vg1, dom), g1_in),
                       (appartient(vg2, dom), g2_in),
                       (egal(Kg1, Kg2), K_eq)])
    inner = N.loi_deduction(hyp, g_eq)
    raw = N.generalisation("g1", N.generalisation("g2", inner))
    inst = instancie(instancie(raw, var("u")), var("up"))
    return N.generalisation("u", N.generalisation("up", inst))


# ═══════════════════════════════════════════════════════════════════════════════
#  Φ EST UNE INJECTION  ⟹  inf_egal_card(𝓕(C;A), 𝓕(C;B)).
# ═══════════════════════════════════════════════════════════════════════════════
def W_phi_est_injection(a, b, c, iota):
    """{ est_injection_de(ι,A,B) } ⊢ est_injection_de(W, 𝓕(C;A), 𝓕(C;B))."""
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_phi_fonctionnel(va, vb, vc, viota), W_phi_domaine(va, vb, vc, viota)),
        W_phi_injective(va, vb, vc, viota)), W_phi_image_incluse(va, vb, vc, viota))


def injection_post_composition(a, b, c, iota):
    """{ est_injection_de(ι,A,B) } ⊢ inf_egal_card(𝓕(C;A), 𝓕(C;B))."""
    va, vb, vc, viota = _t(a), _t(b), _t(c), _t(iota)
    dom = _source(va, vc)
    cod = _but_(vb, vc)
    Wt = W_phi(va, vb, vc, viota)
    inj = W_phi_est_injection(va, vb, vc, viota)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), dom, cod), Wt, "F"))


# ═══════════════════════════════════════════════════════════════════════════════
#  M1 — DÉCHARGE de A≤B : (A ≤ B) ⇒ 𝓕(C;A) ≤ 𝓕(C;B).
# ═══════════════════════════════════════════════════════════════════════════════
def support_monotone_base(a="A", b="B", c="C"):
    """⊢ (A ≤ B) ⇒ (𝓕(C;A) ≤ 𝓕(C;B)).   (INCONDITIONNEL, témoin ι éliminé.)"""
    va, vb, vc = _t(a), _t(b), _t(c)
    viota = var("iota")
    inj_body = est_injection_de(viota, va, vb)
    base = injection_post_composition(va, vb, vc, viota)    # {inj(ι,A,B)} ⊢ 𝓕(C;A)≤𝓕(C;B)
    imp = existe_elimination(N.loi_deduction(inj_body, base), "iota")
    # imp : (∃iota)inj(iota,A,B) ⇒ 𝓕(C;A)≤𝓕(C;B).  α-renommer l'antécédent en (∃F) = A≤B.
    le_ab = inf_egal_card(va, vb)                          # (∃F)inj(F,A,B)
    ren = alpha_existe("iota", "F", est_injection_de(viota, va, vb))  # (∃iota)inj(iota) ⇔ (∃F)inj(F)
    concl = N.modus_ponens(N.modus_ponens(N.assume(le_ab),
                equivalence_arriere(ren)), imp)           # 𝓕(C;A)≤𝓕(C;B)  [A≤B]
    return N.loi_deduction(le_ab, concl)                  # (A≤B) ⇒ 𝓕(C;A)≤𝓕(C;B)


# ═══════════════════════════════════════════════════════════════════════════════
#  M1 FINAL — monotonie en la BASE au niveau des CARDINAUX (INCONDITIONNEL) :
#      (a ≤ b) ⇒ (a^c ≤ b^c),   a^c := exposant_cardinal_binaire(a,c) = Card(𝓕(c;a)).
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_monotone_base(a="a", b="b", c="c"):
    """⊢ (a ≤ b) ⇒ (a^c ≤ b^c).   (a^c = exposant_cardinal_binaire(a,c) = Card(𝓕(c;a)).)

    INCONDITIONNEL, AUCUNE hypothèse de support.  Chaîne :
      support_monotone_base(a,b,c) : (a≤b) ⇒ (𝓕(c;a) ≤ 𝓕(c;b))   [M1, injection ι∘g]
      inf_egal_transporte_cardinal : (𝓕(c;a)≤𝓕(c;b)) ⇒ (Card 𝓕(c;a) ≤ Card 𝓕(c;b))   [(0)]
    et Card 𝓕(c;a) = exposant_cardinal_binaire(a,c) (par DÉFINITION 4)."""
    from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
        inf_egal_transporte_cardinal)
    va, vb, vc = _t(a), _t(b), _t(c)
    Fca = E.applications(vc, va)                          # 𝓕(c;a)
    Fcb = E.applications(vc, vb)                          # 𝓕(c;b)
    # M1 sur NOMS FRAIS capture-safe (A,B,C ≠ binders internes de graphe_de=τa/∃b),
    # puis généralisation + instanciation aux TERMES a,b,c (capture-safe).
    m1_AABC = support_monotone_base("A", "B", "C")       # (A≤B) ⇒ (𝓕(C;A)≤𝓕(C;B))
    m1_gen = N.generalisation("A", N.generalisation("B", N.generalisation("C", m1_AABC)))
    m1 = instancie(instancie(instancie(m1_gen, va), vb), vc)  # (a≤b) ⇒ (𝓕(c;a)≤𝓕(c;b))
    # transport (0) instancié aux supports : (𝓕(c;a)≤𝓕(c;b)) ⇒ (Card 𝓕(c;a) ≤ Card 𝓕(c;b))
    transp_all = N.generalisation("X", N.generalisation("Y",
        inf_egal_transporte_cardinal("X", "Y")))
    transp = instancie(instancie(transp_all, Fca), Fcb)  # (𝓕(c;a)≤𝓕(c;b)) ⇒ (a^c ≤ b^c)
    # chaîne : (a≤b) ⇒ (𝓕(c;a)≤𝓕(c;b)) ⇒ (a^c ≤ b^c)
    h_le = N.assume(inf_egal_card(va, vb))               # a≤b
    sup = N.modus_ponens(h_le, m1)                       # 𝓕(c;a)≤𝓕(c;b)
    exp_le = N.modus_ponens(sup, transp)                 # Card 𝓕(c;a) ≤ Card 𝓕(c;b) = a^c ≤ b^c
    return N.loi_deduction(inf_egal_card(va, vb), exp_le)


__all__ = ["injection_post_composition", "support_monotone_base",
           "exposant_monotone_base", "W_phi_est_injection", "W_phi", "K_g"]
