"""§III.3.5 — a^1 = a, PARTIE 2 : caractérisation de A^{∅}, surjectivité, a^1 = a.

Sous-module de `ensembles_exposant_un`.  Ici : PALIER 3 (tout G∈A^{∅} est le graphe
constant G_{G(∅)} — UNICITÉ du graphe fonctionnel de domaine {∅}, le cœur),
surjectivité image(η,A)=𝓕({∅};A), et PALIER 4 (bijection η, équipotence, a^1 = a).
Importe la PARTIE 1 (G_v, η) depuis ._gv.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, ou, impl, appartient,
                     existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (singleton_membre, membre_paire_gauche,
                                  couple_egal_implique_composantes)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.exposant_un._gv import (
    _t, UN_SOURCE, _gv, gv_dans_exposant, gv_membre,
    _eta_triple_A, _eta, eta_fonctionnel, eta_domaine, eta_valeur, eta_injective)


# PALIER 3 (préparation, CLOS) : depuis G ∈ A^{∅}
# ───────────────────────────────────────────────────────────────────────────────
def _exposant_conjoints(g, a):
    """Renvoie (h, incl, func, domeq) où h = assume(G∈A^{∅}) et les 3 conjoints
    G⊂{∅}×A, est_fonctionnel(G), dom G={∅} extraits via l'axiome (sous h)."""
    vG, vA = _t(g), _t(a)
    one = UN_SOURCE()
    ax = N.axiome(E.theorie_exposant(one, vA), E.axiome_exposant(one, vA))
    car = instancie(ax, vG)                     # G∈A^{∅} ⇔ ((G⊂{∅}×A et G fonct) et dom G={∅})
    h = N.assume(appartient(vG, E.exposant(one, vA)))   # G∈A^{∅}
    corps = N.modus_ponens(h, equivalence_avant(car))   # (G⊂{∅}×A et G fonct) et dom G={∅}
    incl = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # G⊂{∅}×A
    func = conjonction_elim_droite(conjonction_elim_gauche(corps))   # est_fonctionnel(G)
    domeq = conjonction_elim_droite(corps)                          # dom G={∅}
    return h, incl, func, domeq


def exposant_couple_dans(g="G", a="A"):
    """{G ∈ A^{∅}} ⊢ (∅, G(∅)) ∈ G.   (∅ est dans dom G={∅}, donc le couple
    (∅, G(∅)) appartient au graphe.)

    dom G={∅} ⇒ ∅∈dom G (∅∈{∅} + Leibniz) ⇒ (∃y)((∅,y)∈G)  [AXIOME_DOM]
    ⇒ (∅, G(∅))∈G  [valeur_dans_graphe, G(∅)=τy((∅,y)∈G)]."""
    vG, vA = _t(g), _t(a)
    one = UN_SOURCE()
    vy = var("y")
    h, incl, func, domeq = _exposant_conjoints(g, a)
    # ∅∈{∅} et dom G={∅} ⇒ ∅∈dom G
    vide_in_one = membre_paire_gauche(E.VIDE, E.VIDE)            # ∅∈{∅}
    # dom G={∅} ⇒ (∅∈dom G ⇔ ∅∈{∅})  via Leibniz S6 sur 2ᵉ arg de ∈
    leib = N.s6(E.dom(vG), one, "w", appartient(E.VIDE, var("w")))
    vide_in_dom = N.modus_ponens(vide_in_one,
                                 equivalence_arriere(N.modus_ponens(domeq, leib)))   # ∅∈dom G
    # ∅∈dom G ⇔ (∃y)((∅,y)∈G)  [AXIOME_DOM]
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vG), E.VIDE)          # ∅∈dom G ⇔ (∃y)((∅,y)∈G)
    ex_y = N.modus_ponens(vide_in_dom, equivalence_avant(dom_car))   # (∃y)((∅,y)∈G)
    # (∅, G(∅))∈G  via valeur_dans_graphe (décharger l'hyp domaine)
    from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe
    cpl = valeur_dans_graphe(vG, E.VIDE)        # {(∃y)((∅,y)∈G)} ⊢ (∅, G(∅))∈G
    return N.modus_ponens(ex_y,
        N.loi_deduction(existe("y", appartient(E.couple(E.VIDE, vy), vG)), cpl))


def exposant_valeur_dans_A(g="G", a="A"):
    """{G ∈ A^{∅}} ⊢ G(∅) ∈ A.   (la valeur en ∅ est dans le but A.)

    (∅, G(∅))∈G (exposant_couple_dans) et G⊂{∅}×A donnent (∅,G(∅))∈{∅}×A,
    d'où G(∅)∈A par couple_dans_produit_ssi (2ᵉ projection)."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    vG, vA = _t(g), _t(a)
    one = UN_SOURCE()
    fvide = E.valeur(vG, E.VIDE)                # G(∅)
    h, incl, func, domeq = _exposant_conjoints(g, a)
    cpl = exposant_couple_dans(g, a)           # (∅, G(∅))∈G
    # G⊂{∅}×A ⇒ (∅,G(∅))∈G ⇒ (∅,G(∅))∈{∅}×A   (∀z instanciée à (∅,G(∅)))
    incl_inst = instancie(incl, E.couple(E.VIDE, fvide))   # (∅,G(∅))∈G ⇒ (∅,G(∅))∈{∅}×A
    in_prod = N.modus_ponens(cpl, incl_inst)               # (∅,G(∅))∈{∅}×A
    ssi = couple_dans_produit_ssi(E.VIDE, fvide, one, vA)  # ((∅,G(∅))∈{∅}×A) ⇔ (∅∈{∅} et G(∅)∈A)
    return conjonction_elim_droite(N.modus_ponens(in_prod, equivalence_avant(ssi)))  # G(∅)∈A


# ───────────────────────────────────────────────────────────────────────────────
# PALIER 3 (CŒUR — surjectivité) : tout G ∈ A^{∅} est G_{G(∅)}
# ───────────────────────────────────────────────────────────────────────────────
def exposant_membre_implique_couple(g="G", a="A"):
    """{G ∈ A^{∅}} ⊢ (z ∈ G) ⇒ (z = (∅, G(∅))).   (tout élément de G est le couple
    (∅, G(∅)) : G⊂{∅}×A force la 1ʳᵉ coord à ∅, la fonctionnalité force la 2ᵉ.)

    z∈G ⊂{∅}×A ⇒ (∃p)(∃q)(z=(p,q) et p∈{∅} et q∈A) ; p=∅ ; z=(∅,q) ; (∅,q)∈G
    (Leibniz) ; (∅,G(∅))∈G (exposant_couple_dans) ; FONCTIONNALITÉ ⇒ q=G(∅) ;
    donc z=(∅,q)=(∅,G(∅))."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import _instance_produit
    vG, vA = _t(g), _t(a)
    one = UN_SOURCE()
    fvide = E.valeur(vG, E.VIDE)                # G(∅)
    vz, vp, vq = var("z"), var("p"), var("q")
    h, incl, func, domeq = _exposant_conjoints(g, a)
    cpl0 = exposant_couple_dans(g, a)          # (∅, G(∅))∈G   [sous h]
    hz = N.assume(appartient(vz, vG))          # z∈G
    # z∈{∅}×A
    z_in_prod = N.modus_ponens(hz, instancie(incl, vz))     # z∈{∅}×A
    prod_car = _instance_produit(one, vA, vz)  # z∈{∅}×A ⇔ (∃p)(∃q)(z=(p,q) et p∈{∅} et q∈A)
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, one)), appartient(vq, vA))
    # sous le corps body : conclure z=(∅,G(∅))
    hb = N.assume(body)
    z_pq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # z=(p,q)
    p_in = conjonction_elim_droite(conjonction_elim_gauche(hb))   # p∈{∅}
    p_vide = N.modus_ponens(p_in, equivalence_avant(singleton_membre(vp, E.VIDE)))  # p=∅
    # z=(p,q)=(∅,q)  (congruence 1ʳᵉ coord)
    pq_0q = N.modus_ponens(p_vide, congruence_terme(vp, E.VIDE, E.couple(var("w"), vq)))
    z_0q = composer_egalites(z_pq, pq_0q)      # z=(∅,q)
    # (∅,q)∈G  : z∈G et z=(∅,q) ⇒ (∅,q)∈G  (Leibniz S6 sur 1ᵉʳ arg de ∈)
    leib0q = N.s6(vz, E.couple(E.VIDE, vq), "w", appartient(var("w"), vG))
    cpl_0q = N.modus_ponens(hz, equivalence_avant(N.modus_ponens(z_0q, leib0q)))   # (∅,q)∈G
    # FONCTIONNALITÉ : ((∅,q)∈G et (∅,G(∅))∈G) ⇒ q=G(∅)
    func_inst = instancie(instancie(instancie(func, E.VIDE), vq), fvide)  # ((∅,q)∈G et (∅,G(∅))∈G)⇒q=G(∅)
    q_fvide = N.modus_ponens(conjonction_intro(cpl_0q, cpl0), func_inst)   # q=G(∅)
    # z=(∅,q)=(∅,G(∅))  (congruence 2ᵉ coord)
    z0q_0f = N.modus_ponens(q_fvide, congruence_terme(vq, fvide, E.couple(E.VIDE, var("w"))))
    z_0f = composer_egalites(z_0q, z0q_0f)     # z=(∅,G(∅))
    # éliminer les témoins p, q
    inner = existe_elimination(existe_elimination(
        N.loi_deduction(body, z_0f), "q"), "p")     # (∃p)(∃q)body ⇒ z=(∅,G(∅))
    z_imp = syllogisme(equivalence_avant(prod_car), inner)   # z∈{∅}×A ⇒ z=(∅,G(∅))
    concl = N.modus_ponens(z_in_prod, z_imp)   # z=(∅,G(∅))   [sous z∈G, h]
    return N.loi_deduction(appartient(vz, vG), concl)   # (z∈G) ⇒ z=(∅,G(∅))   [sous h]


def exposant_egal_gv(g="G", a="A"):
    """{G ∈ A^{∅}} ⊢ G = G_{G(∅)}.   (UNICITÉ du graphe fonctionnel de domaine {∅} :
    G est exactement le graphe constant {(∅, G(∅))}.)

    Par extension (liant z) : z∈G ⇔ z∈G_{G(∅)}.
      ⇒ : z∈G ⇒ z=(∅,G(∅)) (exposant_membre_implique_couple) ⇒ z∈G_{G(∅)} (gv_membre ⇐).
      ⇐ : z∈G_{G(∅)} ⇒ z=(∅,G(∅)) (gv_membre ⇒) ; (∅,G(∅))∈G (exposant_couple_dans)
          ⇒ z∈G (Leibniz)."""
    vG, vA = _t(g), _t(a)
    one = UN_SOURCE()
    fvide = E.valeur(vG, E.VIDE)               # G(∅)
    Gf = _gv(fvide)                            # G_{G(∅)}
    vz = var("z")
    cpl0 = exposant_couple_dans(g, a)          # (∅,G(∅))∈G   [sous h]
    z_0f = egal(vz, E.couple(E.VIDE, fvide))   # z=(∅,G(∅))
    gvm = gv_membre(fvide, vz)                 # z∈G_{G(∅)} ⇔ z=(∅,G(∅))
    # ⇒ : z∈G ⇒ z=(∅,G(∅)) ⇒ z∈G_{G(∅)}
    in_G_imp = exposant_membre_implique_couple(g, a)   # (z∈G) ⇒ z=(∅,G(∅))   [sous h]
    fwd = syllogisme(in_G_imp, equivalence_arriere(gvm))   # z∈G ⇒ z∈G_{G(∅)}
    # ⇐ : z∈G_{G(∅)} ⇒ z=(∅,G(∅)) ⇒ z∈G
    hgv = N.assume(appartient(vz, Gf))
    z_eq = N.modus_ponens(hgv, equivalence_avant(gvm))     # z=(∅,G(∅))
    # (∅,G(∅))∈G et z=(∅,G(∅)) ⇒ z∈G   (Leibniz S6 sur 1ᵉʳ arg de ∈)
    leib = N.s6(vz, E.couple(E.VIDE, fvide), "w", appartient(var("w"), vG))
    z_in_G = N.modus_ponens(cpl0, equivalence_arriere(N.modus_ponens(z_eq, leib)))   # z∈G
    bwd = N.loi_deduction(appartient(vz, Gf), z_in_G)      # z∈G_{G(∅)} ⇒ z∈G
    equiv_z = conjonction_intro(fwd, bwd)      # z∈G ⇔ z∈G_{G(∅)}
    char = N.generalisation("z", equiv_z)      # (∀z)(z∈G ⇔ z∈G_{G(∅)})  [R = z∈G_{G(∅)}]
    self_Gf = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, Gf)), a_implique_a(appartient(vz, Gf))))   # (∀z)(z∈Gf ⇔ z∈Gf)
    return egalite_par_extension(char, self_Gf, vG, Gf, "z")   # G = G_{G(∅)}   [sous h]


def exposant_un_est_gv(g="G", a="A"):
    """{G ∈ A^{∅}} ⊢ (∃v)(v∈A et G = G_v).   (tout graphe fonctionnel {∅}→A est le
    graphe constant {(∅,v)} d'une valeur v∈A — caractérisation COMPLÈTE de A^{∅}.)

    Témoin v := G(∅) : G(∅)∈A (exposant_valeur_dans_A) et G=G_{G(∅)} (exposant_egal_gv) ;
    S5 conclut l'existentielle."""
    vG, vA = _t(g), _t(a)
    fvide = E.valeur(vG, E.VIDE)               # G(∅)
    vv = var("v")
    fv_in_A = exposant_valeur_dans_A(g, a)     # G(∅)∈A   [sous h]
    G_eq_Gf = exposant_egal_gv(g, a)           # G=G_{G(∅)}   [sous h]
    # corps : (v∈A et G=G_v) ; témoin v:=G(∅) : (G(∅)∈A et G=G_{G(∅)})
    corps = et(appartient(vv, vA), egal(vG, _gv(vv)))
    wit = conjonction_intro(fv_in_A, G_eq_Gf)  # (v|→G(∅))corps
    return N.modus_ponens(wit, N.s5(corps, fvide, "v"))   # (∃v)(v∈A et G=G_v)   [sous h]


# ───────────────────────────────────────────────────────────────────────────────
# PALIER 3 (image — surjectivité de η) : image(η, A) = 𝓕({∅}; A)
# ───────────────────────────────────────────────────────────────────────────────
def _bridge_image_applications(z="z", a="A"):
    """⊢ ((∃u)(u∈A et z=((G_u,{∅}),A))) ⇔ ((∃G)(z=((G,{∅}),A) et G∈A^{∅})).

    Le pont entre le corps existentiel de image(η,A) (côté η, valeurs ((G_u,{∅}),A)
    pour u∈A) et celui de 𝓕({∅};A) (côté triples ((G,{∅}),A) pour G∈A^{∅}).
      ⇒ : témoin G:=G_u ; G_u∈A^{∅} (gv_dans_exposant sous u∈A).
      ⇐ : G∈A^{∅} ⇒ (∃u)(u∈A et G=G_u) (exposant_un_est_gv) ; z=((G,{∅}),A) réécrit
          en ((G_u,{∅}),A) par Leibniz."""
    vz, vA = _t(z), _t(a)
    one = UN_SOURCE()
    # ⚠️ binder existentiel « k » (≠ binders internes u,v,z,x,y,w,p,q des gv_*),
    # binder « Gg » pour le second existentiel (≠ « G » interne des helpers).
    vk, vG = var("k"), var("Gg")
    # corps gauche : Lk = (k∈A et z=((G_k,{∅}),A))
    triple_k = E.couple(E.couple(_gv(vk), one), vA)        # ((G_k,{∅}),A)
    Lk = et(appartient(vk, vA), egal(vz, triple_k))
    # corps droit : RG = (z=((G,{∅}),A) et G∈A^{∅})
    triple_G = E.couple(E.couple(vG, one), vA)             # ((Gg,{∅}),A)
    RG = et(egal(vz, triple_G), appartient(vG, E.exposant(one, vA)))
    # ── ⇒ : (∃k)Lk ⇒ (∃Gg)RG ────────────────────────────────────────────────────
    hLk = N.assume(Lk)
    k_in = conjonction_elim_gauche(hLk)                   # k∈A
    z_tk = conjonction_elim_droite(hLk)                   # z=((G_k,{∅}),A)
    Gk_in = N.modus_ponens(k_in, gv_dans_exposant(vk, vA))   # G_k∈A^{∅}
    # (Gg:=G_k)RG = (z=((G_k,{∅}),A) et G_k∈A^{∅})
    witG = conjonction_intro(z_tk, Gk_in)                 # (Gg|→G_k)RG
    ex_G = N.modus_ponens(witG, N.s5(RG, _gv(vk), "Gg"))  # (∃Gg)RG
    fwd = existe_elimination(N.loi_deduction(Lk, ex_G), "k")   # (∃k)Lk ⇒ (∃Gg)RG
    # ── ⇐ : (∃Gg)RG ⇒ (∃k)Lk ────────────────────────────────────────────────────
    hRG = N.assume(RG)
    z_tG = conjonction_elim_gauche(hRG)                   # z=((Gg,{∅}),A)
    G_in = conjonction_elim_droite(hRG)                   # Gg∈A^{∅}
    # exposant_un_est_gv(Gg,A) : {Gg∈A^{∅}} ⊢ (∃v)(v∈A et Gg=G_v) ; on décharge son
    # hypothèse (loi_deduction) puis MP avec G_in (issu de hRG) pour ne garder QUE RG.
    ex_k_gv_impl = N.loi_deduction(appartient(vG, E.exposant(one, vA)),
                                   exposant_un_est_gv(vG, vA))   # Gg∈A^{∅} ⇒ (∃v)(...)
    ex_k_gv = N.modus_ponens(G_in, ex_k_gv_impl)         # (∃v)(v∈A et Gg=G_v)   [hyp RG via G_in]
    # exposant_un_est_gv lie « v » ; on renomme en « k » pour matcher Lk
    ex_k_gv = N.modus_ponens(ex_k_gv,
        equivalence_avant(alpha_existe("v", "k", et(appartient(var("v"), vA),
                                                    egal(vG, _gv(var("v")))))))   # (∃k)(k∈A et Gg=G_k)
    # sous (k∈A et Gg=G_k) : déduire Lk
    body_k = et(appartient(vk, vA), egal(vG, _gv(vk)))
    hbk = N.assume(body_k)
    k_inA = conjonction_elim_gauche(hbk)                  # k∈A
    G_eq_Gk = conjonction_elim_droite(hbk)                # Gg=G_k
    # ((Gg,{∅}),A)=((G_k,{∅}),A)  via congruence (trou w sur le coin Gg)
    triple_w = E.couple(E.couple(var("w"), one), vA)      # ((w,{∅}),A)
    tG_tk = N.modus_ponens(G_eq_Gk, congruence_terme(vG, _gv(vk), triple_w))   # ((Gg,{∅}),A)=((G_k,{∅}),A)
    z_tk2 = composer_egalites(z_tG, tG_tk)                # z=((G_k,{∅}),A)
    Lk2 = conjonction_intro(k_inA, z_tk2)                 # k∈A et z=((G_k,{∅}),A) = Lk
    ex_k = N.modus_ponens(Lk2, N.s5(Lk, vk, "k"))         # (∃k)Lk   (témoin = k lié, S5 idempotent)
    bwd_inner = existe_elimination(N.loi_deduction(body_k, ex_k), "k")   # (∃k)body_k ⇒ (∃k)Lk
    bwd = existe_elimination(N.loi_deduction(RG,
              N.modus_ponens(ex_k_gv, bwd_inner)), "Gg")  # (∃Gg)RG ⇒ (∃k)Lk
    return conjonction_intro(fwd, bwd)                    # (∃k)Lk ⇔ (∃Gg)RG


def _et_idem_gauche(p, q):
    """⊢ (P et (P et Q)) ⇔ (P et Q).   (idempotence du conjoint gauche dupliqué.)"""
    # ⇒ : projeter P et (P et Q) → (P et Q)
    h1 = N.assume(et(p, et(p, q)))
    fwd = N.loi_deduction(et(p, et(p, q)), conjonction_elim_droite(h1))
    # ⇐ : (P et Q) → P et (P et Q)
    h2 = N.assume(et(p, q))
    pp = conjonction_elim_gauche(h2)
    bwd = N.loi_deduction(et(p, q), conjonction_intro(pp, conjonction_intro(pp, conjonction_elim_droite(h2))))
    return conjonction_intro(fwd, bwd)


def eta_image(a="A"):
    """⊢ image(η, A) = 𝓕({∅}; A).   (SURJECTIVITÉ : l'image de η est exactement
    l'ensemble des applications de {∅} dans A.)

    z∈image(η,A) ⇔ (∃k)(k∈A et (k,z)∈η)  [AXIOME_IMAGE, liant α-renommé en k]
              ⇔ (∃k)(k∈A et (k∈A et z=((G_k,{∅}),A)))  [membre_graphe_terme pour η]
              ⇔ (∃k)(k∈A et z=((G_k,{∅}),A)) = (∃k)Lk   [idempotence du conjoint k∈A]
              ⇔ (∃Gg)(z=((Gg,{∅}),A) et Gg∈A^{∅})        [_bridge_image_applications]
              ⇔ z∈𝓕({∅};A)                              [axiome_applications].
    Par extension (liant z, A1)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_symetrie
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import congruence_existe
    vA = _t(a)
    one = UN_SOURCE()
    eta = _eta(a)
    AF = E.applications(one, vA)               # 𝓕({∅};A)
    vz, vk, vG = var("z"), var("k"), var("Gg")
    # ── (1) z∈image(η,A) ⇔ (∃k)(k∈A et (k,z)∈η)  [AXIOME_IMAGE + α] ──────────────
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, eta), vA), vz)
    impl_LtoEX = img_car0.conclusion.sous[0].sous[0].sous[0]   # ou(non L, EX)
    rhs_ex = impl_LtoEX.sous[1]
    assert rhs_ex.tag == "exists"
    nom = rhs_ex.lieur
    inner = et(appartient(var(nom), vA), appartient(E.couple(var(nom), vz), eta))
    ren = alpha_existe(nom, "k", inner)
    img_car = equivalence_transitivite(img_car0, ren)         # z∈η⟨A⟩ ⇔ (∃k)(k∈A et (k,z)∈η)
    # ── (2) (k,z)∈η ⇔ (k∈A et z=((G_k,{∅}),A))  [membre_graphe_terme] ────────────
    t = _eta_triple_A(var("c"), vA)            # valeur de η (variable de fonction « c »)
    mem = membre_graphe_terme(vA, t, "k", "z", "c", "yb")     # ((k,z)∈η) ⇔ (k∈A et z=((G_k,{∅}),A))
    # corps gauche : (k∈A et (k,z)∈η) ; congruence droite par mem
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import et_congruence_droite
    body1 = et_congruence_droite(appartient(vk, vA), mem)     # (k∈A et (k,z)∈η) ⇔ (k∈A et (k∈A et z=...))
    triple_k = E.couple(E.couple(_gv(vk), one), vA)           # ((G_k,{∅}),A)
    # ── (3) idempotence : (k∈A et (k∈A et z=...)) ⇔ (k∈A et z=...) ───────────────
    idem = _et_idem_gauche(appartient(vk, vA), egal(vz, triple_k))   # = (k∈A et z=...) = Lk
    body_eq = equivalence_transitivite(body1, idem)           # (k∈A et (k,z)∈η) ⇔ Lk
    ex_body = congruence_existe(body_eq, "k")                 # (∃k)(k∈A et (k,z)∈η) ⇔ (∃k)Lk
    img_to_Lk = equivalence_transitivite(img_car, ex_body)    # z∈η⟨A⟩ ⇔ (∃k)Lk
    # ── (4) (∃k)Lk ⇔ (∃Gg)RG  [_bridge] ────────────────────────────────────────
    bridge = _bridge_image_applications(vz, vA)               # (∃k)Lk ⇔ (∃Gg)RG
    img_to_RG = equivalence_transitivite(img_to_Lk, bridge)   # z∈η⟨A⟩ ⇔ (∃Gg)RG
    # ── (5) (∃Gg)RG ⇔ z∈𝓕({∅};A)  [axiome_applications] ────────────────────────
    ax_app = N.axiome(E.theorie_applications(one, vA, "z", "Gg"),
                      E.axiome_applications(one, vA, "z", "Gg"))   # liants t→z, G→Gg
    app_car = instancie(ax_app, vz)            # z∈𝓕 ⇔ (∃Gg)(z=((Gg,{∅}),A) et Gg∈A^{∅})
    img_to_app = equivalence_transitivite(img_to_RG, equivalence_symetrie(app_car))  # z∈η⟨A⟩ ⇔ z∈𝓕
    # ── extension (liant z) ─────────────────────────────────────────────────────
    char = N.generalisation("z", img_to_app)   # (∀z)(z∈η⟨A⟩ ⇔ z∈𝓕)
    in_AF = appartient(vz, AF)
    self_AF = N.generalisation("z", conjonction_intro(a_implique_a(in_AF), a_implique_a(in_AF)))
    return egalite_par_extension(char, self_AF, E.image(eta, vA), AF, "z")   # image(η,A)=𝓕({∅};A)


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER 4 : la bijection η, l'équipotence, et a^1 = a
# ═══════════════════════════════════════════════════════════════════════════════
def eta_bijection(a="A"):
    """⊢ est_bijection_de(η, A, 𝓕({∅};A)).   (η est une bijection A → 𝓕({∅};A).)

    Les 4 conjoints : eta_fonctionnel, eta_domaine (dom η=A), eta_injective
    (injective_dans(η,A)), eta_image (image(η,A)=𝓕({∅};A))."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
    vA = _t(a)
    func = eta_fonctionnel(a)                  # est_fonctionnel(η)
    dom = eta_domaine(a)                        # dom η=A
    inj = eta_injective(a)                      # injective_dans(η,A)
    img = eta_image(a)                          # image(η,A)=𝓕({∅};A)
    # est_bijection_de = et(et(func, dom=A), et(inj, img))
    return conjonction_intro(conjonction_intro(func, dom), conjonction_intro(inj, img))


def eq_A_applications(a="A"):
    """⊢ Eq(A, 𝓕({∅}; A)).   (A est équipotent à l'ensemble des applications {∅}→A,
    via la bijection η = v ↦ ((G_v,{∅}),A).)"""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
    vA = _t(a)
    one = UN_SOURCE()
    eta = _eta(a)
    AF = E.applications(one, vA)               # 𝓕({∅};A)
    bij = eta_bijection(a)                      # est_bijection_de(η, A, 𝓕)
    return N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), vA, AF), eta, "F"))   # Eq(A,𝓕)


def eq_applications_A(a="A"):
    """⊢ Eq(𝓕({∅}; A), A).   (symétrie de eq_A_applications via F⁻¹.)"""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
    vA = _t(a)
    one = UN_SOURCE()
    AF = E.applications(one, vA)
    eq = eq_A_applications(a)                   # Eq(A, 𝓕)
    sym = equipotence_symetrique("F", vA, AF)   # Eq(A,𝓕) ⇒ Eq(𝓕,A)
    return N.modus_ponens(eq, sym)              # Eq(𝓕({∅};A), A)


def exposant_un_egale(a="A"):
    """⊢ Card(𝓕({∅}; A)) = Card(A).   (= a^1 = a ; PROPOSITION 11, E.III.3.5, CLOS.)

    a^1 = exposant_cardinal_binaire(Card A, {∅}) = Card(𝓕({∅};A)).  Eq(𝓕({∅};A), A)
    (eq_applications_A) ; la Proposition 1 (sens direct, version TERME _prop1_direct_t)
    conclut Card(𝓕({∅};A)) = Card(A) = a."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
    vA = _t(a)
    one = UN_SOURCE()
    AF = E.applications(one, vA)                # 𝓕({∅};A)  (support de a^1)
    eq = eq_applications_A(a)                   # Eq(𝓕({∅};A), A)
    prop1 = _prop1_direct_t(AF, vA)            # Eq(𝓕,A) ⇒ Card(𝓕)=Card(A)
    return N.modus_ponens(eq, prop1)           # Card(𝓕({∅};A)) = Card(A) = a^1 = a


def exposant_cardinal_un_egale(a="a"):
    """⊢ a ^ 1 = Card(A).   (= a ; PROPOSITION 11, a^1 = a, sur l'OPÉRATEUR
    exposant_cardinal_un pour A quelconque.  CLOS.)

    Par définition exposant_cardinal_un(A) = exposant_cardinal_binaire(Card A, {∅})
    = Card(𝓕({∅};A)).  exposant_un_egale(A) : Card(𝓕({∅};A)) = Card(A) = A pour un
    cardinal A.  La conclusion est LITTÉRALEMENT exposant_cardinal_un(A) = Card(A)."""
    return exposant_un_egale(_t(a))


