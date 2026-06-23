"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (Proposition 12) : la BIJECTION et le cardinal.

χ : 𝔓(X) → 𝓕(X; 2),  Y ↦ chi_appli(Y) = ((χ_Y, X), 2)  est une BIJECTION ; son
graphe est W = graphe_terme(𝔓X, chi_appli(Y), "Y").  On certifie les quatre
conjoints de est_bijection_de(W, 𝔓X, 𝓕(X;2)) :

  • W fonctionnel + dom W = 𝔓X        (graphe_terme, automatique) ;
  • W injectif sur 𝔓X                 (ρ∘χ = id : Pre(χ_Y)=Y ⇒ χ_Y=χ_{Y'} ⇒ Y=Y') ;
  • image(W, 𝔓X) = 𝓕(X;2)             (⊂ : chi_appli(Y)∈𝓕(X;2) ; ⊃ : tout f=((G,X),2)
        est atteint en Y=Pre(G) car χ_{Pre(G)}=G, le crux chi_eq_graphe).

D'où Eq(𝔓X, 𝓕(X;2)) (témoin W), puis Card(𝔓X) = Card(𝓕(X;2)) = 2^Card X
(_prop1_direct_t + exposant_deux_base), et enfin Cantor 2^a > a (cantor_strict).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, ou, impl, equiv,
                     appartient, existe, pourtout, inclus, subst_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (existe_elimination,
                               alpha_existe)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, membre_graphe_terme)
from bourbaki.cardinaux.ensembles_cantor import (graphe_terme_domaine,
                               graphe_terme_valeur)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes
# socle 2-élément :
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_powerset_exp import (
    deux, exposant_deux_base, cible_powerset_exp)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
    preimage_un, preimage_inclus, membre_parties_t, partie_dans_parties)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_prop12_fin import (
    chi_appli, chi_dans_applications)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_prop12_powerset import chi
from bourbaki.cardinaux.ensembles_cardinaux import (cardinal, equipotent,
                               est_bijection_de, inf_strict_card)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
from ._crux import chi_eq_graphe, rho_chi_identite


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _rho_chi_id_t(vY, vX):
    """⊢ (Y ⊂ X) ⇒ (Pre(χ_Y) = Y) pour un TERME Y quelconque.

    Version TERME de rho_chi_identite (qui ne prend que des NOMS) : on généralise
    en « Y » puis on instancie au terme vY — l'instanciation α-renomme les liants
    internes (u,v,z) de la machinerie, donc aucune capture même si vY = var("u")."""
    gen = N.generalisation("Y", rho_chi_identite("Y", vX))   # (∀Y)(Y⊂X ⇒ Pre(χ_Y)=Y)
    return instancie(gen, vY)                                # Y⊂X ⇒ Pre(χ_Y)=Y


def _W(vX):
    """W := graphe_terme(𝔓X, chi_appli(Y), "Y")  = graphe de  Y ↦ ((χ_Y,X),2).

    La fonction caractéristique χ : 𝔓X → 𝓕(X;2) au niveau du GRAPHE.  Liant « Y »
    (≠ liants internes {x,y} de la machinerie graphe-terme, ≠ trou « w »)."""
    return E.graphe_terme(E.parties(vX), chi_appli(var("Y"), vX), "Y")


# ═══════════════════════════════════════════════════════════════════════════════
# CONJOINTS 1 & 2 — W fonctionnel  et  dom W = 𝔓X   (automatiques, graphe-terme)
# ═══════════════════════════════════════════════════════════════════════════════
def W_fonctionnel(x="X"):
    """⊢ est_fonctionnel(W).   (χ associe à chaque Y∈𝔓X UNE application ; cas C54.)"""
    vX = _t(x)
    return graphe_terme_fonctionnel(E.parties(vX), chi_appli(var("Y"), vX), "Y", "y")


def W_domaine(x="X"):
    """⊢ dom(W) = 𝔓X.   (χ est définie sur TOUT 𝔓X.)"""
    vX = _t(x)
    return graphe_terme_domaine(E.parties(vX), chi_appli(var("Y"), vX), "Y", "y", "z")


def W_valeur(x="X", u="u"):
    """{u ∈ 𝔓X} ⊢ W(u) = chi_appli(u) = ((χ_u, X), 2).   (la valeur de χ en u.)

    ⚠ point d'évaluation « u » ≠ liant « Y » de W (sinon capture de la valeur)."""
    vX = _t(x)
    return graphe_terme_valeur(E.parties(vX), chi_appli(var("Y"), vX), u, "Y", "y")


# ═══════════════════════════════════════════════════════════════════════════════
# CONJOINT 3 — W INJECTIF sur 𝔓X   (Pre(χ_Y) = Y ⇒ χ_Y=χ_{Y'} ⇒ Y=Y')
# ═══════════════════════════════════════════════════════════════════════════════
def W_injective(x="X"):
    """⊢ injective_dans(W, 𝔓X).   (χ injective : ((χ_u,X),2)=((χ_v,X),2) ⇒ u=v.)

    W(u)=chi_appli(u)=((χ_u,X),2) (W_valeur).  De W(u)=W(v) : double
    couple_egal_implique_composantes donne χ_u=χ_v ; par congruence Pre(χ_u)=Pre(χ_v) ;
    or u,v∈𝔓X ⇒ u⊂X, v⊂X, et rho_chi_identite donne Pre(χ_u)=u, Pre(χ_v)=v ; d'où u=v."""
    vX, vu, vv = _t(x), var("u"), var("up")
    W = _W(vX)
    deux_ens = deux()
    chu, chv = chi(vu, vX), chi(vv, vX)
    triple_u = chi_appli(vu, vX)        # ((χ_u,X),2)
    triple_v = chi_appli(vv, vX)        # ((χ_v,X),2)
    inner_u = E.couple(chu, vX)         # (χ_u, X)
    inner_v = E.couple(chv, vX)         # (χ_v, X)
    hyp = et(et(appartient(vu, E.parties(vX)), appartient(vv, E.parties(vX))),
             egal(E.valeur(W, vu), E.valeur(W, vv)))
    h = N.assume(hyp)
    u_inP = conjonction_elim_gauche(conjonction_elim_gauche(h))     # u∈𝔓X
    v_inP = conjonction_elim_droite(conjonction_elim_gauche(h))     # v∈𝔓X
    val_eq = conjonction_elim_droite(h)                            # W(u)=W(v)
    # W(u)=((χ_u,X),2) , W(v)=((χ_v,X),2)
    Wu = N.modus_ponens(u_inP, N.loi_deduction(appartient(vu, E.parties(vX)),
                                               W_valeur(x, "u")))   # W(u)=triple_u
    Wv = N.modus_ponens(v_inP, N.loi_deduction(appartient(vv, E.parties(vX)),
                                               W_valeur(x, "up")))  # W(v)=triple_v
    # triple_u = triple_v
    tu_Wu = N.modus_ponens(Wu, symetrie(E.valeur(W, vu), triple_u))     # triple_u=W(u)
    tu_tv = composer_egalites(composer_egalites(tu_Wu, val_eq), Wv)     # triple_u=triple_v
    # ((χ_u,X),2)=((χ_v,X),2) ⇒ (χ_u,X)=(χ_v,X)   (composante gauche)
    comps1 = N.modus_ponens(tu_tv, couple_egal_implique_composantes(
        inner_u, deux_ens, inner_v, deux_ens))                     # (χ_u,X)=(χ_v,X) et 2=2
    inner_eq = conjonction_elim_gauche(comps1)                     # (χ_u,X)=(χ_v,X)
    # (χ_u,X)=(χ_v,X) ⇒ χ_u=χ_v   (composante gauche)
    comps2 = N.modus_ponens(inner_eq, couple_egal_implique_composantes(chu, vX, chv, vX))
    chi_eq = conjonction_elim_gauche(comps2)                       # χ_u=χ_v
    # Pre(χ_u)=Pre(χ_v)   (congruence sur Pre = preimage_un(·, X))
    pre_eq = N.modus_ponens(chi_eq, congruence_terme(chu, chv,
        preimage_un(var("w"), vX), "w"))                          # Pre(χ_u)=Pre(χ_v)
    # u⊂X , v⊂X   (de u,v ∈ 𝔓X)
    u_incl = N.modus_ponens(u_inP, equivalence_avant(membre_parties_t(vu, vX)))   # u⊂X
    v_incl = N.modus_ponens(v_inP, equivalence_avant(membre_parties_t(vv, vX)))   # v⊂X
    # Pre(χ_u)=u , Pre(χ_v)=v   (rho_chi_identite)
    preu_u = N.modus_ponens(u_incl, _rho_chi_id_t(vu, vX))         # Pre(χ_u)=u
    prev_v = N.modus_ponens(v_incl, _rho_chi_id_t(vv, vX))         # Pre(χ_v)=v
    # u = Pre(χ_u) = Pre(χ_v) = v
    u_preu = N.modus_ponens(preu_u, symetrie(preimage_un(chu, vX), vu))   # u=Pre(χ_u)
    u_eq_v = composer_egalites(composer_egalites(u_preu, pre_eq), prev_v)  # u=v
    inner = N.loi_deduction(hyp, u_eq_v)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(W, 𝔓X)


# ═══════════════════════════════════════════════════════════════════════════════
# CONJOINT 4 — image(W, 𝔓X) = 𝓕(X;2)   (χ surjective : χ_{Pre(G)}=G atteint tout f)
# ═══════════════════════════════════════════════════════════════════════════════
def _image_membre_W(vX, vt):
    """⊢ (z ∈ image(W,𝔓X)) ⇔ (∃S)(S∈𝔓X et (S,z)∈W).   (AXIOME_IMAGE, binder « S ».)"""
    W = _W(vX)
    PX = E.parties(vX)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car0 = instancie(instancie(instancie(ax, W), PX), vt)   # z∈img ⇔ (∃x)(x∈𝔓X et (x,z)∈W)
    inner_x = et(appartient(var("x"), PX), appartient(E.couple(var("x"), vt), W))
    ren = alpha_existe("x", "S", inner_x)                   # (∃x)…x… ⇔ (∃S)…S…
    return equivalence_transitivite(car0, ren)


def _couple_dans_W(vS, vX):
    """{S ∈ 𝔓X} ⊢ (S, chi_appli(S)) ∈ W,  S TERME quelconque.

    graphe_terme_couple_dans n'accepte qu'un NOM de point ; on prouve pour le nom
    « s » (≠ liant « Y » de W), généralise puis instancie au terme S — l'instanciation
    α-renomme les liants internes (pas de capture même si S = preimage_un(G,X))."""
    from bourbaki.cardinaux.ensembles_cantor import graphe_terme_couple_dans
    base = graphe_terme_couple_dans(E.parties(vX), chi_appli(var("Y"), vX), "s", "Y", "y")
    imp = N.loi_deduction(appartient(var("s"), E.parties(vX)), base)   # s∈𝔓X ⇒ (s,chi_appli(s))∈W
    return instancie(N.generalisation("s", imp), vS)     # S∈𝔓X ⇒ (S,chi_appli(S))∈W


def _membre_W_carac(vS, vt, vX):
    """⊢ ((S, z) ∈ W) ⇔ (S∈𝔓X et z = chi_appli(S)),  S TERME quelconque (coord. « z »).

    membre_graphe_terme n'accepte que des NOMS ; on prouve pour le nom « s »,
    généralise « s » puis instancie au terme S.  La 2ᵉ coordonnée est « z »."""
    base = membre_graphe_terme(E.parties(vX), chi_appli(var("Y"), vX),
                               "s", "z", "Y", "y")        # ((s,z)∈W) ⇔ (s∈𝔓X et z=chi_appli(s))
    return instancie(N.generalisation("s", base), vS)     # ((S,z)∈W) ⇔ (S∈𝔓X et z=chi_appli(S))


def W_image_egale_applications(x="X"):
    """⊢ image(W, 𝔓X) = 𝓕(X; 2).   (χ est SURJECTIVE de 𝔓X sur l'espace 𝓕(X;2).)

    ⊂ : t∈img(W,𝔓X) ⇒ (S,t)∈W pour un S∈𝔓X ⇒ t=chi_appli(S) (membre_graphe_terme) ⇒
        t∈𝓕(X;2) (chi_dans_applications, S⊂X) ;
    ⊃ : t∈𝓕(X;2) ⇒ t=((G,X),2), G∈2^X ; poser S:=Pre(G)⊂X∈𝔓X ; chi_appli(S) =
        ((χ_{Pre(G)},X),2) = ((G,X),2) = t  (crux chi_eq_graphe) ; donc (S,t)∈W,
        S∈𝔓X ⇒ t∈img(W,𝔓X)."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    vX, vt = _t(x), var("z")        # élément générique = « z » (binder par défaut de `inclus`)
    W = _W(vX)
    PX = E.parties(vX)
    deux_ens = deux()
    Appl = E.applications(vX, deux_ens)
    img = E.image(W, PX)
    car_img = _image_membre_W(vX, vt)        # z∈img ⇔ (∃S)(S∈𝔓X et (S,z)∈W)

    # ── ⊂ : t∈img ⇒ t∈𝓕(X;2) ─────────────────────────────────────────────────────
    vS = var("S")
    body = et(appartient(vS, PX), appartient(E.couple(vS, vt), W))
    hb = N.assume(body)
    S_inP = conjonction_elim_gauche(hb)                   # S∈𝔓X
    St_inW = conjonction_elim_droite(hb)                  # (S,t)∈W
    carac = _membre_W_carac(vS, vt, vX)                   # (S,t)∈W ⇔ (S∈𝔓X et t=chi_appli(S))
    t_eq = conjonction_elim_droite(N.modus_ponens(St_inW, equivalence_avant(carac)))  # t=chi_appli(S)
    S_incl = N.modus_ponens(S_inP, equivalence_avant(membre_parties_t(vS, vX)))   # S⊂X
    cS_inAppl = N.modus_ponens(S_incl, chi_dans_applications(vS, vX))   # chi_appli(S)∈𝓕(X;2)
    # t∈𝓕(X;2)  (t=chi_appli(S), Leibniz ⇐)
    t_inAppl = N.modus_ponens(cS_inAppl, equivalence_arriere(N.modus_ponens(
        t_eq, N.s6(vt, chi_appli(vS, vX), "w", appartient(var("w"), Appl)))))
    imp_body = N.loi_deduction(body, t_inAppl)
    elim = existe_elimination(imp_body, "S")             # (∃S)body ⇒ t∈𝓕(X;2)
    ht = N.assume(appartient(vt, img))
    ex_body = N.modus_ponens(ht, equivalence_avant(car_img))
    t_inAppl_f = N.modus_ponens(ex_body, elim)
    incl_LR = N.generalisation("z", N.loi_deduction(appartient(vt, img), t_inAppl_f))   # img ⊂ 𝓕(X;2)

    # ── ⊃ : t∈𝓕(X;2) ⇒ t∈img ───────────────────────────────────────────────────
    incl_RL = _applications_inclus_image(vX)            # 𝓕(X;2) ⊂ img

    ext = extensionnalite_appliquee(img, Appl)
    return N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)   # image(W,𝔓X)=𝓕(X;2)


def _applications_inclus_image(vX):
    """⊢ 𝓕(X;2) ⊂ image(W, 𝔓X).   (surjectivité : tout f=((G,X),2) est atteint en Pre(G).)"""
    deux_ens = deux()
    Appl = E.applications(vX, deux_ens)
    W = _W(vX)
    PX = E.parties(vX)
    img = E.image(W, PX)
    vt = var("z")        # élément générique = « z » (binder par défaut de `inclus`)
    car_img = _image_membre_W(vX, vt)        # z∈img ⇔ (∃S)(S∈𝔓X et (S,z)∈W)
    # t∈𝓕(X;2) ⇔ (∃G)(t=((G,X),2) et G∈2^X)
    ax_appl = N.axiome(E.theorie_applications(vX, deux_ens),
                       E.axiome_applications(vX, deux_ens))
    car_appl = instancie(ax_appl, vt)        # t∈𝓕(X;2) ⇔ (∃G)(t=((G,X),2) et G∈2^X)
    vG = var("G")
    body_G = et(egal(vt, E.couple(E.couple(vG, vX), deux_ens)),
                appartient(vG, E.exposant(vX, deux_ens)))
    hb = N.assume(body_G)
    t_eq_triple = conjonction_elim_gauche(hb)            # t=((G,X),2)
    G_in_exp = conjonction_elim_droite(hb)               # G∈2^X
    Y = preimage_un(vG, vX)                              # S := Pre(G)
    # S ⊂ X  ⇒  S ∈ 𝔓X
    S_incl = preimage_inclus(vG, vX)                     # Pre(G)⊂X
    S_inP = N.modus_ponens(S_incl, N.loi_deduction(inclus(Y, vX),
                           partie_dans_parties(Y, vX)))  # Pre(G)∈𝔓X
    # chi_appli(S) = ((χ_{Pre(G)},X),2) = ((G,X),2) = t
    chi_eq = N.modus_ponens(G_in_exp, chi_eq_graphe(vG, vX))   # χ_{Pre(G)}=G
    # ((χ_{Pre(G)},X),2) = ((G,X),2)   (congruence sur la coord la plus interne)
    triple_eq = N.modus_ponens(chi_eq, congruence_terme(chi(Y, vX), vG,
        E.couple(E.couple(var("w"), vX), deux_ens), "w"))   # chi_appli(S)=((G,X),2)
    cappli_eq_t = composer_egalites(triple_eq,
        N.modus_ponens(t_eq_triple, symetrie(vt, E.couple(E.couple(vG, vX), deux_ens))))  # chi_appli(S)=t
    # (S, chi_appli(S)) ∈ W  ,  puis réécriture chi_appli(S)→t : (S,t)∈W
    S_cappli_inW = N.modus_ponens(S_inP, _couple_dans_W(Y, vX))   # (S,chi_appli(S))∈W
    St_inW = N.modus_ponens(S_cappli_inW, equivalence_avant(N.modus_ponens(
        cappli_eq_t, N.s6(chi_appli(Y, vX), vt, "w",
                          appartient(E.couple(Y, var("w")), W)))))   # (S,t)∈W
    # (∃S)(S∈𝔓X et (S,t)∈W)  témoin S = Pre(G)
    inner = et(appartient(var("S"), PX), appartient(E.couple(var("S"), vt), W))
    ex_S = N.modus_ponens(conjonction_intro(S_inP, St_inW), N.s5(inner, Y, "S"))   # (∃S)inner
    t_in_img = N.modus_ponens(ex_S, equivalence_arriere(car_img))   # t∈img
    imp_bodyG = N.loi_deduction(body_G, t_in_img)
    elimG = existe_elimination(imp_bodyG, "G")           # (∃G)body_G ⇒ t∈img
    ht = N.assume(appartient(vt, Appl))
    exG = N.modus_ponens(ht, equivalence_avant(car_appl))
    t_in_img_f = N.modus_ponens(exG, elimG)
    return N.generalisation("z", N.loi_deduction(appartient(vt, Appl), t_in_img_f))


# ═══════════════════════════════════════════════════════════════════════════════
# LA BIJECTION χ : 𝔓X → 𝓕(X;2)  +  Eq(𝔓X, 𝓕(X;2))  +  Card(𝔓X) = 2^Card X
# ═══════════════════════════════════════════════════════════════════════════════
def chi_bijection(x="X"):
    """⊢ est_bijection_de(W, 𝔓X, 𝓕(X;2)).   (χ : 𝔓X → 𝓕(X;2) est une BIJECTION.)

    Les quatre conjoints : W fonctionnel (W_fonctionnel), dom W = 𝔓X (W_domaine),
    W injectif sur 𝔓X (W_injective), image(W,𝔓X) = 𝓕(X;2) (W_image_egale_applications).
    Structure est_bijection_de = (fonct et dom=𝔓X) et (injective_dans et image=)."""
    vX = _t(x)
    fonct = W_fonctionnel(x)
    dom_eq = W_domaine(x)
    inj = W_injective(x)
    surj = W_image_egale_applications(x)             # = est_surjective(W,𝔓X,𝓕(X;2))
    # est_bijective = injective_dans et est_surjective
    bij = conjonction_intro(inj, surj)
    # est_bijection_de = (fonct et dom=𝔓X) et est_bijective
    return conjonction_intro(conjonction_intro(fonct, dom_eq), bij)


def powerset_equipotent_applications(x="X"):
    """⊢ Eq(𝔓X, 𝓕(X;2)).   (𝔓X et 𝓕(X;2) sont ÉQUIPOTENTS, témoin la bijection W.)

    Eq(𝔓X,𝓕(X;2)) = (∃F)(est_bijection_de(F,𝔓X,𝓕(X;2))) ; témoin F := W (S5)."""
    vX = _t(x)
    deux_ens = deux()
    PX, Appl = E.parties(vX), E.applications(vX, deux_ens)
    bij = chi_bijection(x)                           # est_bijection_de(W, 𝔓X, 𝓕(X;2))
    corps = est_bijection_de(var("F"), PX, Appl)     # corps avec liant F
    return N.modus_ponens(bij, N.s5(corps, _W(vX), "F"))   # (∃F)est_bijection_de(F,𝔓X,𝓕(X;2))


def card_parties_egale_deux_exp(x="X"):
    """⊢ Card(𝔓X) = exposant_cardinal_binaire(2, X) = 2^Card X.   (PROPOSITION 12.)

    Eq(𝔓X,𝓕(X;2)) (powerset_equipotent_applications) ⇒ Card(𝔓X)=Card(𝓕(X;2))
    (Proposition 1, sens direct, _prop1_direct_t) ; et Card(𝓕(X;2)) =
    exposant_cardinal_binaire(2,X) (exposant_deux_base, réflexivité)."""
    vX = _t(x)
    deux_ens = deux()
    PX, Appl = E.parties(vX), E.applications(vX, deux_ens)
    eq = powerset_equipotent_applications(x)         # Eq(𝔓X, 𝓕(X;2))
    prop1 = _prop1_direct_t(PX, Appl)                # Eq(𝔓X,𝓕(X;2)) ⇒ Card(𝔓X)=Card(𝓕(X;2))
    card_eq = N.modus_ponens(eq, prop1)              # Card(𝔓X) = Card(𝓕(X;2))
    base = exposant_deux_base(x)                     # 2^Card X = Card(𝓕(X;2))
    base_sym = N.modus_ponens(base, symetrie(        # Card(𝓕(X;2)) = 2^Card X
        exposant_cardinal_binaire(deux_ens, vX), cardinal(Appl)))
    return composer_egalites(card_eq, base_sym)      # Card(𝔓X) = 2^Card X


def cantor_deux_exp(x="X"):
    """⊢ Card X < 2^Card X.   (THÉORÈME 2 de Cantor restaté, E.III.3.6 : 2^a > a.)

    cantor_strict ⊢ X < P(X) (= inf_strict_card(X, P(X))).  REPORTÉ tel quel : le
    pont « X < P(X) (au sens des INJECTIONS de SETS) ⇒ Card X < 2^Card X (au sens
    de l'ORDRE des CARDINAUX) » exige inf_strict_card(Card X, Card P(X)) — la
    monotonie de Card pour ≤ et la fidélité ≠ — non encore disponible (voir REPORTE)."""
    raise NotImplementedError(
        "Cantor restaté 2^Card X > Card X reporté : cantor_strict donne X<P(X) au "
        "niveau des SETS (inf_strict_card(X,P(X))) ; le pont vers inf_strict_card("
        "Card X, 2^Card X) (ordre des CARDINAUX) demande la monotonie de Card pour "
        "≤ + Card(𝔓X)=2^Card X (card_parties_egale_deux_exp, CLOS).")
