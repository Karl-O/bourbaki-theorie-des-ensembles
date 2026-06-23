"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (Proposition 12) : CLÔTURE FINALE.

Bourbaki (Prop. 12) : « Soient X un ensemble et a son cardinal ; le cardinal de
l'ensemble 𝔓(X) des parties de X est 2^a. »

Ce module ASSEMBLE l'infra des rounds 24/25/26/27 (rien redéfini, additif) pour
fermer la BIJECTION caractéristique χ : 𝔓(X) → 𝓕(X; 2), Y ↦ ((χ_Y, X), 2), et en
déduire Card(𝔓X) = 2^Card X (puis restater Cantor 2^a > a).

ÉTAGE GRAPHE (le crux) — χ et ρ sont inverses AU NIVEAU DES GRAPHES :
  • round_trip_rho_chi(Y,X)   {Y⊂X} ⊢ Pre(χ_Y) = Y           [= rho_chi_identite, ρ∘χ] ;
  • chi_eq_graphe(G,X)        {G∈2^X} ⊢ χ_{Pre(G)} = G        [χ∘ρ = id : pour un
        GRAPHE FONCTIONNEL G de X dans 2, recoller la préimage de 1 et la préimage
        de 0 RECONSTRUIT G — par extensionnalité d'ensembles A1 sur les couples].

ÉTAGE BIJECTION — χ : 𝔓(X) → 𝓕(X; 2)  (Y ↦ chi_appli(Y) = ((χ_Y,X),2)) :
  • chi_bijection(X)          ⊢ est_bijection_de(W, 𝔓X, 𝓕(X;2))  [W = graphe de χ ;
        fonctionnel + dom 𝔓X (graphe_terme) + injectif (Pre(χ_Y)=Y) + image 𝓕(X;2)
        (⊃ via χ_{Pre(G)}=G : tout f=((G,X),2)∈𝓕(X;2) est atteint en Y=Pre(G))] ;
  • powerset_equipotent_applications(X)  ⊢ Eq(𝔓X, 𝓕(X;2))      [témoin W] ;

ÉTAGE CARDINAL :
  • card_parties_egale_deux_exp(X)  ⊢ Card(𝔓X) = exposant_cardinal_binaire(2, X)
        = 2^Card X   [_prop1_direct_t sur Eq + exposant_deux_base] ;
  • cantor_deux_exp(X)              ⊢ Card X < 2^Card X         [cantor_strict +
        card_parties_egale_deux_exp ; Théorème 2 de Cantor restaté].

Aucun fichier existant n'est modifié.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, non, ou, impl, equiv,
                     appartient, existe, pourtout, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, equivalence_symetrie,
                               instancie, cas, tiers_exclu, contraposition)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (egalite_par_extension,
                               extensionnalite_appliquee)
# socle 2-élément (0=∅, 1={∅}) — RÉUTILISÉ, jamais redéfini :
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import ZERO, UN
# infra réunion de graphes (recollement) — RÉUTILISÉE :
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    membre_reunion_graphes, _ex_falso)
# infra graphe-terme — RÉUTILISÉE :
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
# ── ACQUIS round 25/26 (χ_Y graphe fonctionnel X→{0,1}) — RÉUTILISÉS ──
from bourbaki.cardinaux.arithmetique.ensembles_prop12_powerset import (
    chi, _chi_gauche, _chi_droite, chi_fonctionnel, chi_est_graphe, chi_domaine,
    chi_valeur_dans_Y, chi_valeur_hors_Y)
# ── ACQUIS round 27 (emballage triple + ρ∘χ=id) — RÉUTILISÉS ──
from bourbaki.cardinaux.arithmetique.ensembles_prop12_fin import (
    chi_appli, chi_dans_applications, couple_un_dans_chi, rho_chi_identite,
    _membre_graphe_terme_coord, _non_egal_sym)
# ── ACQUIS round 24 (ρ : préimage de 1 lue sur un GRAPHE) — RÉUTILISÉS ──
from bourbaki.cardinaux.arithmetique.ensembles_powerset_deux import (
    preimage_un, preimage_membre)
# ── socle 2-élément + cible 2^Card X — RÉUTILISÉS ──
from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import (
    deux, deux_membre, deux_elements_distincts, zero_dans_deux, un_dans_deux,
    exposant_deux_base, cible_powerset_exp)
from bourbaki.cardinaux.ensembles_cardinaux import (cardinal, equipotent,
                               est_bijection_de)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# Le sens ρ∘χ = id sur 𝔓X (réexposé tel quel : Pre(χ_Y) = Y) ──────────────────
def round_trip_rho_chi(y="Y", x="X"):
    """{Y ⊂ X} ⊢ Pre(χ_Y) = Y.   (ρ∘χ = id sur 𝔓X ; = rho_chi_identite, round 27.)"""
    return rho_chi_identite(y, x)


# ═══════════════════════════════════════════════════════════════════════════════
# OUTILS sur un GRAPHE FONCTIONNEL G ∈ 2^X  (G⊂X×2, G fonctionnel, dom G = X)
# ═══════════════════════════════════════════════════════════════════════════════
def _exposant_proprietes(vG, vX):
    """{G∈2^X} ⊢ (G⊂X×2)  ,  ⊢ est_fonctionnel(G)  ,  ⊢ dom G = X.   (axiome_exposant.)"""
    deux_ens = deux()
    ax = N.axiome(E.theorie_exposant(vX, deux_ens), E.axiome_exposant(vX, deux_ens))
    car = instancie(ax, vG)                              # G∈2^X ⇔ (G⊂X×2 et fonct et dom=X)
    h = N.assume(appartient(vG, E.exposant(vX, deux_ens)))
    corps = N.modus_ponens(h, equivalence_avant(car))   # (G⊂X×2 et fonct) et dom=X
    incl = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # G⊂X×2
    fonct = conjonction_elim_droite(conjonction_elim_gauche(corps))  # est_fonctionnel(G)
    domeq = conjonction_elim_droite(corps)              # dom G = X
    return incl, fonct, domeq


def _membre_diff_imp(vz, vx, vy):
    """⊢ (z∈X et ¬(z∈Y)) ⇒ (z ∈ X∖Y).   (sens ⇐ de AXIOME_DIFF.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    car = instancie(instancie(instancie(ax, vx), vy), vz)   # z∈X∖Y ⇔ (z∈X et ¬z∈Y)
    return equivalence_arriere(car)


def _membre_diff_avant(vz, vx, vy):
    """⊢ (z ∈ X∖Y) ⇒ (z∈X et ¬(z∈Y)).   (sens ⇒ de AXIOME_DIFF.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    car = instancie(instancie(instancie(ax, vx), vy), vz)
    return equivalence_avant(car)


def _couple_dans_G_imp(vz, vv, vG, vincl, vX, deux_ens):
    """{G⊂X×2} ⊢ ((z,v)∈G) ⇒ (z∈X et v∈2).   (typage des couples d'un graphe ⊂ X×2.)

    vincl : Γ ⊢ G⊂X×2.  couple (z,v)∈G ⇒ (z,v)∈X×2 ⇒ (z∈X et v∈2)."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    cpl = E.couple(vz, vv)
    h = N.assume(appartient(cpl, vG))                   # (z,v)∈G
    in_prod = N.modus_ponens(h, instancie(vincl, cpl))  # (z,v)∈X×2
    typ = N.modus_ponens(in_prod, equivalence_avant(
        couple_dans_produit_ssi(vz, vv, vX, deux_ens)))  # z∈X et v∈2
    return N.loi_deduction(appartient(cpl, vG), typ)


def _existe_valeur(vz, vG, vdomeq, vX):
    """{dom G = X, z∈X} ⊢ (∃y)((z,y)∈G).   (z∈X=dom G ⇒ z a une image par G.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    car = instancie(instancie(ax, vG), vz)              # z∈dom G ⇔ (∃y)((z,y)∈G)
    hz = N.assume(appartient(vz, vX))                   # z∈X
    # z∈X ⇒ z∈dom G  (dom G = X, Leibniz ⇐)
    leib = N.modus_ponens(vdomeq, N.s6(E.dom(vG), vX, "w", appartient(vz, var("w"))))
    z_in_dom = N.modus_ponens(hz, equivalence_arriere(leib))   # z∈dom G
    ex = N.modus_ponens(z_in_dom, equivalence_avant(car))      # (∃y)((z,y)∈G)
    return N.loi_deduction(appartient(vz, vX), ex)


def _fonct_un_zero(vz, vG, vfonct):
    """{G fonctionnel} ⊢ ((z,1)∈G et (z,0)∈G) ⇒ (1 = 0).   (unicité de la valeur.)"""
    # est_fonctionnel(G) = (∀u)(∀v)(∀zz)(((u,v)∈G et (u,zz)∈G) ⇒ v=zz)
    inst = instancie(instancie(instancie(vfonct, vz), UN), ZERO)
    return inst                                          # ((z,1)∈G et (z,0)∈G) ⇒ 1=0


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX — χ∘ρ = id sur les GRAPHES :  {G ∈ 2^X} ⊢ χ_{Pre(G)} = G
# ═══════════════════════════════════════════════════════════════════════════════
def chi_eq_graphe(g="G", x="X"):
    """{G ∈ 2^X} ⊢ χ_{Pre(G)} = G.   (χ∘ρ = id au niveau des graphes, le crux Prop. 12.)

    Pour un GRAPHE FONCTIONNEL G : X → 2 (G⊂X×2, dom G=X), poser Y := Pre(G) =
    {z∈X | (z,1)∈G} ; alors χ_Y = (Y×{1}) ∪ ((X∖Y)×{0}) = G.  Preuve par A1 (double
    inclusion), réduction de l'appartenance aux couples (membre_reunion_graphes,
    membre_graphe_terme), typage v∈2 ⇒ v=0 ∨ v=1, et fonctionnalité de G (deux
    couples de même 1ʳᵉ coord. ont même 2ᵉ ⇒ pas de conflit 1=0)."""
    vG, vX = _t(g), _t(x)
    deux_ens = deux()
    Y = preimage_un(vG, vX)                              # Y = Pre(G)
    chiY = chi(Y, vX)
    Gc, Hc = _chi_gauche(Y), _chi_droite(Y, vX)         # Y×{1} , (X∖Y)×{0}
    diff = E.difference(vX, Y)
    incl, fonct, domeq = _exposant_proprietes(vG, vX)   # G⊂X×2 , fonct , dom G=X

    vw = var("z")   # élément générique du graphe (= binder par défaut de `inclus`)

    # ── χ_Y ⊂ G  : Gc⊂G et Hc⊂G, recollés (cas) ──────────────────────────────────
    incl_Gc = _Gc_inclus_G(Y, vX, vG)                   # Gc ⊂ G   [via z∈Pre(G)⇒(z,1)∈G]
    incl_Hc = _Hc_inclus_G(Y, vX, vG, incl, fonct, domeq)   # Hc ⊂ G
    car_reun = membre_reunion_graphes(Gc, Hc, vw)       # z∈χ_Y ⇔ (z∈Gc ou z∈Hc)
    hw = N.assume(appartient(vw, chiY))
    disj = N.modus_ponens(hw, equivalence_avant(car_reun))
    w_inG = cas(disj, instancie(incl_Gc, vw), instancie(incl_Hc, vw))   # z∈G
    imp_chiG = N.loi_deduction(appartient(vw, chiY), w_inG)
    incl_chi_G = N.generalisation("z", imp_chiG)        # χ_Y ⊂ G

    # ── G ⊂ χ_Y : w∈G⊂X×2 ⇒ w=(z,v), z∈X, v∈2 ⇒ v=0∨v=1, deux cas ────────────────
    incl_G_chi = _G_inclus_chi(Y, vX, vG, incl, fonct, domeq)   # G ⊂ χ_Y

    ext = extensionnalite_appliquee(chiY, vG)           # (χ_Y⊂G et G⊂χ_Y) ⇒ χ_Y=G
    eq = N.modus_ponens(conjonction_intro(incl_chi_G, incl_G_chi), ext)   # χ_Y=G  [G∈2^X]
    return N.loi_deduction(appartient(vG, E.exposant(vX, deux_ens)), eq)


def _Gc_inclus_G(Y, vX, vG):
    """{} ⊢ (Y×{1}) ⊂ G,  Y = Pre(G).   (tout (z,1) avec z∈Pre(G) est dans G.)

    w∈Y×{1} ⇒ w=(z,1) et z∈Y=Pre(G) (membre_graphe_terme) ; z∈Pre(G)⇒(z,1)∈G
    (preimage_membre, projection droite) ; réécriture w=(z,1) ⇒ w∈G."""
    Gc = _chi_gauche(Y)
    vw, vz = var("w"), var("z")
    # axiome graphe-terme sur w (binders u=z, v=v') : w∈Gc ⇔ (∃z)(∃v')(w=(z,v') et z∈Y et v'=1)
    th = E.theorie_graphe_terme(Y, UN, "z", "v", "yb")
    ax = N.axiome(th, E.axiome_graphe_terme(Y, UN, "z", "v", "yb"))
    car = instancie(ax, vw)                             # w∈Gc ⇔ (∃z∃v')body
    vvp = var("v")
    body = et(et(egal(vw, E.couple(vz, vvp)), appartient(vz, Y)), egal(vvp, UN))
    hb = N.assume(body)
    w_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # w=(z,v')
    z_inY = conjonction_elim_droite(conjonction_elim_gauche(hb))  # z∈Y
    vp_eq_un = conjonction_elim_droite(hb)              # v'=1
    # (z,1)∈G  depuis z∈Pre(G)
    car_pre = preimage_membre(vG, vX, vz)              # z∈Pre(G) ⇔ (z∈X et (z,1)∈G)
    z1_inG = conjonction_elim_droite(N.modus_ponens(z_inY, equivalence_avant(car_pre)))  # (z,1)∈G
    # (z,v')∈G  (v'=1, réécriture)
    zvp_inG = N.modus_ponens(z1_inG, equivalence_arriere(N.modus_ponens(
        vp_eq_un, N.s6(vvp, UN, "w2", appartient(E.couple(vz, var("w2")), vG)))))
    # w∈G  (w=(z,v'), réécriture)
    w_inG = N.modus_ponens(zvp_inG, equivalence_arriere(N.modus_ponens(
        w_eq, N.s6(vw, E.couple(vz, vvp), "w2", appartient(var("w2"), vG)))))
    imp_body = N.loi_deduction(body, w_inG)
    elim = existe_elimination(existe_elimination(imp_body, "v"), "z")
    hw = N.assume(appartient(vw, Gc))
    ex_body = N.modus_ponens(hw, equivalence_avant(car))
    w_inG_f = N.modus_ponens(ex_body, elim)
    return N.generalisation("w", N.loi_deduction(appartient(vw, Gc), w_inG_f))


def _Hc_inclus_G(Y, vX, vG, incl, fonct, domeq):
    """{G∈2^X} ⊢ ((X∖Y)×{0}) ⊂ G,  Y = Pre(G).   (tout (z,0) avec z∈X∖Pre(G) est dans G.)

    w∈Hc ⇒ w=(z,0), z∈X∖Y (membre_graphe_terme) ⇒ z∈X et ¬(z∈Y) ; z∈X=dom G donne
    (∃y)(z,y)∈G, et (z,y)∈G⊂X×2 ⇒ y∈2 ⇒ y=0 ∨ y=1 ; si y=1 alors (z,1)∈G ⇒
    z∈Pre(G)=Y (contredit ¬z∈Y) ; donc y=0, (z,0)∈G, et w=(z,0) ⇒ w∈G."""
    Hc = _chi_droite(Y, vX)
    diff = E.difference(vX, Y)
    vw, vz = var("w"), var("z")
    # w∈Hc ⇔ (∃z)(∃v)(w=(z,v) et z∈X∖Y et v=0)
    th = E.theorie_graphe_terme(diff, ZERO, "z", "v", "yb")
    ax = N.axiome(th, E.axiome_graphe_terme(diff, ZERO, "z", "v", "yb"))
    car = instancie(ax, vw)
    vvp = var("v")
    body = et(et(egal(vw, E.couple(vz, vvp)), appartient(vz, diff)), egal(vvp, ZERO))
    hb = N.assume(body)
    w_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # w=(z,v')
    z_inDiff = conjonction_elim_droite(conjonction_elim_gauche(hb))   # z∈X∖Y
    vp_eq_zero = conjonction_elim_droite(hb)                      # v'=0
    z_inX = conjonction_elim_gauche(N.modus_ponens(z_inDiff, _membre_diff_avant(vz, vX, Y)))   # z∈X
    n_z_inY = conjonction_elim_droite(N.modus_ponens(z_inDiff, _membre_diff_avant(vz, vX, Y))) # ¬z∈Y
    # (z,0)∈G  via le lemme « z∈X, ¬z∈Pre(G) ⇒ (z,0)∈G »
    z0_inG = _couple_zero_dans_G(vz, vG, vX, incl, fonct, domeq, z_inX, n_z_inY, Y)  # (z,0)∈G
    # (z,v')∈G  (v'=0)
    zvp_inG = N.modus_ponens(z0_inG, equivalence_arriere(N.modus_ponens(
        vp_eq_zero, N.s6(vvp, ZERO, "w2", appartient(E.couple(vz, var("w2")), vG)))))
    # w∈G  (w=(z,v'))
    w_inG = N.modus_ponens(zvp_inG, equivalence_arriere(N.modus_ponens(
        w_eq, N.s6(vw, E.couple(vz, vvp), "w2", appartient(var("w2"), vG)))))
    imp_body = N.loi_deduction(body, w_inG)
    elim = existe_elimination(existe_elimination(imp_body, "v"), "z")
    hw = N.assume(appartient(vw, Hc))
    ex_body = N.modus_ponens(hw, equivalence_avant(car))
    w_inG_f = N.modus_ponens(ex_body, elim)
    return N.generalisation("w", N.loi_deduction(appartient(vw, Hc), w_inG_f))


def _couple_zero_dans_G(vz, vG, vX, incl, fonct, domeq, z_inX, n_z_inY, Y):
    """{G∈2^X, z∈X, ¬(z∈Pre(G))} ⊢ (z,0) ∈ G.   (la valeur de G en z hors Pre(G) est 0.)

    z∈X=dom G ⇒ (∃y)((z,y)∈G) ; (z,y)∈G⊂X×2 ⇒ y∈2 ⇒ y=0 ∨ y=1 ; y=1 ⇒ (z,1)∈G ⇒
    z∈Pre(G) (preimage), absurde ; donc y=0, soit (z,0)∈G."""
    vy = var("y")
    ex_y = N.modus_ponens(z_inX, _existe_valeur(vz, vG, domeq, vX))   # (∃y)((z,y)∈G)
    # sous (z,y)∈G : y∈2, deux cas
    hzy = N.assume(appartient(E.couple(vz, vy), vG))                  # (z,y)∈G
    y_in2 = conjonction_elim_droite(N.modus_ponens(hzy,
        _couple_dans_G_imp(vz, vy, vG, incl, vX, deux())))           # y∈2
    y_eq = N.modus_ponens(y_in2, equivalence_avant(deux_membre(vy)))  # y=0 ou y=1  (∅ ou {∅})
    # cas y=0 : (z,0)∈G par réécriture
    h_y0 = N.assume(egal(vy, ZERO))
    zy_z0 = N.modus_ponens(hzy, equivalence_avant(N.modus_ponens(
        h_y0, N.s6(vy, ZERO, "w2", appartient(E.couple(vz, var("w2")), vG)))))   # (z,0)∈G
    br0 = N.loi_deduction(egal(vy, ZERO), zy_z0)                     # y=0 ⇒ (z,0)∈G
    # cas y=1 : (z,1)∈G ⇒ z∈Pre(G) ⇒ contradiction avec ¬z∈Pre(G) ⇒ ex falso (z,0)∈G
    h_y1 = N.assume(egal(vy, UN))
    zy_z1 = N.modus_ponens(hzy, equivalence_avant(N.modus_ponens(
        h_y1, N.s6(vy, UN, "w2", appartient(E.couple(vz, var("w2")), vG)))))     # (z,1)∈G
    car_pre = preimage_membre(vG, vX, vz)              # z∈Pre(G) ⇔ (z∈X et (z,1)∈G)
    z_inPre = N.modus_ponens(conjonction_intro(z_inX, zy_z1), equivalence_arriere(car_pre))  # z∈Pre(G)
    z0_falso = _ex_falso(z_inPre, n_z_inY, appartient(E.couple(vz, ZERO), vG))   # (z,0)∈G
    br1 = N.loi_deduction(egal(vy, UN), z0_falso)      # y=1 ⇒ (z,0)∈G
    z0_inG = cas(y_eq, br0, br1)                       # (z,0)∈G   [sous (z,y)∈G]
    imp_y = N.loi_deduction(appartient(E.couple(vz, vy), vG), z0_inG)
    return N.modus_ponens(ex_y, existe_elimination(imp_y, "y"))      # (z,0)∈G


def _G_inclus_chi(Y, vX, vG, incl, fonct, domeq):
    """{G∈2^X} ⊢ G ⊂ χ_{Pre(G)}.   (tout couple de G est dans la fonction caractéristique.)

    w∈G⊂X×2 ⇒ w=(z,v), z∈X, v∈2 ⇒ v=0 ∨ v=1.  v=1 : (z,1)∈G ⇒ z∈Pre(G) ⇒ (z,1)∈χ_Y ;
    v=0 : (z,0)∈G ⇒ z∉Pre(G) (sinon (z,1)∈G + fonct ⇒ 1=0) ⇒ z∈X∖Y ⇒ (z,0)∈χ_Y."""
    from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import _instance_produit
    chiY = chi(Y, vX)
    diff = E.difference(vX, Y)
    deux_ens = deux()
    # élément = "z" (binder par défaut de `inclus`) ; coords = "p","q" (binders du produit)
    vw, vz, vv = var("z"), var("p"), var("q")
    car_prod = _instance_produit(vX, deux_ens, vw)      # z∈X×2 ⇔ (∃p∃q)(z=(p,q) et p∈X et q∈2)
    body = et(et(egal(vw, E.couple(vz, vv)), appartient(vz, vX)), appartient(vv, deux_ens))
    hb = N.assume(body)
    w_eq = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # w=(z,v)
    z_inX = conjonction_elim_droite(conjonction_elim_gauche(hb))  # z∈X
    v_in2 = conjonction_elim_droite(hb)                          # v∈2
    # (z,v)∈G  (w∈G et w=(z,v))
    hw = N.assume(appartient(vw, vG))                            # w∈G  (hyp locale, déchargée plus tard)
    zv_inG = N.modus_ponens(hw, equivalence_avant(N.modus_ponens(
        w_eq, N.s6(vw, E.couple(vz, vv), "w2", appartient(var("w2"), vG)))))   # (z,v)∈G
    v_eq = N.modus_ponens(v_in2, equivalence_avant(deux_membre(vv)))   # v=0 ou v=1
    # cas v=1
    h_v1 = N.assume(egal(vv, UN))
    z1_inG = N.modus_ponens(zv_inG, equivalence_avant(N.modus_ponens(
        h_v1, N.s6(vv, UN, "w2", appartient(E.couple(vz, var("w2")), vG)))))   # (z,1)∈G
    car_pre = preimage_membre(vG, vX, vz)
    z_inPre = N.modus_ponens(conjonction_intro(z_inX, z1_inG), equivalence_arriere(car_pre))  # z∈Pre(G)
    z1_chi = N.modus_ponens(z_inPre, N.loi_deduction(appartient(vz, Y),
                            chi_valeur_dans_Y(Y, vX, "p")))     # (z,1)∈χ_Y
    # (z,v)∈χ_Y  (v=1)
    zv_chi_1 = N.modus_ponens(z1_chi, equivalence_avant(N.modus_ponens(
        N.modus_ponens(h_v1, symetrie(vv, UN)),
        N.s6(UN, vv, "w2", appartient(E.couple(vz, var("w2")), chiY)))))   # (z,v)∈χ_Y
    w_chi_1 = N.modus_ponens(zv_chi_1, equivalence_avant(N.modus_ponens(
        N.modus_ponens(w_eq, symetrie(vw, E.couple(vz, vv))),
        N.s6(E.couple(vz, vv), vw, "w2", appartient(var("w2"), chiY)))))   # w∈χ_Y
    br1 = N.loi_deduction(egal(vv, UN), w_chi_1)        # v=1 ⇒ w∈χ_Y
    # cas v=0
    h_v0 = N.assume(egal(vv, ZERO))
    z0_inG = N.modus_ponens(zv_inG, equivalence_avant(N.modus_ponens(
        h_v0, N.s6(vv, ZERO, "w2", appartient(E.couple(vz, var("w2")), vG)))))  # (z,0)∈G
    # ¬(z∈Pre(G)) : si z∈Pre(G) alors (z,1)∈G, avec (z,0)∈G + fonct ⇒ 1=0 absurde
    n_z_inPre = _z_hors_pre(vz, vG, vX, fonct, z0_inG, z_inX)   # ¬(z∈Pre(G))
    z_inDiff = N.modus_ponens(conjonction_intro(z_inX, n_z_inPre),
                              _membre_diff_imp(vz, vX, Y))      # z∈X∖Y
    z0_chi = N.modus_ponens(z_inDiff, N.loi_deduction(appartient(vz, diff),
                            chi_valeur_hors_Y(Y, vX, "p")))     # (z,0)∈χ_Y
    zv_chi_0 = N.modus_ponens(z0_chi, equivalence_avant(N.modus_ponens(
        N.modus_ponens(h_v0, symetrie(vv, ZERO)),
        N.s6(ZERO, vv, "w2", appartient(E.couple(vz, var("w2")), chiY)))))   # (z,v)∈χ_Y
    w_chi_0 = N.modus_ponens(zv_chi_0, equivalence_avant(N.modus_ponens(
        N.modus_ponens(w_eq, symetrie(vw, E.couple(vz, vv))),
        N.s6(E.couple(vz, vv), vw, "w2", appartient(var("w2"), chiY)))))
    br0 = N.loi_deduction(egal(vv, ZERO), w_chi_0)      # v=0 ⇒ w∈χ_Y
    w_chi = cas(v_eq, br0, br1)                         # w∈χ_Y   [sous body, w∈G]
    # décharger w∈G, body, éliminer témoins z,v
    imp_w = N.loi_deduction(appartient(vw, vG), w_chi)  # w∈G ⇒ w∈χ_Y   [sous body]
    imp_body = N.loi_deduction(body, imp_w)             # body ⇒ (w∈G ⇒ w∈χ_Y)
    elim = existe_elimination(existe_elimination(imp_body, "q"), "p")  # (∃p∃q)body ⇒ (m∈G⇒m∈χ_Y)
    # w∈G ⇒ w∈X×2 ⇒ (∃z∃v)body ⇒ (w∈G ⇒ w∈χ_Y), donc w∈G ⇒ w∈χ_Y
    hw2 = N.assume(appartient(vw, vG))
    w_prod = N.modus_ponens(hw2, instancie(incl, vw))  # w∈X×2
    ex_body = N.modus_ponens(w_prod, equivalence_avant(car_prod))   # (∃z∃v)body
    w_imp_chi = N.modus_ponens(ex_body, elim)          # w∈G ⇒ w∈χ_Y
    w_in_chi = N.modus_ponens(hw2, w_imp_chi)          # z∈χ_Y
    return N.generalisation("z", N.loi_deduction(appartient(vw, vG), w_in_chi))   # G ⊂ χ_Y


def _z_hors_pre(vz, vG, vX, fonct, z0_inG, z_inX):
    """{(z,0)∈G, G fonctionnel} ⊢ ¬(z ∈ Pre(G)).   (z a la valeur 0, donc pas 1, donc ∉Pre(G).)

    Si z∈Pre(G) alors (z,1)∈G ; avec (z,0)∈G la fonctionnalité donne 1=0, contredisant
    deux_elements_distincts (¬(∅={∅}) = ¬(0=1))."""
    car_pre = preimage_membre(vG, vX, vz)              # z∈Pre(G) ⇔ (z∈X et (z,1)∈G)
    h = N.assume(appartient(vz, preimage_un(vG, vX)))  # z∈Pre(G)
    z1_inG = conjonction_elim_droite(N.modus_ponens(h, equivalence_avant(car_pre)))   # (z,1)∈G
    un_eq_zero = N.modus_ponens(conjonction_intro(z1_inG, z0_inG),
                                _fonct_un_zero(vz, vG, fonct))   # 1=0
    n_un_eq_zero = N.modus_ponens(deux_elements_distincts(), _non_egal_sym(ZERO, UN))  # ¬(1=0)
    falso = _ex_falso(un_eq_zero, n_un_eq_zero, non(appartient(vz, preimage_un(vG, vX))))
    return N.modus_ponens(N.loi_deduction(appartient(vz, preimage_un(vG, vX)), falso),
                          N.s1(non(appartient(vz, preimage_un(vG, vX)))))   # ¬(z∈Pre(G))
