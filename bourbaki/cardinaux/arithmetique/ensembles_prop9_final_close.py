"""§III.3.5 — PROPOSITION 9 (forme exponentielle), CLÔTURE INCONDITIONNELLE :
le DERNIER PAS (DIRECTION B = ψ-injectivité) puis l'assemblage final.

        ⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))           (= cible_prop9_exp_somme)

Tout le reste vient (importé) de ensembles_prop9_close (AUCUN fichier modifié) :
  • DIRECTION A — CLOSE : inf_egal_phi() ⊢ inf_egal_card(𝓕(B⊔C;A), 𝓕(B;A)×𝓕(C;A)).
  • DIRECTION B — ψ : (g,h) ↦ ((K,B⊔C),A), K = K_g ∪ K_h recollement réindexé.
    SONT CLOS dans ensembles_prop9_close : K_fonctionnelle, K_domaine, K_inclus,
    K_dans_exposant, psi_dans_applications_sous_appartenance (BIEN-DÉF de ψ),
    W_psi_fonctionnel / W_psi_domaine / W_psi_image_incluse.

CE MODULE clôt le SEUL conjoint manquant — injective_dans(W_ψ, 𝓕(B;A)×𝓕(C;A)) —
en MIROIR EXACT de W_phi_injective, puis :
  • W_psi_valeur     : {p ∈ cod} ⊢ W_ψ(p) = ψ(p)   (graphe_terme_valeur ; manquait).
  • W_psi_injective  : ⊢ injective_dans(W_ψ, 𝓕(B;A)×𝓕(C;A)).
  • W_psi_est_injection : ⊢ est_injection_de(W_ψ, cod, dom).
  • inf_egal_psi     : ⊢ inf_egal_card(𝓕(B;A)×𝓕(C;A), 𝓕(B⊔C;A))   (DIRECTION B).
  • prop9_close      : ⊢ Card(𝓕(B⊔C;A)) = Card(𝓕(B;A)×𝓕(C;A))  INCONDITIONNEL.

LE CŒUR (ψ-injectivité).  De ψ(p₁)=ψ(p₂) on tire K(g₁,h₁)=K(g₂,h₂) (strip du
triple).  Sur la copie gauche B×{0} : valeur(K_i,(u,0)) = valeur(K_g(g_i),(u,0))
(valeur_reunion_gauche, domaines marqués disjoints) = g_i(u) (graphe_terme +
pr₁((u,0))=u + rebind m→y).  K₁=K₂ ⇒ g₁(u)=g₂(u) pour tout u∈B ⇒ g₁=g₂
(application_egale_par_valeurs).  Idem h₁=h₂ sur C×{1}.  Reconstruction
p_i=(pr₁p_i,pr₂p_i) (les p_i∈cod) ⇒ p₁=p₂.  MÊME back-and-forth que Φ, dupliqué.

theorie_ensembles INCHANGÉE (22 axiomes) ; AUCUN fichier existant modifié.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, appartient,
                                       existe, pourtout, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card)
from bourbaki.cardinaux.arithmetique.ensembles_graphe_de import graphe_de
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN)
from bourbaki.cardinaux.ensembles_cantor import graphe_terme_valeur

from bourbaki.cardinaux.arithmetique.ensembles_prop9_close import (
    domaine_phi, codomaine_phi,
    K_gauche, K_droite, K_psi, psi_valeur,
    K_gauche_domaine, K_droite_domaine,
    K_gauche_fonctionnelle, K_droite_fonctionnelle,
    K_inclus, K_dans_exposant,
    psi_dans_applications_sous_appartenance,
    W_psi, W_psi_fonctionnel, W_psi_domaine, W_psi_image_incluse,
    inf_egal_phi, prop9_depuis_deux_injections,
    _val_Kg, _val_Kh, _B0, _C1, _PTK, _VBK, _t, _cut, _membre_produit)
from bourbaki.cardinaux.arithmetique.ensembles_prop9_exp_somme import (
    cible_prop9_exp_somme)

from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
    application_egale_par_valeurs, egalite_valeurs_application)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
    valeur_reunion_gauche, valeur_reunion_droite)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    domaines_disjoints_si_marques)
from bourbaki.ensembles.familles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (
    _projection_premiere_ab, _membre_produit_pr1_ab, _membre_produit_pr2_ab,
    _membre_produit_egal_couple_ab)


_POINTPS = "p"        # point courant de W_ψ  (un couple (g,h) ∈ cod)


# ═══════════════════════════════════════════════════════════════════════════════
#  W_ψ(p) = ψ(p)   (valuation du graphe-terme W_ψ — manquait dans prop9_close)
# ═══════════════════════════════════════════════════════════════════════════════
def W_psi_valeur(p="q", a="A", b="B", c="C"):
    """{p ∈ 𝓕(B;A)×𝓕(C;A)} ⊢ W_ψ(p) = ψ(p).   (point d'évaluation NOM ≠ p,x,y,k,m.)

    Miroir de W_phi_valeur : W_ψ = graphe_terme(cod, ψ(p), « p »), graphe_terme_valeur
    donne W_ψ(p)=ψ[p] sous p∈cod."""
    if not isinstance(p, str):
        raise ValueError("W_psi_valeur : point d'évaluation = NOM (string)")
    va, vb, vc = _t(a), _t(b), _t(c)
    return graphe_terme_valeur(codomaine_phi(va, vb, vc),
                               psi_valeur(var(_POINTPS), va, vb, vc), p, _POINTPS, "y")


# ═══════════════════════════════════════════════════════════════════════════════
#  DISJONCTION DES DOMAINES marqués de K_g, K_h  (∀u)¬(u∈domKg et u∈domKh)
#   — hypothèse du PIVOT valeur_reunion_gauche/droite.  Identique à K_fonctionnelle.
# ═══════════════════════════════════════════════════════════════════════════════
def _inclus_de_egal(t_eq):
    """De ⊢ X = Y, déduit ⊢ X ⊂ Y   (égalité ⇒ inclusion ; X,Y termes via t_eq)."""
    X = t_eq.conclusion.termes[0]
    Y = t_eq.conclusion.termes[1]
    vz = var("z")
    hz = N.assume(appartient(vz, X))
    z_in_Y = N.modus_ponens(hz, equivalence_avant(N.modus_ponens(t_eq,
        N.s6(X, Y, "w", appartient(vz, var("w"))))))
    return N.generalisation("z", N.loi_deduction(appartient(vz, X), z_in_Y))


def _disjonction_domaines(vg, vh, vb, vc):
    """⊢ (∀u)¬(u∈dom K_g et u∈dom K_h),  K_g=K_gauche(g,b), K_h=K_droite(h,c).

    Copies marquées 0≠1 disjointes.  EXACTEMENT le morceau « disj » de K_fonctionnelle
    de ensembles_prop9_close (généralisé sur u, prêt pour valeur_reunion_*)."""
    Kg, Kh = K_gauche(vg, vb), K_droite(vh, vc)
    domKg_incl = _inclus_de_egal(K_gauche_domaine(vg, vb))   # dom K_g⊂B×{0}
    domKh_incl = _inclus_de_egal(K_droite_domaine(vh, vc))   # dom K_h⊂C×{1}
    disj_u = domaines_disjoints_si_marques(Kg, Kh, vb, vc, "u")
    disj_u = _cut(disj_u, [(inclus(E.dom(Kg), _B0(vb)), domKg_incl),
                           (inclus(E.dom(Kh), _C1(vc)), domKh_incl)])
    return N.generalisation("u", disj_u)


def _disj_formule(vg, vh):
    """La formule (∀u)¬(u∈dom K_g et u∈dom K_h)  (telle qu'attendue par valeur_reunion_*)."""
    Kg, Kh = vg, vh
    return pourtout("u", E.non(et(appartient(var("u"), E.dom(Kg)),
                                  appartient(var("u"), E.dom(Kh)))))


# ═══════════════════════════════════════════════════════════════════════════════
#  VALEUR DE K SUR UNE COPIE MARQUÉE :  K(g,h)((u,marker)) = g(u)  (resp. h(u))
# ───────────────────────────────────────────────────────────────────────────────
#   {u∈D, hyps structurelles K_g/K_h} ⊢ valeur(K(g,h),(u,marker)) = valeur(graphe_de(g),u).
#   Chaîne : valeur(K,(u,marker)) = valeur(K_morceau,(u,marker))  [valeur_reunion]
#                                 = (g/h)(pr₁(u,marker)) [m]       [graphe_terme_valeur]
#                                 = (g/h)(u) [m]                   [pr₁((u,m))=u]
#                                 = (g/h)(u) [y]                   [rebind m→y]
# ═══════════════════════════════════════════════════════════════════════════════
def _valeur_rebind_m_y(vG, vx):
    """⊢ valeur(G, x, « m ») = valeur(G, x, « y »).   (α-renommage du liant τ, CS1.)"""
    r = appartient(E.couple(vx, var(_VBK)), vG)      # (x,m)∈G  (liant courant m)
    return N.alpha_tau(r, _VBK, "y")                 # valeur(G,x,m)=valeur(G,x,y)


def _K_valeur_copie(vg, vh, va, vb, vc, vD, vu, marker, gauche):
    """{ u∈D, func K_g, func K_h, disj } ⊢ valeur(K(g,h),(u,marker)) = valeur(graphe_de(src),u,«y»),
       gauche=True : src=g, D=B, marker=0 ;  gauche=False : src=h, D=C, marker=1.

    valeur(K,(u,marker)) = valeur(K_morceau,(u,marker)) [valeur_reunion_*, sous (u,marker)
    ∈dom K_morceau=D×{marker}] = T[(u,marker)] [graphe_terme_valeur, point binder « k »]
    = valeur(graphe_de(src), pr₁((u,marker)), m) = valeur(graphe_de(src), u, m) [pr₁=u]
    = valeur(graphe_de(src), u, y) [rebind m→y]."""
    Kg, Kh = K_gauche(vg, vb), K_droite(vh, vc)
    K = E.reunion(Kg, Kh)
    src = vg if gauche else vh
    Gsrc = graphe_de(src)
    Km = Kg if gauche else Kh                          # le morceau « propre » de (u,marker)
    Dm = E.produit(vD, E.singleton(marker))           # D×{marker} = dom Km
    valK = _val_Kg(vg) if gauche else _val_Kh(vh)      # T = valeur(graphe_de(src), pr₁ k, m)
    um = E.couple(vu, marker)                          # (u,marker)
    pr1_um = E.pr1(um, "a", "b")                       # pr₁((u,marker))

    # (1) (u,marker) ∈ D×{marker} = dom Km
    from bourbaki.ensembles.base.ensembles_couples import singleton_membre
    mk_in_sing = N.modus_ponens(N.reflexivite(marker),
        equivalence_arriere(singleton_membre(marker, marker)))   # marker∈{marker}
    h_uD = N.assume(appartient(vu, vD))                # u∈D
    um_in_Dm = N.modus_ponens(conjonction_intro(h_uD, mk_in_sing),
        equivalence_arriere(couple_dans_produit_ssi(vu, marker, vD, E.singleton(marker))))  # (u,marker)∈D×{marker}
    dom_Km = K_gauche_domaine(vg, vb) if gauche else K_droite_domaine(vh, vc)   # dom Km=D×{marker}
    um_in_domKm = N.modus_ponens(um_in_Dm, equivalence_arriere(N.modus_ponens(
        dom_Km, N.s6(E.dom(Km), Dm, "w", appartient(um, var("w"))))))   # (u,marker)∈dom Km

    # (2) valeur(K,(u,marker)) = valeur(Km,(u,marker))   [valeur_reunion_*]
    if gauche:
        vr = valeur_reunion_gauche(Kg, Kh, um)         # {func,disj,(u,m)∈domKg}⊢val(K,·)=val(Kg,·)
    else:
        vr = valeur_reunion_droite(Kg, Kh, um)         # {func,disj,(u,m)∈domKh}⊢val(K,·)=val(Kh,·)
    vr = _cut(vr, [
        (E.est_fonctionnel(Kg), K_gauche_fonctionnelle(vg, vb)),
        (E.est_fonctionnel(Kh), K_droite_fonctionnelle(vh, vc)),
        (_disj_formule(Kg, Kh), _disjonction_domaines(vg, vh, vb, vc)),
        (appartient(um, E.dom(Km)), um_in_domKm)])     # valeur(K,(u,m))=valeur(Km,(u,m))

    # (3) valeur(Km,(u,marker)) = T[(u,marker)]   [graphe_terme_valeur, binder « k » de Km]
    #     Km = graphe_terme(D×{marker}, valK, « k »).  Le point d'évaluation est le TERME
    #     (u,marker) ; graphe_terme_valeur exige un NOM POINT ≠ binder → point « kk », généraliser
    #     dessus puis instancier au terme (u,marker).
    _POINT_EV = "kk"                                      # nom de point frais ≠ binder « k »
    gtv = graphe_terme_valeur(Dm, valK, _POINT_EV, _PTK, "y")   # {kk∈D×{m}} ⊢ Km(kk)=valK[k:=kk]
    gtv_imp = N.loi_deduction(appartient(var(_POINT_EV), Dm), gtv)
    gtv_gen = N.generalisation(_POINT_EV, gtv_imp)        # (∀kk)(kk∈D×{m} ⇒ Km(kk)=valK[k:=kk])
    gtv_um = N.modus_ponens(um_in_Dm, instancie(gtv_gen, um))   # Km((u,m))=valK[k:=(u,m)]
    valK_um = subst_t(um, _PTK, valK)                     # valK[k:=(u,m)] = valeur(Gsrc, pr₁((u,m)), m)

    # (4) valK[(u,marker)] = valeur(Gsrc, pr₁((u,m)), m) = valeur(Gsrc, u, m)  [pr₁((u,m))=u]
    pr1_eq_u = _projection_premiere_ab(vu, marker, "a", "b")   # pr₁((u,m))=u
    # valeur(Gsrc, pr₁((u,m)), m) = valeur(Gsrc, u, m)   (congruence)
    valK_um_eq_Gu_m = N.modus_ponens(pr1_eq_u,
        congruence_terme(pr1_um, vu, E.valeur(Gsrc, var("w"), _VBK)))   # valK_um = valeur(Gsrc,u,m)

    # (5) valeur(Gsrc, u, m) = valeur(Gsrc, u, y)  [rebind m→y]
    reb = _valeur_rebind_m_y(Gsrc, vu)                     # valeur(Gsrc,u,m)=valeur(Gsrc,u,y)

    # chaîne : valeur(K,(u,m)) = valeur(Km,(u,m)) = valK_um = valeur(Gsrc,u,m) = valeur(Gsrc,u,y)
    chain = composer_egalites(vr, gtv_um)                 # valeur(K,(u,m)) = valK_um
    chain = composer_egalites(chain, valK_um_eq_Gu_m)     # = valeur(Gsrc,u,m)
    chain = composer_egalites(chain, reb)                 # = valeur(Gsrc,u,y)
    return chain   # {u∈D, func Kg, func Kh, disj} ⊢ valeur(K,(u,m)) = valeur(graphe_de(src),u,y)


# ═══════════════════════════════════════════════════════════════════════════════
#  ÉGALITÉ DES VALEURS DU FACTEUR depuis K(g₁,h₁)=K(g₂,h₂)
# ═══════════════════════════════════════════════════════════════════════════════
def _facteur_valeurs_coincident(vg1, vh1, vg2, vh2, va, vb, vc, gauche):
    """{ K(g₁,h₁)=K(g₂,h₂) } ⊢ (∀u)(u∈D ⇒ valeur(graphe_de(src₁),u,«y»)=valeur(graphe_de(src₂),u,«y»)),
       gauche=True : src_i=g_i, D=B, marker=0 ;  gauche=False : src_i=h_i, D=C, marker=1.

    Pour u∈D : g_i(u)=valeur(K_i,(u,marker)) (_K_valeur_copie, symétrisé) ; K₁=K₂ donne
    valeur(K₁,(u,m))=valeur(K₂,(u,m)) (congruence) ; chaîner g₁(u)=K₁(u,m)=K₂(u,m)=g₂(u).
    C'est exactement la forme egalite_valeurs_application(src₁,src₂,D)."""
    vD = vb if gauche else vc
    marker = ZERO if gauche else UN
    src1 = vg1 if gauche else vh1
    src2 = vg2 if gauche else vh2
    G1, G2 = graphe_de(src1), graphe_de(src2)
    K1 = K_psi(vg1, vh1, vb, vc)
    K2 = K_psi(vg2, vh2, vb, vc)
    vu = var("x")                                          # le liant de egalite_valeurs_application
    um = E.couple(vu, marker)

    # g_i(u) = valeur(K_i,(u,m)) sous {u∈D, func/disj_i}
    val1 = _K_valeur_copie(vg1, vh1, va, vb, vc, vD, vu, marker, gauche)  # valeur(K₁,(u,m))=g₁(u)
    val2 = _K_valeur_copie(vg2, vh2, va, vb, vc, vD, vu, marker, gauche)  # valeur(K₂,(u,m))=g₂(u)
    g1u = E.valeur(G1, vu, "y")
    g2u = E.valeur(G2, vu, "y")
    # g₁(u) = valeur(K₁,(u,m))   (symétrie de val1)
    g1u_eq_K1 = N.modus_ponens(val1, symetrie(E.valeur(K1, um), g1u))    # g₁(u)=valeur(K₁,(u,m))
    # K₁=K₂ ⇒ valeur(K₁,(u,m))=valeur(K₂,(u,m))  (congruence)
    h_K_eq = N.assume(egal(K1, K2))
    K1_eq_K2_um = N.modus_ponens(h_K_eq,
        congruence_terme(K1, K2, E.valeur(var("w"), um)))   # valeur(K₁,(u,m))=valeur(K₂,(u,m))
    # g₁(u) = K₁(u,m) = K₂(u,m) = g₂(u)
    chain = composer_egalites(composer_egalites(g1u_eq_K1, K1_eq_K2_um), val2)   # g₁(u)=g₂(u)
    # décharger les hypothèses func/disj de _K_valeur_copie (closes — déjà fournies SAUF u∈D)
    # _K_valeur_copie a déjà déchargé func/disj en interne ; il reste l'hyp u∈D et K₁=K₂.
    # Construire (∀x)(x∈D ⇒ g₁(x)=g₂(x))  [hyp K₁=K₂]
    imp = N.loi_deduction(appartient(vu, vD), chain)
    return N.generalisation("x", imp)   # {K₁=K₂} ⊢ (∀x)(x∈D ⇒ src₁(x)=src₂(x))


# ═══════════════════════════════════════════════════════════════════════════════
#  ψ-INJECTIVITÉ (cœur)  :  ψ(p₁)=ψ(p₂) ⇒ p₁=p₂
# ═══════════════════════════════════════════════════════════════════════════════
def _strip_triple(triple_eq, g1, mid, top, g2):
    """De ⊢ ((g₁,mid),top)=((g₂,mid),top), tire ⊢ g₁=g₂.  (deux décompos de couples.)"""
    from bourbaki.ensembles.base.ensembles_couples import couple_egal_implique_composantes
    inner1 = E.couple(g1, mid)
    inner2 = E.couple(g2, mid)
    comp1 = N.modus_ponens(triple_eq,
                           couple_egal_implique_composantes(inner1, top, inner2, top))
    inner_eq = conjonction_elim_gauche(comp1)        # (g₁,mid)=(g₂,mid)
    comp2 = N.modus_ponens(inner_eq,
                           couple_egal_implique_composantes(g1, mid, g2, mid))
    return conjonction_elim_gauche(comp2)            # g₁=g₂


def psi_injective_sous_appartenance(p1="p1", p2="p2", a="A", b="B", c="C"):
    """{ p₁∈𝓕(B;A)×𝓕(C;A), p₂∈𝓕(B;A)×𝓕(C;A), ψ(p₁)=ψ(p₂) } ⊢ p₁ = p₂.

    ψ(p_i)=((K(g_i,h_i),B⊔C),A), g_i=pr₁p_i, h_i=pr₂p_i.  Strip du triple ⇒
    K(g₁,h₁)=K(g₂,h₂).  Sur B : g₁,g₂ coïncident en valeur (_facteur_valeurs_coincident,
    gauche) ; g_i∈𝓕(B;A) (pr₁∈facteur) ; application_egale_par_valeurs ⇒ g₁=g₂.  Idem
    h₁=h₂ sur C.  Reconstruction p_i=(pr₁p_i,pr₂p_i) ⇒ p₁=(g₁,h₁)=(g₂,h₂)=p₂."""
    vp1, vp2, va, vb, vc = _t(p1), _t(p2), _t(a), _t(b), _t(c)
    cod = codomaine_phi(va, vb, vc)
    FB = E.applications(vb, va)
    FC = E.applications(vc, va)
    BC = somme_disjointe(vb, vc)
    g1, h1 = E.pr1(vp1, "a", "b"), E.pr2(vp1, "a", "b")
    g2, h2 = E.pr1(vp2, "a", "b"), E.pr2(vp2, "a", "b")
    K1, K2 = K_psi(g1, h1, vb, vc), K_psi(g2, h2, vb, vc)

    psi1 = psi_valeur(vp1, va, vb, vc)
    psi2 = psi_valeur(vp2, va, vb, vc)
    h_psi = N.assume(egal(psi1, psi2))                # ψ(p₁)=ψ(p₂)

    # strip : ((K₁,B⊔C),A)=((K₂,B⊔C),A) ⇒ K₁=K₂
    K_eq = _strip_triple(h_psi, K1, BC, va, K2)       # K₁=K₂

    # p_i ∈ cod ⇒ pr₁p_i∈𝓕(B;A), pr₂p_i∈𝓕(C;A)
    h_p1 = N.assume(appartient(vp1, cod))
    h_p2 = N.assume(appartient(vp2, cod))
    g1_in = _cut(_membre_produit_pr1_ab(FB, FC, vp1), [(appartient(vp1, cod), h_p1)])  # g₁∈𝓕(B;A)
    g2_in = _cut(_membre_produit_pr1_ab(FB, FC, vp2), [(appartient(vp2, cod), h_p2)])  # g₂∈𝓕(B;A)
    h1_in = _cut(_membre_produit_pr2_ab(FB, FC, vp1), [(appartient(vp1, cod), h_p1)])  # h₁∈𝓕(C;A)
    h2_in = _cut(_membre_produit_pr2_ab(FB, FC, vp2), [(appartient(vp2, cod), h_p2)])  # h₂∈𝓕(C;A)

    # g₁=g₂  (application_egale_par_valeurs sur B, valeurs coïncident depuis K₁=K₂)
    valsg = _facteur_valeurs_coincident(g1, h1, g2, h2, va, vb, vc, True)   # {K eq} ⊢ (∀x∈B)g₁(x)=g₂(x)
    valsg = _cut(valsg, [(egal(K1, K2), K_eq)])                             # {ψ eq} ⊢ vals
    aev_g = application_egale_par_valeurs(g1, g2, vb, va)   # {g₁,g₂∈𝓕(B;A), vals} ⊢ g₁=g₂
    g_eq = _cut(aev_g, [
        (appartient(g1, FB), g1_in),
        (appartient(g2, FB), g2_in),
        (egalite_valeurs_application(g1, g2, vb), valsg)])  # g₁=g₂

    # h₁=h₂  (idem sur C)
    valsh = _facteur_valeurs_coincident(g1, h1, g2, h2, va, vb, vc, False)  # {K eq} ⊢ (∀x∈C)h₁(x)=h₂(x)
    valsh = _cut(valsh, [(egal(K1, K2), K_eq)])
    aev_h = application_egale_par_valeurs(h1, h2, vc, va)   # {h₁,h₂∈𝓕(C;A), vals} ⊢ h₁=h₂
    h_eq = _cut(aev_h, [
        (appartient(h1, FC), h1_in),
        (appartient(h2, FC), h2_in),
        (egalite_valeurs_application(h1, h2, vc), valsh)])  # h₁=h₂

    # reconstruction p_i=(pr₁p_i,pr₂p_i)=(g_i,h_i) sous p_i∈cod
    p1_rec = _cut(_membre_produit_egal_couple_ab(FB, FC, vp1),
                  [(appartient(vp1, cod), h_p1)])   # p₁=(g₁,h₁)
    p2_rec = _cut(_membre_produit_egal_couple_ab(FB, FC, vp2),
                  [(appartient(vp2, cod), h_p2)])   # p₂=(g₂,h₂)
    # (g₁,h₁)=(g₂,h₂)  (deux congruences)
    c1 = N.modus_ponens(g_eq, congruence_terme(g1, g2, E.couple(var("w"), h1)))  # (g₁,h₁)=(g₂,h₁)
    c2 = N.modus_ponens(h_eq, congruence_terme(h1, h2, E.couple(g2, var("w"))))  # (g₂,h₁)=(g₂,h₂)
    rec_eq = composer_egalites(c1, c2)              # (g₁,h₁)=(g₂,h₂)
    # p₁=(g₁,h₁)=(g₂,h₂)=p₂
    p2_from = N.modus_ponens(p2_rec, symetrie(vp2, E.couple(g2, h2)))   # (g₂,h₂)=p₂
    return composer_egalites(composer_egalites(p1_rec, rec_eq), p2_from)   # p₁=p₂


def W_psi_injective(a="A", b="B", c="C"):
    """⊢ injective_dans(W_ψ, 𝓕(B;A)×𝓕(C;A)).

    MIROIR de W_phi_injective.  W_ψ(·)=ψ(·) (W_psi_valeur, sous ·∈cod) ⇒ ψ(p₁)=ψ(p₂) ;
    psi_injective_sous_appartenance ⇒ p₁=p₂.  Variables-fonction « p1 », « p2 » SÛRES
    (≠ liants internes), α-renommées ENSUITE en « u », « up » pour s'apparier à la forme
    injective_dans attendue par est_injection_de."""
    va, vb, vc = _t(a), _t(b), _t(c)
    cod = codomaine_phi(va, vb, vc)
    Wt = W_psi(va, vb, vc)
    vp1, vp2 = var("p1"), var("p2")
    psi1 = psi_valeur(vp1, va, vb, vc)
    psi2 = psi_valeur(vp2, va, vb, vc)

    hyp = et(et(appartient(vp1, cod), appartient(vp2, cod)),
             egal(E.valeur(Wt, vp1), E.valeur(Wt, vp2)))   # p₁∈cod et p₂∈cod et W(p₁)=W(p₂)
    h = N.assume(hyp)
    p1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))
    p2_in = conjonction_elim_droite(conjonction_elim_gauche(h))
    W_eq = conjonction_elim_droite(h)                            # W(p₁)=W(p₂)
    Wp1 = _cut(W_psi_valeur("p1", va, vb, vc), [(appartient(vp1, cod), p1_in)])    # W(p₁)=ψ(p₁)
    Wp2 = _cut(W_psi_valeur("p2", va, vb, vc), [(appartient(vp2, cod), p2_in)])    # W(p₂)=ψ(p₂)
    psi_eq = composer_egalites(composer_egalites(
        N.modus_ponens(Wp1, symetrie(E.valeur(Wt, vp1), psi1)), W_eq), Wp2)   # ψ(p₁)=ψ(p₂)
    p_eq = psi_injective_sous_appartenance("p1", "p2", va, vb, vc)
    p_eq = _cut(p_eq, [(appartient(vp1, cod), p1_in),
                       (appartient(vp2, cod), p2_in),
                       (egal(psi1, psi2), psi_eq)])             # p₁=p₂  [hyp]
    inner = N.loi_deduction(hyp, p_eq)
    raw = N.generalisation("p1", N.generalisation("p2", inner))  # (∀p1)(∀p2)…
    inst = instancie(instancie(raw, var("u")), var("up"))        # P[p1:=u, p2:=up]
    return N.generalisation("u", N.generalisation("up", inst))   # (∀u)(∀up)… = injective_dans


# ═══════════════════════════════════════════════════════════════════════════════
#  DIRECTION B :  𝓕(B;A)×𝓕(C;A) ≤ 𝓕(B⊔C;A)   (ψ est une injection)
# ═══════════════════════════════════════════════════════════════════════════════
def W_psi_est_injection(a="A", b="B", c="C"):
    """⊢ est_injection_de(W_ψ, 𝓕(B;A)×𝓕(C;A), 𝓕(B⊔C;A)).

    Les QUATRE conjoints (E.III.3.2) : W_ψ fonctionnel, dom W_ψ=cod=𝓕(B;A)×𝓕(C;A),
    injective sur cod, image⊂dom=𝓕(B⊔C;A).  Mime W_phi_est_injection."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return conjonction_intro(conjonction_intro(conjonction_intro(
        W_psi_fonctionnel(va, vb, vc), W_psi_domaine(va, vb, vc)),
        W_psi_injective(va, vb, vc)), W_psi_image_incluse(va, vb, vc))


def inf_egal_psi(a="A", b="B", c="C"):
    """⊢ inf_egal_card(𝓕(B;A)×𝓕(C;A), 𝓕(B⊔C;A)).   (DIRECTION B : a^b·a^c ≤ a^(b+c).)

    L'injection-témoin est W_ψ (W_psi_est_injection) : par S5 (témoin F:=W_ψ),
    (∃F) est_injection_de(F, 𝓕(B;A)×𝓕(C;A), 𝓕(B⊔C;A)) = inf_egal_card(·,·).
    Mime inf_egal_phi (source = cod de Φ, but = dom de Φ — sens inverse)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    source = codomaine_phi(va, vb, vc)               # 𝓕(B;A)×𝓕(C;A) — SOURCE de ψ
    but = domaine_phi(va, vb, vc)                    # 𝓕(B⊔C;A)       — BUT de ψ
    Wt = W_psi(va, vb, vc)
    inj = W_psi_est_injection(va, vb, vc)            # est_injection_de(W_ψ, source, but)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), source, but), Wt, "F"))


# ═══════════════════════════════════════════════════════════════════════════════
#  CLÔTURE INCONDITIONNELLE DE LA PROPOSITION 9  (Cantor–Bernstein)
# ═══════════════════════════════════════════════════════════════════════════════
def prop9_close(a="A", b="B", c="C"):
    """⊢ Card(𝓕(B⊔C; A)) = Card(𝓕(B;A) × 𝓕(C;A))   INCONDITIONNEL   (= cible_prop9_exp_somme).

    a^(b+c) = a^b · a^c (E.III.3.5).  prop9_depuis_deux_injections (assembleur VÉRIFIÉ,
    Cantor–Bernstein + Prop 1 directe) avec :
      inf_A = inf_egal_phi() : 𝓕(B⊔C;A) ≤ 𝓕(B;A)×𝓕(C;A)  (DIRECTION A, dom≤cod) ;
      inf_B = inf_egal_psi() : 𝓕(B;A)×𝓕(C;A) ≤ 𝓕(B⊔C;A)  (DIRECTION B, cod≤dom).
    La conclusion est LITTÉRALEMENT cible_prop9_exp_somme(A,B,C)."""
    va, vb, vc = _t(a), _t(b), _t(c)
    return prop9_depuis_deux_injections(inf_egal_phi(va, vb, vc),
                                        inf_egal_psi(va, vb, vc), va, vb, vc)


__all__ = [
    "W_psi_valeur", "W_psi_injective", "W_psi_est_injection",
    "psi_injective_sous_appartenance", "inf_egal_psi", "prop9_close",
]
