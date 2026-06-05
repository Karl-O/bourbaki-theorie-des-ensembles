"""§III.3 — Invariance du produit par équipotence  (fondation de l'arithmétique
cardinale, E.III.3) :

        ⊢ (Eq(X, X₁) et Eq(Y, Y₁))  ⇒  Eq(X×Y, X₁×Y₁).

À partir d'une bijection  F : X → X₁  et  G : Y → Y₁,  on construit la bijection
PRODUIT  H : X×Y → X₁×Y₁  définie par  (x,y) ↦ (F(x), G(y)).  Son graphe est

        H := graphe_terme(X×Y, (F(pr₁ k), G(pr₂ k)), "k")

(= {(k, (F(pr₁k), G(pr₂k))) | k ∈ X×Y}, machinerie C54, E.II.46).  Pour aboutir à
Eq, il faut établir que H est : FONCTIONNEL, de DOMAINE X×Y, de VALEUR
H((x,y))=(F(x),G(y)), INJECTIF sur X×Y, d'IMAGE = X₁×Y₁ ; puis assembler
est_bijection_de(H, X×Y, X₁×Y₁) et conclure par S5 (témoin H) + élimination des
deux ∃ de Eq(X,X₁), Eq(Y,Y₁).

VERROU « liant valeur » LEVÉ :  le terme produit  (F(pr₁k), G(pr₂k))  contient les
valeurs  valeur(F, pr₁k) = τc((pr₁k, c)∈F)  écrites avec le liant EXOTIQUE « c »
(et non le défaut « y »).  Ainsi le ∃y du domaine / de l'image (AXIOME_DOM,
AXIOME_IMAGE) et la coordonnée « y » de membre_graphe_terme ne capturent plus le
τ interne des valeurs.  Combiné au fix α (`_fraiche → @0,@1` déterministe), toutes
les substitutions sont déterministes et le matching MP est robuste.  C'est la
même stratégie que le SWAP (ensembles_produit_commute) en liants uniformes a,b,
étendue aux valeurs via le liant c.

ÉTAT — THÉORÈME COMPLET, tout CERTIFIÉ et TESTÉ (test_produit_equipotence.py) :
  • produit_graphe_fonctionnel  (clos)        — H est fonctionnel        (PALIER 1a) ;
  • produit_graphe_domaine      (clos)        — dom H = X×Y              (PALIER 1) ;
  • produit_graphe_valeur       {u∈X×Y}       — H(u)=(F(pr₁u),G(pr₂u))   (PALIER 2) ;
  • produit_graphe_injective    {inj F/X, inj G/Y}       — injective_dans(H, X×Y)  (PALIER 3) ;
  • produit_graphe_image        {F,G func+dom+image}     — image(H, X×Y)=X₁×Y₁     (PALIER 4) ;
  • produit_est_bijection       {bij F, bij G}           — est_bijection_de(H,X×Y,X₁×Y₁) ;
  • eq_produit_invariant        (clos)                   — (Eq(X,X₁) et Eq(Y,Y₁)) ⇒
                                                           Eq(X×Y, X₁×Y₁)  (PALIER 5).

PONTS τc↔τy : la valeur produit s'écrit τc ; `injective_dans`/`valeur_caracterisation`
l'apparient en τy.  `_valeur_cy` (= primitive noyau `alpha_tau`, reflet de CS1)
fait le pont, vérifié à chaque appel par égalité des développements-τ.
"""
from __future__ import annotations

from formule import (Terme, var, egal, et, appartient, existe, subst_t, subst_f)
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege import a_implique_a, syllogisme
from tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie)
from tactiques_abrege_egalite import (symetrie, composer_egalites, congruence_terme)
from tactiques_abrege_quantif import (existe_elimination, congruence_existe,
                                      alpha_existe)
from ensembles_fonction_terme import membre_graphe_terme, graphe_terme_fonctionnel
from ensembles_cantor import (graphe_terme_couple_dans, graphe_terme_domaine,
                              graphe_terme_valeur)
from ensembles_theoremes import egalite_par_extension
from ensembles_couples import couple_egal_implique_composantes
from ensembles_produit import couple_dans_produit_ssi
from ensembles_produit_commute import (_membre_produit_egal_couple_ab,
                                       _membre_produit_pr1_ab, _membre_produit_pr2_ab,
                                       _couple_dans_produit_t, _inst_produit,
                                       _projection_premiere_ab, _projection_seconde_ab)
from ensembles_correspondances import _inst_image
from ensembles_fonctions import valeur_dans_graphe, valeur_caracterisation
from tactiques_abrege import syllogisme as _syll


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Le terme produit  T = (F(pr₁ k), G(pr₂ k))  (liants pr a,b ; valeurs τc) ────
def _prod_terme(f, g, k="k"):
    """T = (F(pr₁ k), G(pr₂ k))  (image du couple k par F sur la 1ʳᵉ coordonnée et
    G sur la 2ᵉ).

    Liants internes des projections a,b (≠ x,y des axiomes) ET liant « c » des
    deux valeurs τc((·,c)∈F)/τc((·,c)∈G) (≠ « y » des ∃y de AXIOME_DOM/AXIOME_IMAGE
    et de membre_graphe_terme) — c'est la levée du verrou « liant valeur » : sans
    cela, renommer le ∃y du domaine ou substituer une variable « y » capturerait le
    τy interne des valeurs (α-divergence ⇒ « mineure ≠ antécédent »)."""
    vk = var(k)
    return E.couple(E.valeur(_t(f), E.pr1(vk, "a", "b"), "c"),
                    E.valeur(_t(g), E.pr2(vk, "a", "b"), "c"))


def _prod_graphe(f, g, x, y, k="k"):
    """H := graphe_terme(X×Y, (F(pr₁ k), G(pr₂ k)), "k")  (graphe de (x,y)↦(F(x),G(y)))."""
    return E.graphe_terme(E.produit(_t(x), _t(y)), _prod_terme(f, g, k), k)


# ── PALIER 1a : H est fonctionnel  (CERTIFIÉ) ─────────────────────────────────
def produit_graphe_fonctionnel(f="F", g="G", x="X", y="Y"):
    """⊢ H est fonctionnel,  H = graphe de (x,y)↦(F(x),G(y)).   (cas C54, clos.)

    Application directe de graphe_terme_fonctionnel au graphe défini par le terme
    T = (F(pr₁k), G(pr₂k)) sur l'ensemble A = X×Y : le graphe d'une fonction
    définie par un terme est toujours fonctionnel (au plus une valeur par
    antécédent), E.II.46."""
    A = E.produit(_t(x), _t(y))
    return graphe_terme_fonctionnel(A, _prod_terme(f, g, "k"), "k", "t")


# ── PALIER 1 : dom H = X×Y  (CERTIFIÉ) ────────────────────────────────────────
def produit_graphe_domaine(f="F", g="G", x="X", y="Y"):
    """⊢ dom(H) = X×Y.   (la fonction produit est définie sur tout X×Y ; clos.)

    z∈dom H ⇔ (∃y)((z,y)∈H) ⇔ (∃y)(z∈X×Y et y=T[z]) ⇔ z∈X×Y.  Application directe
    de graphe_terme_domaine au terme produit (le liant « c » des valeurs évite la
    collision avec le ∃y du domaine)."""
    A = E.produit(_t(x), _t(y))
    return graphe_terme_domaine(A, _prod_terme(f, g, "k"), "k", "y", "z")


# ── PALIER 2 : H(u) = (F(pr₁u), G(pr₂u))  (CERTIFIÉ, hyp u∈X×Y) ────────────────
def produit_graphe_valeur(f="F", g="G", x="X", y="Y", u="u"):
    """{u ∈ X×Y} ⊢ H(u) = (F(pr₁u), G(pr₂u)).   (la valeur de la fonction produit.)

    Application directe de graphe_terme_valeur au terme produit : (u,T[u])∈H donne
    u dans le domaine ; valeur_caracterisation (C46, sous « H fonctionnel »
    déchargé) donne T[u]=H(u) ; symétrie conclut.  T[u]=(F(pr₁u),G(pr₂u))."""
    A = E.produit(_t(x), _t(y))
    return graphe_terme_valeur(A, _prod_terme(f, g, "k"), u, "k", "y")


# ── Conversion du liant de valeur  τc ↔ τy  (pont vers injective_dans) ─────────
def _valeur_cy(fF, t):
    """⊢ valeur(F, t, "c") = valeur(F, t, "y").   (α-renommage du liant de la valeur.)

    Le terme produit écrit les valeurs avec τc (anti-collision domaine/image) ;
    `injective_dans` les apparie avec τy.  alpha_tau (CS1) fait le pont, exact."""
    vt = _t(t)
    Rc = appartient(E.couple(vt, var("c")), fF)        # (t,c)∈F
    return N.alpha_tau(Rc, "c", "y")                    # τc((t,c)∈F) = τy((t,y)∈F)


# ── PALIER 3 : injective_dans(H, X×Y)  (sous F, G injectives) ──────────────────
def produit_graphe_injective(f="F", g="G", x="X", y="Y"):
    """{F injective sur X, G injective sur Y} ⊢ injective_dans(H, X×Y).

    H(u)=(F(pr₁u),G(pr₂u)), H(u')=(F(pr₁u'),G(pr₂u'))  (produit_graphe_valeur).
    Sous H(u)=H(u') : couple_egal donne F(pr₁u)=F(pr₁u') et G(pr₂u)=G(pr₂u') (en
    τc) ; alpha_tau les met en τy (forme de injective_dans) ; comme pr₁u,pr₁u'∈X
    et pr₂u,pr₂u'∈Y (reconstruction du produit, liants a,b), l'injectivité de F sur
    X et de G sur Y donne pr₁u=pr₁u' et pr₂u=pr₂u' ; deux congruences sur la
    reconstruction u=(pr₁u,pr₂u), u'=(pr₁u',pr₂u') concluent u=u'.  Raisonnement
    UNIFORME en liants a,b (comme le swap)."""
    vF, vG = _t(f), _t(g)
    vX, vY = _t(x), _t(y)
    A = E.produit(vX, vY)
    H = _prod_graphe(f, g, x, y, "k")
    vu, vup = var("u"), var("up")
    # projections en liants a,b
    pr1u, pr2u = E.pr1(vu, "a", "b"), E.pr2(vu, "a", "b")
    pr1up, pr2up = E.pr1(vup, "a", "b"), E.pr2(vup, "a", "b")
    # valeurs (forme τc, telle que produit_graphe_valeur la rend)
    Fc1u, Gc2u = E.valeur(vF, pr1u, "c"), E.valeur(vG, pr2u, "c")
    Fc1up, Gc2up = E.valeur(vF, pr1up, "c"), E.valeur(vG, pr2up, "c")
    Hu = E.couple(Fc1u, Gc2u)                              # H(u) = (F(pr₁u), G(pr₂u))
    Hup = E.couple(Fc1up, Gc2up)                           # H(u')
    hyp = et(et(appartient(vu, A), appartient(vup, A)),
             egal(E.valeur(H, vu), E.valeur(H, vup)))
    h = N.assume(hyp)
    uinA = conjonction_elim_gauche(conjonction_elim_gauche(h))      # u∈X×Y
    upinA = conjonction_elim_droite(conjonction_elim_gauche(h))     # u'∈X×Y
    val_eq = conjonction_elim_droite(h)                            # H(u)=H(u')
    Hu_val = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                  produit_graphe_valeur(f, g, x, y, "u")))   # H(u)=Hu
    Hup_val = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                    produit_graphe_valeur(f, g, x, y, "up")))  # H(u')=Hup
    Hu_eq_Hu = N.modus_ponens(Hu_val, symetrie(E.valeur(H, vu), Hu))    # Hu = H(u)
    Hu_eq_Hup = composer_egalites(composer_egalites(Hu_eq_Hu, val_eq), Hup_val)  # Hu = Hup
    comps = N.modus_ponens(Hu_eq_Hup,
        couple_egal_implique_composantes(Fc1u, Gc2u, Fc1up, Gc2up))
    F_eq_c = conjonction_elim_gauche(comps)                        # F(pr₁u)=F(pr₁u')  [τc]
    G_eq_c = conjonction_elim_droite(comps)                        # G(pr₂u)=G(pr₂u')  [τc]
    # passage τc → τy (forme de injective_dans) : Fy(pr₁u) = Fc(pr₁u) = Fc(pr₁u') = Fy(pr₁u')
    Fy1u_eq_Fc1u = N.modus_ponens(_valeur_cy(vF, pr1u),
                                  symetrie(Fc1u, E.valeur(vF, pr1u, "y")))   # Fy(pr₁u)=Fc(pr₁u)
    F_eq = composer_egalites(composer_egalites(Fy1u_eq_Fc1u, F_eq_c),
                             _valeur_cy(vF, pr1up))                          # Fy(pr₁u)=Fy(pr₁u')
    Gy2u_eq_Gc2u = N.modus_ponens(_valeur_cy(vG, pr2u),
                                  symetrie(Gc2u, E.valeur(vG, pr2u, "y")))   # Gy(pr₂u)=Gc(pr₂u)
    G_eq = composer_egalites(composer_egalites(Gy2u_eq_Gc2u, G_eq_c),
                             _valeur_cy(vG, pr2up))                          # Gy(pr₂u)=Gy(pr₂u')
    # appartenances des projections
    pr1u_in = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                   _membre_produit_pr1_ab(x, y, "u")))   # pr₁u∈X
    pr1up_in = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                     _membre_produit_pr1_ab(x, y, "up")))  # pr₁u'∈X
    pr2u_in = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                   _membre_produit_pr2_ab(x, y, "u")))   # pr₂u∈Y
    pr2up_in = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                     _membre_produit_pr2_ab(x, y, "up")))  # pr₂u'∈Y
    # injectivité de F sur X : (pr₁u∈X et pr₁u'∈X et F(pr₁u)=F(pr₁u')) ⇒ pr₁u=pr₁u'
    injF = N.assume(E.injective_dans(vF, vX))
    injF_i = instancie(instancie(injF, pr1u), pr1up)
    pr1_eq = N.modus_ponens(conjonction_intro(conjonction_intro(pr1u_in, pr1up_in), F_eq),
                            injF_i)                          # pr₁u=pr₁u'
    injG = N.assume(E.injective_dans(vG, vY))
    injG_i = instancie(instancie(injG, pr2u), pr2up)
    pr2_eq = N.modus_ponens(conjonction_intro(conjonction_intro(pr2u_in, pr2up_in), G_eq),
                            injG_i)                          # pr₂u=pr₂u'
    # reconstruction u=(pr₁u,pr₂u), u'=(pr₁u',pr₂u')
    u_rec = N.modus_ponens(uinA, N.loi_deduction(appartient(vu, A),
                                                 _membre_produit_egal_couple_ab(x, y, "u")))   # u=(pr₁u,pr₂u)
    up_rec = N.modus_ponens(upinA, N.loi_deduction(appartient(vup, A),
                                                   _membre_produit_egal_couple_ab(x, y, "up")))  # u'=(pr₁u',pr₂u')
    c1 = N.modus_ponens(pr1_eq, congruence_terme(pr1u, pr1up, E.couple(var("w"), pr2u)))   # (pr₁u,pr₂u)=(pr₁u',pr₂u)
    c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2u, pr2up, E.couple(pr1up, var("w"))))  # (pr₁u',pr₂u)=(pr₁u',pr₂u')
    rec_eq = composer_egalites(c1, c2)                            # (pr₁u,pr₂u)=(pr₁u',pr₂u')
    u_eq_up = composer_egalites(composer_egalites(u_rec, rec_eq),
                                N.modus_ponens(up_rec, symetrie(vup, E.couple(pr1up, pr2up))))
    inner = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation("u", N.generalisation("up", inner))   # injective_dans(H, X×Y)


# ── Ponts surjectivité ↔ image (réutilisables) ────────────────────────────────
def _valeur_dans_image(fF, a, X):
    """{a∈X, (∃y)((a,y)∈F)} ⊢ F(a) ∈ F⟨X⟩.   (la valeur en a∈X est dans l'image directe.)

    a doit éviter le liant interne « x » de AXIOME_IMAGE (F(a) contient « a » libre
    ⇒ capture si a=« x »)."""
    fa = E.valeur(fF, a)                                   # F(a)  (τy)
    ii = _inst_image(fF, X, fa)                            # F(a)∈F⟨X⟩ ⇔ (∃x)(x∈X et (x,F(a))∈F)
    xfa = valeur_dans_graphe(fF, a)                        # {(∃y)((a,y)∈F)} ⊢ (a,F(a))∈F
    wit = conjonction_intro(N.assume(appartient(a, X)), xfa)
    body = et(appartient(var("x"), X), appartient(E.couple(var("x"), fa), fF))
    ex = N.modus_ponens(wit, N.s5(body, a, "x"))           # (∃x)(x∈X et (x,F(a))∈F)
    return N.modus_ponens(ex, equivalence_arriere(ii))     # F(a)∈F⟨X⟩


def _antecedent_image(fF, X, x1, a="a"):
    """⊢ (x1 ∈ F⟨X⟩) ⇒ (∃a)(a∈X et (a,x1)∈F).   (extraction d'un antécédent, liant a.)"""
    ii = _inst_image(fF, X, x1)                            # x1∈F⟨X⟩ ⇔ (∃x)(x∈X et (x,x1)∈F)
    ren = alpha_existe("x", a, et(appartient(var("x"), X),
                                  appartient(E.couple(var("x"), x1), fF)))
    return _syll(equivalence_avant(ii), equivalence_avant(ren))


# ── PALIER 4 : image(H, X×Y) = X₁×Y₁  (surjectivité) ──────────────────────────
def produit_graphe_image(f="F", g="G", x="X", y="Y", x1="X1", y1="Y1"):
    """{F func, dom F=X, F⟨X⟩=X₁, G func, dom G=Y, G⟨Y⟩=Y₁} ⊢ image(H, X×Y) = X₁×Y₁.

    z∈H⟨X×Y⟩ ⇔ (∃t)(t∈X×Y et (t,z)∈H) ⇔ (∃t)(t∈X×Y et z=T[t]).
    ⇒ : T[t]=(F(pr₁t),G(pr₂t)) avec F(pr₁t)∈F⟨X⟩=X₁ (pr₁t∈X, pr₁t∈dom F via dom F=X)
        et G(pr₂t)∈G⟨Y⟩=Y₁, donc z∈X₁×Y₁.
    ⇐ : z=(x1,y1)∈X₁×Y₁=F⟨X⟩×G⟨Y⟩ ; x1∈F⟨X⟩ donne a∈X, (a,x1)∈F donc F(a)=x1 (F func) ;
        y1∈G⟨Y⟩ donne b∈Y, G(b)=y1 ; antécédent t:=(a,b)∈X×Y, H((a,b))=(F(a),G(b))=(x1,y1)."""
    vF, vG = _t(f), _t(g)
    vX, vY, vX1, vY1 = _t(x), _t(y), _t(x1), _t(y1)
    A = E.produit(vX, vY)
    X1Y1 = E.produit(vX1, vY1)
    T = _prod_terme(f, g, "k")
    H = E.graphe_terme(A, T, "k")
    vz = var("z")
    # caractérisation de l'image (liant t)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, H), A), vz)
    inner_x = et(appartient(var("x"), A), appartient(E.couple(var("x"), vz), H))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)      # z∈H⟨A⟩ ⇔ (∃t)(t∈A et (t,z)∈H)
    vt = var("t")
    Tt = subst_t(vt, "k", T)                               # T[t] = (F(pr₁t), G(pr₂t))  (τc)
    pr1t, pr2t = E.pr1(vt, "a", "b"), E.pr2(vt, "a", "b")
    # hypothèses
    hFdom = N.assume(egal(E.dom(vF), vX))
    hGdom = N.assume(egal(E.dom(vG), vY))
    hFimg = N.assume(egal(E.image(vF, vX), vX1))
    hGimg = N.assume(egal(E.image(vG, vY), vY1))

    # ── ⇒ : z∈H⟨A⟩ ⇒ z∈X₁×Y₁ ─────────────────────────────────────────────────
    bodyR = et(appartient(vt, A), appartient(E.couple(vt, vz), H))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)                    # t∈A
    cpl_in = conjonction_elim_droite(hbR)                  # (t,z)∈H
    mem = membre_graphe_terme(A, T, "t", "m", "k", "yb")   # ((t,m)∈H)⇔(t∈A et m=T[t]) ; coord m≠y
    mem_all = N.generalisation("m", mem)
    mem_z = instancie(mem_all, vz)                         # ((t,z)∈H)⇔(t∈A et z=T[t])
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=T[t]
    pr1t_inX = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A),
                                                    _membre_produit_pr1_ab(x, y, "t")))   # pr₁t∈X
    pr2t_inY = N.modus_ponens(t_in, N.loi_deduction(appartient(vt, A),
                                                    _membre_produit_pr2_ab(x, y, "t")))   # pr₂t∈Y
    # pr₁t∈dom F  (de pr₁t∈X et dom F=X)
    pr1t_domF = N.modus_ponens(pr1t_inX, equivalence_arriere(N.modus_ponens(
        hFdom, N.s6(E.dom(vF), vX, "w", appartient(pr1t, var("w"))))))
    # F(pr₁t)∈F⟨X⟩  (besoin (∃y)((pr₁t,y)∈F) = pr₁t∈dom F)
    domF_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vF), pr1t)
    pr1t_ex = N.modus_ponens(pr1t_domF, equivalence_avant(domF_car))   # (∃y)((pr₁t,y)∈F)
    Fpr1t_img = _valeur_dans_image(vF, pr1t, vX)           # {pr₁t∈X,(∃y)…} ⊢ F(pr₁t)∈F⟨X⟩
    Fpr1t_img = N.modus_ponens(pr1t_inX, N.loi_deduction(appartient(pr1t, vX),
        N.modus_ponens(pr1t_ex, N.loi_deduction(
            existe("y", appartient(E.couple(pr1t, var("y")), vF)), Fpr1t_img))))
    # F(pr₁t)∈X₁  (réécrire F⟨X⟩=X₁)
    Fpr1t_inX1 = N.modus_ponens(Fpr1t_img, equivalence_avant(N.modus_ponens(
        hFimg, N.s6(E.image(vF, vX), vX1, "w", appartient(E.valeur(vF, pr1t), var("w"))))))
    # même chose pour G
    pr2t_domG = N.modus_ponens(pr2t_inY, equivalence_arriere(N.modus_ponens(
        hGdom, N.s6(E.dom(vG), vY, "w", appartient(pr2t, var("w"))))))
    domG_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vG), pr2t)
    pr2t_ex = N.modus_ponens(pr2t_domG, equivalence_avant(domG_car))
    Gpr2t_img = _valeur_dans_image(vG, pr2t, vY)
    Gpr2t_img = N.modus_ponens(pr2t_inY, N.loi_deduction(appartient(pr2t, vY),
        N.modus_ponens(pr2t_ex, N.loi_deduction(
            existe("y", appartient(E.couple(pr2t, var("y")), vG)), Gpr2t_img))))
    Gpr2t_inY1 = N.modus_ponens(Gpr2t_img, equivalence_avant(N.modus_ponens(
        hGimg, N.s6(E.image(vG, vY), vY1, "w", appartient(E.valeur(vG, pr2t), var("w"))))))
    # (F(pr₁t),G(pr₂t)) ∈ X₁×Y₁  — mais en τy (valeur défaut) ; on convertit en τc pour matcher T[t]
    Fy1t, Gy2t = E.valeur(vF, pr1t), E.valeur(vG, pr2t)        # τy
    Fc1t, Gc2t = E.valeur(vF, pr1t, "c"), E.valeur(vG, pr2t, "c")  # τc (= composantes de T[t])
    # X₁∋ : F(pr₁t)[τy]∈X₁ → F(pr₁t)[τc]∈X₁  (réécriture Fy=Fc via sym de _valeur_cy)
    Fy_eq_Fc_1t = N.modus_ponens(_valeur_cy(vF, pr1t), symetrie(Fc1t, Fy1t))   # Fy(pr₁t)=Fc(pr₁t)
    Fc1t_inX1 = N.modus_ponens(Fpr1t_inX1, equivalence_avant(N.modus_ponens(
        Fy_eq_Fc_1t, N.s6(Fy1t, Fc1t, "w", appartient(var("w"), vX1)))))
    Gy_eq_Gc_2t = N.modus_ponens(_valeur_cy(vG, pr2t), symetrie(Gc2t, Gy2t))   # Gy(pr₂t)=Gc(pr₂t)
    Gc2t_inY1 = N.modus_ponens(Gpr2t_inY1, equivalence_avant(N.modus_ponens(
        Gy_eq_Gc_2t, N.s6(Gy2t, Gc2t, "w", appartient(var("w"), vY1)))))
    Tt_in = N.modus_ponens(conjonction_intro(Fc1t_inX1, Gc2t_inY1),
                           equivalence_arriere(couple_dans_produit_ssi(Fc1t, Gc2t, vX1, vY1)))  # T[t]∈X₁×Y₁
    z_in = N.modus_ponens(Tt_in, equivalence_arriere(
        N.modus_ponens(z_eq_Tt, N.s6(vz, Tt, "w", appartient(var("w"), X1Y1)))))
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in), "t")
    fwd_full = _syll(equivalence_avant(img_car), fwd)         # z∈H⟨A⟩ ⇒ z∈X₁×Y₁

    # ── ⇐ : z∈X₁×Y₁ ⇒ z∈H⟨A⟩ ─────────────────────────────────────────────────
    prod_car0 = _inst_produit(vX1, vY1, vz)                   # liants p,q
    inner_q = et(et(egal(vz, E.couple(var("p"), var("q"))), appartient(var("p"), vX1)),
                 appartient(var("q"), vY1))
    ren_q = alpha_existe("q", "d", inner_q)
    ren_q_under_p = congruence_existe(ren_q, "p")
    inner_p_d = et(et(egal(vz, E.couple(var("p"), var("d"))), appartient(var("p"), vX1)),
                   appartient(var("d"), vY1))
    ren_p = alpha_existe("p", "c1", existe("d", inner_p_d))
    prod_car = equivalence_transitivite(prod_car0,
                  equivalence_transitivite(ren_q_under_p, ren_p))  # z∈X₁×Y₁ ⇔ (∃c1)(∃d)bodyP
    vc1, vd = var("c1"), var("d")
    bodyP = et(et(egal(vz, E.couple(vc1, vd)), appartient(vc1, vX1)), appartient(vd, vY1))
    hP = N.assume(bodyP)
    z_eq_cd = conjonction_elim_gauche(conjonction_elim_gauche(hP))  # z=(x1,y1)
    x1_inX1 = conjonction_elim_droite(conjonction_elim_gauche(hP))  # x1∈X₁
    y1_inY1 = conjonction_elim_droite(hP)                          # y1∈Y₁
    # x1∈X₁=F⟨X⟩ → antécédent a∈X, (a,x1)∈F
    x1_inFX = N.modus_ponens(x1_inX1, equivalence_arriere(N.modus_ponens(
        hFimg, N.s6(E.image(vF, vX), vX1, "w", appartient(vc1, var("w"))))))
    # y1∈Y₁=G⟨Y⟩
    y1_inGY = N.modus_ponens(y1_inY1, equivalence_arriere(N.modus_ponens(
        hGimg, N.s6(E.image(vG, vY), vY1, "w", appartient(vd, var("w"))))))
    # NB : témoins « s » (antécédent de x1 par F) et « e » (de y1 par G) — distincts
    # des liants a,b des projections de T (sinon pr₁((s,e),a,b) capturerait le témoin).
    bodyA = et(appartient(var("s"), vX), appartient(E.couple(var("s"), vc1), vF))
    bodyB = et(appartient(var("e"), vY), appartient(E.couple(var("e"), vd), vG))
    anteA = N.modus_ponens(x1_inFX, _antecedent_image(vF, vX, vc1, "s"))   # (∃s)bodyA
    anteB = N.modus_ponens(y1_inGY, _antecedent_image(vG, vY, vd, "e"))    # (∃e)bodyB
    # sous s, e : construire l'antécédent t0=(s,e) et montrer (t0,z)∈H
    va, vb = var("s"), var("e")
    hA = N.assume(bodyA)
    hB = N.assume(bodyB)
    a_inX = conjonction_elim_gauche(hA)        # a∈X
    ax1_F = conjonction_elim_droite(hA)        # (a,x1)∈F
    b_inY = conjonction_elim_gauche(hB)        # bb∈Y
    by1_G = conjonction_elim_droite(hB)        # (bb,y1)∈G
    t0 = E.couple(va, vb)                       # (a,bb)
    t0_inA = N.modus_ponens(conjonction_intro(a_inX, b_inY),
                            _couple_dans_produit_t(va, vb, vX, vY))   # (a,bb)∈X×Y
    # F(a)=x1 : (a,x1)∈F et a∈dom F → valeur_caracterisation
    a_domF = N.modus_ponens(ax1_F, N.s5(appartient(E.couple(va, var("y")), vF), vc1, "y"))  # (∃y)((a,y)∈F)
    vcF = valeur_caracterisation(vF, va)        # {F func,(∃y)((a,y)∈F)} ⊢ ((a,y)∈F)⇔(y=F(a))
    vcF_x1 = instancie(N.generalisation("y", vcF), vc1)   # ((a,x1)∈F)⇔(x1=F(a))
    x1_eq_Fa = N.modus_ponens(ax1_F, equivalence_avant(vcF_x1))   # x1=F(a)
    x1_eq_Fa = N.modus_ponens(N.assume(E.est_fonctionnel(vF)),
        N.loi_deduction(E.est_fonctionnel(vF), x1_eq_Fa))
    x1_eq_Fa = N.modus_ponens(a_domF, N.loi_deduction(
        existe("y", appartient(E.couple(va, var("y")), vF)), x1_eq_Fa))
    Fa_eq_x1 = N.modus_ponens(x1_eq_Fa, symetrie(vc1, E.valeur(vF, va)))   # F(a)=x1
    # G(bb)=y1
    b_domG = N.modus_ponens(by1_G, N.s5(appartient(E.couple(vb, var("y")), vG), vd, "y"))
    vcG = valeur_caracterisation(vG, vb)
    vcG_y1 = instancie(N.generalisation("y", vcG), vd)
    y1_eq_Gb = N.modus_ponens(by1_G, equivalence_avant(vcG_y1))
    y1_eq_Gb = N.modus_ponens(N.assume(E.est_fonctionnel(vG)),
        N.loi_deduction(E.est_fonctionnel(vG), y1_eq_Gb))
    y1_eq_Gb = N.modus_ponens(b_domG, N.loi_deduction(
        existe("y", appartient(E.couple(vb, var("y")), vG)), y1_eq_Gb))
    Gb_eq_y1 = N.modus_ponens(y1_eq_Gb, symetrie(vd, E.valeur(vG, vb)))    # G(bb)=y1
    # (t0, z) ∈ H directement via membre_graphe_terme ⇐ (t0∈A et z=T[t0])
    Tt0 = subst_t(t0, "k", T)                          # (F(pr₁(a,bb)), G(pr₂(a,bb)))  (τc)
    pr1_t0 = _projection_premiere_ab(va, vb, "a", "b")   # pr₁((a,bb),a,b)=a
    pr2_t0 = _projection_seconde_ab(va, vb, "a", "b")    # pr₂((a,bb),a,b)=bb
    # T[t0] = (F(pr₁t0), G(pr₂t0)) → (F(a), G(bb)) → (x1, y1) → z
    Fc_pr1t0 = E.valeur(vF, E.pr1(t0, "a", "b"), "c")
    Gc_pr2t0 = E.valeur(vG, E.pr2(t0, "a", "b"), "c")
    Fc_a = E.valeur(vF, va, "c")
    Gc_b = E.valeur(vG, vb, "c")
    # F(pr₁t0)[τc] = F(a)[τc]
    Fpr_eq_Fa_c = N.modus_ponens(pr1_t0, congruence_terme(E.pr1(t0, "a", "b"), va,
                                                          E.valeur(vF, var("w"), "c")))
    Gpr_eq_Gb_c = N.modus_ponens(pr2_t0, congruence_terme(E.pr2(t0, "a", "b"), vb,
                                                          E.valeur(vG, var("w"), "c")))
    # F(a)[τc]=F(a)[τy]=x1
    Fa_c_eq_x1 = composer_egalites(_valeur_cy(vF, va), Fa_eq_x1)   # Fc(a)=x1
    Ga_c_eq_y1 = composer_egalites(_valeur_cy(vG, vb), Gb_eq_y1)   # Gc(bb)=y1
    Fc_pr1t0_eq_x1 = composer_egalites(Fpr_eq_Fa_c, Fa_c_eq_x1)    # Fc(pr₁t0)=x1
    Gc_pr2t0_eq_y1 = composer_egalites(Gpr_eq_Gb_c, Ga_c_eq_y1)    # Gc(pr₂t0)=y1
    # T[t0] = (Fc(pr₁t0),Gc(pr₂t0)) = (x1,y1)
    cc1 = N.modus_ponens(Fc_pr1t0_eq_x1, congruence_terme(Fc_pr1t0, vc1,
                                                          E.couple(var("w"), Gc_pr2t0)))   # T[t0]=(x1,Gc(pr₂t0))
    cc2 = N.modus_ponens(Gc_pr2t0_eq_y1, congruence_terme(Gc_pr2t0, vd,
                                                          E.couple(vc1, var("w"))))        # (x1,Gc)=(x1,y1)
    Tt0_eq_cd = composer_egalites(cc1, cc2)                        # T[t0]=(x1,y1)
    cd_eq_z = N.modus_ponens(z_eq_cd, symetrie(vz, E.couple(vc1, vd)))   # (x1,y1)=z
    Tt0_eq_z = composer_egalites(Tt0_eq_cd, cd_eq_z)              # T[t0]=z
    z_eq_Tt0 = N.modus_ponens(Tt0_eq_z, symetrie(Tt0, vz))       # z=T[t0]
    # (t0,z)∈H directement via l'axiome du graphe (témoins k:=t0=(s,e), yb:=z)
    ax_H = N.axiome(E.theorie_graphe_terme(A, T, "k", "yb", "zz"),
                    E.axiome_graphe_terme(A, T, "k", "yb", "zz"))   # (∀zz)(zz∈H ⇔ (∃k)(∃yb)body)
    cpl_z = E.couple(t0, vz)                                      # (t0, z)
    car_z = instancie(ax_H, cpl_z)                               # (t0,z)∈H ⇔ (∃k)(∃yb)body
    gbody_k = et(et(egal(cpl_z, E.couple(var("k"), var("yb"))), appartient(var("k"), A)),
                 egal(var("yb"), T))
    body_k0 = subst_f(t0, "k", gbody_k)                          # (k|→t0) body  (libre yb)
    wit_yb = conjonction_intro(conjonction_intro(N.reflexivite(cpl_z), t0_inA), z_eq_Tt0)
    ex_yb = N.modus_ponens(wit_yb, N.s5(body_k0, vz, "yb"))      # (∃yb)body[k:=t0]
    ex_kyb = N.modus_ponens(ex_yb, N.s5(existe("yb", gbody_k), t0, "k"))  # (∃k)(∃yb)body
    t0z_inH = N.modus_ponens(ex_kyb, equivalence_arriere(car_z))   # (t0,z)∈H
    wit_body = conjonction_intro(t0_inA, t0z_inH)                # t0∈A et (t0,z)∈H
    ex_t = N.modus_ponens(wit_body, N.s5(bodyR, t0, "t"))        # (∃t)(t∈A et (t,z)∈H)
    in_img = N.modus_ponens(ex_t, equivalence_arriere(img_car))  # z∈H⟨A⟩
    # éliminer témoins s, e
    in_img_a = existe_elimination(N.loi_deduction(bodyA, in_img), "s")    # (∃s)bodyA ⇒ z∈H⟨A⟩
    in_img_b = existe_elimination(N.loi_deduction(bodyB,
        N.modus_ponens(anteA, in_img_a)), "e")                   # (∃e)bodyB ⇒ z∈H⟨A⟩
    z_in_img = N.modus_ponens(anteB, in_img_b)                   # z∈H⟨A⟩  [sous bodyP, hyps]
    bwd_inner = existe_elimination(existe_elimination(
        N.loi_deduction(bodyP, z_in_img), "d"), "c1")            # (∃c1)(∃d)bodyP ⇒ z∈H⟨A⟩
    bwd_full = _syll(equivalence_avant(prod_car), bwd_inner)     # z∈X₁×Y₁ ⇒ z∈H⟨A⟩
    # ── double inclusion → egalite_par_extension ──────────────────────────────
    equiv_z = conjonction_intro(fwd_full, bwd_full)             # z∈H⟨A⟩ ⇔ z∈X₁×Y₁
    char_u = N.generalisation("z", equiv_z)
    selfYX = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, X1Y1)), a_implique_a(appartient(vz, X1Y1))))
    return egalite_par_extension(char_u, selfYX, E.image(H, A), X1Y1, "z")


# ── PALIER 5 : assemblage est_bijection_de(H,X×Y,X₁×Y₁) puis Eq(X×Y,X₁×Y₁) ────
def _cut(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


def produit_est_bijection(f="F", g="G", x="X", y="Y", x1="X1", y1="Y1"):
    """{F bijection X→X₁, G bijection Y→Y₁} ⊢ est_bijection_de(H, X×Y, X₁×Y₁).

    Les 4 conjoints (fonctionnel, domaine, injectif, image) sont fournis par les
    paliers 1a/1/3/4 ; on coupe leurs hypothèses (injectivité, fonctionnalité,
    domaines, images de F et G) par les conjoints de est_bijection_de(F,X,X₁) et
    est_bijection_de(G,Y,Y₁)."""
    from ensembles_cardinaux import est_bijection_de
    vF, vG = _t(f), _t(g)
    vX, vY, vX1, vY1 = _t(x), _t(y), _t(x1), _t(y1)
    hF = N.assume(est_bijection_de(vF, vX, vX1))
    hG = N.assume(est_bijection_de(vG, vY, vY1))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(hF))
    Fdom = conjonction_elim_droite(conjonction_elim_gauche(hF))
    Finj = conjonction_elim_gauche(conjonction_elim_droite(hF))
    Fimg = conjonction_elim_droite(conjonction_elim_droite(hF))
    Gfunc = conjonction_elim_gauche(conjonction_elim_gauche(hG))
    Gdom = conjonction_elim_droite(conjonction_elim_gauche(hG))
    Ginj = conjonction_elim_gauche(conjonction_elim_droite(hG))
    Gimg = conjonction_elim_droite(conjonction_elim_droite(hG))
    pFf = (E.est_fonctionnel(vF), Ffunc); pFd = (egal(E.dom(vF), vX), Fdom)
    pFi = (E.injective_dans(vF, vX), Finj); pFm = (egal(E.image(vF, vX), vX1), Fimg)
    pGf = (E.est_fonctionnel(vG), Gfunc); pGd = (egal(E.dom(vG), vY), Gdom)
    pGi = (E.injective_dans(vG, vY), Ginj); pGm = (egal(E.image(vG, vY), vY1), Gimg)
    c1 = produit_graphe_fonctionnel(f, g, x, y)                 # H fonctionnel  (clos)
    c2 = produit_graphe_domaine(f, g, x, y)                     # dom H = X×Y    (clos)
    c3 = _cut(produit_graphe_injective(f, g, x, y), [pFi, pGi])  # inj H / X×Y
    c4 = _cut(produit_graphe_image(f, g, x, y, x1, y1),
              [pFf, pFd, pFm, pGf, pGd, pGm])                   # image H = X₁×Y₁
    return conjonction_intro(conjonction_intro(c1, c2), conjonction_intro(c3, c4))


def eq_produit_invariant(f="F", g="G", x="X", y="Y", x1="X1", y1="Y1"):
    """⊢ (Eq(X,X₁) et Eq(Y,Y₁)) ⇒ Eq(X×Y, X₁×Y₁).   (INVARIANCE DU PRODUIT CARDINAL,
    keystone de l'arithmétique cardinale, E.III.3.)

    Témoin = le graphe produit H ; S5 sur est_bijection_de(F',X×Y,X₁×Y₁) donne
    (∃F')bij = Eq(X×Y, X₁×Y₁), sous les bijections F:X→X₁, G:Y→Y₁ extraites de
    Eq(X,X₁), Eq(Y,Y₁) par élimination des deux témoins existentiels."""
    from ensembles_cardinaux import est_bijection_de, equipotent
    from tactiques_abrege_quantif import alpha_existe as _alpha
    vF, vG = _t(f), _t(g)
    vX, vY, vX1, vY1 = _t(x), _t(y), _t(x1), _t(y1)
    A = E.produit(vX, vY)
    X1Y1 = E.produit(vX1, vY1)
    H = _prod_graphe(f, g, x, y, "k")
    bij = produit_est_bijection(f, g, x, y, x1, y1)             # bij(H,X×Y,X₁×Y₁)  [hyps bij F, bij G]
    eq_prod = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), A, X1Y1), H, "F"))  # Eq(X×Y,X₁×Y₁)
    # éliminer le témoin G de Eq(Y,Y₁)
    stepG = N.loi_deduction(est_bijection_de(vG, vY, vY1), eq_prod)
    elimG = existe_elimination(stepG, "G")                      # (∃G)bij(G,Y,Y₁) ⇒ Eq(X×Y,X₁×Y₁)
    alphaG = _alpha("G", "F", est_bijection_de(var("G"), vY, vY1))  # (∃G)bij ⇔ equipotent(Y,Y₁)
    elimG = syllogisme(equivalence_arriere(alphaG), elimG)     # equipotent(Y,Y₁) ⇒ Eq(X×Y,X₁×Y₁)
    # éliminer le témoin F de Eq(X,X₁)
    stepF = N.loi_deduction(est_bijection_de(vF, vX, vX1), elimG)
    elimF = existe_elimination(stepF, "F")                      # Eq(X,X₁) ⇒ (Eq(Y,Y₁) ⇒ Eq(X×Y,X₁×Y₁))
    # importation : A⇒(B⇒C) ⟹ (A et B)⇒C
    hab = N.assume(et(equipotent(vX, vX1), equipotent(vY, vY1)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimF))
    return N.loi_deduction(et(equipotent(vX, vX1), equipotent(vY, vY1)), c)


__all__ = ["produit_graphe_fonctionnel", "produit_graphe_domaine",
           "produit_graphe_valeur", "produit_graphe_injective",
           "produit_graphe_image", "produit_est_bijection", "eq_produit_invariant"]
