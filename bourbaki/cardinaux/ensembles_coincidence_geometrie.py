"""§III.2 — DÉCHARGE de la géométrie de `coincidence_sur_chevauchement` (vers la clôture
de la trichotomie, Théorème 3).

`coincidence_sur_chevauchement` (ensembles_trichotomie_restriction, CLOS sous hyps) prend
en hypothèses la GÉOMÉTRIE de c=φ'⁻¹∘φ et k=φ⁻¹∘φ' :
    (∀t)(t∈S ⇒ c(t)∈S),   (∀t)(t∈S ⇒ k(t)∈S),   (∀x)(x∈S ⇒ k(c(x))=x),
    (∀u)(u∈S ⇒ φ'(c(u))=φ(u)).
Avec c, k pris comme les TERMES composées (ψ∘φ, χ∘φ'), ces hyps se DÉRIVENT des données
d'iso (graphe⊂S×T, dom, fonctionnel) via :
  • `valeur_dans_codomaine`  (G(x)∈F sous G⊂E×F, dom G=E, x∈E)   — pour c,k : S→S ;
  • `composition_valeur`     ((g∘f)(x)=g(f(x)))                  — déplie la composée ;
  • `section_reciproque`     (φ(φ⁻¹(x))=x)                       — rétraction / raccord ;
  • pont liant-valeur j↔y (`valeur_j_egal_y`) aux frontières (coincidence écrit c(t) en
    « j » via `_val` ; les helpers fonctions écrivent en « y »).

theorie=22.  Rien postulé : chaque conclusion est dérivée, hyps structurelles explicites.

⚠️ Construction GRADUÉE — on commit brique par brique (testée).  BRIQUE 1 ci-dessous :
   c=g∘f : S→S (codomaine de la composée).
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, appartient, inclus, pourtout, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie, conjonction_intro,
)
from bourbaki.ordre.ensembles_valeur_bridge import valeur_j_egal_y
from bourbaki.ensembles.fonctions.ensembles_valeur_codomaine import valeur_dans_codomaine
from bourbaki.ensembles.fonctions.ensembles_fonctions_composee import composition_valeur


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def composee_dans_S(g="psi", f="phi", S="S", T="T", t="t"):
    """⊢ { f⊂S×T, dom f=S, f fonctionnel,  g⊂T×S, dom g=T, g fonctionnel }
         ⊢ (∀t)( t∈S ⇒ valeur(g∘f, t, b="j") ∈ S ).

    c := g∘f : S→S.  Pour t∈S : f(t)∈T (valeur_dans_codomaine sur f), g(f(t))∈S
    (valeur_dans_codomaine sur g), (g∘f)(t)=g(f(t)) (composition_valeur), d'où
    (g∘f)(t)∈S ; pont « y→j » pour la forme `_val` attendue par coincidence.
    Binders/valeurs en « y » (helpers) ; conclusion en « j » (séquent coincidence)."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    vf, vg, vS, vT, vt, vy = var(f), var(g), var(S), var(T), var(t), var("y")
    comp = E.composee(vg, vf)
    ft_y = E.valeur(vf, vt)               # f(t)[y]
    gft_y = E.valeur(vg, ft_y)            # g(f(t))[y]
    ct_y = E.valeur(comp, vt)             # (g∘f)(t)[y]
    ct_j = E.valeur(comp, vt, b="j")      # (g∘f)(t)[j]  (forme _val du séquent coincidence)
    Ht = N.assume(appartient(vt, vS))     # t∈S

    # f(t)∈T  : valeur_dans_codomaine(f,S,T,t)  [hyps f⊂S×T, dom f=S, t∈S]
    ft_in_T = valeur_dans_codomaine(f, S, T, t)          # ⊢ f(t)[y]∈T
    # g(f(t))∈S : valeur_dans_codomaine(g,T,S, f(t))  [hyps g⊂T×S, dom g=T, f(t)∈T]
    gft_in_S = valeur_dans_codomaine(vg, vT, vS, ft_y)   # ⊢ g(f(t))[y]∈S  [hyp f(t)∈T]
    gft_in_S = N.modus_ponens(ft_in_T,
                              N.loi_deduction(appartient(ft_y, vT), gft_in_S))   # g(f(t))[y]∈S

    # ── dériver les hyps de domaine (∃) de composition_valeur (contiennent t) ──
    #   t∈dom f  (de t∈S et dom f=S) puis (∃y)((t,y)∈f)  [AXIOME_DOM]
    Hdomf = N.assume(egal(E.dom(vf), vS))                 # dom f = S (hyp structurelle)
    t_in_domf = N.modus_ponens(Ht, equivalence_arriere(N.modus_ponens(
        Hdomf, N.s6(E.dom(vf), vS, "hdf", appartient(vt, var("hdf"))))))    # t∈dom f
    axdf = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vf), vt)
    exF = N.modus_ponens(t_in_domf, equivalence_avant(axdf))    # (∃y)((t,y)∈f)
    #   f(t)∈dom g  (de f(t)∈T et dom g=T) puis (∃y)((f(t),y)∈g)
    Hdomg = N.assume(egal(E.dom(vg), vT))                 # dom g = T (hyp structurelle)
    ft_in_domg = N.modus_ponens(ft_in_T, equivalence_arriere(N.modus_ponens(
        Hdomg, N.s6(E.dom(vg), vT, "hdg", appartient(ft_y, var("hdg"))))))  # f(t)∈dom g
    axdg = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vg), ft_y)
    exG = N.modus_ponens(ft_in_domg, equivalence_avant(axdg))   # (∃y)((f(t),y)∈g)

    # (g∘f)(t)[y] = g(f(t))[y]   : composition_valeur(g,f,t), hyps domaine (∃) déchargées
    comp_eq = composition_valeur(g, f, t)                # ⊢ … [hyps f func, g func, exF, exG]
    comp_eq = N.modus_ponens(exF, N.loi_deduction(
        existe("y", appartient(E.couple(vt, vy), vf)), comp_eq))
    comp_eq = N.modus_ponens(exG, N.loi_deduction(
        existe("y", appartient(E.couple(ft_y, vy), vg)), comp_eq))   # ⊢ (g∘f)(t)[y]=g(f(t))[y]

    # (g∘f)(t)[y] ∈ S   : Leibniz, réécrit g(f(t)) → (g∘f)(t) dans « g(f(t))∈S »
    #   de comp_eq : (g∘f)(t)=g(f(t)) ; s6 sur (g∘f)(t)=g(f(t)) ⇒ (·∈S ⇔ ·∈S)
    eqv_y = N.modus_ponens(comp_eq,
                           N.s6(ct_y, gft_y, "hgy", appartient(var("hgy"), vS)))
    #   eqv_y : ((g∘f)(t)[y]∈S) ⇔ (g(f(t))[y]∈S)
    ct_y_in_S = N.modus_ponens(gft_in_S, equivalence_arriere(eqv_y))   # (g∘f)(t)[y]∈S

    # pont y→j : (g∘f)(t)[j] = (g∘f)(t)[y]  → (g∘f)(t)[j]∈S
    eq_jy = valeur_j_egal_y(comp, vt)                    # ⊢ (g∘f)(t)[j] = (g∘f)(t)[y]
    eqv_j = N.modus_ponens(eq_jy,
                           N.s6(ct_j, ct_y, "hgj", appartient(var("hgj"), vS)))
    #   eqv_j : ((g∘f)(t)[j]∈S) ⇔ ((g∘f)(t)[y]∈S)
    ct_j_in_S = N.modus_ponens(ct_y_in_S, equivalence_arriere(eqv_j))  # (g∘f)(t)[j]∈S

    body = N.loi_deduction(appartient(vt, vS), ct_j_in_S)    # t∈S ⇒ (g∘f)(t)[j]∈S
    return N.generalisation(t, body)                         # (∀t)(t∈S ⇒ (g∘f)(t)[j]∈S)


def composee_dans_S_t(g, f, S, T, t="t"):
    """⊢ { f⊂S×T, dom f=S, f func, g⊂T×S, dom g=T, g func, (g∘f) func }
         ⊢ (∀t)( t∈S ⇒ valeur(g∘f, t, b="j") ∈ S ).   (version TERMES de composee_dans_S.)

    Identique à composee_dans_S mais g, f sont des TERMES (ex. g=reciproque φ') : utilise
    `composition_valeur_t` (au lieu de composition_valeur, name-based) — d'où l'hyp
    (g∘f) fonctionnel EXPLICITE en plus."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    from bourbaki.ensembles.fonctions.ensembles_composee_valeurs import composition_valeur_t
    vg, vf, vS, vT, vt, vy = _t(g), _t(f), _t(S), _t(T), var(t), var("y")
    comp = E.composee(vg, vf)
    ft_y = E.valeur(vf, vt)               # f(t)[y]
    gft_y = E.valeur(vg, ft_y)            # g(f(t))[y]
    ct_y = E.valeur(comp, vt)             # (g∘f)(t)[y]
    ct_j = E.valeur(comp, vt, b="j")      # (g∘f)(t)[j]
    Ht = N.assume(appartient(vt, vS))

    ft_in_T = valeur_dans_codomaine(vf, vS, vT, vt)          # f(t)[y]∈T
    gft_in_S = valeur_dans_codomaine(vg, vT, vS, ft_y)       # g(f(t))[y]∈S [hyp f(t)∈T]
    gft_in_S = N.modus_ponens(ft_in_T, N.loi_deduction(appartient(ft_y, vT), gft_in_S))

    comp_eq = composition_valeur_t(vg, vf, vt)               # (g∘f)(t)[y]=g(f(t))[y]  [hyps ∃dom×2, comp func]
    comp_eq = N.modus_ponens(_decharge_exists_dom(vf, vt, N.assume(egal(E.dom(vf), vS)), vS, Ht),
        N.loi_deduction(existe("y", appartient(E.couple(vt, vy), vf)), comp_eq))
    comp_eq = N.modus_ponens(_decharge_exists_dom(vg, ft_y, N.assume(egal(E.dom(vg), vT)), vT, ft_in_T),
        N.loi_deduction(existe("y", appartient(E.couple(ft_y, vy), vg)), comp_eq))

    eqv_y = N.modus_ponens(comp_eq, N.s6(ct_y, gft_y, "hgy", appartient(var("hgy"), vS)))
    ct_y_in_S = N.modus_ponens(gft_in_S, equivalence_arriere(eqv_y))   # (g∘f)(t)[y]∈S
    eqv_j = N.modus_ponens(valeur_j_egal_y(comp, vt),
                           N.s6(ct_j, ct_y, "hgj", appartient(var("hgj"), vS)))
    ct_j_in_S = N.modus_ponens(ct_y_in_S, equivalence_arriere(eqv_j))  # (g∘f)(t)[j]∈S
    body = N.loi_deduction(appartient(vt, vS), ct_j_in_S)
    return N.generalisation(t, body)


def retraction_phi(phi="phi", S="S", T="T", x="x"):
    """⊢ { dom φ=S,  φ⁻¹ fonctionnel }  ⊢ (∀x)( x∈S ⇒ valeur(φ⁻¹, valeur(φ,x), )=x ).

    φ⁻¹∘φ = id sur S (RETRACTION de φ, sens domaine — distinct de `section_reciproque`
    qui donne φ∘φ⁻¹=id sur l'image).  (x,φ(x))∈φ (valeur_dans_graphe), donc (φ(x),x)∈φ⁻¹
    (couple_reciproque) ; φ⁻¹ fonctionnel ⇒ φ⁻¹(φ(x))=x (valeur_caracterisation).  Liant
    « y » (helpers).  φ⁻¹ fonctionnel = φ injective (vrai pour un iso).  Sous-lemme BRIQUE 3."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    from bourbaki.ensembles.fonctions.ensembles_fonctions import (
        valeur_dans_graphe, valeur_caracterisation)
    from bourbaki.ensembles.fonctions.ensembles_reciproque import couple_reciproque
    from bourbaki.ordre.ensembles_valeur_bridge import valeur_y_egal_j
    vphi, vS, vT, vx, vy = var(phi), var(S), var(T), var(x), var("y")
    Phinv = E.reciproque(vphi)
    Hx = N.assume(appartient(vx, vS))            # x∈S
    phi_x_y = E.valeur(vphi, vx)                 # φ(x)[y]  (sortie des helpers)
    phi_x = E.valeur(vphi, vx, b="j")            # φ(x)[j]  (POINT en « j » : évite la capture
    #                                              du liant « y » interne de valeur_caracterisation)
    finv_phix = E.valeur(Phinv, phi_x)           # φ⁻¹(φ(x)[j])[y]

    # (x,φ(x)[y])∈φ  [valeur_dans_graphe, hyp (∃y)(x,y)∈φ déchargée via x∈dom φ=S]
    x_phix = valeur_dans_graphe(vphi, vx)
    Hdomphi = N.assume(egal(E.dom(vphi), vS))
    x_in_domphi = N.modus_ponens(Hx, equivalence_arriere(N.modus_ponens(
        Hdomphi, N.s6(E.dom(vphi), vS, "hdx", appartient(vx, var("hdx"))))))
    axd = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vphi), vx)
    exx = N.modus_ponens(x_in_domphi, equivalence_avant(axd))
    x_phix = N.modus_ponens(exx, N.loi_deduction(
        existe("y", appartient(E.couple(vx, vy), vphi)), x_phix))     # (x,φ(x)[y])∈φ
    # pont y→j sur le point φ(x) (x plaine → sûr) : (x,φ(x)[j])∈φ
    x_phix = N.modus_ponens(x_phix, equivalence_avant(N.modus_ponens(
        valeur_y_egal_j(vphi, vx),
        N.s6(phi_x_y, phi_x, "hpj", appartient(E.couple(vx, var("hpj")), vphi)))))   # (x,φ(x)[j])∈φ

    # (φ(x),x)∈φ⁻¹  [couple_reciproque(φ, φ(x), x), CLOS]
    cr = couple_reciproque(vphi, phi_x, vx)      # ((φ(x),x)∈φ⁻¹) ⇔ ((x,φ(x))∈φ)
    phix_x = N.modus_ponens(x_phix, equivalence_arriere(cr))          # (φ(x),x)∈φ⁻¹

    # φ⁻¹(φ(x))=x  [valeur_caracterisation(φ⁻¹, φ(x)) ; hyps φ⁻¹ func + (∃y)(φ(x),y)∈φ⁻¹]
    vc = valeur_caracterisation(Phinv, phi_x)    # ((φ(x),y)∈φ⁻¹ ⇔ y=φ⁻¹(φ(x)))
    vc_x = instancie(N.generalisation("y", vc), vx)   # ((φ(x),x)∈φ⁻¹ ⇔ x=φ⁻¹(φ(x)))
    x_eq = N.modus_ponens(phix_x, equivalence_avant(vc_x))            # x=φ⁻¹(φ(x))
    eq = N.modus_ponens(x_eq, symetrie(vx, finv_phix))               # φ⁻¹(φ(x))=x
    #   décharge l'hyp domaine (∃y)(φ(x),y)∈φ⁻¹ de valeur_caracterisation via phix_x
    ex_recip = N.modus_ponens(phix_x, N.s5(appartient(E.couple(phi_x, vy), Phinv), vx, "y"))
    eq = N.modus_ponens(ex_recip, N.loi_deduction(
        existe("y", appartient(E.couple(phi_x, vy), Phinv)), eq))     # φ⁻¹(φ(x))=x

    body = N.loi_deduction(appartient(vx, vS), eq)
    return N.generalisation(x, body)             # (∀x)(x∈S ⇒ φ⁻¹(φ(x))=x)


def retraction_phi_cible(phi="phi", S="S", T="T", x="x"):
    """ÉNONCÉ-cible (test miroir) : (∀x)(x∈S ⇒ φ⁻¹(φ(x)[j])=x)  (point φ(x) en « j »)."""
    vphi, vS, vx = var(phi), var(S), var(x)
    Phinv = E.reciproque(vphi)
    return pourtout(x, impl(appartient(vx, vS),
                            egal(E.valeur(Phinv, E.valeur(vphi, vx, b="j")), vx)))


def raccord_phip(phi="phi", phip="phip", S="S", T="T", u="u"):
    """⊢ { φ⊂S×T, dom φ=S, φ func, φ' func, dom(φ'⁻¹)=T, (φ'⁻¹∘φ) func }
         ⊢ (∀u)( u∈S ⇒ valeur(φ', valeur(c,u,b="j"), b="j") = valeur(φ,u,b="j") )
       où c := φ'⁻¹∘φ = composee(reciproque(φ'), φ).   (BRIQUE 4 — raccord φ'(c(u))=φ(u).)

    c(u)=φ'⁻¹(φ(u)) (composition_valeur_t) ; φ'(φ'⁻¹(φ(u)))=φ(u) (section_reciproque,
    sous φ(u)∈T) ; pont liant j↔y aux frontières (le point c(u)[j] porte un τ_j, donc
    le pont externe sur φ'(c(u)) NE capture PAS — contrairement au cas τ_y)."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites
    from bourbaki.cardinaux.ensembles_iso_ordre_reciproque import section_reciproque
    from bourbaki.ensembles.fonctions.ensembles_composee_valeurs import composition_valeur_t
    vphi, vphip, vS, vT, vu, vy = _t(phi), _t(phip), _t(S), _t(T), var(u), var("y")
    Phinv = E.reciproque(vphip)               # φ'⁻¹
    c = E.composee(Phinv, vphi)               # c = φ'⁻¹∘φ
    Hu = N.assume(appartient(vu, vS))         # u∈S
    phi_u_y = E.valeur(vphi, vu)              # φ(u)[y]
    cu_j = E.valeur(c, vu, b="j")             # c(u)[j]  (forme _val du séquent coincidence)
    finv_phiu_y = E.valeur(Phinv, phi_u_y)    # φ'⁻¹(φ(u))[y]

    # φ(u)[y] ∈ T  (codomaine φ:S→T)
    phiu_in_T = valeur_dans_codomaine(phi, S, T, u)       # [hyps φ⊂S×T, dom φ=S, u∈S]

    # c(u)[y] = φ'⁻¹(φ(u))[y]  : composition_valeur_t(φ'⁻¹, φ, u), hyps domaine (∃) déchargées
    comp_eq = composition_valeur_t(Phinv, vphi, vu)       # c(u)[y] = φ'⁻¹(φ(u))[y]
    #   (∃y)((u,y)∈φ)  [u∈dom φ de u∈S + dom φ=S]
    Hdomphi = N.assume(egal(E.dom(vphi), vS))
    u_in_domphi = N.modus_ponens(Hu, equivalence_arriere(N.modus_ponens(
        Hdomphi, N.s6(E.dom(vphi), vS, "hdp", appartient(vu, var("hdp"))))))
    axdphi = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vphi), vu)
    exF = N.modus_ponens(u_in_domphi, equivalence_avant(axdphi))
    comp_eq = N.modus_ponens(exF, N.loi_deduction(
        existe("y", appartient(E.couple(vu, vy), vphi)), comp_eq))
    #   (∃y)((φ(u),y)∈φ'⁻¹)  [φ(u)∈dom φ'⁻¹=T de φ(u)∈T]
    Hdomrec = N.assume(egal(E.dom(Phinv), vT))
    phiu_in_domrec = N.modus_ponens(phiu_in_T, equivalence_arriere(N.modus_ponens(
        Hdomrec, N.s6(E.dom(Phinv), vT, "hdr", appartient(phi_u_y, var("hdr"))))))
    axdrec = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), Phinv), phi_u_y)
    exG = N.modus_ponens(phiu_in_domrec, equivalence_avant(axdrec))
    comp_eq = N.modus_ponens(exG, N.loi_deduction(
        existe("y", appartient(E.couple(phi_u_y, vy), Phinv)), comp_eq))   # c(u)[y]=φ'⁻¹(φ(u))[y] [hyp comp func]

    # section : φ'(φ'⁻¹(φ(u)[y]))[y] = φ(u)[y]   (section_reciproque, hyp φ(u)∈T déchargée)
    sec = section_reciproque(vphip, phi_u_y, vT)          # φ'(φ'⁻¹(φ(u)))[y] = φ(u)[y]  [hyp φ(u)∈T]
    sec = N.modus_ponens(phiu_in_T, N.loi_deduction(appartient(phi_u_y, vT), sec))

    # ── chaînage vers la cible (tout ramené en « j » par ponts sûrs) ──
    #   c(u)[j] = c(u)[y] = φ'⁻¹(φ(u))[y]   (pont sur c + comp_eq)
    cu_j_eq_finv = composer_egalites(valeur_j_egal_y(c, vu), comp_eq)      # c(u)[j] = φ'⁻¹(φ(u))[y]
    #   φ'(c(u)[j])[j] = φ'(c(u)[j])[y]   (pont externe ; point c(u)[j] porte τ_j → sûr)
    lhs_jy = valeur_j_egal_y(vphip, cu_j)                 # φ'(c(u)[j])[j] = φ'(c(u)[j])[y]
    #   φ'(c(u)[j])[y] = φ'(φ'⁻¹(φ(u))[y])[y]   (Leibniz : c(u)[j] → φ'⁻¹(φ(u))[y])
    rew = N.modus_ponens(cu_j_eq_finv, N.s6(cu_j, finv_phiu_y, "hr1",
        egal(E.valeur(vphip, cu_j), E.valeur(vphip, var("hr1")))))
    #   rew : (φ'(c(u)[j])[y] = φ'(c(u)[j])[y]) ⇔ (φ'(c(u)[j])[y] = φ'(φ'⁻¹(φ(u))[y])[y])
    lhsy_eq_seclhs = N.modus_ponens(N.reflexivite(E.valeur(vphip, cu_j)),
                                    equivalence_avant(rew))    # φ'(c(u)[j])[y] = φ'(φ'⁻¹(φ(u))[y])[y]
    #   chaîne : φ'(c(u)[j])[j] = φ'(c(u)[j])[y] = φ'(φ'⁻¹(φ(u))[y])[y] = φ(u)[y]
    lhs_eq_phiuy = composer_egalites(composer_egalites(lhs_jy, lhsy_eq_seclhs), sec)   # φ'(c(u)[j])[j] = φ(u)[y]
    #   φ(u)[y] = φ(u)[j]   (pont inverse)
    from bourbaki.ordre.ensembles_valeur_bridge import valeur_y_egal_j
    lhs_eq_phiuj = composer_egalites(lhs_eq_phiuy, valeur_y_egal_j(vphi, vu))   # φ'(c(u)[j])[j] = φ(u)[j]

    body = N.loi_deduction(appartient(vu, vS), lhs_eq_phiuj)
    return N.generalisation(u, body)          # (∀u)(u∈S ⇒ φ'(c(u))[j]=φ(u)[j])


def raccord_phip_cible(phi="phi", phip="phip", S="S", T="T", u="u"):
    """ÉNONCÉ-cible (test miroir) : (∀u)(u∈S ⇒ φ'(c(u))[j]=φ(u)[j]), c=φ'⁻¹∘φ."""
    vphi, vphip, vS, vu = var(phi), var(phip), var(S), var(u)
    c = E.composee(E.reciproque(vphip), vphi)
    cu_j = E.valeur(c, vu, b="j")
    return pourtout(u, impl(appartient(vu, vS),
                            egal(E.valeur(vphip, cu_j, b="j"), E.valeur(vphi, vu, b="j"))))


def _decharge_exists_dom(g, x_term, dom_eq_thm, dom_set, in_dom_thm):
    """⊢ (∃y)((x_term, y) ∈ g)  à partir de : (x_term ∈ dom_set), (dom g = dom_set).
    Renvoie (∃y)((x,y)∈g) [AXIOME_DOM], via x∈dom_set + dom g=dom_set ⇒ x∈dom g."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    vy = var("y")
    x_in_domg = N.modus_ponens(in_dom_thm, equivalence_arriere(N.modus_ponens(
        dom_eq_thm, N.s6(E.dom(g), dom_set, "hde", appartient(x_term, var("hde"))))))
    axd = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), g), x_term)
    return N.modus_ponens(x_in_domg, equivalence_avant(axd))         # (∃y)((x_term,y)∈g)


def retraction_kc(phi="phi", phip="phip", S="S", T="T", x="x"):
    """⊢ { φ⊂S×T, dom φ=S, φ func, φ⁻¹ func,  φ'⊂S×T, dom φ'=S, φ' func, dom(φ'⁻¹)=T,
           (φ'⁻¹∘φ) func, (φ⁻¹∘φ') func }
         ⊢ (∀x)( x∈S ⇒ valeur(k, valeur(c,x,j), j) = x )
       où c := φ'⁻¹∘φ = composee(reciproque φ',φ),  k := φ⁻¹∘φ' = composee(reciproque φ,φ').

    🎯 BRIQUE 3 — RÉTRACTION k∘c = id_S.  k(c(x)) = φ⁻¹(φ'(φ'⁻¹(φ(x)))) = φ⁻¹(φ(x)) = x :
      • c(x) = φ'⁻¹(φ(x))               (composition_valeur_t sur c)
      • φ'(c(x)) = φ'(φ'⁻¹(φ(x))) = φ(x) (section_reciproque φ', φ(x)∈T)
      • k(c(x)) = φ⁻¹(φ'(c(x))) = φ⁻¹(φ(x))  (composition_valeur_t sur k ; c(x) en τ_j → sûr)
      • φ⁻¹(φ(x)) = x                    (retraction_phi)
    Ponts liant j↔y sur points PLAINS / τ_j (jamais τ_y) → pas de capture."""
    from bourbaki.logique.formule import existe
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_arriere
    from bourbaki.cardinaux.ensembles_iso_ordre_reciproque import section_reciproque
    from bourbaki.ensembles.fonctions.ensembles_composee_valeurs import composition_valeur_t
    from bourbaki.ordre.ensembles_valeur_bridge import valeur_y_egal_j
    vphi, vphip, vS, vT, vx, vy = _t(phi), _t(phip), _t(S), _t(T), var(x), var("y")
    PhiInv = E.reciproque(vphi)               # φ⁻¹
    PhipInv = E.reciproque(vphip)             # φ'⁻¹
    c = E.composee(PhipInv, vphi)             # c = φ'⁻¹∘φ
    k = E.composee(PhiInv, vphip)             # k = φ⁻¹∘φ'
    Hx = N.assume(appartient(vx, vS))         # x∈S
    phi_x_y = E.valeur(vphi, vx)              # φ(x)[y]
    phi_x_j = E.valeur(vphi, vx, b="j")       # φ(x)[j]
    cx_j = E.valeur(c, vx, b="j")             # c(x)[j]   (point τ_j)

    Hdomphi = N.assume(egal(E.dom(vphi), vS))
    Hdomphip = N.assume(egal(E.dom(vphip), vS))
    Hdomrec = N.assume(egal(E.dom(PhipInv), vT))      # dom φ'⁻¹ = T
    phiu_in_T = valeur_dans_codomaine(phi, S, T, x)   # φ(x)[y]∈T   [hyps φ⊂S×T, dom φ=S, x∈S]

    # ── (A) c(x)[j] = φ'⁻¹(φ(x))[y]  (composition_valeur_t sur c + pont) ──
    comp_c = composition_valeur_t(PhipInv, vphi, vx)          # c(x)[y] = φ'⁻¹(φ(x)[y])[y]
    comp_c = N.modus_ponens(_decharge_exists_dom(vphi, vx, Hdomphi, vS, Hx),
        N.loi_deduction(existe("y", appartient(E.couple(vx, vy), vphi)), comp_c))
    comp_c = N.modus_ponens(_decharge_exists_dom(PhipInv, phi_x_y, Hdomrec, vT, phiu_in_T),
        N.loi_deduction(existe("y", appartient(E.couple(phi_x_y, vy), PhipInv)), comp_c))
    finv_phix_y = E.valeur(PhipInv, phi_x_y)                  # φ'⁻¹(φ(x))[y]
    cxj_eq_finv = composer_egalites(valeur_j_egal_y(c, vx), comp_c)   # c(x)[j] = φ'⁻¹(φ(x))[y]

    # ── (C) φ'(c(x)[j])[y] = φ(x)[y]  (réécrit c(x)[j]→φ'⁻¹(φ(x)), section_reciproque) ──
    #   réécrire c(x)[j] → φ'⁻¹(φ(x))[y] dans valeur(φ', ·, y)
    phip_cxj_y = E.valeur(vphip, cx_j)                        # φ'(c(x)[j])[y]
    rewC = N.modus_ponens(cxj_eq_finv, N.s6(cx_j, finv_phix_y, "hrc",
        egal(phip_cxj_y, E.valeur(vphip, var("hrc")))))
    phip_cxj_eq = N.modus_ponens(N.reflexivite(phip_cxj_y), equivalence_avant(rewC))  # φ'(c(x)[j])[y]=φ'(φ'⁻¹(φ(x)))[y]
    sec = section_reciproque(vphip, phi_x_y, vT)              # φ'(φ'⁻¹(φ(x)[y]))[y]=φ(x)[y]  [hyp φ(x)∈T]
    sec = N.modus_ponens(phiu_in_T, N.loi_deduction(appartient(phi_x_y, vT), sec))
    phip_cxj_y_eq_phix = composer_egalites(phip_cxj_eq, sec)  # φ'(c(x)[j])[y] = φ(x)[y]

    # ── (B) k(c(x)[j])[j] = φ⁻¹(φ'(c(x)[j]))[y]  (pont externe + composition_valeur_t sur k) ──
    lhs_j = E.valeur(k, cx_j, b="j")                          # TARGET LHS : k(c(x)[j])[j]
    lhs_jy = valeur_j_egal_y(k, cx_j)                         # k(c(x)[j])[j] = k(c(x)[j])[y]  (cx_j τ_j → sûr)
    comp_k = composition_valeur_t(PhiInv, vphip, cx_j)        # k(c(x)[j])[y] = φ⁻¹(φ'(c(x)[j]))[y]
    #   décharge domaines : c(x)[j]∈dom φ'=S, φ'(c(x)[j])∈dom φ⁻¹=T
    #   c(x)[j]∈S : φ'⁻¹(φ(x))[y]∈S (valeur_dans_codomaine, φ(x)∈T) + c(x)[j]=φ'⁻¹(φ(x))[y]
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie as _sym
    finv_in_S = valeur_dans_codomaine(PhipInv, vT, vS, phi_x_y)   # φ'⁻¹(φ(x))[y]∈S  [hyp φ(x)∈T]
    finv_in_S = N.modus_ponens(phiu_in_T, N.loi_deduction(appartient(phi_x_y, vT), finv_in_S))
    cxj_in_S = N.modus_ponens(finv_in_S, equivalence_avant(N.modus_ponens(
        N.modus_ponens(cxj_eq_finv, _sym(cx_j, finv_phix_y)),     # φ'⁻¹(φ(x))[y] = c(x)[j]
        N.s6(finv_phix_y, cx_j, "hcs", appartient(var("hcs"), vS)))))   # c(x)[j]∈S
    comp_k = N.modus_ponens(_decharge_exists_dom(vphip, cx_j, Hdomphip, vS, cxj_in_S),
        N.loi_deduction(existe("y", appartient(E.couple(cx_j, vy), vphip)), comp_k))
    #   φ'(c(x)[j])[y]∈T : de φ'(c(x)[j])[y]=φ(x)[y] (C) et φ(x)[y]∈T
    HdomPhiInv = N.assume(egal(E.dom(PhiInv), vT))            # dom φ⁻¹ = T
    phipcxj_in_T = N.modus_ponens(phiu_in_T, equivalence_arriere(N.modus_ponens(
        phip_cxj_y_eq_phix, N.s6(phip_cxj_y, phi_x_y, "hpt", appartient(var("hpt"), vT)))))  # φ'(c(x)[j])[y]∈T
    comp_k = N.modus_ponens(_decharge_exists_dom(PhiInv, phip_cxj_y, HdomPhiInv, vT, phipcxj_in_T),
        N.loi_deduction(existe("y", appartient(E.couple(phip_cxj_y, vy), PhiInv)), comp_k))
    #   k(c(x)[j])[j] = φ⁻¹(φ'(c(x)[j]))[y]
    lhs_eq_kfinv = composer_egalites(lhs_jy, comp_k)         # k(c(x)[j])[j] = φ⁻¹(φ'(c(x)[j])[y])[y]

    # ── (D) réécrit φ'(c(x)[j])[y] → φ(x)[y] dans φ⁻¹(·)[y], puis φ(x)[y]→φ(x)[j], puis retraction ──
    finv_phipcxj_y = E.valeur(PhiInv, phip_cxj_y)            # φ⁻¹(φ'(c(x)[j]))[y]
    finv_phix_y2 = E.valeur(PhiInv, phi_x_y)                 # φ⁻¹(φ(x)[y])[y]
    rewD = N.modus_ponens(phip_cxj_y_eq_phix, N.s6(phip_cxj_y, phi_x_y, "hrd",
        egal(finv_phipcxj_y, E.valeur(PhiInv, var("hrd")))))
    d_eq = N.modus_ponens(N.reflexivite(finv_phipcxj_y), equivalence_avant(rewD))  # φ⁻¹(φ'(c(x)[j]))[y]=φ⁻¹(φ(x)[y])[y]
    #   φ⁻¹(φ(x)[y])[y] = φ⁻¹(φ(x)[j])[y]   (pont φ(x) y→j, x plaine)
    finv_phix_j = E.valeur(PhiInv, phi_x_j)                  # φ⁻¹(φ(x)[j])[y]
    yj_eq = N.modus_ponens(valeur_y_egal_j(vphi, vx), N.s6(phi_x_y, phi_x_j, "hyj",
        egal(finv_phix_y2, E.valeur(PhiInv, var("hyj")))))
    finvy_eq_finvj = N.modus_ponens(N.reflexivite(finv_phix_y2), equivalence_avant(yj_eq))  # φ⁻¹(φ(x)[y])[y]=φ⁻¹(φ(x)[j])[y]
    #   retraction_phi : φ⁻¹(φ(x)[j])[y] = x
    retr = retraction_phi(phi, S, T, x)                      # (∀x)(x∈S⇒φ⁻¹(φ(x)[j])=x)
    retr_x = N.modus_ponens(Hx, instancie(retr, vx))        # φ⁻¹(φ(x)[j])[y]=x

    # ── chaîne finale : k(c(x)[j])[j] = φ⁻¹(φ'(c(x)[j]))[y] = φ⁻¹(φ(x)[y])[y] = φ⁻¹(φ(x)[j])[y] = x ──
    chain = composer_egalites(composer_egalites(composer_egalites(lhs_eq_kfinv, d_eq), finvy_eq_finvj), retr_x)
    body = N.loi_deduction(appartient(vx, vS), chain)
    return N.generalisation(x, body)          # (∀x)(x∈S ⇒ k(c(x))[j]=x)


def retraction_kc_cible(phi="phi", phip="phip", S="S", T="T", x="x"):
    """ÉNONCÉ-cible (test miroir) : (∀x)(x∈S ⇒ valeur(k, valeur(c,x,j), j)=x)."""
    vphi, vphip, vS, vx = var(phi), var(phip), var(S), var(x)
    c = E.composee(E.reciproque(vphip), vphi)
    k = E.composee(E.reciproque(vphi), vphip)
    cx_j = E.valeur(c, vx, b="j")
    return pourtout(x, impl(appartient(vx, vS),
                            egal(E.valeur(k, cx_j, b="j"), vx)))


def coincidence_close(phi="phi", phip="phip", S="S", T="T", u="u"):
    """⊢ { est_bien_ordonne(R,S),  c strict. croissante S→S,  k strict. croissante S→S,
           + structurelles de φ,φ' (graphe⊂S×T, dom, func, func réciproque) }
         ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ),   c:=φ'⁻¹∘φ, k:=φ⁻¹∘φ'.

    🎯🎯 ASSEMBLAGE Jalon1-a — coïncidence de deux isos sur le chevauchement, RÉSIDU
    GÉOMÉTRIE DÉCHARGÉ.  On appelle `coincidence_sur_chevauchement` avec c,k = les TERMES
    composées (φ'⁻¹∘φ, φ⁻¹∘φ') — possible depuis le fix var→_t de A_vide/lemme_4/
    point_fixe_automorphisme (verrou composite-vs-nom levé) — et on DÉCHARGE ses 4 familles
    de géométrie par les briques (formes TERMES, matching exact, AUCUN pont de nom) :
      • cod_c, cod_k  ← composee_dans_S_t ;
      • k∘c=id        ← retraction_kc ;
      • φ'(c(u))=φ(u) ← raccord_phip.
    Restent en hyps : bon ordre + stricte croissance de c,k (vraies — c,k sont des isos —
    et déchargeables via auto_de_deux_isos+strict_croissante_depuis_iso, REPORT mineur) +
    les structurelles d'iso.  Conclusion φ(u)=φ'(u) sur S, NON tautologique."""
    from bourbaki.cardinaux.ensembles_trichotomie_restriction import coincidence_sur_chevauchement
    vphi, vphip, vS, vT = _t(phi), _t(phip), _t(S), _t(T)
    PhipInv, PhiInv = E.reciproque(vphip), E.reciproque(vphi)
    c = E.composee(PhipInv, vphi)             # c = φ'⁻¹∘φ  (TERME)
    k = E.composee(PhiInv, vphip)             # k = φ⁻¹∘φ'  (TERME)
    base = coincidence_sur_chevauchement("R", S, phi, phip, c, k, u)   # 7 hyps (c,k TERMES)
    bricks = [
        composee_dans_S_t(PhipInv, vphi, vS, vT),    # (∀t)(t∈S⇒c(t)[j]∈S)
        composee_dans_S_t(PhiInv, vphip, vS, vT),    # (∀t)(t∈S⇒k(t)[j]∈S)
        retraction_kc(phi, phip, S, T, x="u"),       # (∀u)(u∈S⇒k(c(u))[j]=u)
        raccord_phip(phi, phip, S, T, u="u"),        # (∀u)(u∈S⇒φ'(c(u))[j]=φ(u))
    ]
    out = base
    for b in bricks:
        assert b.conclusion in out.hypotheses, "brique ne matche pas une hyp de coincidence"
        out = N.modus_ponens(b, N.loi_deduction(b.conclusion, out))   # décharge la famille
    return out


def coincidence_univ_close(phi1="phi1", phi2="phi2", S1="S1", T1="T1", u="u"):
    """⊢ { hyps de coincidence_close(φ1, φ2|S1, S1, T1)  +  φ2 fonctionnel,  S1 ⊂ dom φ2 }
         ⊢ (∀u)( u∈S1 ⇒ φ1(u) = φ2(u) ).

    🎯 VERSION NESTÉE de la coïncidence (cœur de fusion_hyp / Lemme 1 §III.2) : φ1:S1≅T1
    et φ2 sur un segment plus grand (S1⊂dom φ2) coïncident sur S1.  On applique
    `coincidence_close` à φ2|S1 = restriction(φ2,S1) (qui donne φ1(u)=(φ2|S1)(u) sur S1),
    puis `restriction_valeur` réécrit (φ2|S1)(u)=φ2(u) (ponts liant j↔y).  Géométrie
    déchargée (via coincidence_close) ; reste les hyps structurelles de φ2|S1 + φ2."""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import composer_egalites
    from bourbaki.logique.tactiques.tactiques_abrege2 import instancie as _i
    from bourbaki.ordre.ensembles_valeur_bridge import valeur_y_egal_j
    from bourbaki.cardinaux.ensembles_cantor_bernstein_bij import restriction_valeur
    vphi1, vphi2, vS1, vu = var(phi1), var(phi2), var(S1), var(u)
    phi2S1 = E.restriction(vphi2, vS1)
    base = coincidence_close(phi1, phi2S1, S1, T1, u)         # (∀u)(u∈S1⇒φ1(u)[j]=(φ2|S1)(u)[j])
    Hu = N.assume(appartient(vu, vS1))
    base_u = N.modus_ponens(Hu, _i(base, vu))                # φ1(u)[j]=(φ2|S1)(u)[j]
    # u∈dom φ2  (de u∈S1 et S1⊂dom φ2)
    Hsub = N.assume(inclus(vS1, E.dom(vphi2)))
    u_in_dom = N.modus_ponens(Hu, _i(Hsub, vu))             # u∈dom φ2
    # restriction_valeur : (φ2|S1)(u)[y]=φ2(u)[y]  [φ2 func, u∈S1, u∈dom φ2]
    rv = restriction_valeur(phi2, S1, u)
    rv = N.modus_ponens(Hu, N.loi_deduction(appartient(vu, vS1), rv))
    rv = N.modus_ponens(u_in_dom, N.loi_deduction(appartient(vu, E.dom(vphi2)), rv))   # (φ2|S1)(u)[y]=φ2(u)[y]
    # ponts j↔y : (φ2|S1)(u)[j] = (φ2|S1)(u)[y] = φ2(u)[y] = φ2(u)[j]
    rvj = composer_egalites(composer_egalites(valeur_j_egal_y(phi2S1, vu), rv),
                            valeur_y_egal_j(vphi2, vu))      # (φ2|S1)(u)[j] = φ2(u)[j]
    # φ1(u)[j] = (φ2|S1)(u)[j] = φ2(u)[j]
    final = composer_egalites(base_u, rvj)                   # φ1(u)[j]=φ2(u)[j]
    body = N.loi_deduction(appartient(vu, vS1), final)
    return N.generalisation(u, body)


def coincidence_univ_close_cible(phi1="phi1", phi2="phi2", S1="S1", T1="T1", u="u"):
    """ÉNONCÉ-cible : (∀u)(u∈S1 ⇒ φ1(u)=φ2(u))."""
    vphi1, vphi2, vS1, vu = var(phi1), var(phi2), var(S1), var(u)
    return pourtout(u, impl(appartient(vu, vS1),
                            egal(E.valeur(vphi1, vu, b="j"), E.valeur(vphi2, vu, b="j"))))


def coincidence_close_cible(phi="phi", phip="phip", S="S", T="T", u="u"):
    """ÉNONCÉ-cible (test miroir) : (∀u)(u∈S ⇒ φ(u)=φ'(u))."""
    from bourbaki.cardinaux.ensembles_trichotomie_restriction import coincidence_sur_chevauchement_cible
    return coincidence_sur_chevauchement_cible("R", S, phi, phip, "c", "k", u)


def coincidence_close_isos(phi="phi", phip="phip", S="S", T="T", u="u"):
    """⊢ { est_bien_ordonne(R,S) + isos d'ordre de φ,φ' (et de leurs réciproques φ'⁻¹,φ⁻¹)
           + structurelles }  ⊢  (∀u)( u∈S ⇒ φ(u) = φ'(u) ).

    🎯🎯 coincidence_close AVEC LA STRICTE CROISSANCE de c=φ'⁻¹∘φ et k=φ⁻¹∘φ' DÉCHARGÉE
    (plus AUCUNE hyp de stricte croissance postulée — c'était le dernier résidu « modulo
    isos »).  c,k sont des AUTOMORPHISMES D'ORDRE de (S,R) : `auto_de_deux_isos` (composée
    de deux isos = iso, CLOS) en fournit l'iso(c,S,S,R,R) [resp. k], et
    `strict_croissante_depuis_iso` (CLOS) en tire la stricte croissance τ_j EXACTE
    consommée par coincidence_close.  Les liants d'ordre de l'iso sont x,x2 (sortie de
    composee_isomorphisme_ordre), passés à strict_croissante_depuis_iso via ib_x/ib_y.

    Reste en hyps : bon ordre + isos de φ,φ',φ'⁻¹,φ⁻¹ + structurelles — PLUS de stricte
    croissance.  Conclusion φ(u)=φ'(u) sur S, NON tautologique."""
    from bourbaki.cardinaux.ensembles_coincidence_pont import strict_croissante_depuis_iso
    from bourbaki.cardinaux.ensembles_coincidence_decharge import auto_de_deux_isos
    vphi, vphip = _t(phi), _t(phip)
    base = coincidence_close(phi, phip, S, T, u)                  # 15 hyps incl strict_c, strict_k
    c_term = E.composee(E.reciproque(vphip), vphi)               # c = φ'⁻¹∘φ
    k_term = E.composee(E.reciproque(vphi), vphip)               # k = φ⁻¹∘φ'
    # c = composee(reciproque φ', φ) ⇒ auto(phi, reciproque φ') ; k = composee(reciproque φ, φ') ⇒ auto(phip, reciproque φ)
    for ct, ph_arg, psi_arg in [(c_term, phi, E.reciproque(vphip)),
                                (k_term, phip, E.reciproque(vphi))]:
        scr = strict_croissante_depuis_iso(ct, S, "R", ib_x="x", ib_y="x2")   # 1 hyp : iso(.,S,S,R,R)[x,x2]
        iso_t = auto_de_deux_isos(ph_arg, psi_arg, S, T, "R", "Rp")           # ⊢ iso(composee(psi,ph),S,S,R,R)
        scr = N.modus_ponens(iso_t, N.loi_deduction(iso_t.conclusion, scr))   # décharge l'iso → strict (6 hyps iso/func/dom)
        assert scr.conclusion in base.hypotheses, "stricte croissance ne matche pas une hyp de coincidence_close"
        base = N.modus_ponens(scr, N.loi_deduction(scr.conclusion, base))     # décharge strict_c / strict_k
    return base


def composee_dans_S_cible(g="psi", f="phi", S="S", T="T", t="t"):
    """ÉNONCÉ-cible (test miroir) : (∀t)(t∈S ⇒ valeur(g∘f,t,b="j") ∈ S)."""
    vf, vg, vS, vt = var(f), var(g), var(S), var(t)
    comp = E.composee(vg, vf)
    return pourtout(t, impl(appartient(vt, vS),
                            appartient(E.valeur(comp, vt, b="j"), vS)))


__all__ = ["composee_dans_S", "composee_dans_S_cible"]
