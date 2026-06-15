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
    vphi, vphip, vS, vT, vu, vy = var(phi), var(phip), var(S), var(T), var(u), var("y")
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


def composee_dans_S_cible(g="psi", f="phi", S="S", T="T", t="t"):
    """ÉNONCÉ-cible (test miroir) : (∀t)(t∈S ⇒ valeur(g∘f,t,b="j") ∈ S)."""
    vf, vg, vS, vt = var(f), var(g), var(S), var(t)
    comp = E.composee(vg, vf)
    return pourtout(t, impl(appartient(vt, vS),
                            appartient(E.valeur(comp, vt, b="j"), vS)))


__all__ = ["composee_dans_S", "composee_dans_S_cible"]
