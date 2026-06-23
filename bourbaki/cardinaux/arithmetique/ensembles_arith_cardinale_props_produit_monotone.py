"""§III.3.2 / III.3.3 — MONOTONIE de l'ordre ≤ des cardinaux pour le PRODUIT.

ÉNONCÉS (E.III.3.2-3.3, dérivés ; rien postulé, theorie=22) :

  (1) `produit_graphe_image_inclus`  {F func, dom F=X, F⟨X⟩⊂X₁, G func, dom G=Y,
        G⟨Y⟩⊂Y₁} ⊢ image(H, X×Y) ⊂ X₁×Y₁.   (palier IMAGE version INJECTION du
      produit, « forward-only » de produit_graphe_image : pour une injection l'image
      n'est plus ÉGALE à X₁×Y₁ mais seulement INCLUSE dedans.)

  (2) `inf_egal_produit_invariant`  ⊢ (A ≤ A₁ et B ≤ B₁) ⇒ (A×B ≤ A₁×B₁).
      MONOTONIE du produit cardinal pour ≤ — l'analogue INJECTION de l'invariance
      par équipotence eq_produit_invariant (qui prouve Eq(X,X₁)∧Eq(Y,Y₁)⇒
      Eq(X×Y,X₁×Y₁)).  D'une injection F:A→A₁ et d'une injection G:B→B₁ on construit
      l'injection PRODUIT  H : A×B → A₁×B₁,  (x,y)↦(F(x),G(y)).  C'est le MÊME graphe
      produit  H := graphe_terme(A×B, (F(pr₁k), G(pr₂k)))  que la bijection produit de
      ensembles_produit_equipotence ; on REUTILISE tels quels ses paliers fonctionnel
      / domaine / injectif, et on remplace seulement le palier IMAGE par la version
      INCLUSION (1).

  (3) `cardinal_inf_egal_produit_invariant`  ⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁)
      ⇒ (Card(Card A × Card B) ≤ Card(Card A₁ × Card B₁)) : (2) généralisé puis
      INSTANCIÉ aux termes Card A, Card B, Card A₁, Card B₁.

  (4) `inf_egal_produit_gauche`  ⊢ (A ≤ A₁) ⇒ (A×C ≤ A₁×C)   (monotonie à droite par
      un facteur fixe C : cas (2) avec B=B₁=C et C≤C par réflexivité).
  (5) `inf_egal_produit_droite`  ⊢ (B ≤ B₁) ⇒ (C×B ≤ C×B₁)   (symétrique, facteur
      gauche fixe C).

──────────────────────────────────────────────────────────────────────────────
INDÉPENDANT de Cantor–Bernstein (réservé à l'antisymétrie de ≤).  Réflexivité de ≤
est certifiée ailleurs (ensembles_cardinaux_theoremes.inf_egal_reflexif) — on ne la
duplique pas.  La forme du palier IMAGE forward suit EXACTEMENT le sens ⇒ de
produit_graphe_image (ensembles_produit_equipotence), où les deux Leibniz « F⟨X⟩=X₁ »
(égalité) deviennent des instances de l'inclusion « F⟨X⟩⊂X₁ ».  Strictement
réutilisé : _prod_terme, _prod_graphe, _valeur_dans_image, _valeur_cy,
produit_graphe_fonctionnel / _domaine / _injective.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, appartient, existe, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (_membre_produit_pr1_ab,
                                       _membre_produit_pr2_ab)
from bourbaki.cardinaux.arithmetique.ensembles_produit_equipotence import (
                               _prod_terme, _prod_graphe, _valeur_dans_image, _valeur_cy,
                               produit_graphe_fonctionnel, produit_graphe_domaine,
                               produit_graphe_injective)
from bourbaki.cardinaux.ensembles_cardinaux import (est_injection_de, inf_egal_card, cardinal)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, pairs):
    """Remplace dans `thm` chaque hypothèse `formule` par les hyps de sa `preuve`."""
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


# ═══════════════════════════════════════════════════════════════════════════════
# PALIER IMAGE (version INJECTION) : image(H, X×Y) ⊂ X₁×Y₁
# ═══════════════════════════════════════════════════════════════════════════════
def produit_graphe_image_inclus(f="F", g="G", x="X", y="Y", x1="X1", y1="Y1"):
    """{F func, dom F=X, F⟨X⟩⊂X₁, G func, dom G=Y, G⟨Y⟩⊂Y₁} ⊢ image(H, X×Y) ⊂ X₁×Y₁.

    Version « forward-only » (INCLUSION) du palier produit_graphe_image (qui prouve
    l'ÉGALITÉ image=X₁×Y₁ sous des bijections).  On ne garde que le sens ⇒ :
        z∈H⟨X×Y⟩ ⇔ (∃t)(t∈X×Y et (t,z)∈H) ⇔ (∃t)(t∈X×Y et z=T[t]).
    Sous le corps : T[t]=(F(pr₁t),G(pr₂t)) avec pr₁t∈X (donc pr₁t∈dom F via dom F=X,
    F(pr₁t)∈F⟨X⟩ par _valeur_dans_image) et pr₂t∈Y (G(pr₂t)∈G⟨Y⟩).  La SEULE
    différence avec produit_graphe_image (sens ⇒) est l'étape « ∈image » : Leibniz
    F⟨X⟩=X₁ y est remplacé par l'instanciation de l'inclusion F⟨X⟩⊂X₁.  Liant z,
    témoin t ; aucun ∃-fuite."""
    vF, vG = _t(f), _t(g)
    vX, vY, vX1, vY1 = _t(x), _t(y), _t(x1), _t(y1)
    A = E.produit(vX, vY)
    X1Y1 = E.produit(vX1, vY1)
    T = _prod_terme(f, g, "k")
    H = E.graphe_terme(A, T, "k")
    vz = var("z")
    # caractérisation de l'image (liant interne « x » d'AXIOME_IMAGE renommé « t »)
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
    hFsub = N.assume(inclus(E.image(vF, vX), vX1))         # F⟨X⟩ ⊂ X₁  (INCLUSION)
    hGsub = N.assume(inclus(E.image(vG, vY), vY1))         # G⟨Y⟩ ⊂ Y₁  (INCLUSION)

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
    domF_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vF), pr1t)
    pr1t_ex = N.modus_ponens(pr1t_domF, equivalence_avant(domF_car))   # (∃y)((pr₁t,y)∈F)
    Fpr1t_img = _valeur_dans_image(vF, pr1t, vX)           # {pr₁t∈X,(∃y)…} ⊢ F(pr₁t)∈F⟨X⟩
    Fpr1t_img = N.modus_ponens(pr1t_inX, N.loi_deduction(appartient(pr1t, vX),
        N.modus_ponens(pr1t_ex, N.loi_deduction(
            existe("y", appartient(E.couple(pr1t, var("y")), vF)), Fpr1t_img))))
    # ── le SWAP clé : F⟨X⟩⊂X₁ donne F(pr₁t)[τy]∈X₁ (vs Leibniz F⟨X⟩=X₁) ──
    Fpr1t_inX1 = N.modus_ponens(Fpr1t_img, instancie(hFsub, E.valeur(vF, pr1t)))   # F(pr₁t)[τy]∈X₁
    # même chose pour G
    pr2t_domG = N.modus_ponens(pr2t_inY, equivalence_arriere(N.modus_ponens(
        hGdom, N.s6(E.dom(vG), vY, "w", appartient(pr2t, var("w"))))))
    domG_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vG), pr2t)
    pr2t_ex = N.modus_ponens(pr2t_domG, equivalence_avant(domG_car))
    Gpr2t_img = _valeur_dans_image(vG, pr2t, vY)
    Gpr2t_img = N.modus_ponens(pr2t_inY, N.loi_deduction(appartient(pr2t, vY),
        N.modus_ponens(pr2t_ex, N.loi_deduction(
            existe("y", appartient(E.couple(pr2t, var("y")), vG)), Gpr2t_img))))
    Gpr2t_inY1 = N.modus_ponens(Gpr2t_img, instancie(hGsub, E.valeur(vG, pr2t)))   # G(pr₂t)[τy]∈Y₁
    # (F(pr₁t),G(pr₂t)) ∈ X₁×Y₁ — en τy ; on convertit en τc pour matcher T[t]
    Fy1t, Gy2t = E.valeur(vF, pr1t), E.valeur(vG, pr2t)        # τy
    Fc1t, Gc2t = E.valeur(vF, pr1t, "c"), E.valeur(vG, pr2t, "c")  # τc (= composantes de T[t])
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
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)    # z∈H⟨A⟩ ⇒ z∈X₁×Y₁
    return N.generalisation("z", fwd_full)                    # image(H,X×Y) ⊂ X₁×Y₁


# ═══════════════════════════════════════════════════════════════════════════════
# (2) MONOTONIE du produit pour ≤   (l'injection produit F×G)
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_produit_invariant(f="F", g="G", a="A", b="B", a1="A1", b1="B1"):
    """⊢ (A ≤ A₁ et B ≤ B₁) ⇒ (A × B ≤ A₁ × B₁).   (monotonie du produit ; clos.)

    Témoin = le graphe produit H = F×G : (x,y)↦(F(x),G(y)).  est_injection_de(H, A×B,
    A₁×B₁) tient par ses quatre conjoints (fonctionnel/domaine [closes] ; injectif
    [produit_graphe_injective] ; image⊂A₁×B₁ [palier ci-dessus]), dont on coupe les
    hypothèses par les conjoints de est_injection_de(F,A,A₁) et est_injection_de(G,B,B₁) ;
    S5 témoin H + double élimination des existentiels (avec alpha_existe G→F pour le
    liant de inf_egal_card) donne la conclusion."""
    vF, vG = _t(f), _t(g)
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    AB = E.produit(va, vb)
    A1B1 = E.produit(va1, vb1)
    H = _prod_graphe(f, g, a, b, "k")
    hF = N.assume(est_injection_de(vF, va, va1))
    hG = N.assume(est_injection_de(vG, vb, vb1))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hF)))
    Fdom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hF)))
    Finj = conjonction_elim_droite(conjonction_elim_gauche(hF))
    Fsub = conjonction_elim_droite(hF)                      # image(F,A)⊂A₁
    Gfunc = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hG)))
    Gdom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hG)))
    Ginj = conjonction_elim_droite(conjonction_elim_gauche(hG))
    Gsub = conjonction_elim_droite(hG)                      # image(G,B)⊂B₁
    c1 = produit_graphe_fonctionnel(f, g, a, b)            # H fonctionnel  (clos)
    c2 = produit_graphe_domaine(f, g, a, b)               # dom H = A×B    (clos)
    c3 = _cut(produit_graphe_injective(f, g, a, b),
              [(E.injective_dans(vF, va), Finj), (E.injective_dans(vG, vb), Ginj)])  # inj H/A×B
    c4 = _cut(produit_graphe_image_inclus(f, g, a, b, a1, b1),
              [(egal(E.dom(vF), va), Fdom), (egal(E.dom(vG), vb), Gdom),
               (inclus(E.image(vF, va), va1), Fsub), (inclus(E.image(vG, vb), vb1), Gsub)])  # image⊂A₁×B₁
    inj_H = conjonction_intro(conjonction_intro(conjonction_intro(c1, c2), c3), c4)
    le = N.modus_ponens(inj_H, N.s5(est_injection_de(var("F"), AB, A1B1), H, "F"))  # A×B ≤ A₁×B₁
    stepG = N.loi_deduction(est_injection_de(vG, vb, vb1), le)
    elimG = existe_elimination(stepG, "G")
    alphaG = alpha_existe("G", "F", est_injection_de(var("G"), vb, vb1))
    elimG = syllogisme(equivalence_arriere(alphaG), elimG)  # (B≤B₁) ⇒ (A×B ≤ A₁×B₁)
    stepF = N.loi_deduction(est_injection_de(vF, va, va1), elimG)
    elimF = existe_elimination(stepF, "F")                 # (A≤A₁) ⇒ ((B≤B₁) ⇒ …)
    hab = N.assume(et(inf_egal_card(va, va1), inf_egal_card(vb, vb1)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimF))
    return N.loi_deduction(et(inf_egal_card(va, va1), inf_egal_card(vb, vb1)), c)


def cardinal_inf_egal_produit_invariant(a="A", b="B", a1="A1", b1="B1"):
    """⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁) ⇒
          (Card A × Card B ≤ Card A₁ × Card B₁).   (= « a≤a₁ et b≤b₁ ⇒ a·b ≤ a₁·b₁ ».)

    inf_egal_produit_invariant généralisé en (∀A)(∀B)(∀A₁)(∀B₁) puis INSTANCIÉ aux
    TERMES Card A, Card B, Card A₁, Card B₁."""
    va, vb, va1, vb1 = _t(a), _t(b), _t(a1), _t(b1)
    gen = N.generalisation("A", N.generalisation("B", N.generalisation("A1",
        N.generalisation("B1", inf_egal_produit_invariant("F", "G", "A", "B", "A1", "B1")))))
    return instancie(instancie(instancie(instancie(gen, cardinal(va)), cardinal(vb)),
                               cardinal(va1)), cardinal(vb1))


# ═══════════════════════════════════════════════════════════════════════════════
# (4)-(5) Monotonie par un FACTEUR FIXE C  (cas particuliers de (2) avec réflexivité)
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_produit_gauche(a="A", a1="A1", c="C"):
    """⊢ (A ≤ A₁) ⇒ (A × C ≤ A₁ × C).   (monotonie à gauche, facteur droit fixe C ; clos.)

    Cas particulier de inf_egal_produit_invariant avec B:=C, B₁:=C et C≤C
    (réflexivité de ≤, inf_egal_reflexif au terme C) : de A≤A₁ on tire A×C ≤ A₁×C."""
    va, va1, vc = _t(a), _t(a1), _t(c)
    hAA1 = N.assume(inf_egal_card(va, va1))               # A ≤ A₁
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))   # (∀X) X ≤ X
    refl_c = instancie(refl_all, vc)                     # C ≤ C
    inv = inf_egal_produit_invariant("F", "G", va, vc, va1, vc)   # (A≤A₁ et C≤C)⇒(A×C ≤ A₁×C)
    le = N.modus_ponens(conjonction_intro(hAA1, refl_c), inv)    # A×C ≤ A₁×C  [sous A≤A₁]
    return N.loi_deduction(inf_egal_card(va, va1), le)


def inf_egal_produit_droite(b="B", b1="B1", c="C"):
    """⊢ (B ≤ B₁) ⇒ (C × B ≤ C × B₁).   (monotonie à droite, facteur gauche fixe C ; clos.)

    Cas particulier de inf_egal_produit_invariant avec A:=C, A₁:=C et C≤C
    (réflexivité de ≤) : de B≤B₁ on tire C×B ≤ C×B₁."""
    vb, vb1, vc = _t(b), _t(b1), _t(c)
    hBB1 = N.assume(inf_egal_card(vb, vb1))              # B ≤ B₁
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))   # (∀X) X ≤ X
    refl_c = instancie(refl_all, vc)                     # C ≤ C
    inv = inf_egal_produit_invariant("F", "G", vc, vb, vc, vb1)   # (C≤C et B≤B₁)⇒(C×B ≤ C×B₁)
    le = N.modus_ponens(conjonction_intro(refl_c, hBB1), inv)    # C×B ≤ C×B₁  [sous B≤B₁]
    return N.loi_deduction(inf_egal_card(vb, vb1), le)


__all__ = ["produit_graphe_image_inclus", "inf_egal_produit_invariant",
           "cardinal_inf_egal_produit_invariant",
           "inf_egal_produit_gauche", "inf_egal_produit_droite"]
