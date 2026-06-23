"""§III.3.2 / III.3.3 — MONOTONIE de l'ordre ≤ des cardinaux pour la somme, et le
cas particulier « le successeur cardinal est croissant ».

ÉNONCÉS (E.III.3.2-3.3, dérivés ; rien postulé) :

  (1) `inf_egal_somme_invariant`  ⊢ (A ≤ B₁ et B ≤ N₁) ⇒ (A ⊔ B ≤ B₁ ⊔ N₁).
      MONOTONIE de la somme disjointe pour ≤ — l'analogue INJECTION de l'invariance
      par équipotence eq_somme_invariant (qui prouve Eq(A,A₁)∧Eq(B,B₁)⇒Eq(A⊔B,A₁⊔B₁)).
      D'une injection F:A→B₁ et d'une injection G:B→N₁ on construit l'injection
      « somme »  K = F ⊔ G : A⊔B → B₁⊔N₁,  (u,0)↦(F(u),0), (v,1)↦(G(v),1).  C'est le
      MÊME graphe somme  K := graphe_terme(A⊔B, (W(k), pr₂k))  que la bijection somme
      de ensembles_somme_equipotence (W = sélecteur F-ou-G selon la copie) ; on
      REUTILISE tels quels ses paliers fonctionnel / domaine / injectif, et on
      remplace seulement le palier IMAGE : pour une injection l'image n'est plus
      ÉGALE à B₁⊔N₁ mais seulement INCLUSE dedans (palier `somme_graphe_image_inclus`,
      version « forward-only » de somme_graphe_image, où l'étape F(u)∈F⟨A⟩=A₁ par
      Leibniz devient F(u)∈F⟨A⟩ ⊂ B₁ par instanciation de l'inclusion).

  (2) `inf_egal_monotone_successeur`  ⊢ (A ≤ B) ⇒ (A ⊔ {∅} ≤ B ⊔ {∅}).
      « Le successeur cardinal est CROISSANT » (E.III.3.2 ; le successeur fidèle est
      𝔞+1 = Card(𝔞⊔{∅})).  Cas particulier de (1) avec B := {∅}, N₁ := {∅} et
      {∅} ≤ {∅} (réflexivité de ≤, inf_egal_reflexif instanciée au terme {∅}) : de
      A ≤ B on tire A⊔{∅} ≤ B⊔{∅}.  C'est l'injection « somme de l'injection A→B et de
      l'IDENTITÉ sur {∅} » — le marqueur va sur le marqueur, exactement comme demandé.

  (3) `cardinal_inf_egal_monotone_successeur`  ⊢ (Card A ≤ Card B) ⇒ (a+1 ≤ b+1),
      où a+1 = Card(Card A ⊔ {∅}), b+1 = Card(Card B ⊔ {∅}) : (2) généralisé puis
      INSTANCIÉ aux termes Card A, Card B.

──────────────────────────────────────────────────────────────────────────────
INDÉPENDANT de Cantor–Bernstein (réservé à l'antisymétrie de ≤).  Réflexivité et
transitivité de ≤ sont certifiées ailleurs (ensembles_cardinaux_theoremes,
ensembles_cardinaux_ordre) — on ne les duplique pas.

THÉORÈMES CERTIFIÉS (chacun testé, cf. test_somme_monotone.py) :
  • somme_graphe_image_inclus(F,G,A,B,B₁,N₁)  {F func,dom F=A,F⟨A⟩⊂B₁,G func,dom G=B,
        G⟨B⟩⊂N₁} ⊢ image(K, A⊔B) ⊂ B₁⊔N₁   (palier IMAGE de l'injection somme) ;
  • inf_egal_somme_invariant(...)              (clos) — (A≤B₁ et B≤N₁)⇒(A⊔B ≤ B₁⊔N₁) ;
  • inf_egal_monotone_successeur(A,B)          (clos) — (A≤B)⇒(A⊔{∅} ≤ B⊔{∅}) ;
  • cardinal_inf_egal_monotone_successeur(A,B) (clos) — (Card A≤Card B)⇒(a+1 ≤ b+1).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, appartient, existe, inclus, subst_t)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie, cas)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (existe_elimination, alpha_existe)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import membre_graphe_terme
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                               injection_gauche_dans_somme, injection_droite_dans_somme,
                               membre_somme_caracterise, _ou_congruence)
from bourbaki.cardinaux.arithmetique import ensembles_somme_equipotence as S
from bourbaki.cardinaux.arithmetique.ensembles_produit_equipotence import (_valeur_dans_image,
                               _valeur_cy)
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
# PALIER IMAGE (version INJECTION) : image(K, A⊔B) ⊂ B₁⊔N₁
# ═══════════════════════════════════════════════════════════════════════════════
def somme_graphe_image_inclus(f="F", g="G", a="A", b="B", b1="B1", n1="N1"):
    """{F func, dom F=A, F⟨A⟩⊂B₁, G func, dom G=B, G⟨B⟩⊂N₁} ⊢ image(K, A⊔B) ⊂ B₁⊔N₁.

    Version « forward-only » (INCLUSION) du palier somme_graphe_image (qui prouve
    l'ÉGALITÉ image=B₁⊔N₁ sous des bijections).  On ne garde que le sens ⇒ :
        z∈K⟨A⊔B⟩ ⇔ (∃t)(t∈A⊔B et (t,z)∈K) ⇔ (∃t)(t∈A⊔B et z=T[t]).
    Cas sur t (membre_somme_caracterise) :
      • t=(p,0), p∈A : z=T[(p,0)]=(F(p),0) ; F(p)∈F⟨A⟩ (τ-valeur dans l'image) et
        F⟨A⟩⊂B₁ donnent F(p)∈B₁, d'où (F(p),0)∈B₁⊔N₁ (injection gauche), z∈B₁⊔N₁ ;
      • t=(q,1), q∈B : symétrique (G⟨B⟩⊂N₁, injection droite).
    La SEULE différence avec somme_graphe_image (sens ⇒) est l'étape « ∈image » :
    Leibniz F⟨A⟩=A₁ y est remplacé par l'instanciation de l'inclusion F⟨A⟩⊂B₁.
    Liants : témoins t, m1, m2 du sens ⇒ ; aucun ∃-fuite (existe_elimination)."""
    vF, vG = _t(f), _t(g)
    va, vb, vb1, vn1 = _t(a), _t(b), _t(b1), _t(n1)
    AB = somme_disjointe(va, vb)
    B1N1 = somme_disjointe(vb1, vn1)
    T = S._somme_terme(f, g, "k")
    K = E.graphe_terme(AB, T, "k")
    vz, vt = var("z"), var("t")
    # caractérisation de l'image (liant interne « x » de AXIOME_IMAGE renommé « t »)
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, K), AB), vz)
    inner_x = et(appartient(var("x"), AB), appartient(E.couple(var("x"), vz), K))
    ren = alpha_existe("x", "t", inner_x)
    img_car = equivalence_transitivite(img_car0, ren)
    hFdom = N.assume(egal(E.dom(vF), va))
    hGdom = N.assume(egal(E.dom(vG), vb))
    hFsub = N.assume(inclus(E.image(vF, va), vb1))
    hGsub = N.assume(inclus(E.image(vG, vb), vn1))
    bodyR = et(appartient(vt, AB), appartient(E.couple(vt, vz), K))
    hbR = N.assume(bodyR)
    t_in = conjonction_elim_gauche(hbR)
    cpl_in = conjonction_elim_droite(hbR)
    mem = membre_graphe_terme(AB, T, "t", "m", "k", "yb")     # coord m ≠ y
    mem_z = instancie(N.generalisation("m", mem), vz)
    z_eq_Tt = conjonction_elim_droite(N.modus_ponens(cpl_in, equivalence_avant(mem_z)))  # z=T[t]
    # décomposer t∈A⊔B en (∃m1)(m1∈A et t=(m1,0)) ou (∃m2)(m2∈B et t=(m2,1))
    dec_t0 = N.modus_ponens(t_in, equivalence_avant(membre_somme_caracterise(a, b, vt)))
    exA0, exB0 = dec_t0.conclusion.sous[0], dec_t0.conclusion.sous[1]
    renA = alpha_existe(exA0.lieur, "m1", exA0.sous[0])
    renB = alpha_existe(exB0.lieur, "m2", exB0.sous[0])
    dec_t = N.modus_ponens(dec_t0, equivalence_avant(_ou_congruence(renA, renB)))
    exA, exB = dec_t.conclusion.sous[0], dec_t.conclusion.sous[1]
    nA, bA = exA.lieur, exA.sous[0]
    nB, bB = exB.lieur, exB.sous[0]
    vp, vq = var(nA), var(nB)

    def _fwd_copy(fn, witness, marker, body_w, val_lemma):
        """De (t=(w,m)) déduire z=(fn(w)[τc], m).  (réutilise sélecteur + projection.)"""
        hw = N.assume(body_w)
        w_in = conjonction_elim_gauche(hw)                   # w∈in_set
        t_eq = conjonction_elim_droite(hw)                   # t=(w,m)
        # T[t]=T[(w,m)]  (Leibniz t=(w,m))
        Tt_Twm = N.modus_ponens(t_eq, N.s6(vt, E.couple(witness, marker), "w",
                                           egal(subst_t(vt, "k", T), subst_t(var("w"), "k", T))))
        Tt_Twm = N.modus_ponens(N.reflexivite(subst_t(vt, "k", T)), equivalence_avant(Tt_Twm))
        z_eq_Twm = composer_egalites(z_eq_Tt, Tt_Twm)        # z=T[(w,m)]
        # T[(w,m)] = (fn(w)[τc], m)  (sélecteur W[(w,m)]=fn(w)[τc], puis pr₂(w,m)=m)
        sel = S._selecteur_valeur(f, g, witness, gauche=(marker is ZERO))
        Wwm = subst_t(E.couple(witness, marker), "k", S._sel_terme(f, g, "k"))
        pr2wm = E.pr2(E.couple(witness, marker), "a", "b")
        fnc = E.valeur(fn, witness, "c")
        pr2_eq = S._projection_seconde_ab(witness, marker, "a", "b")
        c1 = N.modus_ponens(sel, congruence_terme(Wwm, fnc, E.couple(var("w"), pr2wm)))
        c2 = N.modus_ponens(pr2_eq, congruence_terme(pr2wm, marker, E.couple(fnc, var("w"))))
        Twm_eq = composer_egalites(c1, c2)
        z_eq_fnwm = composer_egalites(z_eq_Twm, Twm_eq)      # z=(fn(w)[τc], m)
        return hw, w_in, z_eq_fnwm, fnc

    def _fwd_left():
        val_lemma = S.somme_graphe_valeur_gauche(f, g, a, b, vp)
        hw, w_in, z_eq_fnwm, Fpc = _fwd_copy(vF, vp, ZERO, bA, val_lemma)
        # F(m1)∈F⟨A⟩ : m1∈dom F (dom F=A), (∃y)((m1,y)∈F), puis _valeur_dans_image
        m1_domF = N.modus_ponens(w_in, equivalence_arriere(N.modus_ponens(
            hFdom, N.s6(E.dom(vF), va, "w", appartient(vp, var("w"))))))
        domF_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vF), vp)
        m1_ex = N.modus_ponens(m1_domF, equivalence_avant(domF_car))
        Fm1_img = _valeur_dans_image(vF, vp, va)
        Fm1_img = N.modus_ponens(w_in, N.loi_deduction(appartient(vp, va),
            N.modus_ponens(m1_ex, N.loi_deduction(
                existe("y", appartient(E.couple(vp, var("y")), vF)), Fm1_img))))   # F(m1)[τy]∈F⟨A⟩
        Fy1, Fc1 = E.valeur(vF, vp), E.valeur(vF, vp, "c")
        Fy_Fc = N.modus_ponens(_valeur_cy(vF, vp), symetrie(Fc1, Fy1))             # Fy=Fc
        Fc1_img = N.modus_ponens(Fm1_img, equivalence_avant(N.modus_ponens(
            Fy_Fc, N.s6(Fy1, Fc1, "w", appartient(var("w"), E.image(vF, va))))))   # F(m1)[τc]∈F⟨A⟩
        # ── le SWAP clé : F⟨A⟩⊂B₁ donne F(m1)[τc]∈B₁ (vs Leibniz F⟨A⟩=A₁) ──
        Fc1_inB1 = N.modus_ponens(Fc1_img, instancie(hFsub, Fc1))                 # F(m1)[τc]∈B₁
        cpl_in_sum = N.modus_ponens(Fc1_inB1, injection_gauche_dans_somme(Fpc, vb1, vn1))
        z_in = N.modus_ponens(cpl_in_sum, equivalence_arriere(N.modus_ponens(
            z_eq_fnwm, N.s6(vz, E.couple(Fpc, ZERO), "w", appartient(var("w"), B1N1)))))
        return N.loi_deduction(bA, z_in)

    def _fwd_right():
        val_lemma = S.somme_graphe_valeur_droite(f, g, a, b, vq)
        hw, w_in, z_eq_fnwm, Gqc = _fwd_copy(vG, vq, UN, bB, val_lemma)
        m2_domG = N.modus_ponens(w_in, equivalence_arriere(N.modus_ponens(
            hGdom, N.s6(E.dom(vG), vb, "w", appartient(vq, var("w"))))))
        domG_car = instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vG), vq)
        m2_ex = N.modus_ponens(m2_domG, equivalence_avant(domG_car))
        Gm2_img = _valeur_dans_image(vG, vq, vb)
        Gm2_img = N.modus_ponens(w_in, N.loi_deduction(appartient(vq, vb),
            N.modus_ponens(m2_ex, N.loi_deduction(
                existe("y", appartient(E.couple(vq, var("y")), vG)), Gm2_img))))
        Gy1, Gc1 = E.valeur(vG, vq), E.valeur(vG, vq, "c")
        Gy_Gc = N.modus_ponens(_valeur_cy(vG, vq), symetrie(Gc1, Gy1))
        Gc1_img = N.modus_ponens(Gm2_img, equivalence_avant(N.modus_ponens(
            Gy_Gc, N.s6(Gy1, Gc1, "w", appartient(var("w"), E.image(vG, vb))))))
        Gc1_inN1 = N.modus_ponens(Gc1_img, instancie(hGsub, Gc1))                 # G(m2)[τc]∈N₁
        cpl_in_sum = N.modus_ponens(Gc1_inN1, injection_droite_dans_somme(Gqc, vb1, vn1))
        z_in = N.modus_ponens(cpl_in_sum, equivalence_arriere(N.modus_ponens(
            z_eq_fnwm, N.s6(vz, E.couple(Gqc, UN), "w", appartient(var("w"), B1N1)))))
        return N.loi_deduction(bB, z_in)

    impL = existe_elimination(_fwd_left(), nA)
    impR = existe_elimination(_fwd_right(), nB)
    z_in_sum = cas(dec_t, impL, impR)                        # z∈B₁⊔N₁  [sous bodyR, hyps]
    fwd = existe_elimination(N.loi_deduction(bodyR, z_in_sum), "t")
    fwd_full = syllogisme(equivalence_avant(img_car), fwd)   # z∈K⟨A⊔B⟩ ⇒ z∈B₁⊔N₁
    return N.generalisation("z", fwd_full)                  # image(K,A⊔B) ⊂ B₁⊔N₁


# ═══════════════════════════════════════════════════════════════════════════════
# (1) MONOTONIE de la somme pour ≤   (l'injection somme F⊔G)
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_somme_invariant(f="F", g="G", a="A", b="B", b1="B1", n1="N1"):
    """⊢ (A ≤ B₁ et B ≤ N₁) ⇒ (A ⊔ B ≤ B₁ ⊔ N₁).   (monotonie de la somme ; clos.)

    Témoin = le graphe somme K = F⊔G.  est_injection_de(K, A⊔B, B₁⊔N₁) tient par ses
    quatre conjoints (fonctionnel/domaine [closes] ; injectif [somme_graphe_injective
    aligné en liants u,up par _renomme_injective] ; image⊂B₁⊔N₁ [palier ci-dessus]),
    dont on coupe les hypothèses par les conjoints de est_injection_de(F,A,B₁) et
    est_injection_de(G,B,N₁) ; S5 témoin K + double élimination des existentiels (avec
    alpha_existe G→F pour le liant de inf_egal_card) donne la conclusion."""
    vF, vG = _t(f), _t(g)
    va, vb, vb1, vn1 = _t(a), _t(b), _t(b1), _t(n1)
    AB = somme_disjointe(va, vb)
    B1N1 = somme_disjointe(vb1, vn1)
    K = S._somme_graphe(f, g, a, b, "k")
    hF = N.assume(est_injection_de(vF, va, vb1))
    hG = N.assume(est_injection_de(vG, vb, vn1))
    Ffunc = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hF)))
    Fdom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hF)))
    Finj = conjonction_elim_droite(conjonction_elim_gauche(hF))
    Fsub = conjonction_elim_droite(hF)
    Gfunc = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hG)))
    Gdom = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(hG)))
    Ginj = conjonction_elim_droite(conjonction_elim_gauche(hG))
    Gsub = conjonction_elim_droite(hG)
    c1 = _cut(S.somme_graphe_fonctionnel(f, g, a, b),
              [(E.est_fonctionnel(vF), Ffunc), (E.est_fonctionnel(vG), Gfunc)])
    c2 = S.somme_graphe_domaine(f, g, a, b)                 # dom K = A⊔B  (clos)
    c3 = _cut(S._renomme_injective(S.somme_graphe_injective(f, g, a, b)),
              [(E.injective_dans(vF, va), Finj), (E.injective_dans(vG, vb), Ginj)])
    c4 = _cut(somme_graphe_image_inclus(f, g, a, b, b1, n1),
              [(egal(E.dom(vF), va), Fdom), (egal(E.dom(vG), vb), Gdom),
               (inclus(E.image(vF, va), vb1), Fsub), (inclus(E.image(vG, vb), vn1), Gsub)])
    inj_K = conjonction_intro(conjonction_intro(conjonction_intro(c1, c2), c3), c4)
    le = N.modus_ponens(inj_K, N.s5(est_injection_de(var("F"), AB, B1N1), K, "F"))  # A⊔B ≤ B₁⊔N₁
    stepG = N.loi_deduction(est_injection_de(vG, vb, vn1), le)
    elimG = existe_elimination(stepG, "G")
    alphaG = alpha_existe("G", "F", est_injection_de(var("G"), vb, vn1))
    elimG = syllogisme(equivalence_arriere(alphaG), elimG)  # (B≤N₁) ⇒ (A⊔B ≤ B₁⊔N₁)
    stepF = N.loi_deduction(est_injection_de(vF, va, vb1), elimG)
    elimF = existe_elimination(stepF, "F")                 # (A≤B₁) ⇒ ((B≤N₁) ⇒ …)
    hab = N.assume(et(inf_egal_card(va, vb1), inf_egal_card(vb, vn1)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimF))
    return N.loi_deduction(et(inf_egal_card(va, vb1), inf_egal_card(vb, vn1)), c)


# ═══════════════════════════════════════════════════════════════════════════════
# (2) Le successeur cardinal est CROISSANT :  A ≤ B  ⇒  A⊔{∅} ≤ B⊔{∅}
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_monotone_successeur(a="A", b="B"):
    """⊢ (A ≤ B) ⇒ (A ⊔ {∅} ≤ B ⊔ {∅}).   (le successeur est croissant ; clos.)

    Cas particulier de inf_egal_somme_invariant avec B:={∅}, N₁:={∅} et {∅}≤{∅}
    (réflexivité de ≤, inf_egal_reflexif instanciée au terme {∅}) : l'injection
    « somme » envoie A→B par l'injection donnée et l'IDENTITÉ {∅}→{∅} (le marqueur
    sur le marqueur).  De A≤B on tire A⊔{∅} ≤ B⊔{∅}."""
    SING = E.singleton(E.VIDE)                             # {∅} (= 1)
    va, vb = _t(a), _t(b)
    hAB = N.assume(inf_egal_card(va, vb))                  # A ≤ B
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))   # (∀X) X ≤ X
    refl_sing = instancie(refl_all, SING)                  # {∅} ≤ {∅}
    inv = inf_egal_somme_invariant("F", "G", va, SING, vb, SING)   # (A≤B et {∅}≤{∅})⇒(A⊔{∅} ≤ B⊔{∅})
    le = N.modus_ponens(conjonction_intro(hAB, refl_sing), inv)    # A⊔{∅} ≤ B⊔{∅}  [sous A≤B]
    return N.loi_deduction(inf_egal_card(va, vb), le)


def cardinal_inf_egal_monotone_successeur(a="A", b="B"):
    """⊢ (Card A ≤ Card B) ⇒ (Card A ⊔ {∅} ≤ Card B ⊔ {∅}).   (= « a≤b ⇒ a+1≤b+1 ».)

    inf_egal_monotone_successeur généralisé en (∀A)(∀B) puis INSTANCIÉ aux TERMES
    Card A, Card B : a+1 = Card(Card A ⊔ {∅}) et b+1 = Card(Card B ⊔ {∅}) sont les
    successeurs cardinaux, et la conclusion est leur comparaison ≤."""
    va, vb = _t(a), _t(b)
    gen = N.generalisation("A", N.generalisation("B", inf_egal_monotone_successeur("A", "B")))
    return instancie(instancie(gen, cardinal(va)), cardinal(vb))


__all__ = ["somme_graphe_image_inclus", "inf_egal_somme_invariant",
           "inf_egal_monotone_successeur", "cardinal_inf_egal_monotone_successeur"]
