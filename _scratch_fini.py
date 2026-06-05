"""Scratch: develop the pigeonhole keystone for Fini(1)/Fini(2)."""
from __future__ import annotations

from formule import var, egal, et, non, appartient, existe
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, instancie)
from tactiques_abrege_egalite import symetrie, composer_egalites
from ensembles_correspondances import coupe_membre
from ensembles_fonctions import valeur_caracterisation


def _t(v):
    return v if isinstance(v, str) and var(v) or not isinstance(v, str) and v else v

def T(v):
    from formule import Terme
    return v if isinstance(v, Terme) else var(v)


# Keystone: {F func, (∃y)((a,y)∈F)} ⊢ (y ∈ F⟨{a}⟩) ⇒ (y = F(a))
def membre_image_singleton(f, a, yname="y"):
    """{F func, (∃y0)((a,y0)∈F)} ⊢ (y ∈ F⟨{a}⟩) ⇒ (y = F(a))  — generalized over y."""
    vF, va = T(f), T(a)
    vy = var(yname)
    fa = E.valeur(vF, va)                                # F(a)
    # y∈F⟨{a}⟩ ⇔ (a,y)∈F
    coupe = coupe_membre_t(vF, va)                       # (y∈F⟨{a}⟩) ⇔ ((a,y)∈F)   liant y
    # valeur_caracterisation(F,a): {F func, (∃y)((a,y)∈F)} ⊢ ((a,y)∈F) ⇔ (y=F(a))
    vc = valeur_caracterisation(vF, va)                  # y libre
    # hypothesis y∈F⟨{a}⟩
    h = N.assume(appartient(vy, E.image(vF, E.singleton(va))))
    ay = N.modus_ponens(h, equivalence_avant(coupe))     # (a,y)∈F
    y_eq_fa = N.modus_ponens(ay, equivalence_avant(vc))  # y=F(a)  [hyps F func, a∈dom]
    return N.loi_deduction(appartient(vy, E.image(vF, E.singleton(va))), y_eq_fa)


def coupe_membre_t(f, a):
    """⊢ (y ∈ F⟨{a}⟩) ⇔ ((a,y) ∈ F) for terms f,a (coupe_membre accepts names only).
    coupe_membre uses g='G', a='a' as names and liant y; we re-derive via instance."""
    # coupe_membre returns with var('y') free; we need terms F, a substituted.
    # Easiest: re-prove via the same axiom path but accept terms.
    from tactiques_abrege2 import equivalence_transitivite
    from tactiques_abrege_quantif import existe_elimination
    from ensembles_couples import singleton_membre
    from ensembles_theoremes import appartient_singleton
    vG, va, vx, vy = T(f), T(a), var("x"), var("y")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    inst = instancie(instancie(instancie(ax, vG), E.singleton(va)), vy)
    body = et(appartient(vx, E.singleton(va)), appartient(E.couple(vx, vy), vG))
    hb = N.assume(body)
    xeqa = N.modus_ponens(conjonction_elim_gauche(hb), equivalence_avant(singleton_membre(vx, va)))
    ay_in = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(N.modus_ponens(
        xeqa, N.s6(vx, va, "w", appartient(E.couple(var("w"), vy), vG)))))
    avant = existe_elimination(N.loi_deduction(body, ay_in), "x")
    # backward: need a∈{a}
    from ensembles_couples import membre_paire_gauche
    a_in = membre_paire_gauche(va, va)                   # a∈{a,a}={a}
    h = N.assume(appartient(E.couple(va, vy), vG))
    wit = conjonction_intro(a_in, h)
    arriere = N.loi_deduction(appartient(E.couple(va, vy), vG),
                              N.modus_ponens(wit, N.s5(body, va, "x")))
    eq_ex = conjonction_intro(avant, arriere)
    return equivalence_transitivite(inst, eq_ex)


def _a_dans_dom(f, a):
    """{dom F = {a}} ⊢ (∃y)((a,y)∈F).   (a∈{a}, dom F={a} → a∈dom F → ∃y.)"""
    from ensembles_couples import membre_paire_gauche
    vF, va, vy = T(f), T(a), var("y")
    sa = E.singleton(va)
    a_in_sa = membre_paire_gauche(va, va)                 # a∈{a}
    hdom = N.assume(egal(E.dom(vF), sa))                  # dom F = {a}
    sa_eq_dom = N.modus_ponens(hdom, symetrie(E.dom(vF), sa))   # {a} = dom F
    leib = N.s6(sa, E.dom(vF), "w", appartient(va, var("w")))   # ({a}=domF)⇒(a∈{a}⇔a∈domF)
    a_in_dom = N.modus_ponens(a_in_sa, equivalence_avant(N.modus_ponens(sa_eq_dom, leib)))  # a∈dom F
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, vF), va)        # a∈dom F ⇔ (∃y)((a,y)∈F)
    ex = N.modus_ponens(a_in_dom, equivalence_avant(dom_car))  # (∃y)((a,y)∈F)  [hyp dom F={a}]
    return ex


def un_non_vide():
    """⊢ ¬(1 = ∅)   where 1 = UN.   (le cardinal 1 est non vide : il est équipotent à {∅}.)

    Si UN=∅, alors Eq(UN,{∅}) (eq_un_singleton) devient Eq(∅,{∅}) (Leibniz),
    contredisant vide_non_equipotent_singleton."""
    from ensembles_cardinaux import equipotent
    from ensembles_vide_singleton import vide_non_equipotent_singleton
    import ensembles_entiers as Ent
    sing = E.singleton(E.VIDE)
    UN = Ent.UN
    eqU = eq_un_singleton()                             # Eq(UN, {∅})
    notEq0 = vide_non_equipotent_singleton()           # ¬Eq(∅, {∅})
    h = N.assume(egal(UN, E.VIDE))                      # UN = ∅
    leib = N.s6(UN, E.VIDE, "w", equipotent(var("w"), sing))   # (UN=∅)⇒(Eq(UN,{∅})⇔Eq(∅,{∅}))
    eq0 = N.modus_ponens(eqU, equivalence_avant(N.modus_ponens(h, leib)))   # Eq(∅,{∅})  [hyp]
    contra = _ex_falso(eq0, notEq0, non(egal(UN, E.VIDE)))   # ¬(UN=∅)  [hyp]
    return N.modus_ponens(N.loi_deduction(egal(UN, E.VIDE), contra), N.s1(non(egal(UN, E.VIDE))))


def singleton_non_equipotent_un_plus_un():
    """⊢ ¬ Eq({∅}, UN ⊔ {∅}).   (pigeonhole : {∅} (1 élt) vs UN⊔{∅} (≥2 élts) ; 1 ≠ 1+1.)

    UN est non vide (un_non_vide) → témoin c∈UN.  Alors (c,0)∈UN⊔{∅} et (∅,1)∈UN⊔{∅}
    sont distincts (2ᵉ composantes 0=∅ ≠ 1={∅}).  Pigeonhole général conclut ¬Eq."""
    from ensembles_somme_disjointe import (somme_disjointe, ZERO, UN as MARQ1,
                                           injection_gauche_dans_somme,
                                           injection_droite_dans_somme)
    from ensembles_zero_plus_un import membre_singleton_vide
    from ensembles_couples import couple_egal_implique_composantes
    from ensembles_vide_singleton import vide_distinct_singleton
    from ensembles_vide import non_vide_ssi_element
    from tactiques_abrege_quantif import existe_elimination
    import ensembles_entiers as Ent
    vide = E.VIDE
    sing = E.singleton(vide)                            # {∅}
    UN = Ent.UN
    Tset = somme_disjointe(UN, sing)                    # UN ⊔ {∅}
    vc = var("c")                                       # témoin c∈UN
    c0 = E.couple(vc, ZERO)                             # (c,0)
    e1 = E.couple(vide, MARQ1)                          # (∅,1)
    # under c∈UN :
    hc = N.assume(appartient(vc, UN))                  # c∈UN
    c0_in = N.modus_ponens(hc, injection_gauche_dans_somme(vc, UN, sing))   # (c,0)∈UN⊔{∅}  [c∈UN]
    vis = membre_singleton_vide()                      # ∅∈{∅}
    e1_in = N.modus_ponens(vis, injection_droite_dans_somme(vide, UN, sing))  # (∅,1)∈UN⊔{∅}
    # (c,0) ≠ (∅,1) : 2nd components 0=∅, 1={∅} differ
    impl_comp = couple_egal_implique_composantes(vc, ZERO, vide, MARQ1)  # ((c,0)=(∅,1))⇒(c=∅ et 0=1)
    vds = vide_distinct_singleton()                    # ¬(∅={∅}) = ¬(0=1)
    hh = N.assume(egal(c0, e1))
    comp = N.modus_ponens(hh, impl_comp)
    zero_eq_un = conjonction_elim_droite(comp)         # 0=1
    contra_c = _ex_falso(zero_eq_un, vds, non(egal(c0, e1)))
    ne_c = N.modus_ponens(N.loi_deduction(egal(c0, e1), contra_c), N.s1(non(egal(c0, e1))))  # ¬((c,0)=(∅,1))
    # pigeonhole under c∈UN
    notEq_under_c = singleton_non_equipotent_si_deux(vide, c0_in, e1_in, ne_c)  # ¬Eq({∅},UN⊔{∅})  [c∈UN]
    # eliminate witness c : c∈UN ⇒ ¬Eq , then (∃c)(c∈UN) ⇒ ¬Eq ; UN non vide gives (∃c)(c∈UN)
    imp_c = N.loi_deduction(appartient(vc, UN), notEq_under_c)   # (c∈UN) ⇒ ¬Eq
    ex_imp = existe_elimination(imp_c, "c")            # (∃c)(c∈UN) ⇒ ¬Eq
    nv = un_non_vide()                                 # ¬(UN=∅)
    ex_z = N.modus_ponens(nv, equivalence_avant(non_vide_ssi_element(UN)))   # (∃z)(z∈UN)
    # non_vide_ssi_element uses liant 'z' → renommer en 'c' (alpha) pour matcher ex_imp
    from tactiques_abrege_quantif import alpha_existe
    ren = alpha_existe("z", "c", appartient(var("z"), UN))   # (∃z)(z∈UN) ⇔ (∃c)(c∈UN)
    ex_c = N.modus_ponens(ex_z, equivalence_avant(ren))      # (∃c)(c∈UN)
    return N.modus_ponens(ex_c, ex_imp)               # ¬Eq({∅}, UN⊔{∅})


def card_un_distinct_card_deux():
    """⊢ ¬(Card({∅}) = Card({∅}⊔{∅})).   (« 1 ≠ 2 » au niveau cardinal.)

    Contraposée de Prop1 (Card X=Card Y ⇒ Eq(X,Y)) sur ¬Eq({∅},{∅}⊔{∅})."""
    from ensembles_cardinaux import cardinal, equipotent
    from ensembles_cardinaux_theoremes import equipotent_si_cardinal_egal
    from ensembles_somme_disjointe import somme_disjointe
    sing = E.singleton(E.VIDE)
    deux = somme_disjointe(sing, sing)
    c1, c2 = cardinal(sing), cardinal(deux)
    # (Card({∅})=Card({∅}⊔{∅})) ⇒ Eq({∅},{∅}⊔{∅})
    gen = N.generalisation("X", N.generalisation("Y", equipotent_si_cardinal_egal("X", "Y")))
    impl_eq = instancie(instancie(gen, sing), deux)
    notEq = singleton_non_equipotent_deux()            # ¬Eq({∅},{∅}⊔{∅})
    h = N.assume(egal(c1, c2))
    eq = N.modus_ponens(h, impl_eq)                    # Eq({∅},{∅}⊔{∅})  [hyp]
    contra = _ex_falso(eq, notEq, non(egal(c1, c2)))   # ¬(Card({∅})=Card({∅}⊔{∅}))  [hyp]
    return N.modus_ponens(N.loi_deduction(egal(c1, c2), contra), N.s1(non(egal(c1, c2))))


def eq_un_singleton():
    """⊢ Eq(1, {∅})   where 1 = UN = successeur(0).   (the cardinal 1 is equipotent to {∅}.)"""
    from ensembles_cardinaux import cardinal, equipotent
    from ensembles_cardinaux_theoremes import equipotent_son_cardinal
    import ensembles_entiers as Ent
    from ensembles_fini_zero import successeur_zero_egale_un
    sing = E.singleton(E.VIDE)
    UN = Ent.UN                                        # successeur(ZERO) = τ-cardinal
    cSing = cardinal(sing)                             # Card({∅})
    # Eq({∅}, Card({∅}))
    refl_all = N.generalisation("X", equipotent_son_cardinal("X"))
    eq_sing_cSing = instancie(refl_all, sing)          # Eq({∅}, Card({∅}))
    # symmetry → Eq(Card({∅}), {∅})
    from ensembles_bijection import equipotence_symetrique
    sym_all = equipotence_symetrique("F", "X", "Y")    # Eq(X,Y)⇒Eq(Y,X)?
    # Actually use equipotence_symetrique signature; fallback: use proposition over terms
    # Simpler: Eq is symmetric via eq relation; use the term-level symmetry helper.
    from ensembles_cardinaux_theoremes import proposition_1_cardinaux  # placeholder
    # We'll instead get Eq(Card({∅}),{∅}) by symmetrie of Eq via dedicated lemma:
    eq_cSing_sing = _eq_sym(eq_sing_cSing, sing, cSing)   # Eq(Card({∅}), {∅})
    # rewrite Card({∅}) → UN  using UN = Card({∅}) (successeur_zero_egale_un)
    un_eq_cSing = successeur_zero_egale_un()           # successeur(0)=Card({∅})  i.e. UN=Card({∅})
    leib = N.s6(cSing, UN, "w", equipotent(var("w"), sing))   # (Card{∅}=UN)⇒(Eq(Card{∅},{∅})⇔Eq(UN,{∅}))
    cSing_eq_un = N.modus_ponens(un_eq_cSing, symetrie(UN, cSing))   # Card({∅})=UN
    equ = N.modus_ponens(cSing_eq_un, leib)
    return N.modus_ponens(eq_cSing_sing, equivalence_avant(equ))     # Eq(UN, {∅})


def _eq_sym(thm_eq, X, Y):
    """⊢ Eq(X,Y) (as thm)  ⟹  ⊢ Eq(Y,X)  for terms X,Y, via equipotence_symetrique."""
    from ensembles_cardinaux import equipotent
    from ensembles_bijection import equipotence_symetrique
    # equipotence_symetrique(F,X,Y) ⊢ Eq(X,Y) ⇒ Eq(Y,X) ; generalize over X,Y and instancie
    # but its first arg F is the bijection name; it generalizes internally? Inspect needed.
    sym = equipotence_symetrique("F", "AX", "AY")
    gen = N.generalisation("AX", N.generalisation("AY", sym))
    inst = instancie(instancie(gen, X), Y)             # Eq(X,Y)⇒Eq(Y,X)
    return N.modus_ponens(thm_eq, inst)


def succ_un_egale_card_deux():
    """⊢ successeur(1) = Card({∅}⊔{∅}).   (« 1+1 = 2 » au niveau cardinal.)

    successeur(1) = Card(1 ⊔ {∅}).  Eq(1⊔{∅}, {∅}⊔{∅}) par invariance (eq_somme_invariant
    avec Eq(1,{∅}) et Eq({∅},{∅})) ⇒ Card(1⊔{∅})=Card({∅}⊔{∅}) (Prop1)."""
    from ensembles_cardinaux import cardinal, equipotent
    from ensembles_somme_disjointe import somme_disjointe
    from ensembles_somme_equipotence import eq_somme_invariant
    from ensembles_arith_cardinale import _prop1_direct_t
    from ensembles_equipotence import equipotence_reflexive
    import ensembles_entiers as Ent
    sing = E.singleton(E.VIDE)
    UN = Ent.UN
    succ1 = Ent.successeur(UN)                          # Card(UN ⊔ {∅})
    AB = somme_disjointe(UN, sing)                      # UN ⊔ {∅}
    deux = somme_disjointe(sing, sing)                  # {∅} ⊔ {∅}
    # eq_somme_invariant: (Eq(A,A1) et Eq(B,B1)) ⇒ Eq(A⊔B, A1⊔B1) ; A=UN,A1={∅},B={∅},B1={∅}
    inv = eq_somme_invariant("F", "G", UN, sing, sing, sing)
    eqA = eq_un_singleton()                             # Eq(UN, {∅})
    eqB = equipotence_reflexive(sing)                   # Eq({∅}, {∅})
    eq_AB = N.modus_ponens(conjonction_intro(eqA, eqB), inv)   # Eq(UN⊔{∅}, {∅}⊔{∅})
    prop1 = _prop1_direct_t(AB, deux)                  # Eq(UN⊔{∅},{∅}⊔{∅}) ⇒ Card(UN⊔{∅})=Card({∅}⊔{∅})
    return N.modus_ponens(eq_AB, prop1)                # Card(UN⊔{∅})=Card({∅}⊔{∅}) = successeur(1)=Card({∅}⊔{∅})


def un_distinct_succ_un():
    """⊢ ¬(1 = 1 + 1)   =  ¬(UN = successeur(UN)).   (« 1 ≠ 2 », 2ᵉ conjoint de Fini(1).)

    successeur(UN) = Card(UN ⊔ {∅}).  Si UN=successeur(UN), comme UN=Card({∅})
    (successeur_zero_egale_un), on aurait Card({∅})=Card(UN⊔{∅}), d'où par Prop1
    Eq({∅}, UN⊔{∅}), réfutée par le pigeonhole (singleton_non_equipotent_un_plus_un)."""
    from ensembles_cardinaux import cardinal, equipotent
    from ensembles_cardinaux_theoremes import equipotent_si_cardinal_egal
    from ensembles_somme_disjointe import somme_disjointe
    from ensembles_fini_zero import successeur_zero_egale_un
    import ensembles_entiers as Ent
    vide = E.VIDE
    sing = E.singleton(vide)
    UN = Ent.UN
    succU = Ent.successeur(UN)                          # Card(UN ⊔ {∅})
    AB = somme_disjointe(UN, sing)                      # UN ⊔ {∅}
    cAB = cardinal(AB)                                  # Card(UN⊔{∅}) = successeur(UN)
    cSing = cardinal(sing)                              # Card({∅})
    un_eq_cSing = successeur_zero_egale_un()            # UN = Card({∅})
    # ¬(Card({∅}) = Card(UN⊔{∅}))  par Prop1 contraposée sur pigeonhole
    notEq = singleton_non_equipotent_un_plus_un()       # ¬Eq({∅}, UN⊔{∅})
    gen = N.generalisation("X", N.generalisation("Y", equipotent_si_cardinal_egal("X", "Y")))
    impl_eq = instancie(instancie(gen, sing), AB)       # (Card{∅}=Card(UN⊔{∅}))⇒Eq({∅},UN⊔{∅})
    h = N.assume(egal(cSing, cAB))
    eq = N.modus_ponens(h, impl_eq)
    contra = _ex_falso(eq, notEq, non(egal(cSing, cAB)))
    ne_card = N.modus_ponens(N.loi_deduction(egal(cSing, cAB), contra), N.s1(non(egal(cSing, cAB))))
    # ne_card : ¬(Card({∅}) = Card(UN⊔{∅}))
    # rewrite Card({∅}) → UN   and   Card(UN⊔{∅}) → successeur(UN)
    # successeur(UN) IS Card(UN⊔{∅}) literally (def), so cAB == succU already? check by building target.
    # rewrite left:  Card({∅}) → UN  via un_eq_cSing : UN=Card({∅}), symmetrie → Card({∅})=UN
    cSing_eq_un = N.modus_ponens(un_eq_cSing, symetrie(UN, cSing))   # Card({∅}) = UN
    leibL = N.s6(cSing, UN, "w", non(egal(var("w"), cAB)))   # (Card{∅}=UN)⇒(¬(Card{∅}=cAB)⇔¬(UN=cAB))
    ne1 = N.modus_ponens(ne_card, equivalence_avant(N.modus_ponens(cSing_eq_un, leibL)))  # ¬(UN=Card(UN⊔{∅}))
    return ne1


def _ex_falso(thm_a, thm_na, z):
    a = thm_a.conclusion
    a_imp_z = N.modus_ponens(thm_na, N.s2(non(a), z))
    return N.modus_ponens(thm_a, a_imp_z)


def couples_01_distincts():
    """⊢ ¬((∅,0) = (∅,1)).   où 0=∅, 1={∅}.   (les deux marqueurs sont distincts.)"""
    from ensembles_somme_disjointe import ZERO, UN     # 0=∅, 1={∅}
    from ensembles_couples import couple_egal_implique_composantes
    from ensembles_vide_singleton import vide_distinct_singleton
    c0 = E.couple(E.VIDE, ZERO)                          # (∅,0)=(∅,∅)
    c1 = E.couple(E.VIDE, UN)                            # (∅,1)=(∅,{∅})
    # ((∅,0)=(∅,1)) ⇒ (∅=∅ et 0=1)
    impl_comp = couple_egal_implique_composantes(E.VIDE, ZERO, E.VIDE, UN)
    vds = vide_distinct_singleton()                     # ¬(∅={∅}) = ¬(0=1)
    h = N.assume(egal(c0, c1))
    comp = N.modus_ponens(h, impl_comp)                 # (∅=∅ et 0=1)
    zero_eq_un = conjonction_elim_droite(comp)          # 0=1 = (∅={∅})
    contra = _ex_falso(zero_eq_un, vds, non(egal(c0, c1)))   # ¬((∅,0)=(∅,1))  [hyp]
    return N.modus_ponens(N.loi_deduction(egal(c0, c1), contra), N.s1(non(egal(c0, c1))))


def singleton_non_equipotent_si_deux(a, p_in_T, q_in_T, p_ne_q):
    """GENERAL PIGEONHOLE.  Given a term a and proofs:
         ⊢ p ∈ T ,  ⊢ q ∈ T ,  ⊢ ¬(p = q)   (T = the same target set),
       conclude  ⊢ ¬ Eq({a}, T)   (under the same hyps as the three inputs).

    A bijection F:{a}→T forces image(F,{a})=T (surjectivity); but every element
    of F⟨{a}⟩ equals F(a) (image of a singleton is a singleton), so p=F(a)=q,
    contradicting p≠q.  ALL hyps of the inputs flow through."""
    from ensembles_cardinaux import est_bijection_de, equipotent
    from tactiques_abrege_quantif import existe_elimination
    va = T(a)
    sa = E.singleton(va)                               # {a}  (source, 1 element)
    # recover T (target) from the conclusions of p_in_T : p∈T
    p_form = p_in_T.conclusion                          # p∈T  (tag 'in')
    q_form = q_in_T.conclusion
    p = p_form.termes[0]; Tset = p_form.termes[1]
    q = q_form.termes[0]
    vF = var("F")
    bij = est_bijection_de(vF, sa, Tset)
    Eq = equipotent(sa, Tset)
    imgF = E.image(vF, sa)                              # F⟨{a}⟩
    hbij = N.assume(bij)
    func = conjonction_elim_gauche(conjonction_elim_gauche(hbij))   # F fonctionnel
    domeq = conjonction_elim_droite(conjonction_elim_gauche(hbij))  # dom F = {a}
    surj = conjonction_elim_droite(conjonction_elim_droite(hbij))   # image(F,{a}) = T
    # discharge (∃y)((a,y)∈F) from domeq
    ex_dom = N.modus_ponens(domeq, N.loi_deduction(egal(E.dom(vF), sa), _a_dans_dom(vF, va)))
    # keystone (y∈F⟨{a}⟩)⇒(y=F(a))
    key = membre_image_singleton(vF, va)
    key = N.modus_ponens(func, N.loi_deduction(E.est_fonctionnel(vF), key))
    key = N.modus_ponens(ex_dom, N.loi_deduction(
        existe("y", appartient(E.couple(va, var("y")), vF)), key))   # (y∈F⟨{a}⟩)⇒(y=F(a)) [bij]
    fa = E.valeur(vF, va)                              # F(a)
    # rewrite T → F⟨{a}⟩ via surj symmetry + Leibniz
    surj_sym = N.modus_ponens(surj, symetrie(imgF, Tset))   # T = F⟨{a}⟩
    def to_img(thm_in, c):
        leib = N.s6(Tset, imgF, "w", appartient(c, var("w")))
        return N.modus_ponens(thm_in, equivalence_avant(N.modus_ponens(surj_sym, leib)))
    p_in_img = to_img(p_in_T, p)                       # p∈F⟨{a}⟩  [bij + hyps]
    q_in_img = to_img(q_in_T, q)                       # q∈F⟨{a}⟩  [bij + hyps]
    key_all = N.generalisation("y", key)               # (∀y)((y∈F⟨{a}⟩)⇒(y=F(a)))
    p_eq_fa = N.modus_ponens(p_in_img, instancie(key_all, p))   # p=F(a)
    q_eq_fa = N.modus_ponens(q_in_img, instancie(key_all, q))   # q=F(a)
    fa_eq_q = N.modus_ponens(q_eq_fa, symetrie(q, fa))          # F(a)=q
    p_eq_q = composer_egalites(p_eq_fa, fa_eq_q)               # p=q  [bij + hyps]
    notEq_under = _ex_falso(p_eq_q, p_ne_q, non(Eq))          # ¬Eq  [bij + hyps]
    bij_imp = N.loi_deduction(bij, notEq_under)               # bij ⇒ ¬Eq  [hyps]
    Eq_imp = existe_elimination(bij_imp, "F")                 # Eq ⇒ ¬Eq  [hyps]
    return N.modus_ponens(Eq_imp, N.s1(non(Eq)))             # ¬Eq({a}, T)  [hyps]


def singleton_non_equipotent_deux():
    """⊢ ¬ Eq({∅}, {∅}⊔{∅}).   (pigeonhole concret : 1 ≠ 2 éléments.)"""
    from ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                           injection_gauche_dans_somme,
                                           injection_droite_dans_somme)
    from ensembles_zero_plus_un import membre_singleton_vide
    vide = E.VIDE
    sing = E.singleton(vide)
    c0 = E.couple(vide, ZERO)                           # (∅,0)
    c1 = E.couple(vide, UN)                             # (∅,1)
    vis = membre_singleton_vide()                      # ∅∈{∅}
    c0_in = N.modus_ponens(vis, injection_gauche_dans_somme(vide, sing, sing))  # (∅,0)∈{∅}⊔{∅}
    c1_in = N.modus_ponens(vis, injection_droite_dans_somme(vide, sing, sing))  # (∅,1)∈{∅}⊔{∅}
    notc = couples_01_distincts()                      # ¬((∅,0)=(∅,1))
    return singleton_non_equipotent_si_deux(vide, c0_in, c1_in, notc)


if __name__ == "__main__":
    th = coupe_membre_t(var("F"), E.VIDE)
    print("coupe_membre_t ok")
    th2 = membre_image_singleton(var("F"), E.VIDE)
    print("membre_image_singleton clos:", th2.est_clos, "nhyps:", len(th2.hypotheses))
    th3 = _a_dans_dom(var("F"), E.VIDE)
    print("_a_dans_dom conclusion:", th3.conclusion.tag, "clos:", th3.est_clos, "nhyps:", len(th3.hypotheses))
    th4 = couples_01_distincts()
    print("couples_01_distincts clos:", th4.est_clos, "tag:", th4.conclusion.tag)
    th5 = singleton_non_equipotent_deux()
    print("singleton_non_equipotent_deux clos:", th5.est_clos, "nhyps:", len(th5.hypotheses))
    th6 = card_un_distinct_card_deux()
    print("card_un_distinct_card_deux clos:", th6.est_clos, "tag:", th6.conclusion.tag)
    th7 = eq_un_singleton()
    print("eq_un_singleton clos:", th7.est_clos, "tag:", th7.conclusion.tag)
    th9 = un_non_vide()
    print("un_non_vide clos:", th9.est_clos, "tag:", th9.conclusion.tag)
    th10 = un_distinct_succ_un()
    print("un_distinct_succ_un clos:", th10.est_clos, "tag:", th10.conclusion.tag)
