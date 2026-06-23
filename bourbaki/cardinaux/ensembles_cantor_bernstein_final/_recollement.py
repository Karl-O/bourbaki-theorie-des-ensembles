"""§III.3.2 — CANTOR–BERNSTEIN, ÉTAPES 3-4 : recollement h = (f|D) ∪ (g⁻¹|(A∖D))
et conclusion (a≤b et b≤a) ⇒ Eq(a,b).

ÉTAPE 3 — recollement_h :
    ⊢ (est_injection_de(f,a,b) et est_injection_de(g,b,a))
          ⇒ est_bijection_de(h, a, b)   où h = (f|D) ∪ (g⁻¹|(A∖D)).
ÉTAPE 4 — cantor_bernstein (GRAND PRIX) :
    ⊢ (inf_egal_card(a,b) et inf_egal_card(b,a)) ⇒ equipotent(a,b).

Tout sort du noyau (PROUVE == certifie) ; AUCUN axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein as CB
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (est_injection_de,
                                                    est_bijection_de, equipotent,
                                                    inf_egal_card)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import morceau_fD
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_fin import (
    partie_disjoint_complement, partie_reunion_complement)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    dom_reunion_graphes, reunion_graphes_fonctionnelle)
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_recollement_bijection import (
    image_reunion_graphes, reunion_graphes_injective)
from ._etapes12 import morceau_gI


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, pairs):
    for formule, preuve in pairs:
        thm = N.modus_ponens(preuve, N.loi_deduction(formule, thm))
    return thm


def _inst_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B)   (instance de AXIOME_INTER)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _disjoint_to_forall(x, y, u="u"):
    """⊢ (X∩Y=∅) ⇒ (∀u)¬(u∈X et u∈Y).   (deux ensembles d'intersection vide n'ont
    aucun élément commun.)"""
    vX, vY, vu = _t(x), _t(y), var(u)
    hinter = N.assume(egal(E.intersection(vX, vY), E.VIDE))    # X∩Y=∅
    hcommun = N.assume(et(appartient(vu, vX), appartient(vu, vY)))
    u_inter = N.modus_ponens(hcommun, equivalence_arriere(_inst_inter(vX, vY, vu)))  # u∈X∩Y
    u_vide = N.modus_ponens(u_inter, equivalence_avant(N.modus_ponens(
        hinter, N.s6(E.intersection(vX, vY), E.VIDE, "w", appartient(vu, var("w"))))))  # u∈∅
    n_vide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vu)   # ¬(u∈∅)
    # u∈∅ et ¬(u∈∅) : ex falso → ¬(u∈X et u∈Y)
    n_commun = N.modus_ponens(u_vide, N.modus_ponens(n_vide,
        N.s2(non(appartient(vu, E.VIDE)), non(et(appartient(vu, vX), appartient(vu, vY))))))
    inner = N.loi_deduction(et(appartient(vu, vX), appartient(vu, vY)), n_commun)
    # inner : (u∈X et u∈Y) ⇒ ¬(u∈X et u∈Y) ; or (P⇒¬P)⇒¬P → ¬(u∈X et u∈Y)
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_fin import _absorption_neg
    n_and = N.modus_ponens(inner, _absorption_neg(et(appartient(vu, vX), appartient(vu, vY))))
    return N.loi_deduction(egal(E.intersection(vX, vY), E.VIDE), N.generalisation(u, n_and))


def _D_inclus_a_terme(a, b, f, g):
    """⊢ D ⊂ a   pour des TERMES a,b,f,g."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein import D_inclus_A
    th = D_inclus_A("A", "B", "f", "g")
    for nm, tm in (("A", _t(a)), ("B", _t(b)), ("f", _t(f)), ("g", _t(g))):
        th = instancie(N.generalisation(nm, th), tm)
    return th


def _image_dans_b(a, b, f, g):
    """{est_injection_de(f,a,b)} ⊢ f⟨D⟩ ⊂ b.

    f⟨D⟩ ⊂ f⟨a⟩ (image croissante, D⊂a) ⊂ b (4e conjoint image(f,a)⊂b)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_fin import (
        _img_croiss, inclusion_transitive_terme)
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    dterm = CB.D(vA, vB, vf, vg)
    fD, fa = E.image(vf, dterm), E.image(vf, vA)
    D_in_a = _D_inclus_a_terme(a, b, f, g)             # D⊂a
    sub_fD_fa = N.modus_ponens(D_in_a, _img_croiss(vf, dterm, vA))  # f⟨D⟩⊂f⟨a⟩
    hinj = N.assume(est_injection_de(vf, vA, vB))
    sub_fa_b = conjonction_elim_droite(hinj)           # image(f,a)⊂b
    trans = inclusion_transitive_terme(fD, fa, vB)
    return N.modus_ponens(conjonction_intro(sub_fD_fa, sub_fa_b), trans)  # {inj f}⊢ f⟨D⟩⊂b


def _img_cong(fX, domFX, X, dom_eq):
    """De ⊢ dom(f|X)=X (dom_eq), produit ⊢ image(f|X, dom f|X) = image(f|X, X)."""
    return N.modus_ponens(dom_eq, congruence_terme(domFX, X, E.image(fX, var("w"))))


def _inj_rewrite(inj_thm, fX, X, domFX, dom_eq):
    """De ⊢ injective_dans(f|X, X) (inj_thm) et ⊢ dom(f|X)=X (dom_eq), produit
    ⊢ injective_dans(f|X, dom f|X)   (réécriture X → dom f|X)."""
    X_eq_domFX = N.modus_ponens(dom_eq, symetrie(domFX, X))   # X = dom f|X
    return N.modus_ponens(inj_thm, equivalence_avant(N.modus_ponens(
        X_eq_domFX, N.s6(X, domFX, "w", E.injective_dans(fX, var("w"))))))


def _conjoints_bij(bij, F, X, Y):
    """Décompose ⊢ est_bijection_de(F,X,Y) en (func, dom=X, inj/X, image=Y)."""
    func = conjonction_elim_gauche(conjonction_elim_gauche(bij))
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(bij))
    inj = conjonction_elim_gauche(conjonction_elim_droite(bij))
    img_eq = conjonction_elim_droite(conjonction_elim_droite(bij))
    return func, dom_eq, inj, img_eq


def _partie_disjoint_terme(x, a):
    """⊢ X ∩ (A∖X) = ∅   pour des TERMES x, a."""
    th = partie_disjoint_complement("A", "X", "z")
    th = instancie(N.generalisation("A", th), _t(a))
    th = instancie(N.generalisation("X", th), _t(x))
    return th


def _partie_reunion_terme(x, a):
    """⊢ (X ⊂ A) ⇒ (X ∪ (A∖X) = A)   pour des TERMES x, a."""
    th = partie_reunion_complement("A", "X", "z")
    th = instancie(N.generalisation("A", th), _t(a))
    th = instancie(N.generalisation("X", th), _t(x))
    return th


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — RECOLLEMENT  h = (f|D) ∪ (g⁻¹|(A∖D))  bijection a → b
# ════════════════════════════════════════════════════════════════════════════
def recollement_h(a="A", b="B", f="f", g="g"):
    """⊢ (est_injection_de(f,a,b) et est_injection_de(g,b,a))
            ⇒ est_bijection_de((f|D) ∪ (g⁻¹|(A∖D)), a, b).

    G:=f|D bijection D→f⟨D⟩ (morceau_fD), H:=g⁻¹|(A∖D) bijection A∖D→B∖f⟨D⟩ (morceau_gI).
    h=G∪H : fonctionnel (domaines D, A∖D disjoints), dom=D∪(A∖D)=a, injectif (images
    f⟨D⟩, B∖f⟨D⟩ disjointes), image=f⟨D⟩∪(B∖f⟨D⟩)=b.  ⇒ bijection a→b."""
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    dterm = CB.D(vA, vB, vf, vg)
    fD = E.restriction(vf, dterm)                      # G = f|D
    AmD = E.difference(vA, dterm)
    gI = E.restriction(E.reciproque(vg), AmD)          # H = g⁻¹|(A∖D)
    fImD = E.image(vf, dterm)                           # f⟨D⟩
    BmfD = E.difference(vB, fImD)                       # B∖f⟨D⟩
    h = E.reunion(fD, gI)                               # h = G∪H

    hinjf = N.assume(est_injection_de(vf, vA, vB))
    hinjg = N.assume(est_injection_de(vg, vB, vA))

    # bijections des deux morceaux
    bijG = N.modus_ponens(hinjf, morceau_fD(a, b, f, g))   # est_bijection_de(f|D, D, f⟨D⟩)
    bijH = N.modus_ponens(hinjg, morceau_gI(a, b, f, g))   # est_bijection_de(gI, A∖D, B∖f⟨D⟩)
    G_func, G_dom, G_inj, G_img = _conjoints_bij(bijG, fD, dterm, fImD)
    H_func, H_dom, H_inj, H_img = _conjoints_bij(bijH, gI, AmD, BmfD)
    #   G_dom : dom(f|D)=D    ;  H_dom : dom(gI)=A∖D
    #   G_img : image(f|D,D)=f⟨D⟩  ;  H_img : image(gI,A∖D)=B∖f⟨D⟩

    domG, domH = E.dom(fD), E.dom(gI)                   # dom(f|D), dom(gI)
    imgG, imgH = E.image(fD, domG), E.image(gI, domH)   # image(f|D,dom f|D), image(gI,dom gI)

    # ── DISJONCTION DES DOMAINES : (∀u)¬(u∈dom f|D et u∈dom gI) ────────────────
    # D∩(A∖D)=∅  → réécrire D→dom(f|D), A∖D→dom(gI)
    disj_DD = _partie_disjoint_terme(dterm, vA)         # D∩(A∖D)=∅
    # réécrire 1er facteur D→dom(f|D) via D=dom(f|D)
    D_eq_domG = symetrie(domG, dterm)                   # ⊢ (dom(f|D)=D) ⇒ (D=dom(f|D))
    D_eq_domG = N.modus_ponens(G_dom, D_eq_domG)        # D=dom(f|D)
    AmD_eq_domH = N.modus_ponens(H_dom, symetrie(domH, AmD))  # A∖D=dom(gI)
    inter_eq1 = N.modus_ponens(D_eq_domG, N.s6(dterm, domG, "w",
        egal(E.intersection(var("w"), AmD), E.VIDE)))   # (D∩(A∖D)=∅)⇔(dom f|D∩(A∖D)=∅)
    disj_1 = N.modus_ponens(disj_DD, equivalence_avant(inter_eq1))   # dom(f|D)∩(A∖D)=∅
    inter_eq2 = N.modus_ponens(AmD_eq_domH, N.s6(AmD, domH, "w",
        egal(E.intersection(domG, var("w")), E.VIDE)))  # ⇔(dom f|D∩dom gI=∅)
    disj_domains = N.modus_ponens(disj_1, equivalence_avant(inter_eq2))  # dom(f|D)∩dom(gI)=∅
    forall_disj = N.modus_ponens(disj_domains, _disjoint_to_forall(domG, domH))  # (∀u)¬(…)

    # ── DISJONCTION DES IMAGES : image(f|D,dom f|D) ∩ image(gI,dom gI) = ∅ ─────
    # f⟨D⟩∩(B∖f⟨D⟩)=∅ → réécrire f⟨D⟩→image(f|D,dom f|D), B∖f⟨D⟩→image(gI,dom gI)
    disj_II = _partie_disjoint_terme(fImD, vB)          # f⟨D⟩∩(B∖f⟨D⟩)=∅
    # image(f|D,dom f|D)=f⟨D⟩  : image(f|D,dom f|D)=image(f|D,D) (G_dom) = f⟨D⟩ (G_img)
    imgG_eq_fD = composer_egalites(_img_cong(fD, domG, dterm, G_dom), G_img)  # imgG=f⟨D⟩
    imgH_eq_BmfD = composer_egalites(_img_cong(gI, domH, AmD, H_dom), H_img)  # imgH=B∖f⟨D⟩
    fD_eq_imgG = N.modus_ponens(imgG_eq_fD, symetrie(imgG, fImD))   # f⟨D⟩=imgG
    BmfD_eq_imgH = N.modus_ponens(imgH_eq_BmfD, symetrie(imgH, BmfD))  # B∖f⟨D⟩=imgH
    ii_eq1 = N.modus_ponens(fD_eq_imgG, N.s6(fImD, imgG, "w",
        egal(E.intersection(var("w"), BmfD), E.VIDE)))  # ⇔(imgG∩(B∖f⟨D⟩)=∅)
    disj_i1 = N.modus_ponens(disj_II, equivalence_avant(ii_eq1))    # imgG∩(B∖f⟨D⟩)=∅
    ii_eq2 = N.modus_ponens(BmfD_eq_imgH, N.s6(BmfD, imgH, "w",
        egal(E.intersection(imgG, var("w")), E.VIDE)))  # ⇔(imgG∩imgH=∅)
    disj_images = N.modus_ponens(disj_i1, equivalence_avant(ii_eq2))  # imgG∩imgH=∅

    # ── CONJOINT 1 : h fonctionnel ────────────────────────────────────────────
    c_func = _cut(reunion_graphes_fonctionnelle(fD, gI),
                  [(E.est_fonctionnel(fD), G_func),
                   (E.est_fonctionnel(gI), H_func),
                   (pourtout("u", non(et(appartient(var("u"), domG),
                                         appartient(var("u"), domH)))), forall_disj)])

    # ── CONJOINT 2 : dom h = a ────────────────────────────────────────────────
    # dom(h)=dom(f|D)∪dom(gI)=D∪(A∖D)=a
    dom_h = dom_reunion_graphes(fD, gI)                 # dom(h)=domG∪domH
    # domG∪domH = D∪domH  (congruence domG→D) = D∪(A∖D)  (congruence domH→A∖D)
    cg1 = N.modus_ponens(G_dom, congruence_terme(domG, dterm,
        E.reunion(var("w"), domH)))                     # domG∪domH = D∪domH
    cg2 = N.modus_ponens(H_dom, congruence_terme(domH, AmD,
        E.reunion(dterm, var("w"))))                    # D∪domH = D∪(A∖D)
    domR_eq_DAmD = composer_egalites(cg1, cg2)          # domG∪domH = D∪(A∖D)
    # D∪(A∖D)=a  (partie_reunion_complement, D⊂a)
    D_in_a = _D_inclus_a_terme(a, b, f, g)              # D⊂a
    DAmD_eq_a = N.modus_ponens(D_in_a, _partie_reunion_terme(dterm, vA))  # D∪(A∖D)=a
    c_dom = composer_egalites(composer_egalites(dom_h, domR_eq_DAmD), DAmD_eq_a)  # dom(h)=a

    domR = E.reunion(domG, domH)
    domR_eq_a = composer_egalites(domR_eq_DAmD, DAmD_eq_a)   # domG∪domH = a

    # ── CONJOINT 3 : h injective sur a ────────────────────────────────────────
    # reunion_graphes_injective sur domR=domG∪domH ; puis réécrire domR→a.
    inj_R = _cut(reunion_graphes_injective(fD, gI),
                 [(E.est_fonctionnel(fD), G_func),
                  (E.est_fonctionnel(gI), H_func),
                  (pourtout("u", non(et(appartient(var("u"), domG),
                                        appartient(var("u"), domH)))), forall_disj),
                  (E.injective_dans(fD, domG), _inj_rewrite(G_inj, fD, dterm, domG, G_dom)),
                  (E.injective_dans(gI, domH), _inj_rewrite(H_inj, gI, AmD, domH, H_dom)),
                  (egal(E.intersection(imgG, imgH), E.VIDE), disj_images)])
    # inj_R : injective_dans(h, domR) ; réécrire domR → a
    c_inj = N.modus_ponens(inj_R, equivalence_avant(N.modus_ponens(domR_eq_a,
        N.s6(domR, vA, "w", E.injective_dans(h, var("w"))))))   # injective_dans(h, a)

    # ── CONJOINT 4 : image h = b ──────────────────────────────────────────────
    img_h = image_reunion_graphes(fD, gI)              # image(h, domR)=imgG∪imgH
    ci1 = N.modus_ponens(imgG_eq_fD, congruence_terme(imgG, fImD,
        E.reunion(var("w"), imgH)))                     # imgG∪imgH = f⟨D⟩∪imgH
    ci2 = N.modus_ponens(imgH_eq_BmfD, congruence_terme(imgH, BmfD,
        E.reunion(fImD, var("w"))))                     # f⟨D⟩∪imgH = f⟨D⟩∪(B∖f⟨D⟩)
    imgR_eq = composer_egalites(ci1, ci2)               # imgG∪imgH = f⟨D⟩∪(B∖f⟨D⟩)
    fD_in_b = _cut(_image_dans_b(a, b, f, g),
                   [(est_injection_de(vf, vA, vB), hinjf)])       # f⟨D⟩⊂b
    fDBmfD_eq_b = N.modus_ponens(fD_in_b, _partie_reunion_terme(fImD, vB))  # f⟨D⟩∪(B∖f⟨D⟩)=b
    img_eq_b = composer_egalites(composer_egalites(img_h, imgR_eq), fDBmfD_eq_b)  # image(h,domR)=b
    # image(h, domR) → image(h, a)  (congruence domR→a)
    domR_to_a = N.modus_ponens(domR_eq_a, congruence_terme(domR, vA,
        E.image(h, var("w"))))                          # image(h,domR)=image(h,a)
    a_to_domR = N.modus_ponens(domR_to_a, symetrie(
        E.image(h, domR), E.image(h, vA)))              # image(h,a)=image(h,domR)
    c_img = composer_egalites(a_to_domR, img_eq_b)      # image(h,a)=b

    # ── ASSEMBLAGE est_bijection_de(h, a, b) ──────────────────────────────────
    bij = conjonction_intro(conjonction_intro(c_func, c_dom),
                            conjonction_intro(c_inj, c_img))
    # bij a deux hyps ouvertes : est_injection_de(f,a,b), est_injection_de(g,b,a).
    himp = N.loi_deduction(est_injection_de(vg, vB, vA),
                           N.loi_deduction(est_injection_de(vf, vA, vB), bij))
    # importation : A⇒(B⇒C) ⟹ (A et B)⇒C  (ordre f puis g)
    hab = N.assume(et(est_injection_de(vf, vA, vB), est_injection_de(vg, vB, vA)))
    c = N.modus_ponens(conjonction_elim_gauche(hab),
                       N.modus_ponens(conjonction_elim_droite(hab), himp))
    return N.loi_deduction(et(est_injection_de(vf, vA, vB),
                              est_injection_de(vg, vB, vA)), c)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — CANTOR–BERNSTEIN  (GRAND PRIX : antisymétrie de ≤)
# ════════════════════════════════════════════════════════════════════════════
def cantor_bernstein(a="A", b="B", f="f", g="g"):
    """⊢ (inf_egal_card(a,b) et inf_egal_card(b,a)) ⇒ equipotent(a,b).

    Corollaire 2 du Théorème 1 (E.III.3.2) : « Deux ensembles tels que chacun soit
    équipotent à une partie de l'autre sont équipotents. »  C'est l'ANTISYMÉTRIE de
    la relation d'ordre ≤ entre cardinaux (Cantor–Bernstein–Schröder).

    Témoin f de a≤b (∃F inj a→b), témoin g de b≤a (∃F inj b→a) ; recollement_h
    donne est_bijection_de(h,a,b) ; S5 témoin h → equipotent(a,b) ; décharge des
    deux ∃ (existe_elimination, comme equipotence_transitive)."""
    vA, vB, vf, vg = _t(a), _t(b), _t(f), _t(g)
    dterm = CB.D(vA, vB, vf, vg)
    fD = E.restriction(vf, dterm)
    AmD = E.difference(vA, dterm)
    gI = E.restriction(E.reciproque(vg), AmD)
    h = E.reunion(fD, gI)                                # h = (f|D)∪(g⁻¹|(A∖D))

    # est_bijection_de(h,a,b)  sous {inj f, inj g} (recollement_h, hyps importées)
    rec = recollement_h(a, b, f, g)                     # (inj f et inj g)⇒bij(h,a,b)
    hinjf = N.assume(est_injection_de(vf, vA, vB))
    hinjg = N.assume(est_injection_de(vg, vB, vA))
    bij_h = N.modus_ponens(conjonction_intro(hinjf, hinjg), rec)   # est_bijection_de(h,a,b)
    # equipotent(a,b) = (∃F)est_bijection_de(F,a,b) : témoin h via S5
    eq_ab = N.modus_ponens(bij_h, N.s5(est_bijection_de(var("F"), vA, vB), h, "F"))  # Eq(a,b)

    # décharge ∃ g : inf_egal_card(b,a)=(∃F)est_injection_de(F,b,a)  (binder « F »)
    stepg = N.loi_deduction(est_injection_de(vg, vB, vA), eq_ab)   # inj(g,b,a)⇒Eq(a,b)
    elimg = existe_elimination(stepg, g if isinstance(g, str) else g.nom)  # (∃g)inj(g,b,a)⇒Eq(a,b)
    alphag = alpha_existe(g if isinstance(g, str) else g.nom, "F",
                          est_injection_de(vg, vB, vA))   # (∃g)inj(g,b,a) ⇔ inf_egal_card(b,a)
    elimg = syllogisme(equivalence_arriere(alphag), elimg)  # inf_egal_card(b,a)⇒Eq(a,b)
    # décharge ∃ f : inf_egal_card(a,b)=(∃F)est_injection_de(F,a,b)
    stepf = N.loi_deduction(est_injection_de(vf, vA, vB), elimg)   # inj(f,a,b)⇒(b≤a⇒Eq(a,b))
    elimf = existe_elimination(stepf, f if isinstance(f, str) else f.nom)  # (∃f)inj(f,a,b)⇒(b≤a⇒Eq)
    alphaf = alpha_existe(f if isinstance(f, str) else f.nom, "F",
                          est_injection_de(vf, vA, vB))   # (∃f)inj(f,a,b) ⇔ inf_egal_card(a,b)
    elimf = syllogisme(equivalence_arriere(alphaf), elimf)  # inf_egal_card(a,b)⇒(b≤a⇒Eq(a,b))
    # importation : A⇒(B⇒C) ⟹ (A et B)⇒C
    hab = N.assume(et(inf_egal_card(vA, vB), inf_egal_card(vB, vA)))
    c = N.modus_ponens(conjonction_elim_droite(hab),
                       N.modus_ponens(conjonction_elim_gauche(hab), elimf))   # Eq(a,b)
    return N.loi_deduction(et(inf_egal_card(vA, vB), inf_egal_card(vB, vA)), c)


__all__ = ["recollement_h", "cantor_bernstein"]
