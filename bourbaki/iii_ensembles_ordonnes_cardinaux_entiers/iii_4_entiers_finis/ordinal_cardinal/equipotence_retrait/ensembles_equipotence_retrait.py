"""§III.4 — GEN : le retrait d'un point de deux ensembles ÉQUIPOTENTS donne deux
ensembles équipotents (E.III.4, surgery ponctuelle).

    GEN := (∀X)(∀Y)(∀x)(∀y)( ( Eq(X,Y) et x∈X et y∈Y ) ⇒ Eq(X∖{x}, Y∖{y}) ).

C'est l'UNIQUE résidu combinatoire de la branche non surjective du LEMME N « pas de
cardinal strictement entre c et c+1 » (cf. ensembles_retrait_surgery :
equipotence_retrait_un_point_general est la formule GEN ; cardinal_pas_entre_mod_general
en déduit le LEMME N modulo (est_cardinal(b) et GEN)).

────────────────────────────────────────────────────────────────────────────────
ARCHITECTURE (du bas vers le haut) :

  (1) image_diff (LE VERROU, INCONDITIONNEL) — pour β bijection X→Y et x∈X :
          image(β, X∖{x}) = Y∖{β(x)}.
      Preuve par double inclusion (A1) :
        • β⟨X∖{x}⟩ ⊂ Y∖{β(x)} : w∈β⟨X∖{x}⟩ ⇒ (∃u)(u∈X, u≠x, (u,w)∈β) ; w∈Y (image
          β⟨X⟩=Y) ; si w=β(x) alors β(u)=β(x) ⇒ u=x (inj) contredit u≠x ⇒ w≠β(x).
        • Y∖{β(x)} ⊂ β⟨X∖{x}⟩ : w∈Y∖{β(x)} ⇒ w∈Y=β⟨X⟩ ⇒ (∃u)(u∈X, (u,w)∈β) ; u≠x
          (sinon w=β(x)) ⇒ u∈X∖{x} ⇒ w∈β⟨X∖{x}⟩.

  (2) eq_retrait_via_bijection (CORE, INCONDITIONNEL) — pour β bijection X→Y, x∈X :
          Eq(X∖{x}, Y∖{β(x)}).
      γ = β|(X∖{x}) : fonctionnel, dom=X∖{x} (X∖{x}⊂X=dom β), injectif (β inj/X⊃X∖{x}),
      image(γ,X∖{x})=image(β,X∖{x})=Y∖{β(x)} (restriction_image_egale_image + image_diff).
      S5 témoin γ ⇒ Eq(X∖{x}, Y∖{β(x)}).

  (3) eq_retrait_meme_ensemble (INCONDITIONNEL) — pour p,y∈Y :
          Eq(Y∖{p}, Y∖{y}).
      • p=y : réflexivité Eq(Y∖{p},Y∖{p}) + Leibniz.
      • p≠y : transposition σ:Y→Y (transposition_existe) avec σ(p)=y ;
        eq_retrait_via_bijection(σ,Y,Y,p) ⇒ Eq(Y∖{p}, Y∖{σ(p)}) = Eq(Y∖{p}, Y∖{y}).

  (4) equipotence_retrait_un_point_general — GEN, par transitivité de Eq :
          Eq(X∖{x},Y∖{β(x)}) [étape 2] et Eq(Y∖{β(x)},Y∖{y}) [étape 3]
              ⇒ Eq(X∖{x}, Y∖{y}).

RÉUTILISE (rien redéfini) : restriction_* (ensembles_cantor_bernstein_bij, clos),
transposition_existe (clos), equipotence_transitive/equipotence_reflexive (clos),
valeur_caracterisation / valeur_dans_graphe (clos).  theorie_ensembles()=22 intangible,
AUCUN axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, ou, non, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite,
    instancie, cas, contraposition)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe, valeur_caracterisation)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de, equipotent)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X)).   (instance de AXIOME_DIFF.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, _t(e)), _t(x)), _t(z))


def _inst_image(g, xset, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G).   (instance de AXIOME_IMAGE.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, _t(g)), _t(xset)), _t(y))


def _inst_dom(f, x):
    """⊢ (x ∈ dom F) ⇔ (∃y)((x,y) ∈ F).   (instance de AXIOME_DOM.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _t(f)), _t(x))


def _z_in_diff_ssi(e, x, z):
    """⊢ (z ∈ E∖{x}) ⇔ (z∈E et ¬(z=x)).

    AXIOME_DIFF (z∈E∖{x} ⇔ z∈E et ¬(z∈{x})) composé avec singleton_membre
    (z∈{x} ⇔ z=x), donc ¬(z∈{x}) ⇔ ¬(z=x)."""
    vE, vx, vz = _t(e), _t(x), _t(z)
    diff = _inst_diff(vE, E.singleton(vx), vz)         # z∈E∖{x} ⇔ (z∈E et ¬(z∈{x}))
    sing = singleton_membre(vz, vx)                    # (z∈{x}) ⇔ (z=x)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import et_congruence_droite
    # ¬(z∈{x}) ⇔ ¬(z=x)   [fwd : ¬(z∈{x})⇒¬(z=x) = contraposée de (z=x)⇒(z∈{x})]
    neg_eq = conjonction_intro(contraposition(equivalence_arriere(sing)),
                               contraposition(equivalence_avant(sing)))
    body = et_congruence_droite(appartient(vz, vE), neg_eq)   # (z∈E et ¬(z∈{x})) ⇔ (z∈E et ¬(z=x))
    return equivalence_transitivite(diff, body)


# ════════════════════════════════════════════════════════════════════════════
#  (1) LE VERROU — image(β, X∖{x}) = Y∖{β(x)}   pour β bijection X→Y, x∈X
# ════════════════════════════════════════════════════════════════════════════
def image_diff(f="F", x="X", y="Y", a="a"):
    """{est_bijection_de(F,X,Y), a∈X} ⊢ image(F, X∖{a}) = Y∖{F(a)}.

    🎯 LE VERROU réutilisable : l'image d'un ensemble PRIVÉ d'un point a par une
    BIJECTION F:X→Y est l'ensemble d'arrivée privé de la valeur F(a).  Preuve par
    double inclusion (A1), via injectivité + surjectivité (image(F,X)=Y) + les
    valeurs (β(u)=w pour (u,w)∈F)."""
    vF, vX, vY, va = _t(f), _t(x), _t(y), _t(a)
    Fa = E.valeur(vF, va)                              # F(a)
    XmA = E.difference(vX, E.singleton(va))            # X∖{a}
    YmFa = E.difference(vY, E.singleton(Fa))           # Y∖{F(a)}
    imgXmA = E.image(vF, XmA)                           # F⟨X∖{a}⟩
    vz, vu = var("z"), var("u")                         # z = élément (liant A1) ; u = antécédent

    # hypothèses de bijectivité
    hbij = N.assume(est_bijection_de(vF, vX, vY))
    f_func = conjonction_elim_gauche(conjonction_elim_gauche(hbij))   # est_fonctionnel(F)
    f_dom = conjonction_elim_droite(conjonction_elim_gauche(hbij))    # dom F = X
    f_bije = conjonction_elim_droite(hbij)                            # est_bijective(F,X,Y)
    f_injX = conjonction_elim_gauche(f_bije)                          # injective_dans(F,X)
    f_surj = conjonction_elim_droite(f_bije)                          # image(F,X)=Y
    ha = N.assume(appartient(va, vX))                                 # a∈X

    # caractérisation des valeurs : ((u,w)∈F) ⇔ (w=F(u))   sous u∈dom F (et F func)
    def w_eq_Fu(u_term, w_term, uw_proof, u_in_dom_proof):
        """{F func, u∈dom F} : de (u,w)∈F déduire w=F(u)."""
        vc = valeur_caracterisation(vF, u_term)        # ((u,y)∈F ⇔ y=F(u))  hyps func, (∃y)(u,y)∈F
        vc_w = instancie(N.generalisation("y", vc), w_term)   # ((u,w)∈F) ⇔ (w=F(u))
        eq = N.modus_ponens(uw_proof, equivalence_avant(vc_w))   # w=F(u)  [hyps func, (∃y)(u,y)∈F]
        # décharger (∃y)(u,y)∈F (de u∈dom F) et func F
        ex = N.modus_ponens(u_in_dom_proof, equivalence_avant(_inst_dom(vF, u_term)))
        eq = N.modus_ponens(ex, N.loi_deduction(
            existe("y", appartient(E.couple(u_term, var("y")), vF)), eq))
        eq = N.modus_ponens(f_func, N.loi_deduction(E.est_fonctionnel(vF), eq))
        return eq                                       # w=F(u)   [hyps déjà ouvertes : aucune nouvelle]

    # ── caractérisation : w∈F⟨X∖{a}⟩ ⇔ (∃u)(u∈X∖{a} et (u,w)∈F)   (binder x→u) ──
    carImg = _inst_image(vF, XmA, vz)                  # z∈F⟨X∖{a}⟩ ⇔ (∃x)(x∈X∖{a} et (x,z)∈F)
    carImg = equivalence_transitivite(carImg, alpha_existe("x", "u",
        et(appartient(var("x"), XmA), appartient(E.couple(var("x"), vz), vF))))
    body_img = et(appartient(vu, XmA), appartient(E.couple(vu, vz), vF))  # u∈X∖{a} et (u,z)∈F

    # ════════════════════════════════════════════════════════════════════════
    #  ⇒  :  z∈F⟨X∖{a}⟩  ⇒  z∈Y∖{F(a)}
    # ════════════════════════════════════════════════════════════════════════
    hb = N.assume(body_img)
    u_inXmA = conjonction_elim_gauche(hb)              # u∈X∖{a}
    uz_F = conjonction_elim_droite(hb)                 # (u,z)∈F
    # u∈X et u≠a
    u_split = N.modus_ponens(u_inXmA, equivalence_avant(_z_in_diff_ssi(vX, va, vu)))  # u∈X et ¬(u=a)
    u_inX = conjonction_elim_gauche(u_split)           # u∈X
    u_ne_a = conjonction_elim_droite(u_split)          # ¬(u=a)
    # u∈dom F
    u_in_dom = N.modus_ponens(u_inX, equivalence_avant(N.modus_ponens(
        N.modus_ponens(f_dom, symetrie(E.dom(vF), vX)),
        N.s6(vX, E.dom(vF), "w", appartient(vu, var("w"))))))        # u∈dom F
    # z∈Y : z∈F⟨X⟩=Y.  z∈F⟨X⟩ via (∃u)(u∈X et (u,z)∈F) témoin u
    body_X = et(appartient(vu, vX), appartient(E.couple(vu, vz), vF))
    z_in_imgX = N.modus_ponens(conjonction_intro(u_inX, uz_F),
                               N.s5(body_X, vu, "u"))                # (∃u)(u∈X et (u,z)∈F)
    z_in_imgX = N.modus_ponens(z_in_imgX, equivalence_arriere(
        equivalence_transitivite(_inst_image(vF, vX, vz), alpha_existe("x", "u",
            et(appartient(var("x"), vX), appartient(E.couple(var("x"), vz), vF))))))  # z∈F⟨X⟩
    z_in_Y = N.modus_ponens(z_in_imgX, equivalence_avant(N.modus_ponens(
        f_surj, N.s6(E.image(vF, vX), vY, "w", appartient(vz, var("w"))))))  # z∈Y
    # z≠F(a) : suppose z=F(a) ⇒ F(u)=z=F(a) ⇒ u=a (inj) contredit ¬(u=a)
    z_eq_Fu = w_eq_Fu(vu, vz, uz_F, u_in_dom)          # z=F(u)
    Fu_eq_z = N.modus_ponens(z_eq_Fu, symetrie(vz, E.valeur(vF, vu)))   # F(u)=z
    h_zFa = N.assume(egal(vz, Fa))                     # z=F(a)
    Fu_eq_Fa = composer_egalites(Fu_eq_z, h_zFa)       # F(u)=F(a)
    inj_inst = instancie(instancie(f_injX, vu), va)    # (u∈X et a∈X et F(u)=F(a)) ⇒ u=a
    u_eq_a = N.modus_ponens(conjonction_intro(conjonction_intro(u_inX, ha), Fu_eq_Fa), inj_inst)  # u=a
    falso = N.modus_ponens(u_eq_a, N.modus_ponens(u_ne_a,
        N.s2(non(egal(vu, va)), non(egal(vz, Fa)))))   # ¬(z=F(a))
    z_ne_Fa = N.modus_ponens(N.loi_deduction(egal(vz, Fa), falso),
                             N.s1(non(egal(vz, Fa))))   # ¬(z=F(a))
    z_in_YmFa = N.modus_ponens(conjonction_intro(z_in_Y, z_ne_Fa),
                               equivalence_arriere(_z_in_diff_ssi(vY, Fa, vz)))   # z∈Y∖{F(a)}
    fwd_body = N.loi_deduction(body_img, z_in_YmFa)    # body_img ⇒ z∈Y∖{F(a)}
    fwd = existe_elimination(fwd_body, "u")            # (∃u)body_img ⇒ z∈Y∖{F(a)}
    fwd = syllogisme(equivalence_avant(carImg), fwd)   # z∈F⟨X∖{a}⟩ ⇒ z∈Y∖{F(a)}

    # ════════════════════════════════════════════════════════════════════════
    #  ⇐  :  z∈Y∖{F(a)}  ⇒  z∈F⟨X∖{a}⟩
    # ════════════════════════════════════════════════════════════════════════
    hz = N.assume(appartient(vz, YmFa))                # z∈Y∖{F(a)}
    z_split = N.modus_ponens(hz, equivalence_avant(_z_in_diff_ssi(vY, Fa, vz)))   # z∈Y et ¬(z=F(a))
    z_inY = conjonction_elim_gauche(z_split)           # z∈Y
    z_ne_Fa2 = conjonction_elim_droite(z_split)        # ¬(z=F(a))
    # z∈Y=F⟨X⟩ ⇒ (∃u)(u∈X et (u,z)∈F)
    Y_eq_imgX = N.modus_ponens(f_surj, symetrie(E.image(vF, vX), vY))   # Y = F⟨X⟩
    z_inImgX = N.modus_ponens(z_inY, equivalence_avant(N.modus_ponens(
        Y_eq_imgX, N.s6(vY, E.image(vF, vX), "w", appartient(vz, var("w"))))))  # z∈F⟨X⟩
    carImgX = equivalence_transitivite(_inst_image(vF, vX, vz), alpha_existe("x", "u",
        et(appartient(var("x"), vX), appartient(E.couple(var("x"), vz), vF))))  # z∈F⟨X⟩ ⇔ (∃u)(u∈X et (u,z)∈F)
    ex_uz = N.modus_ponens(z_inImgX, equivalence_avant(carImgX))        # (∃u)(u∈X et (u,z)∈F)
    # corps : (u∈X et (u,z)∈F) ⇒ z∈F⟨X∖{a}⟩
    body_u2 = et(appartient(vu, vX), appartient(E.couple(vu, vz), vF))
    hbu = N.assume(body_u2)
    u_inX2 = conjonction_elim_gauche(hbu)              # u∈X
    uz_F2 = conjonction_elim_droite(hbu)               # (u,z)∈F
    u_in_dom2 = N.modus_ponens(u_inX2, equivalence_avant(N.modus_ponens(
        N.modus_ponens(f_dom, symetrie(E.dom(vF), vX)),
        N.s6(vX, E.dom(vF), "w", appartient(vu, var("w"))))))        # u∈dom F
    # u≠a : si u=a alors z=F(u)=F(a) contredit ¬(z=F(a))
    z_eq_Fu2 = w_eq_Fu(vu, vz, uz_F2, u_in_dom2)       # z=F(u)
    h_ua = N.assume(egal(vu, va))                      # u=a
    Fu_eq_Fa2 = N.modus_ponens(h_ua, congruence_terme(vu, va, E.valeur(vF, var("w")), "w"))  # F(u)=F(a)
    z_eq_Fa = composer_egalites(z_eq_Fu2, Fu_eq_Fa2)   # z=F(a)
    falso2 = N.modus_ponens(z_eq_Fa, N.modus_ponens(z_ne_Fa2,
        N.s2(non(egal(vz, Fa)), non(egal(vu, va)))))   # ¬(u=a)
    u_ne_a2 = N.modus_ponens(N.loi_deduction(egal(vu, va), falso2),
                             N.s1(non(egal(vu, va))))   # ¬(u=a)
    u_inXmA2 = N.modus_ponens(conjonction_intro(u_inX2, u_ne_a2),
                              equivalence_arriere(_z_in_diff_ssi(vX, va, vu)))   # u∈X∖{a}
    z_in_imgXmA = N.modus_ponens(conjonction_intro(u_inXmA2, uz_F2),
                                 N.s5(body_img, vu, "u"))            # (∃u)body_img
    z_in_imgXmA = N.modus_ponens(z_in_imgXmA, equivalence_arriere(carImg))   # z∈F⟨X∖{a}⟩
    bwd_body = N.loi_deduction(body_u2, z_in_imgXmA)   # (u∈X et (u,z)∈F) ⇒ z∈F⟨X∖{a}⟩
    bwd_imp = existe_elimination(bwd_body, "u")        # (∃u)(u∈X et (u,z)∈F) ⇒ z∈F⟨X∖{a}⟩
    z_in_imgXmA_final = N.modus_ponens(ex_uz, bwd_imp) # z∈F⟨X∖{a}⟩
    bwd = N.loi_deduction(appartient(vz, YmFa), z_in_imgXmA_final)   # z∈Y∖{F(a)} ⇒ z∈F⟨X∖{a}⟩

    # ── extensionnalité A1 ────────────────────────────────────────────────────
    incl_LR = N.generalisation("z", fwd)               # F⟨X∖{a}⟩ ⊂ Y∖{F(a)}
    incl_RL = N.generalisation("z", bwd)               # Y∖{F(a)} ⊂ F⟨X∖{a}⟩
    ext = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), imgXmA), YmFa)
    return N.modus_ponens(conjonction_intro(incl_LR, incl_RL), ext)   # F⟨X∖{a}⟩=Y∖{F(a)}


# ════════════════════════════════════════════════════════════════════════════
#  (2) CORE — β bijection X→Y, a∈X  ⊢  Eq(X∖{a}, Y∖{β(a)})
# ════════════════════════════════════════════════════════════════════════════
def _diff_inclus_terme(e, x):
    """⊢ (E∖X) ⊂ E  pour des TERMES e, x.

    On généralise les DEUX lettres E, X AVANT toute instanciation (sinon capture :
    instancier E:=X puis re-généraliser « X » lie aussi le X fraîchement introduit)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_fin import _diff_inclus
    vE, vX = _t(e), _t(x)
    gen = N.generalisation("E", N.generalisation("X", _diff_inclus("E", "X")))   # (∀X)(∀E)(E∖X⊂E)
    return instancie(instancie(gen, vE), vX)                                     # E:=e, X:=x


def eq_retrait_via_bijection(f="Bij", x="X", y="Y", a="a"):
    """⊢ est_bijection_de(F,X,Y) ⇒ ( a∈X ⇒ Eq(X∖{a}, Y∖{F(a)}) ).   (THÉORÈME CLOS.)

    🎯 CORE INCONDITIONNEL : restreindre une bijection F:X→Y au domaine privé de a
    donne une bijection X∖{a} → Y∖{F(a)}, donc Eq(X∖{a}, Y∖{F(a)}).
      γ = F|(X∖{a}) : fonctionnel (F func), dom=X∖{a} (X∖{a}⊂X=dom F), injectif
      (F inj sur X⊃X∖{a}), image(γ,X∖{a})=image(F,X∖{a})=Y∖{F(a)} (restriction_image
      + image_diff).  S5 témoin γ ⇒ Eq(X∖{a}, Y∖{F(a)}).

    ⚠️ Le nom de la bijection f doit DIFFÉRER du liant existentiel « F » de equipotent
    (car Y∖{F(a)} contient f libre : avec f=« F », equipotent(·, Y∖{F(a)}) CAPTURERAIT
    le F de F(a)).  Défaut f=« Bij » ; assertion ci-dessous."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
        restriction_dom_sous_inclusion, restriction_injective,
        restriction_image_egale_image, _restriction_fonctionnelle_terme,
        _injective_dans_restreint)
    nom_f = f if isinstance(f, str) else f.nom
    assert nom_f != "F", "le nom de la bijection doit différer du liant « F » de equipotent (capture)"
    vF, vX, vY, va = _t(f), _t(x), _t(y), _t(a)
    Fa = E.valeur(vF, va)                              # F(a)
    XmA = E.difference(vX, E.singleton(va))            # X∖{a}
    YmFa = E.difference(vY, E.singleton(Fa))           # Y∖{F(a)}
    gamma = E.restriction(vF, XmA)                     # γ = F|(X∖{a})

    hbij = N.assume(est_bijection_de(vF, vX, vY))
    f_func = conjonction_elim_gauche(conjonction_elim_gauche(hbij))   # est_fonctionnel(F)
    f_dom = conjonction_elim_droite(conjonction_elim_gauche(hbij))    # dom F = X
    f_injX = conjonction_elim_gauche(conjonction_elim_droite(hbij))   # injective_dans(F,X)
    ha = N.assume(appartient(va, vX))                                 # a∈X

    # X∖{a} ⊂ dom F : X∖{a}⊂X (=_diff_inclus_terme) et X=dom F (sym de dom F=X)
    XmA_inX = _diff_inclus_terme(vX, E.singleton(va))                 # X∖{a} ⊂ X
    X_eq_domF = N.modus_ponens(f_dom, symetrie(E.dom(vF), vX))        # X = dom F
    XmA_inDom = N.modus_ponens(XmA_inX, equivalence_avant(N.modus_ponens(
        X_eq_domF, N.s6(vX, E.dom(vF), "w", inclus(XmA, var("w"))))))  # X∖{a} ⊂ dom F

    # injective_dans(F, X∖{a}) : restriction de F inj/X (X∖{a}⊂X)
    f_inj_XmA = _injective_dans_restreint(vF, vX, XmA, XmA_inX)       # {inj/X} ⊢ inj/X∖{a}
    f_inj_XmA = N.modus_ponens(f_injX, N.loi_deduction(
        E.injective_dans(vF, vX), f_inj_XmA))                        # injective_dans(F,X∖{a})

    # ── 4 conjoints de est_bijection_de(γ, X∖{a}, Y∖{F(a)}) ───────────────────
    c_func = N.modus_ponens(f_func, _restriction_fonctionnelle_terme(vF, XmA))   # γ fonctionnel
    c_dom = N.modus_ponens(XmA_inDom, restriction_dom_sous_inclusion(vF, XmA))   # dom(γ)=X∖{a}
    ri = restriction_injective(vF, XmA)            # {F func, inj/X∖{a}, X∖{a}⊂dom F} ⊢ inj(γ,X∖{a})
    c_inj = N.modus_ponens(f_func, N.loi_deduction(E.est_fonctionnel(vF),
            N.modus_ponens(f_inj_XmA, N.loi_deduction(E.injective_dans(vF, XmA),
            N.modus_ponens(XmA_inDom, N.loi_deduction(inclus(XmA, E.dom(vF)), ri))))))
    # image(γ,X∖{a})=image(F,X∖{a})=Y∖{F(a)}
    img_restr = restriction_image_egale_image(vF, XmA)               # image(γ,X∖{a})=image(F,X∖{a})
    id_thm = _cut_bij_a(image_diff(f, x, y, a), hbij, ha,            # image(F,X∖{a})=Y∖{F(a)}
                        est_bijection_de(vF, vX, vY), appartient(va, vX))
    c_img = composer_egalites(img_restr, id_thm)                     # image(γ,X∖{a})=Y∖{F(a)}

    # est_bijection_de(γ, X∖{a}, Y∖{F(a)}) = ((func ∧ dom) ∧ (inj ∧ image))
    bij = conjonction_intro(conjonction_intro(c_func, c_dom),
                            conjonction_intro(c_inj, c_img))         # est_bijection_de(γ,X∖{a},Y∖{F(a)})
    # S5 témoin γ ⇒ Eq(X∖{a}, Y∖{F(a)})   [liant « F » de equipotent ; f≠"F" ⇒ pas de
    #  capture du F libre de Y∖{F(a)} (le terme témoin γ est substitué, pas réécrit)]
    eq = N.modus_ponens(bij, N.s5(est_bijection_de(var("F"), XmA, YmFa), gamma, "F"))
    assert eq.conclusion == equipotent(XmA, YmFa), "la conclusion n'égale pas Eq(X∖{a}, Y∖{F(a)})"
    inner = N.loi_deduction(appartient(va, vX), eq)                  # a∈X ⇒ Eq(…)  [hyp bij]
    return N.loi_deduction(est_bijection_de(vF, vX, vY), inner)      # bij ⇒ (a∈X ⇒ Eq(…))


def _cut_bij_a(thm, hbij_proof, ha_proof, bij_formule, a_formule):
    """Décharge dans `thm` les hypothèses bij_formule (par hbij_proof) et a_formule
    (par ha_proof)."""
    thm = N.modus_ponens(hbij_proof, N.loi_deduction(bij_formule, thm))
    thm = N.modus_ponens(ha_proof, N.loi_deduction(a_formule, thm))
    return thm


# ════════════════════════════════════════════════════════════════════════════
#  (3) Deux retraits ponctuels du MÊME ensemble sont équipotents
#       p,y∈Y  ⊢  Eq(Y∖{p}, Y∖{y})    (via transposition si p≠y, identité si p=y)
# ════════════════════════════════════════════════════════════════════════════
def eq_retrait_meme_ensemble(y="Y", p="p", yy="yy"):
    """⊢ ( p∈Y et yy∈Y ) ⇒ Eq(Y∖{p}, Y∖{yy}).   (THÉORÈME CLOS, 0 hyp.)

    Retirer deux points p, yy d'un MÊME ensemble Y donne des restes équipotents :
      • p=yy : Y∖{p}=Y∖{yy} (Leibniz) et Eq(Y∖{p},Y∖{p}) (réflexivité) ;
      • p≠yy : transposition σ:Y→Y (transposition_existe) avec σ(p)=yy ;
        eq_retrait_via_bijection(σ,Y,Y,p) ⇒ Eq(Y∖{p}, Y∖{σ(p)}) = Eq(Y∖{p}, Y∖{yy})
        (réécriture σ(p)=yy)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import equipotence_reflexive
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition import transposition_existe
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import tiers_exclu
    vY, vp, vyy = _t(y), _t(p), _t(yy)
    Ymp = E.difference(vY, E.singleton(vp))            # Y∖{p}
    Ymyy = E.difference(vY, E.singleton(vyy))          # Y∖{yy}
    cible = equipotent(Ymp, Ymyy)                      # Eq(Y∖{p}, Y∖{yy})

    h_pin = N.assume(appartient(vp, vY))               # p∈Y
    h_yin = N.assume(appartient(vyy, vY))              # yy∈Y

    # ── cas p=yy : réflexivité + Leibniz (réécriture yy:=p dans le 2e arg) ──────
    h_eq = N.assume(egal(vp, vyy))                     # p=yy
    refl = equipotence_reflexive_pour(Ymp)             # Eq(Y∖{p}, Y∖{p})
    #   Eq(Y∖{p},Y∖{p}) ⇒ Eq(Y∖{p},Y∖{yy})  via p=yy (Leibniz dans le 2e arg, position « w »)
    leib = N.modus_ponens(h_eq, N.s6(vp, vyy, "w",
        equipotent(Ymp, E.difference(vY, E.singleton(var("w"))))))   # Eq(..Y∖{p})⇔Eq(..Y∖{yy})
    eq_caseA = N.modus_ponens(refl, equivalence_avant(leib))         # Eq(Y∖{p},Y∖{yy})
    caseA = N.loi_deduction(egal(vp, vyy), eq_caseA)                 # (p=yy) ⇒ Eq(…)

    # ── cas p≠yy : transposition σ:Y→Y, σ(p)=yy ────────────────────────────────
    h_ne = N.assume(non(egal(vp, vyy)))                # ¬(p=yy)
    # transposition_existe(Y, yy, p) : (yy∈Y et p∈Y et ¬(yy=p)) ⇒ (∃σ)(bij(σ,Y,Y) et σ(p)=yy)
    trex = transposition_existe(y, yy, p)
    # antécédent (yy∈Y et p∈Y et ¬(yy=p))
    yy_ne_p = N.modus_ponens(h_ne, _ne_symetrie(vp, vyy))           # ¬(yy=p)
    ante_tr = conjonction_intro(conjonction_intro(h_yin, h_pin), yy_ne_p)
    ex_sigma_F = N.modus_ponens(ante_tr, trex)         # (∃F)(bij(F,Y,Y) et F(p)=yy)  [binder « F »]
    # renommer le liant « F » → « Sg » (transposition_existe lie « F », réutilisé interdit)
    nom_s = "Sg"
    vS = var(nom_s)
    matrice_F = et(est_bijection_de(var("F"), vY, vY), egal(E.valeur(var("F"), vp), vyy))
    ex_sigma = N.modus_ponens(ex_sigma_F, equivalence_avant(alpha_existe("F", nom_s, matrice_F)))
    # corps : (bij(σ,Y,Y) et σ(p)=yy) ⇒ Eq(Y∖{p}, Y∖{yy})
    body_sigma = et(est_bijection_de(vS, vY, vY), egal(E.valeur(vS, vp), vyy))
    h_body = N.assume(body_sigma)
    bij_s = conjonction_elim_gauche(h_body)            # bij(σ,Y,Y)
    sp_eq_yy = conjonction_elim_droite(h_body)         # σ(p)=yy
    # eq_retrait_via_bijection(Sg, Y, Y, p) : bij(σ,Y,Y) ⇒ (p∈Y ⇒ Eq(Y∖{p}, Y∖{σ(p)}))
    core = eq_retrait_via_bijection(nom_s, y, y, p)
    eq_sp = N.modus_ponens(h_pin, N.modus_ponens(bij_s, core))      # Eq(Y∖{p}, Y∖{σ(p)})
    Ymsp = E.difference(vY, E.singleton(E.valeur(vS, vp)))          # Y∖{σ(p)}
    #   réécrire σ(p):=yy dans le 2e arg ⇒ Eq(Y∖{p}, Y∖{yy})
    leib2 = N.modus_ponens(sp_eq_yy, N.s6(E.valeur(vS, vp), vyy, "w",
        equipotent(Ymp, E.difference(vY, E.singleton(var("w"))))))  # Eq(..Y∖{σ(p)})⇔Eq(..Y∖{yy})
    eq_caseB_inner = N.modus_ponens(eq_sp, equivalence_avant(leib2))   # Eq(Y∖{p}, Y∖{yy})  [hyp body_sigma]
    corps_imp = N.loi_deduction(body_sigma, eq_caseB_inner)           # body_sigma ⇒ Eq(…)
    ex_imp = existe_elimination(corps_imp, nom_s)                     # (∃σ)body_sigma ⇒ Eq(…)
    eq_caseB = N.modus_ponens(ex_sigma, ex_imp)                       # Eq(Y∖{p},Y∖{yy})  [hyp ¬(p=yy)]
    caseB = N.loi_deduction(non(egal(vp, vyy)), eq_caseB)            # ¬(p=yy) ⇒ Eq(…)

    # ── recombinaison par tiers exclu ─────────────────────────────────────────
    eq_final = cas(tiers_exclu(egal(vp, vyy)), caseA, caseB)         # Eq(Y∖{p},Y∖{yy})  [hyps p∈Y, yy∈Y]
    # décharge de la conjonction ( p∈Y et yy∈Y )
    ante = et(appartient(vp, vY), appartient(vyy, vY))
    h = N.assume(ante)
    eq_under_conj = _cut_bij_a(eq_final,
        conjonction_elim_gauche(h), conjonction_elim_droite(h),
        appartient(vp, vY), appartient(vyy, vY))                    # Eq(…)  [hyp ante]
    return N.loi_deduction(ante, eq_under_conj)                     # (p∈Y et yy∈Y) ⇒ Eq(…)


def equipotence_reflexive_pour(t):
    """⊢ Eq(T, T)  pour un TERME T quelconque (instance de equipotence_reflexive)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import equipotence_reflexive
    th = equipotence_reflexive("X")
    return instancie(N.generalisation("X", th), _t(t))


def _ne_symetrie(a, b):
    """⊢ ¬(a=b) ⇒ ¬(b=a).   (contraposée de la symétrie de l'égalité.)"""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
    return contraposition(symetrie(b, a))              # (b=a)⇒(a=b) contraposé : ¬(a=b)⇒¬(b=a)


def _valeur_dans_codomaine_image(f, x, y, a):
    """{est_bijection_de(F,X,Y), a∈X} ⊢ F(a) ∈ Y.

    (a,F(a))∈F (couple_valeur_dans_graphe, a∈dom F=X) ⇒ F(a)∈F⟨X⟩ (AXIOME_IMAGE,
    témoin a∈X) ⇒ F(a)∈Y (réécriture image(F,X)=Y, surjectivité)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_valeur_codomaine import couple_valeur_dans_graphe
    vF, vX, vY, va = _t(f), _t(x), _t(y), _t(a)
    Fa = E.valeur(vF, va)
    hbij = N.assume(est_bijection_de(vF, vX, vY))
    f_dom = conjonction_elim_droite(conjonction_elim_gauche(hbij))   # dom F = X
    f_surj = conjonction_elim_droite(conjonction_elim_droite(hbij))  # image(F,X)=Y
    ha = N.assume(appartient(va, vX))                                # a∈X
    # (a, F(a)) ∈ F
    cpl = couple_valeur_dans_graphe(vF, vX, va)                      # {dom F=X, a∈X} ⊢ (a,F(a))∈F
    cpl = N.modus_ponens(f_dom, N.loi_deduction(egal(E.dom(vF), vX), cpl))
    cpl = N.modus_ponens(ha, N.loi_deduction(appartient(va, vX), cpl))   # (a,F(a))∈F
    # F(a) ∈ F⟨X⟩  via AXIOME_IMAGE (∃u)(u∈X et (u,F(a))∈F), témoin a
    body = et(appartient(var("u"), vX), appartient(E.couple(var("u"), Fa), vF))
    ex = N.modus_ponens(conjonction_intro(ha, cpl), N.s5(body, va, "u"))   # (∃u)(u∈X et (u,F(a))∈F)
    carImg = equivalence_transitivite(_inst_image(vF, vX, Fa), alpha_existe("x", "u",
        et(appartient(var("x"), vX), appartient(E.couple(var("x"), Fa), vF))))  # F(a)∈F⟨X⟩ ⇔ (∃u)…
    Fa_in_imgX = N.modus_ponens(ex, equivalence_arriere(carImg))     # F(a)∈F⟨X⟩
    # réécrire F⟨X⟩=Y ⇒ F(a)∈Y
    Fa_in_Y = N.modus_ponens(Fa_in_imgX, equivalence_avant(N.modus_ponens(
        f_surj, N.s6(E.image(vF, vX), vY, "w", appartient(Fa, var("w"))))))   # F(a)∈Y
    return Fa_in_Y


def _eq_transitive_t(ta, tb, tc):
    """⊢ (Eq(A,B) et Eq(B,C)) ⇒ Eq(A,C)  pour des TERMES A,B,C quelconques.

    On instancie le théorème CLOS equipotence_transitive (preuve faite avec des NOMS
    Xt,Yt,Zt) : capture-safe même si B contient des τ-termes (le noyau renomme)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_transitive
    th = equipotence_transitive("F", "G", "Xt", "Yt", "Zt")       # CLOS (liants ∃ « F »/« G »)
    gen = N.generalisation("Xt", N.generalisation("Yt", N.generalisation("Zt", th)))  # (∀Xt)(∀Yt)(∀Zt)…
    return instancie(instancie(instancie(gen, _t(ta)), _t(tb)), _t(tc))   # Xt:=A, Yt:=B, Zt:=C


# ════════════════════════════════════════════════════════════════════════════
#  (4) GEN — retrait d'un point de deux ensembles ÉQUIPOTENTS
# ════════════════════════════════════════════════════════════════════════════
def gen_corps(x="X", y="Y", xp="xpt", yp="ypt"):
    """⊢ ( Eq(X,Y) et x∈X et y∈Y ) ⇒ Eq(X∖{x}, Y∖{y}).   (corps de GEN, THÉORÈME CLOS.)

    ⚠️ Les POINTS retirés sont nommés « xpt »/« ypt » (et non « x »/« y ») : les lemmes
    d'image réutilisés (restriction_image_egale_image, image_diff) lient « x » en
    interne (AXIOME_IMAGE) ; un point nommé « x » dans X∖{x} serait CAPTURÉ.  Le
    renommage vers les liants « x »/« y » de GEN est fait dans
    equipotence_retrait_un_point_general (α-conversion des ∀, jamais affaibli).

    🎯 LE RÉSIDU COMBINATOIRE de la branche non surjective du LEMME N.  Chaîne :
      • Eq(X,Y) ⇒ témoin β:X→Y (existe_elimination, liant renommé F→Bij pour que la
        valeur β(x) ne capture pas le « F » de equipotent) ;
      • CORE eq_retrait_via_bijection(β,X,Y,x) sous x∈X ⇒ Eq(X∖{x}, Y∖{β(x)}) ;
      • β(x)∈Y (valeur dans codomaine) ;  eq_retrait_meme_ensemble(Y,β(x),y) sous
        (β(x)∈Y et y∈Y) ⇒ Eq(Y∖{β(x)}, Y∖{y}) ;
      • transitivité de Eq ⇒ Eq(X∖{x}, Y∖{y}).
    La conclusion ne mentionnant ni β ni F, l'élimination de l'existentielle est propre."""
    vX, vY, vx, vy = _t(x), _t(y), _t(xp), _t(yp)
    XmX = E.difference(vX, E.singleton(vx))            # X∖{x}
    YmY = E.difference(vY, E.singleton(vy))            # Y∖{y}
    cible = equipotent(XmX, YmY)                        # Eq(X∖{x}, Y∖{y})

    ante = et(et(equipotent(vX, vY), appartient(vx, vX)), appartient(vy, vY))
    h = N.assume(ante)
    h_eq = conjonction_elim_gauche(conjonction_elim_gauche(h))   # Eq(X,Y)
    h_xX = conjonction_elim_droite(conjonction_elim_gauche(h))   # x∈X
    h_yY = conjonction_elim_droite(h)                            # y∈Y

    # renommer le liant existentiel « F » → « Bij » dans Eq(X,Y)
    nom_b = "Bij"
    vB = var(nom_b)
    bodyF = est_bijection_de(var("F"), vX, vY)
    h_eq_B = N.modus_ponens(h_eq, equivalence_avant(alpha_existe("F", nom_b, bodyF)))  # (∃Bij)bij(Bij,X,Y)
    Bx = E.valeur(vB, vx)                              # β(x)
    YmBx = E.difference(vY, E.singleton(Bx))           # Y∖{β(x)}

    # corps : bij(β,X,Y) ⇒ Eq(X∖{x}, Y∖{y})   [sous x∈X, y∈Y]
    h_bij = N.assume(est_bijection_de(vB, vX, vY))
    # CORE : Eq(X∖{x}, Y∖{β(x)})
    core = eq_retrait_via_bijection(nom_b, x, y, xp)   # bij(β,X,Y)⇒(x∈X⇒Eq(X∖{x},Y∖{β(x)}))
    eq1 = N.modus_ponens(h_xX, N.modus_ponens(h_bij, core))      # Eq(X∖{x}, Y∖{β(x)})
    # β(x)∈Y
    Bx_in_Y = _cut_bij_a(_valeur_dans_codomaine_image(nom_b, x, y, xp),
                         h_bij, h_xX, est_bijection_de(vB, vX, vY), appartient(vx, vX))  # β(x)∈Y
    # Eq(Y∖{β(x)}, Y∖{y}).  On INSTANCIE le point β(x) dans le théorème CLOS
    # eq_retrait_meme_ensemble (preuve par transposition faite avec le NOM propre
    # « pPt ») : β(x)=valeur(Bij,x) est un τ-terme (liant « y ») ; le passer en argument
    # de la transposition CAPTURERAIT son liant interne.  L'instanciation dans le
    # théorème déjà clos est, elle, capture-safe (le noyau renomme les liants).
    meme_gen = N.generalisation("pPt", eq_retrait_meme_ensemble(y, "pPt", yp))   # (∀pPt)((pPt∈Y et y∈Y)⇒Eq(Y∖{pPt},Y∖{y}))
    meme = instancie(meme_gen, Bx)                     # (β(x)∈Y et y∈Y) ⇒ Eq(Y∖{β(x)}, Y∖{y})
    eq2 = N.modus_ponens(conjonction_intro(Bx_in_Y, h_yY), meme)  # Eq(Y∖{β(x)}, Y∖{y})
    # transitivité : (Eq(X∖{x},Y∖{β(x)}) et Eq(Y∖{β(x)},Y∖{y})) ⇒ Eq(X∖{x},Y∖{y}).
    # On INSTANCIE les ensembles dans le théorème CLOS equipotence_transitive (preuve
    # faite avec des NOMS Xt,Yt,Zt) : le terme milieu Y∖{β(x)} contient un τ (liant
    # « y »), qui CAPTURERAIT les liants internes de composee_domaine/_image si on
    # relançait la preuve dessus.  L'instanciation dans le clos est capture-safe.
    trans = _eq_transitive_t(XmX, YmBx, YmY)
    eq3 = N.modus_ponens(conjonction_intro(eq1, eq2), trans)      # Eq(X∖{x}, Y∖{y})
    assert eq3.conclusion == cible, "transitivité : conclusion ≠ Eq(X∖{x}, Y∖{y})"

    corps_imp = N.loi_deduction(est_bijection_de(vB, vX, vY), eq3)   # bij(β,X,Y) ⇒ Eq(…)
    eq_final = N.modus_ponens(h_eq_B, existe_elimination(corps_imp, nom_b))   # Eq(X∖{x},Y∖{y})
    return N.loi_deduction(ante, eq_final)             # (Eq(X,Y) et x∈X et y∈Y) ⇒ Eq(X∖{x},Y∖{y})


# @livre Ch.III §4.2 Demo.2 | E III.31 L.18-28 | PDF p.134
def equipotence_retrait_un_point_general():
    """⊢ GEN := (∀X)(∀Y)(∀x)(∀ypt)( ( Eq(X,Y) et x∈X et ypt∈Y ) ⇒ Eq(X∖{x}, Y∖{ypt}) ).

    🎯🎯 GEN INCONDITIONNEL (E.III.4) : le retrait d'un point de deux ensembles
    ÉQUIPOTENTS donne deux ensembles équipotents.  Généralise gen_corps (corps clos)
    sur X, Y, le point-x (renommé « x ») et le point-y.

    ⚠️ FORME CANONIQUE : le point-y reste lié « ypt » (et non « y »).  La valeur
    valeur(F,·) = τ_y(…) lie « y » en interne (E.valeur) ; lier le point ∀ « y »
    forcerait le noyau à α-renommer ce τ_y (« @0 » canonique, anti-capture conservatif).
    Lier le point « ypt » garde la forme NON normalisée τ_y.  Cette forme est
    α-ÉQUIVALENTE au littéral de ensembles_retrait_surgery (qui lie « y ») et lui est
    INTERCHANGEABLE : instanciée aux mêmes termes (succ_c, S, q, *), elle donne la MÊME
    formule (cf. _hd_depuis_gen / cardinal_pas_entre_inconditionnel).  THÉORÈME CLOS,
    jamais affaibli."""
    th_corps = gen_corps("X", "Y", "xpt", "ypt")                  # ⊢ corps  (clos, 0 hyp)
    # xpt := x  (x n'est lié nulle part dans le corps : substitution clean, pas de τ_x)
    th_x = instancie(N.generalisation("xpt", th_corps), var("x"))    # corps[xpt:=x]  (τ_y intact)
    return N.generalisation("X", N.generalisation("Y",
               N.generalisation("x", N.generalisation("ypt", th_x))))  # (∀X)(∀Y)(∀x)(∀ypt) corps


# ════════════════════════════════════════════════════════════════════════════
#  (5) CAPSTONE — décharge de GEN ⇒ LEMME N « pas de cardinal entre c et c+1 »
#                 INCONDITIONNEL (modulo le SEUL est_cardinal(b), structurel)
# ════════════════════════════════════════════════════════════════════════════
def _hd_depuis_gen(b="b", c="c", q="q"):
    """⊢ HD(b,c).   (THÉORÈME CLOS, 0 hyp.)

    HD(b,c) = (∀q)( q∈c+1 ⇒ Eq((c+1)∖{q}, (C⊔{∅})∖{*}) ), le « résidu » de la surgery.
    Réplique de ensembles_retrait_surgery.retrait_un_point_depuis_general, mais en
    DÉCHARGEANT GEN par notre PREUVE close (equipotence_retrait_un_point_general,
    forme canonique liant « ypt ») au lieu de l'ASSUMER : on INSTANCIE directement la
    GEN prouvée en X:=c+1, Y:=C⊔{∅}, x:=q, y:=*.  L'instanciation à ces termes (sans
    « y » libre) donne EXACTEMENT l'instance attendue (vérifié : == à l'instance de la
    GEN-littéral de surgery)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import _S, _STAR, eq_succ_ensemble
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_prop8_plus_point import marqueur_dans_somme
    vc, vq = _t(c), _t(q)
    succ_c = successeur(vc)                                  # c+1 = Card(C⊔{∅})
    S = _S(vc)                                               # C⊔{∅}
    gen = equipotence_retrait_un_point_general()            # ⊢ GEN  (CLOS, liant « ypt »)
    # instancie X:=c+1, Y:=S, x:=q, y(=ypt):=*   (capture-safe, termes sans « y » libre)
    inst = instancie(instancie(instancie(instancie(gen, succ_c), S), vq), _STAR)
    # antécédent ( Eq(c+1,S) et q∈c+1 et *∈S )
    eq_cs = eq_succ_ensemble(c)                              # Eq(c+1, S)   (CLOS)
    star_in = marqueur_dans_somme(c)                         # *∈S          (CLOS)
    q_in = appartient(vq, succ_c)
    h_qin = N.assume(q_in)                                   # q∈c+1
    ante = conjonction_intro(conjonction_intro(eq_cs, h_qin), star_in)
    eq_diff = N.modus_ponens(ante, inst)                    # Eq((c+1)∖{q}, S∖{*})  [hyp q∈c+1]
    corps_q = N.loi_deduction(q_in, eq_diff)                # q∈c+1 ⇒ Eq((c+1)∖{q}, S∖{*})
    nomq = q if isinstance(q, str) else q.nom
    return N.generalisation(nomq, corps_q)                  # HD(b,c)   (CLOS)


def cardinal_pas_entre_inconditionnel(b="b", c="c", f="F", q="q"):
    """⊢ est_cardinal(b) ⇒ ( ( b ≤ c+1 ) ⇒ ( b ≤ c OU b = c+1 ) ).   (THÉORÈME CLOS, 0 hyp.)

    🎯🎯🎯 LEMME N « pas de cardinal STRICTEMENT entre c et c+1 », INCONDITIONNEL modulo
    le SEUL est_cardinal(b) (structurel) — GEN est désormais PROUVÉE (et non plus une
    hypothèse).  Chaîne (toutes les briques de surgery sont des conditionnels CLOS qui
    prennent HD / retrait_surgery_hyp / (∀F)retrait_point_hyp en hypothèse, indépendants
    de la REPRÉSENTATION de GEN) :
        _hd_depuis_gen           ⊢ HD(b,c)                              [GEN déchargée]
        retrait_surgery_mod_HD   ⊢ HD ⇒ retrait_surgery_hyp(b,c,F)
        retrait_point_hyp_mod_surgery ⊢ retrait_surgery_hyp ⇒ retrait_point_hyp
        généralisation F         ⊢ (∀F)retrait_point_hyp(b,c,F)
        cardinal_pas_entre_conditionnel ⊢ (est_cardinal(b) et (∀F)rp) ⇒ cardinal_pas_entre.
    Conclusion == cardinal_pas_entre(b,c) sous est_cardinal(b) SEUL.  theorie=22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_surgery import (
        retrait_surgery_mod_HD, retrait_un_point_hypothese)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_retrait_point import retrait_point_hyp_mod_surgery
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_cardinal_pas_entre import (
        cardinal_pas_entre_conditionnel, retrait_point_hyp_universel)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal
    vb = _t(b)
    nomf = f if isinstance(f, str) else f.nom
    # HD(b,c)  (GEN déchargée par notre preuve)
    hd = _hd_depuis_gen(b, c, q)                            # ⊢ HD(b,c)  (CLOS)
    # HD ⇒ retrait_surgery_hyp(b,c,F)   (surgery, CLOS)
    hd2surg = retrait_surgery_mod_HD(b, c, f, q)           # ⊢ HD ⇒ retrait_surgery_hyp
    surg = N.modus_ponens(hd, hd2surg)                     # retrait_surgery_hyp(b,c,F)
    # retrait_surgery_hyp ⇒ retrait_point_hyp(b,c,F)   (retrait_point, CLOS)
    surg2rp = retrait_point_hyp_mod_surgery(b, c, f)       # ⊢ retrait_surgery_hyp ⇒ retrait_point_hyp
    rp = N.modus_ponens(surg, surg2rp)                     # retrait_point_hyp(b,c,F)
    rp_univ = N.generalisation(nomf, rp)                   # (∀F)retrait_point_hyp(b,c,F)
    assert rp_univ.conclusion == retrait_point_hyp_universel(b, c, f), \
        "(∀F)retrait_point_hyp ne matche pas retrait_point_hyp_universel"
    # (est_cardinal(b) et (∀F)rp) ⇒ cardinal_pas_entre(b,c)   (CLOS)
    cond = cardinal_pas_entre_conditionnel(b, c, f)
    ec = est_cardinal(vb)
    h_ec = N.assume(ec)
    cpe = N.modus_ponens(conjonction_intro(h_ec, rp_univ), cond)   # cardinal_pas_entre(b,c)  [hyp est_cardinal(b)]
    return N.loi_deduction(ec, cpe)                        # est_cardinal(b) ⇒ cardinal_pas_entre(b,c)


__all__ = ["image_diff", "eq_retrait_via_bijection", "eq_retrait_meme_ensemble",
           "gen_corps", "equipotence_retrait_un_point_general",
           "cardinal_pas_entre_inconditionnel"]
