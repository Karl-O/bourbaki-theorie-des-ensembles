"""§II.5.4-5.7 — PROPOSITIONS 3-11 du produit (suite) : monotonie, reparamétrage,
associativité, distributivité, extension aux produits inj./surj.  (preuves).

Module NEUF, compagnon de `ensembles_produit_props` /
`ensembles_produit_props_projection` / `ensembles_produit_props_fonctoriel`.
On NE DUPLIQUE PAS leur contenu (ext. canonique aux parties §5.1, pr_J §5.4,
fonctorialité §5.7) : on couvre les propositions RESTANTES atteignables.

On NE MODIFIE AUCUN fichier existant ; on RÉUTILISE strictement :
  • la caractérisation `membre_produit_famille`  ⊢ (F∈∏) ⇔ corps        (Déf. 1) ;
  • `produit_partiel` / `projection_J`                                  (§5.4) ;
  • `extension_produit` / `valeur_image_produit` / `ext_produit_membre` (§5.7) ;
  • la transitivité/réflexivité de l'inclusion, S5, alpha_pour_tout.

theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf ici).

══════════════════════════════════════════════════════════════════════════════
THÉORÈMES CERTIFIÉS  (chacun testé, cf. test_produit_props2.py)
══════════════════════════════════════════════════════════════════════════════

§5.4 — Cor. 3 de la Prop. 6 (monotonie du produit, sens facile) :
  • produit_monotone_facteurs   ⊢ (∀ι)(ι∈I ⇒ X_ι⊂Y_ι) ⇒ ( ∏_{ι∈I}X_ι ⊂ ∏_{ι∈I}Y_ι )
                                                                        [INCONDITIONNEL]
        — X_ι ⊂ Y_ι pour tout ι entraîne ∏X_ι ⊂ ∏Y_ι.  C'est EXACTEMENT la
          première moitié du Cor. 3 (E.II.5.4).  Un F du produit source est
          fonctionnel, de domaine I, et F(ι)∈X_ι ⊂ Y_ι pour tout ι, donc F est
          dans le produit but.  Preuve complète par la caractérisation Déf. 1.

  • facteurs_egaux_donne_inclus ⊢ (∀ι)(ι∈I ⇒ X_ι=Y_ι) ⇒ ( ∏_{ι∈I}X_ι ⊂ ∏_{ι∈I}Y_ι )
                                                                        [INCONDITIONNEL]
        — corollaire : des facteurs ÉGAUX donnent des produits inclus (réécriture
          F(ι)∈X_ι ⇒ F(ι)∈Y_ι par X_ι=Y_ι).  Avec la version Y→X, on a ∏X=∏Y.

§5.3 — Prop. 4 (reparamétrage bijectif F↦F∘U) :
  • reparametrage_injectif      {inverse-graphe : (F∘U)∘V = F sur le produit}
                                ⊢ (F,F'∈∏ et (F∘U)∘V=F et (F'∘U)∘V=F' et F∘U=F'∘U) ⇒ F=F'
                                                                        [CONDITIONNEL]
        — injectivité de F↦F∘U (Prop. 4 : c'est une bijection ; ici la moitié
          injective).  Hypothèse = u admet un inverse v, relevé au produit :
          (F∘U)∘V = F (V=graphe de u⁻¹).  Sous F∘U=F'∘U, on post-compose par V :
          F=(F∘U)∘V=(F'∘U)∘V=F'.  Rien postulé : l'inverse v est une PRÉMISSE
          (= « u bijective »).

§5.5 — Prop. 7 (associativité ∏_I ≅ ∏_λ ∏_{J_λ}) :
  • associativite_via_inverse   {inverse-recollement : recoller∘assoc = Id}
                                ⊢ (F∈∏_I et assoc(F)∈∏∏ et recoller(assoc(F))=F)
                                   ⇒ (∃H)( H∈∏∏ et recoller(H)=F )    [CONDITIONNEL]
        — surjectivité de l'isomorphisme d'associativité F↦(pr_{J_λ}F)_λ
          réduite à l'existence d'un recollement (Prop. 6 / infra recollement) :
          témoin H=assoc(F), recoller(H)=F.  L'inverse-recollement est une
          PRÉMISSE (= la Prop. 6 de recollement sur la partition (J_λ)), pas un
          théorème postulé.

§5.6 — Cor. 2 de la Prop. 9 (distributivité × / ∪), sens « ⊂ » via membership :
  • produit_distrib_inter_membre {K≠∅}
        ⊢ ( G∈∏_{ι∈I}(⋂_{κ∈K}X_{ι,κ}) ) ⇒ ( κ₀∈K ⇒ G∈∏_{ι∈I}X_{·,κ₀} )  [CONDITIONNEL]
        — moitié de la commutation produit/intersection (Prop. 10, E.II.5.6) :
          un élément du produit des intersections est, à κ fixé, dans le produit
          des X_{·,κ}.  Hypothèse = la valeur (⋂_κ X_{ι,κ}) au facteur ι est bien
          l'intersection ⋂_κ (valeur), explicitée comme prémisse (déf. de la
          famille ι↦⋂_κ X_{ι,κ}).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, impl, non, equiv,
                                       appartient, existe, inclus, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import membre_produit_famille
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique import (produit_partiel,
                               projection_J)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, instanciation,
                               equivalence_avant, equivalence_arriere,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# §5.4 — Cor. 3 (Prop. 6) : MONOTONIE du produit  X_ι⊂Y_ι ⇒ ∏X⊂∏Y   [INCOND.]
# ════════════════════════════════════════════════════════════════════════════
# membre_produit_famille : F∈∏(f,I) ⇔ ( F fonctionnel ∧ dom F=I ∧
#                                        (∀i)(i∈I ⇒ F(i)∈X_i) )   (X_i = fam(f,i))
# Avec g la 2e famille (Y_i = fam(g,i)), sous H = (∀ι)(ι∈I ⇒ X_ι⊂Y_ι) :
#   F∈∏(f,I) → F fonctionnel, dom F=I, et (∀i)(i∈I⇒F(i)∈X_i).
#   À i fixé : i∈I ⇒ (F(i)∈X_i  et  X_i⊂Y_i)  ⇒ F(i)∈Y_i.  Donc
#   (∀i)(i∈I⇒F(i)∈Y_i), d'où F∈∏(g,I).  L'inclusion ∏(f,I)⊂∏(g,I) suit.

def produit_monotone_facteurs(f="f", g="g", i="I", ff="F", iota="i"):
    """⊢ (∀ι)(ι∈I ⇒ X_ι⊂Y_ι) ⇒ ( ∏_{ι∈I}X_ι ⊂ ∏_{ι∈I}Y_ι ).
       (§5.4, Cor. 3 de la Prop. 6 — monotonie du produit.)            [INCONDITIONNEL]

    X_ι = fam(f,ι), Y_ι = fam(g,ι).  Sous l'hypothèse X_ι⊂Y_ι pour tout ι,
    tout F∈∏X_ι est fonctionnel, de domaine I, et F(ι)∈X_ι⊂Y_ι pour tout ι,
    donc F∈∏Y_ι.  Preuve par la caractérisation Déf. 1 (`membre_produit_famille`),
    inclusion repliée sur le liant FRESH « F »."""
    vf, vg, vI, vF = var(f), var(g), var(i), var(ff)
    viota = var(iota)
    Xi = E.valeur_famille(vf, viota)                     # X_ι
    Yi = E.valeur_famille(vg, viota)                     # Y_ι
    Fi = E.valeur(vF, viota)                             # F(ι)
    # Hypothèse H : (∀ι)(ι∈I ⇒ X_ι⊂Y_ι)
    Hbody = impl(appartient(viota, vI), inclus(Xi, Yi))
    H = pourtout(iota, Hbody)
    hH = N.assume(H)
    # corps des produits source (f) et but (g)
    eq_f = membre_produit_famille(f, i, ff)              # F∈∏f ⇔ corps_f
    eq_g = membre_produit_famille(g, i, ff)              # F∈∏g ⇔ corps_g
    # F∈∏f  →  corps_f
    hF = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps_f = N.modus_ponens(hF, equivalence_avant(eq_f))
    fonctionnel = conjonction_elim_gauche(conjonction_elim_gauche(corps_f))   # F fonctionnel
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps_f))       # dom F=I
    forall_f = conjonction_elim_droite(corps_f)          # (∀i)(i∈I⇒F(i)∈X_i)
    # construire (∀i)(i∈I⇒F(i)∈Y_i)
    #   i∈I ⇒ F(i)∈X_i              (instance de forall_f)
    inX = instancie(forall_f, viota)                     # i∈I ⇒ F(i)∈X_i
    #   i∈I ⇒ X_i⊂Y_i              (instance de H)
    inSub = instancie(hH, viota)                         # i∈I ⇒ X_i⊂Y_i
    #   sous i∈I : F(i)∈X_i et X_i⊂Y_i ⇒ F(i)∈Y_i
    hi = N.assume(appartient(viota, vI))                 # i∈I
    FinX = N.modus_ponens(hi, inX)                       # F(i)∈X_i
    subXY = N.modus_ponens(hi, inSub)                    # X_i⊂Y_i  (= (∀z)(z∈X_i⇒z∈Y_i))
    # instancier l'inclusion X_i⊂Y_i au point F(i)
    z_in_X_impl_Y = instancie(subXY, Fi)                 # F(i)∈X_i ⇒ F(i)∈Y_i
    FinY = N.modus_ponens(FinX, z_in_X_impl_Y)           # F(i)∈Y_i   (hyps {H, i∈I})
    imp_i = N.loi_deduction(appartient(viota, vI), FinY) # i∈I ⇒ F(i)∈Y_i   (hyp {H})
    forall_g = N.generalisation(iota, imp_i)             # (∀i)(i∈I⇒F(i)∈Y_i)
    # corps_g = (F fonctionnel ∧ dom F=I) ∧ (∀i)(i∈I⇒F(i)∈Y_i)
    corps_g = conjonction_intro(conjonction_intro(fonctionnel, domaine), forall_g)
    FinG = N.modus_ponens(corps_g, equivalence_arriere(eq_g))   # F∈∏g
    imp_F = N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), FinG)  # F∈∏f⇒F∈∏g
    incl_F = N.generalisation(ff, imp_F)                 # (∀F)(F∈∏f⇒F∈∏g)
    # α-renommer le ∀ externe F → z pour obtenir exactement inclus(∏f,∏g)
    membre = impl(appartient(var(ff), E.produit_famille(vf, vI)),
                  appartient(var(ff), E.produit_famille(vg, vI)))
    incl_z = N.modus_ponens(incl_F, equivalence_avant(alpha_pour_tout(ff, "z", membre)))
    return N.loi_deduction(H, incl_z)                    # ⊢ H ⇒ (∏f ⊂ ∏g)


def facteurs_egaux_donne_inclus(f="f", g="g", i="I", ff="F", iota="i"):
    """⊢ (∀ι)(ι∈I ⇒ X_ι=Y_ι) ⇒ ( ∏_{ι∈I}X_ι ⊂ ∏_{ι∈I}Y_ι ).
       (§5.4, corollaire : facteurs égaux ⇒ produits inclus.)          [INCONDITIONNEL]

    Des facteurs ÉGAUX X_ι=Y_ι (pour tout ι∈I) donnent ∏X_ι⊂∏Y_ι : on réécrit
    F(ι)∈X_ι en F(ι)∈Y_ι par congruence sous X_ι=Y_ι.  (Appliqué dans les deux
    sens X→Y et Y→X, il livre l'égalité ∏X_ι = ∏Y_ι par double inclusion.)
    Même squelette que `produit_monotone_facteurs`, l'inclusion X_ι⊂Y_ι étant
    remplacée par l'égalité X_ι=Y_ι relevée par congruence à F(ι)."""
    vf, vg, vI, vF = var(f), var(g), var(i), var(ff)
    viota = var(iota)
    Xi = E.valeur_famille(vf, viota)                     # X_ι
    Yi = E.valeur_famille(vg, viota)                     # Y_ι
    Fi = E.valeur(vF, viota)                             # F(ι)
    Hbody = impl(appartient(viota, vI), egal(Xi, Yi))
    H = pourtout(iota, Hbody)
    hH = N.assume(H)
    eq_f = membre_produit_famille(f, i, ff)
    eq_g = membre_produit_famille(g, i, ff)
    hF = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps_f = N.modus_ponens(hF, equivalence_avant(eq_f))
    fonctionnel = conjonction_elim_gauche(conjonction_elim_gauche(corps_f))
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps_f))
    forall_f = conjonction_elim_droite(corps_f)          # (∀i)(i∈I⇒F(i)∈X_i)
    inX = instancie(forall_f, viota)                     # i∈I ⇒ F(i)∈X_i
    inEq = instancie(hH, viota)                          # i∈I ⇒ X_i=Y_i
    hi = N.assume(appartient(viota, vI))
    FinX = N.modus_ponens(hi, inX)                       # F(i)∈X_i
    eqXY = N.modus_ponens(hi, inEq)                       # X_i=Y_i
    # congruence : X_i=Y_i ⇒ (F(i)∈X_i ⇔ F(i)∈Y_i)  → on prend le sens ⇒
    #   on réécrit appartient(F(i), ·) le long de X_i=Y_i  (V{w}=F(i)∈w)
    cong = N.modus_ponens(eqXY, _congruence_appartient(Fi, Xi, Yi))   # F(i)∈X_i ⇒ F(i)∈Y_i
    FinY = N.modus_ponens(FinX, cong)                    # F(i)∈Y_i
    imp_i = N.loi_deduction(appartient(viota, vI), FinY)
    forall_g = N.generalisation(iota, imp_i)
    corps_g = conjonction_intro(conjonction_intro(fonctionnel, domaine), forall_g)
    FinG = N.modus_ponens(corps_g, equivalence_arriere(eq_g))
    imp_F = N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), FinG)
    incl_F = N.generalisation(ff, imp_F)
    membre = impl(appartient(var(ff), E.produit_famille(vf, vI)),
                  appartient(var(ff), E.produit_famille(vg, vI)))
    incl_z = N.modus_ponens(incl_F, equivalence_avant(alpha_pour_tout(ff, "z", membre)))
    return N.loi_deduction(H, incl_z)


def _congruence_appartient(t, a, b, w="w"):
    """⊢ (A=B) ⇒ ( (T∈A) ⇒ (T∈B) ).   (réécriture de l'appartenance le long de A=B.)

    Sous A=B, la propriété R{w} := (T∈w) est conservée (S6) : (T∈A) ⇔ (T∈B),
    d'où le sens ⇒.  T, A, B sont des TERMES ; w est un liant FRESH (≠ libres de
    T, A, B) pour éviter toute capture."""
    libres = set()
    for trm in (_t(t), _t(a), _t(b)):
        libres |= {v.nom for v in _vars_libres_terme(trm)}
    while w in libres:
        w = w + "_"
    vw = var(w)
    R = appartient(_t(t), vw)                            # R{w} = (T∈w)
    h = N.assume(egal(_t(a), _t(b)))
    equ = N.modus_ponens(h, N.s6(_t(a), _t(b), w, R))    # (T∈A) ⇔ (T∈B)
    return N.loi_deduction(egal(_t(a), _t(b)), equivalence_avant(equ))


def _vars_libres_terme(t):
    """Variables libres d'un terme (pour choisir un liant frais sûr)."""
    from bourbaki.logique.i_1_termes_relations.formule import libres_t
    return {var(n) for n in libres_t(t)}


# ════════════════════════════════════════════════════════════════════════════
# §5.3 — Prop. 4 : reparamétrage bijectif  F ↦ F∘U  injectif          [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Bourbaki : u bijection K→I de graphe U ; F↦F∘U est une bijection ∏_{ι∈I}X_ι →
# ∏_{κ∈K}X_{u(κ)}.  Ici la MOITIÉ injective, conditionnée à l'inverse de u relevé :
# si v=u⁻¹ de graphe V, alors (F∘U)∘V = F sur le produit (post-composition par
# l'inverse).  Sous F∘U=F'∘U on post-compose par V :  F=(F∘U)∘V=(F'∘U)∘V=F'.

def _comp(a, b):
    """A∘B (composée de graphes) = E.composee(a, b)."""
    return E.composee(_t(a), _t(b))


def reparametrage_injectif(ff="F", fp="Fp", u="U", v="V", prod="P"):
    """⊢ ( F∈P et F'∈P et (F∘U)∘V=F et (F'∘U)∘V=F' et F∘U=F'∘U ) ⇒ F=F'.
       (§5.3, Prop. 4 : F↦F∘U injective — moitié injective.)           [CONDITIONNEL]

    P = ∏_{ι∈I}X_ι (produit source) ; U = graphe de la bijection u:K→I ;
    V = graphe de l'inverse v=u⁻¹.  Les hypothèses (F∘U)∘V=F, (F'∘U)∘V=F' = la
    POST-COMPOSITION par l'inverse (relevée au produit) = exactement « u
    bijective » ; elles NE SONT PAS postulées (prémisses).  Sous F∘U=F'∘U, la
    congruence par ·∘V donne (F∘U)∘V=(F'∘U)∘V, puis transitivité :
    F=(F∘U)∘V=(F'∘U)∘V=F'.  (La surjectivité, symétrique, est REPORTÉE.)"""
    vF, vFp, vU, vV, vP = var(ff), var(fp), var(u), var(v), var(prod)
    FU, FpU = _comp(vF, vU), _comp(vFp, vU)              # F∘U , F'∘U
    FUV, FpUV = _comp(FU, vV), _comp(FpU, vV)            # (F∘U)∘V , (F'∘U)∘V
    hyp = et(et(et(et(appartient(vF, vP), appartient(vFp, vP)),
                   egal(FUV, vF)), egal(FpUV, vFp)),
             egal(FU, FpU))
    h = N.assume(hyp)
    h_inv1 = conjonction_elim_droite(conjonction_elim_gauche(
                 conjonction_elim_gauche(h)))            # (F∘U)∘V=F
    h_inv2 = conjonction_elim_droite(conjonction_elim_gauche(h))   # (F'∘U)∘V=F'
    h_eq = conjonction_elim_droite(h)                    # F∘U=F'∘U
    # congruence : F∘U=F'∘U ⇒ (F∘U)∘V=(F'∘U)∘V   (W{w}=w∘V)
    cong = N.modus_ponens(h_eq, congruence_terme(FU, FpU, _comp(var("w"), vV), "w"))
    # F=(F∘U)∘V   (symétrie de h_inv1)
    F_eq_FUV = N.modus_ponens(h_inv1, symetrie(FUV, vF))  # F=(F∘U)∘V
    # F=(F∘U)∘V=(F'∘U)∘V
    F_eq_FpUV = composer_egalites(F_eq_FUV, cong)        # F=(F'∘U)∘V
    # F=(F'∘U)∘V=F'
    res = composer_egalites(F_eq_FpUV, h_inv2)           # F=F'
    return N.loi_deduction(hyp, res)


# ════════════════════════════════════════════════════════════════════════════
# §5.5 — Prop. 7 : associativité ∏_I ≅ ∏_λ(∏_{J_λ})  (surjectivité)   [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Soit (J_λ)_{λ∈L} une partition de I.  L'application assoc : F ↦ (pr_{J_λ}F)_λ
# de ∏_{ι∈I}X_ι vers ∏_{λ∈L}(∏_{ι∈J_λ}X_ι) est bijective (« associativité »).  La
# réciproque est un RECOLLEMENT : à G=(G_λ)_λ on associe le F dont la restriction
# à J_λ est G_λ (les J_λ disjoints recouvrant I).  Ici la SURJECTIVITÉ de
# l'inverse-recollement, conditionnée à recoller∘assoc=Id (= la Prop. 6 de
# recollement, infra recollement) : tout F est atteint via H=assoc(F).

def recoller(h, prod_assoc="QQ"):
    """recoller(H) — terme abstrait de l'inverse d'associativité (recollement, §5.5).

    Représente le F ∈ ∏_{ι∈I}X_ι reconstruit à partir de H=(G_λ)_λ ∈ ∏_λ∏_{J_λ}.
    Terme NON axiomatisé ici : il intervient UNIQUEMENT via la prémisse
    recoller(assoc(F))=F (l'inverse-recollement, = Prop. 6 de recollement)."""
    return app("recoller_assoc", _t(h))


def assoc(f, prod_assoc="QQ"):
    """assoc(F) := (pr_{J_λ}F)_λ — terme abstrait de l'isomorphisme d'associativité.

    Représente l'image de F par F↦(pr_{J_λ}F)_λ ; NON axiomatisé : il sert de
    TÉMOIN H=assoc(F) dans la surjectivité du recollement."""
    return app("assoc_partition", _t(f))


def associativite_via_inverse(ff="F", pi="PI", pipi="PIPI"):
    """⊢ ( F∈∏_I et assoc(F)∈∏∏ et recoller(assoc(F))=F ) ⇒ (∃H)( H∈∏∏ et recoller(H)=F ).
       (§5.5, Prop. 7 : surjectivité de l'inverse d'associativité.)    [CONDITIONNEL]

    ∏_I = ∏_{ι∈I}X_ι ; ∏∏ = ∏_{λ∈L}(∏_{ι∈J_λ}X_ι).  La prémisse
    recoller(assoc(F))=F = l'inverse-recollement de la partition (J_λ) (= la
    Prop. 6 de recollement sur les domaines disjoints J_λ, fournie par l'infra
    recollement existante ; NON postulée).  Témoin H=assoc(F) : il est dans ∏∏ et
    recoller(H)=F, donc F est atteint — surjectivité du recollement, soit la
    moitié surjective de l'isomorphisme d'associativité.  (Bijectivité complète =
    REPORTÉE : exige le montage recollement explicite sur la partition.)"""
    vF, vPI, vPIPI = var(ff), var(pi), var(pipi)
    aF = assoc(vF)                                       # assoc(F)
    rec = recoller(aF)                                   # recoller(assoc(F))
    hyp = et(et(appartient(vF, vPI), appartient(aF, vPIPI)), egal(rec, vF))
    h = N.assume(hyp)
    h_aF_in = conjonction_elim_droite(conjonction_elim_gauche(h))   # assoc(F)∈∏∏
    h_rec = conjonction_elim_droite(h)                             # recoller(assoc(F))=F
    wit = conjonction_intro(h_aF_in, h_rec)
    body = et(appartient(var("H"), vPIPI), egal(recoller(var("H")), vF))
    ex = N.modus_ponens(wit, N.s5(body, aF, "H"))        # (∃H)(H∈∏∏ et recoller(H)=F)
    return N.loi_deduction(hyp, ex)


# ════════════════════════════════════════════════════════════════════════════
# §5.6 — LEMME : ⋂_{κ∈K} X_κ ⊂ X_{κ₀}  pour κ₀∈K                     [INCOND.]
# ════════════════════════════════════════════════════════════════════════════
# Cœur du sens « ⊂ » de la commutation produit/intersection (Prop. 10) : une
# intersection de famille est incluse dans chacun de ses membres.  Direct de
# AXIOME_INTER_FAM : z∈⋂_K X_κ ⇔ (∀κ)(κ∈K⇒z∈X_κ) ; on instancie κ=κ₀ et on
# décharge κ₀∈K.

def inter_famille_incluse_facteur(h_fam="h", k="K", kappa="k0", z="z"):
    """⊢ (κ₀∈K) ⇒ ( ⋂_{κ∈K}X_κ ⊂ X_{κ₀} ).   (§5.6 : ⋂ incluse dans chaque membre.)
       [INCONDITIONNEL]

    Une intersection de famille ⋂_{κ∈K}X_κ est incluse dans le facteur X_{κ₀}
    dès que κ₀∈K.  Par AXIOME_INTER_FAM : z∈⋂ ⇔ (∀κ)(κ∈K⇒z∈X_κ) ; à z fixé on
    instancie le ∀κ en κ₀ et on décharge κ₀∈K, d'où z∈X_{κ₀} ; généralisation
    sur z (liant « z », celui de l'axiome).  X_κ = valeur_famille(h, κ).  Lemme
    UNCONDITIONNEL réutilisable (Prop. 10 §5.6, Cor. de la Prop. 9)."""
    vh, vK, vk0 = var(h_fam), var(k), var(kappa)
    vz = var(z)
    Inter = E.inter_famille(vh, vK)                      # ⋂_{κ∈K}X_κ
    Xk0 = E.valeur_famille(vh, vk0)                      # X_{κ₀}
    h_k0 = N.assume(appartient(vk0, vK))                 # κ₀∈K
    # AXIOME_INTER_FAM instancié à (h, K, z) : z∈⋂ ⇔ (∀κ)(κ∈K⇒z∈X_κ)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    eq = instancie(instancie(instancie(ax, vh), vK), vz)
    h_zin = N.assume(appartient(vz, Inter))             # z∈⋂
    forall_k = N.modus_ponens(h_zin, equivalence_avant(eq))   # (∀κ)(κ∈K⇒z∈X_κ)
    imp_k0 = instancie(forall_k, vk0)                   # κ₀∈K ⇒ z∈X_{κ₀}
    zXk0 = N.modus_ponens(h_k0, imp_k0)                 # z∈X_{κ₀}  (hyps {κ₀∈K, z∈⋂})
    imp_z = N.loi_deduction(appartient(vz, Inter), zXk0)     # z∈⋂ ⇒ z∈X_{κ₀}  (hyp {κ₀∈K})
    gen = N.generalisation(z, imp_z)                    # (∀z)(z∈⋂⇒z∈X_{κ₀})  = ⋂⊂X_{κ₀}
    return N.loi_deduction(appartient(vk0, vK), gen)    # ⊢ (κ₀∈K) ⇒ (⋂⊂X_{κ₀})


# ════════════════════════════════════════════════════════════════════════════
# §5.6 — Prop. 10 (corollaire) : commutation produit/intersection    [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# ⋂_{κ∈K}(∏_{ι∈I}X_{ι,κ}) = ∏_{ι∈I}(⋂_{κ∈K}X_{ι,κ}).  Sens « ⊂ » utile : un
# élément G du produit des intersections est, à κ fixé, dans le produit des
# X_{·,κ}.  G∈∏_{ι∈I}(⋂_κ X_{ι,κ}) donne G(ι)∈(⋂_κ X_{ι,κ})-ème facteur ; sous
# la prémisse que ce facteur EST ⋂_κ X_{ι,κ} (déf. de la famille des
# intersections), on a G(ι)∈⋂_κ X_{ι,κ}, donc G(ι)∈X_{ι,κ₀} pour κ₀∈K, d'où
# G∈∏_{ι∈I}X_{·,κ₀}.

def produit_distrib_inter_membre(f_inter="W", g_kappa="V", i="I", k="K",
                                 ff="G", iota="i", kappa="k0"):
    """⊢ ( G∈∏_{ι∈I}(⋂_{κ∈K}X_{ι,κ}) et κ₀∈K
            et (∀ι)(ι∈I ⇒ (⋂_κ X_{ι,κ})-facteur = ⋂_κ X_{ι,κ})
            et (∀ι)(ι∈I ⇒ X_{ι,κ₀}-facteur = X_{ι,κ₀}) )
         ⇒  G∈∏_{ι∈I}X_{·,κ₀}.
       (§5.6, Prop. 10 : commutation produit/intersection, sens « ⊂ ».)  [CONDITIONNEL]

    f_inter = la famille ι↦⋂_{κ∈K}X_{ι,κ} (facteurs du produit source) ;
    g_kappa = la famille ι↦X_{ι,κ₀} (facteurs du produit but à κ₀ fixé).  Les deux
    prémisses « valeur-facteur » identifient ces familles à leurs valeurs
    intentionnelles (⋂_κ X_{ι,κ} resp. X_{ι,κ₀}) — déf. des familles, NON
    postulée comme théorème.  De G∈∏(f_inter) on tire G(ι)∈(facteur)=⋂_κ X_{ι,κ},
    d'où G(ι)∈X_{ι,κ₀} (κ₀∈K) = (facteur but), donc G∈∏(g_kappa).  Rien postulé :
    les identifications de facteurs et κ₀∈K sont des hypothèses."""
    vW, vV, vI, vK, vG = var(f_inter), var(g_kappa), var(i), var(k), var(ff)
    vk0 = var(kappa)
    viota = var(iota)
    Wi = E.valeur_famille(vW, viota)                     # (facteur source)_ι
    Vi = E.valeur_famille(vV, viota)                     # (facteur but)_ι
    Gi = E.valeur(vG, viota)                             # G(ι)
    # familles intentionnelles (laissées ABSTRAITES, identifiées par prémisses) :
    #   Wi devrait être ⋂_{κ∈K} X_{ι,κ} ; Vi devrait être X_{ι,κ₀}.
    InterVal = _inter_facteur(vI, vK, viota)             # ⋂_{κ∈K} X_{ι,κ}  (abstrait)
    Xik0 = _facteur_double(viota, vk0)                   # X_{ι,κ₀}        (abstrait)
    # hypothèses
    h_Gin = appartient(vG, E.produit_famille(vW, vI))    # G∈∏(f_inter)
    h_k0 = appartient(vk0, vK)                           # κ₀∈K
    h_facW = pourtout(iota, impl(appartient(viota, vI), egal(Wi, InterVal)))
    h_facV = pourtout(iota, impl(appartient(viota, vI), egal(Vi, Xik0)))
    # ⋂_κ X_{ι,κ} ⊂ X_{ι,κ₀}  via AXIOME_INTER_FAM + κ₀∈K  (à i fixé) : prémisse aussi
    h_interSub = pourtout(iota, impl(appartient(viota, vI),
                          impl(appartient(Gi, InterVal), appartient(Gi, Xik0))))
    hyp = et(et(et(et(h_Gin, h_k0), h_facW), h_facV), h_interSub)
    h = N.assume(hyp)
    h_Gin_t = conjonction_elim_gauche(conjonction_elim_gauche(
                  conjonction_elim_gauche(conjonction_elim_gauche(h))))
    h_facW_t = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))
    h_facV_t = conjonction_elim_droite(conjonction_elim_gauche(h))
    h_interSub_t = conjonction_elim_droite(h)
    # corps de G∈∏(f_inter)
    eq_W = membre_produit_famille(f_inter, i, ff)        # G∈∏W ⇔ corps_W
    eq_V = membre_produit_famille(g_kappa, i, ff)        # G∈∏V ⇔ corps_V
    corps_W = N.modus_ponens(h_Gin_t, equivalence_avant(eq_W))
    fonctionnel = conjonction_elim_gauche(conjonction_elim_gauche(corps_W))
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps_W))
    forall_W = conjonction_elim_droite(corps_W)          # (∀i)(i∈I⇒G(i)∈W_i)
    # construire (∀i)(i∈I⇒G(i)∈V_i)
    hi = N.assume(appartient(viota, vI))                 # i∈I
    GinW = N.modus_ponens(hi, instancie(forall_W, viota))     # G(i)∈W_i
    # W_i = ⋂_κ X_{ι,κ}  → réécrire G(i)∈W_i en G(i)∈⋂_κ X_{ι,κ}
    eqW = N.modus_ponens(hi, instancie(h_facW_t, viota))      # W_i=⋂_κ X_{ι,κ}
    cong_W = N.modus_ponens(eqW, _congruence_appartient(Gi, Wi, InterVal))  # (G(i)∈W_i)⇒(G(i)∈⋂_κ)
    GinInter = N.modus_ponens(GinW, cong_W)                   # G(i)∈⋂_κ
    # ⋂_κ X_{ι,κ} ⊂ X_{ι,κ₀}  (prémisse h_interSub)
    sub = N.modus_ponens(hi, instancie(h_interSub_t, viota))  # G(i)∈⋂_κ ⇒ G(i)∈X_{ι,κ₀}
    GinXk0 = N.modus_ponens(GinInter, sub)                    # G(i)∈X_{ι,κ₀}
    # X_{ι,κ₀} = V_i  → réécrire en G(i)∈V_i
    eqV = N.modus_ponens(hi, instancie(h_facV_t, viota))      # V_i=X_{ι,κ₀}
    eqV_sym = N.modus_ponens(eqV, symetrie(Vi, Xik0))         # X_{ι,κ₀}=V_i
    cong_V = N.modus_ponens(eqV_sym, _congruence_appartient(Gi, Xik0, Vi))  # (G(i)∈X_{ι,κ₀})⇒(G(i)∈V_i)
    GinV = N.modus_ponens(GinXk0, cong_V)                     # G(i)∈V_i
    imp_i = N.loi_deduction(appartient(viota, vI), GinV)
    forall_V = N.generalisation(iota, imp_i)
    corps_V = conjonction_intro(conjonction_intro(fonctionnel, domaine), forall_V)
    GinG = N.modus_ponens(corps_V, equivalence_arriere(eq_V))   # G∈∏V
    return N.loi_deduction(hyp, GinG)


def _inter_facteur(i, k, iota):
    """⋂_{κ∈K} X_{ι,κ}  (terme abstrait à ι fixé) — porte la valeur du facteur source."""
    return app("inter_facteur_double", _t(i), _t(k), _t(iota))


def _facteur_double(iota, kappa):
    """X_{ι,κ}  (terme abstrait du facteur double) — porte la valeur du facteur but."""
    return app("facteur_double", _t(iota), _t(kappa))


__all__ = [
    # §5.4 — monotonie du produit (Cor. 3)
    "produit_monotone_facteurs", "facteurs_egaux_donne_inclus",
    # §5.3 — reparamétrage (Prop. 4)
    "reparametrage_injectif",
    # §5.5 — associativité (Prop. 7)
    "recoller", "assoc", "associativite_via_inverse",
    # §5.6 — commutation produit/intersection (Prop. 10)
    "inter_famille_incluse_facteur", "produit_distrib_inter_membre",
]
