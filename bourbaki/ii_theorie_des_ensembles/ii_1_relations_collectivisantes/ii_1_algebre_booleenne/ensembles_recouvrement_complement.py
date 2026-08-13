"""§II.1 — RECOUVREMENT caractérisé par le COMPLÉMENT (Résumé E.R.4 nº14 f).

Bourbaki, Résumé des résultats, E.R.4 §1.13/§1.14 (relecture de l'algèbre des
parties, Chap II.1).  Le nº14 pose le contexte : « Dans l'énoncé des propositions
qui suivent, X, Y, Z désignent des parties quelconques d'un même ensemble E. »
Le nº14 f) affirme alors que les relations

    X ∪ Y = E ,    ∁_E X ⊂ Y ,    ∁_E Y ⊂ X

sont ÉQUIVALENTES   (∁_E = complément RELATIF à E, c.-à-d. ∁_E X = E∖X).
C'est le DUAL de nº14 e) (disjonction / complément) déjà formalisé.

On formalise ici la PREMIÈRE équivalence (la troisième, ∁_E Y ⊂ X, est l'image
miroir, prouvée par la même fonction en échangeant X et Y) :

    ( X ∪ Y = E )  ⇔  ( ∁_E X ⊂ Y )      sous les hypothèses honnêtes X⊂E et Y⊂E.

FIDÉLITÉ / HYPOTHÈSES HONNÊTES (point crucial).  Le complément de Bourbaki est
TOUJOURS relatif à E, et le nº14 travaille « entre parties de E ».  L'équivalence
visée n'est valide que dans ce contexte ; on garde donc les inclusions
RÉELLEMENT requises comme hypothèses non déchargées (PAS de fausse clôture) :

  • Sens ⇐ (∁X⊂Y ⟹ X∪Y=E).  Pour bâtir l'égalité X∪Y=E par extensionnalité il
    faut les DEUX inclusions :
       – X∪Y ⊂ E : pour z∈X∪Y, soit z∈X (⟹ z∈E par X⊂E), soit z∈Y (⟹ z∈E par
         Y⊂E) ; ce demi-sens utilise H_X = X⊂E ET H_Y = Y⊂E.
       – E ⊂ X∪Y : pour z∈E, par tiers exclu sur z∈X ; si z∈X alors z∈X∪Y ; sinon
         (z∈E et ¬z∈X) ⟹ z∈E∖X ⟹ z∈Y (par ∁X⊂Y) ⟹ z∈X∪Y.  (ce demi-sens
         n'utilise PAS H_X, H_Y.)
  • Sens ⇒ (X∪Y=E ⟹ ∁X⊂Y).  Pour z∈∁X = (z∈E et ¬z∈X) : de X∪Y=E (congruence
    de =, S6) z∈E ⟹ z∈X∪Y ⟹ (z∈X ou z∈Y) ; avec ¬z∈X, syllogisme disjonctif
    ⟹ z∈Y.  (ce sens n'utilise PAS H_X, H_Y.)

  → l'ensemble EXACT des hypothèses non déchargées est { X⊂E , Y⊂E }, toutes deux
    imposées par le demi-sens « X∪Y⊂E » du ⇐.  C'est exactement le contexte
    « X, Y parties de E » du nº14.

STRATÉGIE.
  Appartenances de base (sans hypothèse) :
    z∈X∪Y ⇔ (z∈X ou z∈Y)        [_instance_reunion = instance de AXIOME_REUNION]
    z∈E∖X ⇔ (z∈E et ¬z∈X)       [_inst_diff       = instance de AXIOME_DIFF, 22]
  ⇒ : congruence de = (S6) déplie X∪Y=E en (z∈X∪Y ⇔ z∈E), d'où z∈E⟹(z∈X ou z∈Y) ;
      pour z∈E∖X on a z∈E et ¬z∈X, le syllogisme disjonctif (disj_syll_thm)
      donne z∈Y ; généralisation ⟹ ∁X⊂Y ; décharge de X∪Y=E.
  ⇐ : (cas) z∈X∪Y⟹(z∈X ou z∈Y)⟹z∈E (sous H_X,H_Y) ⟹ X∪Y⊂E ; (tiers exclu+cas)
      z∈E⟹z∈X∪Y ⟹ E⊂X∪Y ; extensionnalite_appliquee bâtit X∪Y=E ; décharge de ∁X⊂Y.
  conjonction_intro des deux sens ⟹ l'équivalence.  Les implications INTERNES
  sont déchargées par loi_deduction ; SEULES H_X=X⊂E et H_Y=Y⊂E restent.

INVARIANTS : hypotheses == {inclus(X,E), inclus(Y,E)} EXACTEMENT (les deux
« parties de E » du nº14, requises par le demi-sens X∪Y⊂E du ⇐) ; est_clos ==
False ; conclusion == cible (== structurelle, l'équivalence Bourbaki) ; PAS de
tautologie déguisée ; theorie_ensembles() INCHANGÉE = 22 ; aucun axiome ajouté,
aucune théorie dédiée / S8 (les seuls axiomes ensemblistes utilisés sont
AXIOME_REUNION et AXIOME_DIFF, membres des 22, réinjectés via _instance_reunion
et _inst_diff ; l'extensionnalité A1 via extensionnalite_appliquee).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, ou, non, appartient, inclus, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee, _instance_reunion)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, projection_gauche, projection_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
    disj_syll_thm, tiers_exclu,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))   (instance de AXIOME_DIFF, dans les 22)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def cible_recouvrement_complement(x="X", y="Y", e="E"):
    """L'énoncé Bourbaki visé : (X∪Y=E) ⇔ ∁_E X⊂Y   (E.R.4 nº14 f, 1ʳᵉ équivalence).

    ∁_E X = E∖X = E.difference(E, X)  (complément relatif à E)."""
    vX, vY, vE = _t(x), _t(y), _t(e)
    return equiv(egal(E.reunion(vX, vY), vE),
                 inclus(E.difference(vE, vX), vY))


# @livre Ch.R §1.14 Prop.(14f) | E.R.4 L.38-40 | PDF p.307
def recouvrement_complement(x="X", y="Y", e="E"):
    """⊢_{X⊂E, Y⊂E}  ( (X∪Y=E) ⇔ ∁_E X⊂Y ).   (E.R.4 nº14 f ; ∁_E X = E∖X.)

    Théorème CLOS-SOUS-LES-HYPOTHÈSES-HONNÊTES {inclus(X,E), inclus(Y,E)} : c'est
    le contexte « X, Y parties de E » du nº14, REQUIS par le demi-sens X∪Y⊂E du
    ⇐ (z∈X⟹z∈E et z∈Y⟹z∈E).  Les inclusions X⊂E et Y⊂E ne sont PAS déchargées ;
    est_clos == False et hypotheses == {inclus(X,E), inclus(Y,E)}."""
    vX, vY, vE, vz = _t(x), _t(y), _t(e), var("z")
    zX, zY, zE = appartient(vz, vX), appartient(vz, vY), appartient(vz, vE)
    union = E.reunion(vX, vY)
    diff = E.difference(vE, vX)                                  # ∁_E X = E∖X
    egE = egal(union, vE)                                        # X∪Y = E
    zdiff = appartient(vz, diff)                                 # z ∈ E∖X
    inclDiff = inclus(diff, vY)                                  # ∁X ⊂ Y
    ou_xy = ou(zX, zY)                                           # z∈X ou z∈Y

    # Briques d'appartenance communes aux deux sens (sans hypothèse).
    reunion_eq = _instance_reunion(vX, vY, vz)                   # z∈X∪Y ⇔ (z∈X ∨ z∈Y)
    diff_eq = _inst_diff(vE, vX, vz)                             # z∈E∖X ⇔ (z∈E ∧ ¬z∈X)

    # Hypothèses honnêtes X⊂E, Y⊂E = (∀z)(z∈· ⇒ z∈E), non déchargées (requises par ⇐).
    HX = N.assume(inclus(vX, vE))
    HY = N.assume(inclus(vY, vE))
    zX_to_zE = instancie(HX, vz)                                 # z∈X ⇒ z∈E   [sous HX]
    zY_to_zE = instancie(HY, vz)                                 # z∈Y ⇒ z∈E   [sous HY]

    # ── sens ⇒ : (X∪Y=E) ⇒ (∁X ⊂ Y)   (libre, n'utilise PAS HX, HY) ──────────
    h_eq = N.assume(egE)                                         # X∪Y = E
    leib = N.s6(union, vE, "w", appartient(vz, var("w")))        # (U=E) ⇒ ((z∈U)⇔(z∈E))
    zU_iff_zE = N.modus_ponens(h_eq, leib)                       # {U=E} ⊢ (z∈U ⇔ z∈E)
    zE_to_ou = syllogisme(equivalence_arriere(zU_iff_zE),        # z∈E ⇒ z∈X∪Y
                          equivalence_avant(reunion_eq))         # ⇒ (z∈X ∨ z∈Y)
    h_zdiff = N.assume(zdiff)                                    # z∈E∖X
    et_zEnX = N.modus_ponens(h_zdiff, equivalence_avant(diff_eq))    # (z∈E ∧ ¬z∈X)
    z_in_E = N.modus_ponens(et_zEnX, projection_gauche(zE, non(zX)))     # z∈E
    z_not_X = N.modus_ponens(et_zEnX, projection_droite(zE, non(zX)))    # ¬z∈X
    ou_zXzY = N.modus_ponens(z_in_E, zE_to_ou)                  # (z∈X ∨ z∈Y)
    # syllogisme disjonctif : (z∈X∨z∈Y) ⇒ (¬z∈X ⇒ z∈Y)
    ds = N.modus_ponens(ou_zXzY, disj_syll_thm(zX, zY))         # (¬z∈X ⇒ z∈Y)
    z_in_Y = N.modus_ponens(z_not_X, ds)                       # z∈Y
    incl_fwd = N.generalisation("z", N.loi_deduction(zdiff, z_in_Y))  # {U=E} ⊢ ∁X⊂Y
    sens_avant = N.loi_deduction(egE, incl_fwd)                # ⊢ (X∪Y=E) ⇒ ∁X⊂Y

    # ── sens ⇐ : (∁X ⊂ Y) ⇒ (X∪Y=E)   (utilise HX, HY pour X∪Y⊂E) ───────────
    h_incl = N.assume(inclDiff)                                 # ∁X ⊂ Y
    zdiff_to_zY = instancie(h_incl, vz)                        # z∈E∖X ⇒ z∈Y

    # (a) X∪Y ⊂ E : z∈X∪Y ⇒ (z∈X ∨ z∈Y) ⇒ z∈E   (par cas, sous HX, HY)
    ou_to_zE = cas(N.assume(ou_xy), zX_to_zE, zY_to_zE)        # {ou_xy,HX,HY} ⊢ z∈E
    zunion_to_zE = syllogisme(equivalence_avant(reunion_eq),    # z∈X∪Y ⇒ (z∈X∨z∈Y)
                              N.loi_deduction(ou_xy, ou_to_zE)) # ⇒ z∈E
    incl_union_E = N.generalisation("z", zunion_to_zE)         # {HX,HY} ⊢ X∪Y ⊂ E

    # (b) E ⊂ X∪Y : z∈E ⇒ z∈X∪Y  (tiers exclu sur z∈X, puis cas)
    h_zE = N.assume(zE)                                        # z∈E
    zX_to_zunion = syllogisme(N.s2(zX, zY),                    # z∈X ⇒ (z∈X∨z∈Y)
                              equivalence_arriere(reunion_eq)) # ⇒ z∈X∪Y
    h_nzX = N.assume(non(zX))                                  # ¬z∈X
    z_in_diff = N.modus_ponens(conjonction_intro(h_zE, h_nzX),
                               equivalence_arriere(diff_eq))   # {z∈E,¬z∈X} ⊢ z∈E∖X
    z_in_Y_b = N.modus_ponens(z_in_diff, zdiff_to_zY)          # z∈Y
    zY_to_zunion = syllogisme(N.s3(zY, zX),                    # z∈Y ⇒ (z∈X∨z∈Y)  [via z∈Y∨z∈X]
                              equivalence_arriere(reunion_eq)) # ⇒ z∈X∪Y
    z_in_union_b = N.modus_ponens(z_in_Y_b,
                                  syllogisme(N.s2(zY, zX), zY_to_zunion))  # z∈X∪Y
    nzX_to_zunion = N.loi_deduction(non(zX), z_in_union_b)     # {∁X⊂Y,z∈E} ⊢ ¬z∈X ⇒ z∈X∪Y
    z_in_union_E = cas(tiers_exclu(zX), zX_to_zunion, nzX_to_zunion)  # {∁X⊂Y,z∈E} ⊢ z∈X∪Y
    incl_E_union = N.generalisation("z", N.loi_deduction(zE, z_in_union_E))  # {∁X⊂Y} ⊢ E⊂X∪Y

    # extensionnalité (A1) : (X∪Y⊂E et E⊂X∪Y) ⇒ X∪Y=E
    ext = extensionnalite_appliquee(union, vE)
    eq_UE = N.modus_ponens(conjonction_intro(incl_union_E, incl_E_union), ext)  # X∪Y=E
    sens_arriere = N.loi_deduction(inclDiff, eq_UE)           # {HX,HY} ⊢ ∁X⊂Y ⇒ X∪Y=E

    return conjonction_intro(sens_avant, sens_arriere)        # {X⊂E,Y⊂E} ⊢ (X∪Y=E)⇔∁X⊂Y


__all__ = ["recouvrement_complement", "cible_recouvrement_complement"]
