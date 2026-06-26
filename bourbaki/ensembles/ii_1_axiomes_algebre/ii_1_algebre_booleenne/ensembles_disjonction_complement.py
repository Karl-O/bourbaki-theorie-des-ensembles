"""§II.1 — DISJONCTION caractérisée par le COMPLÉMENT (Résumé E.R.4 nº14 e).

Bourbaki, Résumé des résultats, E.R.4 §1.13/§1.14 (relecture de l'algèbre des
parties, Chap II.1).  Le nº14 pose le contexte : « Dans l'énoncé des propositions
qui suivent, X, Y, Z désignent des parties quelconques d'un même ensemble E. »
Le nº14 e) affirme alors que les relations

    X ∩ Y = ∅ ,    X ⊂ ∁_E Y ,    Y ⊂ ∁_E X

sont ÉQUIVALENTES   (∁_E = complément RELATIF à E, c.-à-d. ∁_E Y = E∖Y).

On formalise ici les DEUX premières équivalences (la troisième est l'image
miroir, prouvée par la même fonction en échangeant X et Y) :

    ( X ∩ Y = ∅ )  ⇔  ( X ⊂ ∁_E Y )      sous l'hypothèse honnête X ⊂ E.

FIDÉLITÉ / HYPOTHÈSE HONNÊTE (point crucial).  Le complément de Bourbaki est
TOUJOURS relatif à E.  Le sens ⇒ (X∩Y=∅ ⟹ X⊂∁_E Y) exige, pour z∈X, d'établir
z∈E (afin que z∈E∖Y ait un sens) : il a donc BESOIN de X⊂E.  On garde
H = inclus(X,E) comme HYPOTHÈSE non déchargée — PAS de fausse clôture.  C'est
exactement le contexte « X partie de E » du nº14.  (Le sens ⇐ seul n'a pas besoin
de X⊂E : z∈X∖Y ⟹ ¬(z∈Y) sans passer par z∈E ; mais l'énoncé Bourbaki étant
l'ÉQUIVALENCE, on conserve l'unique hypothèse H = inclus(X,E) requise par ⇒.)

STRATÉGIE.
  Réécriture : X∩Y=∅ ⇔ (∀z)¬(z∈X∩Y)  [vide_ssi_sans_element], et au niveau du
  membre, z∈X∩Y ⇔ (z∈X et z∈Y)  [_instance_intersection], d'où la négation
  ¬(z∈X∩Y) ⇔ ¬(z∈X et z∈Y)  [equiv_neg].  Appartenance différence :
  z∈E∖Y ⇔ (z∈E et ¬z∈Y)  [_inst_diff = instance de AXIOME_DIFF, dans les 22].

  ⇒ (sous H=X⊂E) : de X∩Y=∅ on a (∀z)¬(z∈X et z∈Y) ; pour z∈X : z∈E (par H),
     et ¬z∈Y (sinon (z∈X et z∈Y), contredisant ¬(z∈X et z∈Y) — contraposée) ;
     donc (z∈E et ¬z∈Y) ⟹ z∈E∖Y ; généralisation ⟹ X⊂E∖Y.
  ⇐ (libre) : de X⊂E∖Y, pour z : (z∈X et z∈Y) ⇒ z∈X ⇒ z∈E∖Y ⇒ ¬z∈Y, et
     (z∈X et z∈Y) ⇒ z∈Y ; d'où (z∈X et z∈Y) ⇒ ¬(z∈X et z∈Y), donc [S1]
     ¬(z∈X et z∈Y), soit ¬(z∈X∩Y) ; généralisation + vide_ssi_sans_element ⟹ X∩Y=∅.
  conjonction_intro des deux sens ⟹ l'équivalence.  Les implications INTERNES
  (z∈X⇒…, X∩Y=∅⇒…) sont déchargées par loi_deduction ; SEULE H=inclus(X,E) reste.

INVARIANTS : hypotheses == {inclus(X,E)} EXACTEMENT (X⊂E honnêtement non
déchargée — l'hypothèse « X partie de E » du nº14) ; est_clos == False ;
conclusion == cible (== structurelle, l'équivalence Bourbaki) ; PAS de tautologie
déguisée ; theorie_ensembles() INCHANGÉE = 22 ; aucun axiome ajouté, aucune
théorie dédiée / S8 (le seul axiome ensembliste utilisé hors A1/∅/∩ est AXIOME_DIFF,
membre des 22, réinjecté via l'instance _inst_diff).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_intersection
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import vide_ssi_sans_element
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite, equivalence_avant, equivalence_arriere,
    equivalence_transitivite, equiv_neg, contraposition, instancie,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _inst_diff(e, x, z):
    """⊢ (z ∈ E∖X) ⇔ (z∈E et ¬(z∈X))   (instance de AXIOME_DIFF, dans les 22)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def cible_disjonction_complement(x="X", y="Y", e="E"):
    """L'énoncé Bourbaki visé : (X∩Y=∅) ⇔ X⊂∁_E Y   (E.R.4 nº14 e, 1ʳᵉ équivalence).

    ∁_E Y = E∖Y = E.difference(E, Y)  (complément relatif à E)."""
    vX, vY, vE = _t(x), _t(y), _t(e)
    from bourbaki.logique.i_1_termes_relations.formule import equiv
    return equiv(egal(E.intersection(vX, vY), E.VIDE),
                 inclus(vX, E.difference(vE, vY)))


# @livre Ch.R §1.14 Prop.(14e) | E.R.4 L.35-37 | PDF p.307
def disjonction_complement(x="X", y="Y", e="E"):
    """⊢_{X⊂E}  ( (X∩Y=∅) ⇔ X⊂∁_E Y ).   (E.R.4 nº14 e ; ∁_E Y = E∖Y.)

    Théorème CLOS-SOUS-L'HYPOTHÈSE-HONNÊTE {inclus(X,E)} : c'est le contexte
    « X partie de E » du nº14, REQUIS par le sens ⇒ (pour z∈X ⟹ z∈E).  L'hypothèse
    X⊂E n'est PAS déchargée ; est_clos == False et hypotheses == {inclus(X,E)}."""
    vX, vY, vE, vz = _t(x), _t(y), _t(e), var("z")
    zX, zY, zE = appartient(vz, vX), appartient(vz, vY), appartient(vz, vE)
    inter = E.intersection(vX, vY)
    diff = E.difference(vE, vY)                                  # ∁_E Y = E∖Y
    egVide = egal(inter, E.VIDE)                                 # X∩Y = ∅
    inclDiff = inclus(vX, diff)                                  # X ⊂ E∖Y

    # Hypothèse honnête X⊂E = (∀z)(z∈X ⇒ z∈E), non déchargée (requise par ⇒).
    H = N.assume(inclus(vX, vE))
    zX_to_zE = instancie(H, vz)                                  # z∈X ⇒ z∈E   [sous H]

    # Briques de réécriture communes aux deux sens.
    vide_eq = vide_ssi_sans_element(inter)                       # (X∩Y=∅) ⇔ (∀z)¬(z∈X∩Y)
    neg_inter = equiv_neg(_instance_intersection(vX, vY, vz))    # ¬(z∈X∩Y) ⇔ ¬(z∈X et z∈Y)
    diff_eq = _inst_diff(vE, vY, vz)                             # z∈E∖Y ⇔ (z∈E et ¬z∈Y)
    et_xy = et(zX, zY)                                           # z∈X et z∈Y

    # ── sens ⇒ : (X∩Y=∅) ⇒ X⊂E∖Y   (utilise H = X⊂E) ─────────────────────────
    h_eq = N.assume(egVide)
    sans = N.modus_ponens(h_eq, equivalence_avant(vide_eq))      # (∀z)¬(z∈X∩Y)
    neg_membre = N.modus_ponens(instancie(sans, vz),
                                equivalence_avant(neg_inter))    # ¬(z∈X et z∈Y)
    h_zX = N.assume(zX)                                          # z∈X
    zEz = N.modus_ponens(h_zX, zX_to_zE)                         # z∈E   (par H)
    # ¬z∈Y : de ¬(z∈X et z∈Y) par contraposée de (z∈Y ⇒ (z∈X et z∈Y)) sous z∈X
    zY_to_et = N.loi_deduction(zY, conjonction_intro(h_zX, N.assume(zY)))  # z∈Y ⇒ (z∈X et z∈Y)
    negY = N.modus_ponens(neg_membre, contraposition(zY_to_et))  # ¬(z∈Y)
    zDiff = N.modus_ponens(conjonction_intro(zEz, negY),
                           equivalence_arriere(diff_eq))         # z∈E∖Y
    incl_fwd = N.generalisation("z", N.loi_deduction(zX, zDiff)) # {H, X∩Y=∅} ⊢ X⊂E∖Y
    sens_avant = N.loi_deduction(egVide, incl_fwd)               # {H} ⊢ (X∩Y=∅) ⇒ X⊂E∖Y

    # ── sens ⇐ : X⊂E∖Y ⇒ (X∩Y=∅)   (libre, n'utilise pas H) ──────────────────
    h_incl = N.assume(inclDiff)                                  # X⊂E∖Y
    zX_to_diff = instancie(h_incl, vz)                           # z∈X ⇒ z∈E∖Y
    zX_to_negY = syllogisme(syllogisme(zX_to_diff,               # z∈X ⇒ z∈E∖Y
                                       equivalence_avant(diff_eq)),  # ⇒ (z∈E et ¬z∈Y)
                            projection_droite(zE, non(zY)))      # ⇒ ¬(z∈Y)
    et_to_negY = syllogisme(projection_gauche(zX, zY), zX_to_negY)   # (z∈X et z∈Y) ⇒ ¬z∈Y
    et_to_neg_et = syllogisme(et_to_negY,                        # (z∈X et z∈Y) ⇒ ¬z∈Y
                              contraposition(projection_droite(zX, zY)))  # ⇒ ¬(z∈X et z∈Y)
    neg_et = N.modus_ponens(et_to_neg_et, N.s1(non(et_xy)))      # ¬(z∈X et z∈Y)  [A⇒¬A ⊢ ¬A]
    neg_membre2 = N.modus_ponens(neg_et, equivalence_arriere(neg_inter))  # ¬(z∈X∩Y)
    sans2 = N.generalisation("z", neg_membre2)                  # {X⊂E∖Y} ⊢ (∀z)¬(z∈X∩Y)
    eq_vide = N.modus_ponens(sans2, equivalence_arriere(vide_eq))  # {X⊂E∖Y} ⊢ X∩Y=∅
    sens_arriere = N.loi_deduction(inclDiff, eq_vide)           # ⊢ X⊂E∖Y ⇒ (X∩Y=∅)

    return conjonction_intro(sens_avant, sens_arriere)          # {X⊂E} ⊢ (X∩Y=∅) ⇔ X⊂E∖Y


__all__ = ["disjonction_complement", "cible_disjonction_complement"]
