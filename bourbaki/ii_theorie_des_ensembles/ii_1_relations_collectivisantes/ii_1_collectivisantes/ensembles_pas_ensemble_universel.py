"""Chapitre II §1.7 — « Il n'existe pas d'ensemble universel » (E II.6, Remarque).

Théorème (Bourbaki, E.II.6, Remarque n°7) :

    ⊢ ¬(∃X)(∀x)(x ∈ X)

« Il n'existe pas d'ensemble dont tous les objets soient éléments » — il n'y a pas
d'« ensemble de tous les ensembles ».  Énoncé CLOS (zéro hypothèse), corollaire
DIRECT du paradoxe de Russell (`non_collectivisante_appartenance_propre`, E.II.3 n°4 :
⊢ ¬Coll_x(x∉x)), comme dans le livre.

────────────────────────────────────────────────────────────────────────────────
STRATÉGIE (preuve de Bourbaki, E.II.6 Rem. → E.II.7 ; raisonnement par l'absurde)

  Bourbaki : « s'il existait un tel ensemble, toute relation serait collectivisante
  d'après C52.  Or [...] la relation x ∉ x n'est pas collectivisante. »  On reproduit
  FIDÈLEMENT cette preuve.

  H := (∃X)(∀x)(x ∈ X).  Par `N.existe_temoin` sur le corps (∀x)(x∈X), on obtient
  le témoin X0 := τX((∀x)(x∈X)) avec, SOUS H, (∀x)(x ∈ X0)  (« X0 contient tout »).

  ÉTAPE C52 (sélection S8 dans l'ensemble EXISTANT X0).  La relation « x∉x » est
  collectivisante DÈS QU'UN ensemble la borne : l'ensemble R0 := {x ∈ X0 | x∉x}
  existe (sélection S8 dans X0, unicité A1).  C'est exactement le mécanisme déjà
  employé pour la différence E∖Y, l'intervalle, ou la diagonale de Cantor
  D_{X,F} = {z∈X | ¬(z∈F(z))} (cf. `axiome_diagonale_cantor` / `theorie_diagonale_cantor`,
  utilisés dans la preuve certifiée du Théorème de Cantor).  On porte donc cette
  sélection par une THÉORIE DÉDIÉE `theorie_russell_dans(X0)`, paramétrée par X0 —
  `theorie_ensembles()` reste INCHANGÉE à 22 axiomes.

  De x ∈ R0 ⇔ (x∈X0 et x∉x) et de x∈X0 (vrai sous H pour tout x, car X0 contient
  tout), on tire x ∈ R0 ⇔ (x∉x) ; en généralisant sur x puis par S5 (témoin R0),

      SOUS H :  Coll_x(x∉x) = (∃y)(∀x)(x∈y ⇔ x∉x).

  Mais Russell donne ⊢ ¬Coll_x(x∉x).  Contradiction : H ⇒ Coll_x(x∉x) (déduction)
  et ¬Coll_x(x∉x) ⇒ ¬H (contraposition) donnent ⊢ ¬H par modus ponens.

INVARIANTS
  • conclusion == non(existe('X', pourtout('x', appartient(var('x'), var('X'))))).
  • est_clos == True : H est déchargée (déduction + contraposition), le témoin X0 et
    l'ensemble R0 sont ÉLIMINÉS du résultat ; AUCUN τ résiduel dans la conclusion.
  • theorie_ensembles() reste à 22 axiomes ; la sélection S8 de R0 vit dans une
    théorie DÉDIÉE paramétrée par X0 (mécanisme Bourbaki C52/S8, comme Cantor).
  • Le contenu EST Russell : sans `non_collectivisante_appartenance_propre`, rien ne
    se prouve (ce n'est pas une tautologie déguisée).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, tau, app, non, et, equiv, appartient,
                     existe, pourtout, coll)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instancie, conjonction_intro,
                               equivalence_avant, equivalence_arriere,
                               projection_droite, contraposition)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import non_collectivisante_appartenance_propre


def _russell_dans(b):
    """R_b := {x ∈ b | x ∉ x}  (ensemble de Russell SÉLECTIONNÉ dans l'ensemble b).

    Terme défini par sélection S8 dans l'ensemble b (unicité A1), exactement comme
    la différence E∖Y = {z | z∈E et ¬(z∈Y)} ou la diagonale de Cantor
    D_{X,F} = {z∈X | ¬(z∈F(z))} : ici le test borné est « ¬(x∈x) »."""
    return app("russell_dans", b)


def _axiome_russell_dans(b, x="x"):
    """⊢-schéma : (∀x)(x ∈ R_b ⇔ (x∈b et x∉x))  (instance de sélection S8 + A1).

    b est un PARAMÈTRE ; le liant interne est « x ».  Légitime — c'est la
    caractérisation d'appartenance d'un ensemble obtenu par sélection dans b, sur le
    MÊME modèle que `axiome_diagonale_cantor` (théorie dédiée, hors des 22 axiomes)."""
    vx = var(x)
    return pourtout(x, equiv(appartient(vx, _russell_dans(b)),
                             et(appartient(vx, b), non(appartient(vx, vx)))))


def _theorie_russell_dans(b, x="x"):
    """Théorie ne contenant que l'instance de l'axiome de R_b = {x∈b | x∉x}.

    Paramétrée par b (comme `theorie_diagonale_cantor` / `theorie_graphe_terme`) :
    `theorie_ensembles()` reste à 22 axiomes."""
    return N.Theorie("Russell-dans", [_axiome_russell_dans(b, x)])


# @livre Ch.II §1.7 Rem.- | E II.6 L.34-35 → E II.7 L.1-2 | PDF p.57
def pas_ensemble_universel():
    """⊢ ¬(∃X)(∀x)(x ∈ X).  (E.II.6, Remarque : pas d'ensemble universel ; CLOS.)

    Corollaire DIRECT de Russell, suivant la preuve de Bourbaki (E.II.6 Rem. →
    E.II.7).  Voir le docstring du module pour la stratégie complète."""
    inner = pourtout("x", appartient(var("x"), var("X")))   # (∀x)(x ∈ X)
    H = existe("X", inner)                                   # (∃X)(∀x)(x ∈ X)

    # ── témoin X0 : sous H, X0 contient tout objet ───────────────────────────────
    h_H = N.assume(H)
    inst = N.modus_ponens(h_H, N.existe_temoin(inner, "X"))  # {H} ⊢ (∀x)(x ∈ X0)
    X0 = tau("X", inner)                                     # X0 = τX((∀x)(x∈X))

    # ── R0 = {x ∈ X0 | x∉x} : sélection S8 dans X0 (théorie dédiée, C52) ──────────
    R0 = _russell_dans(X0)
    car = instancie(N.axiome(_theorie_russell_dans(X0), _axiome_russell_dans(X0)),
                    var("x"))                                # ⊢ (x∈R0) ⇔ (x∈X0 et x∉x)
    inX0 = appartient(var("x"), X0)
    notinx = non(appartient(var("x"), var("x")))

    # ── sous H : (x ∈ R0) ⇔ ¬(x∈x) ───────────────────────────────────────────────
    fwd = syllogisme(equivalence_avant(car),                # (x∈R0) ⇒ (x∈X0 et x∉x)
                     projection_droite(inX0, notinx))        # … ⇒ ¬(x∈x)
    x_in_X0 = instancie(inst, var("x"))                     # {H} ⊢ x ∈ X0
    h_notin = N.assume(notinx)                              # ¬(x∈x)
    x_in_R0 = N.modus_ponens(conjonction_intro(x_in_X0, h_notin),
                             equivalence_arriere(car))       # {H, ¬(x∈x)} ⊢ x ∈ R0
    bwd = N.loi_deduction(notinx, x_in_R0)                  # {H} ⊢ ¬(x∈x) ⇒ (x∈R0)
    equ = N.generalisation("x", conjonction_intro(fwd, bwd))  # {H} ⊢ (∀x)(x∈R0 ⇔ x∉x)

    # ── témoin R0 : sous H, Coll_x(x∉x) ; contradiction avec Russell ─────────────
    cf = coll("x", notinx)                                  # (∃y)(∀x)(x∈y ⇔ x∉x)
    s5 = N.s5(cf.sous[0], R0, cf.lieur)                     # ⊢ (R0|y)corps ⇒ Coll_x(x∉x)
    coll_sous_H = N.modus_ponens(equ, s5)                  # {H} ⊢ Coll_x(x∉x)

    russell = non_collectivisante_appartenance_propre("x")  # ⊢ ¬Coll_x(x∉x)
    H_imp_coll = N.loi_deduction(H, coll_sous_H)           # ⊢ H ⇒ Coll_x(x∉x)
    return N.modus_ponens(russell, contraposition(H_imp_coll))   # ⊢ ¬H


__all__ = ["pas_ensemble_universel"]
