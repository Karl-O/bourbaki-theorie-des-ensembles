"""§III.3.2 — Propositions DIVERSES sur l'ordre ≤ des cardinaux : INVARIANCE de ≤
par équipotence (et corollaires directs).

L'ordre ≤ de Bourbaki est défini ENTRE CARDINAUX (E.III.3.1-2), c'est-à-dire entre
classes d'équipotence : « x ≤ y » ne dépend QUE des classes de x et y.  Au niveau
des ensembles représentants, cela se traduit par la propriété d'INVARIANCE :

    si Eq(X, X')  et  Eq(Y, Y'),  alors   X ≤ Y   ⇔   X' ≤ Y'.

C'est exactement ce qui légitime de parler de l'ordre « entre cardinaux » et non
seulement « entre ensembles ».  Bourbaki l'invoque implicitement (la relation ≤
est compatible avec l'équipotence) ; on la CERTIFIE ici, INCONDITIONNELLEMENT, en
assemblant trois théorèmes déjà clos du noyau :

  • equipotence_implique_inf_egal  (ensembles_cardinaux_ordre)  : Eq(X,Y) ⇒ X≤Y ;
  • equipotence_symetrique         (ensembles_bijection)        : Eq(X,Y) ⇒ Eq(Y,X) ;
  • inf_egal_transitive            (ensembles_cardinaux_ordre)  : (X≤Y et Y≤Z)⇒X≤Z.

THÉORÈMES (tous CLOS, 0 hypothèse ; variables X, X', Y, Y' libres distinctes) :

  (1) `equipotence_implique_inf_egal_inverse`  ⊢ Eq(X, Y) ⇒ (Y ≤ X).
      (Eq(X,Y) ⇒ Eq(Y,X) ⇒ Y ≤ X : la « petite » des deux inégalités manquantes.)

  (2) `equipotents_mutuellement_inf_egal`  ⊢ Eq(X, Y) ⇒ (X ≤ Y  et  Y ≤ X).
      (deux ensembles équipotents se majorent mutuellement ; demi-trivial de
      l'antisymétrie de Cantor–Bernstein, dans le sens FACILE.)

  (3) `inf_egal_invariant_gauche`  ⊢ Eq(X, X') ⇒ ((X ≤ Y) ⇒ (X' ≤ Y)).
      (remplacer le membre GAUCHE par un ensemble équipotent : X'≤X (via Eq(X,X')
      symétrisé) puis X'≤X≤Y par transitivité.)

  (4) `inf_egal_invariant_droite`  ⊢ Eq(Y, Y') ⇒ ((X ≤ Y) ⇒ (X ≤ Y')).
      (remplacer le membre DROIT : X≤Y et Y≤Y' (via Eq(Y,Y')) → X≤Y' par transitivité.)

  (5) `inf_egal_invariant_equipotence`
      ⊢ (Eq(X, X')  et  Eq(Y, Y'))  ⇒  ((X ≤ Y)  ⇒  (X' ≤ Y')).
      🎯 INVARIANCE PLEINE de ≤ : compose (3) et (4).  C'est la compatibilité de
      l'ordre cardinal avec l'équipotence (E.III.3.2).

RIEN POSTULÉ, RIEN AFFAIBLI : chaque énoncé est une implication littérale assemblée
par modus ponens / syllogisme / loi de déduction à partir de théorèmes déjà certifiés.
theorie_ensembles() reste à 22 axiomes (aucun axiome introduit).

Les théorèmes du noyau réutilisés (equipotence_implique_inf_egal, etc.) attendent des
NOMS DE VARIABLES (chaînes), pas des termes arbitraires ; on travaille donc avec des
variables libres distinctes X, Xp, Y, Yp — ce qui est l'énoncé d'invariance voulu et
se généralise/instancie librement.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, equipotent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import (equipotence_implique_inf_egal,
                               inf_egal_transitive)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  Eq(X, Y) ⇒ (Y ≤ X)   —   le sens « inverse » de equipotence_implique_inf_egal
# ═══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.2 Rem.- | E III.24 L.11-14 | PDF p.127
#   (l'ordre ≤ est défini ENTRE CARDINAUX : « elle équivaut aussi à la relation
#    "Card(X) est équipotent à une partie de Card(Y)" » — l'invariance de ≤ par
#    équipotence, implicite dans le livre, est certifiée dans ce module.)
def equipotence_implique_inf_egal_inverse(x="X", y="Y"):
    """⊢ Eq(X, Y) ⇒ (Y ≤ X).   (E.III.3.2 ; via symétrie de Eq puis injection.)

    De Eq(X,Y) on tire Eq(Y,X) (equipotence_symetrique), puis Y ≤ X
    (equipotence_implique_inf_egal au couple (Y,X)).  Syllogisme des deux."""
    sym = equipotence_symetrique("F", x, y)                  # Eq(X,Y) ⇒ Eq(Y,X)
    inj = equipotence_implique_inf_egal("F", y, x)           # Eq(Y,X) ⇒ Y ≤ X
    return syllogisme(sym, inj)                              # Eq(X,Y) ⇒ Y ≤ X


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  Eq(X, Y) ⇒ (X ≤ Y  et  Y ≤ X)   —   les deux inégalités à la fois
# ═══════════════════════════════════════════════════════════════════════════════
def equipotents_mutuellement_inf_egal(x="X", y="Y"):
    """⊢ Eq(X, Y) ⇒ (X ≤ Y et Y ≤ X).   (deux équipotents se majorent mutuellement.)

    Sous l'hypothèse Eq(X,Y) : X ≤ Y (equipotence_implique_inf_egal) ET Y ≤ X
    (1, ci-dessus) ; on assemble la conjonction puis on décharge."""
    vX, vY = var(x), var(y)
    h = N.assume(equipotent(vX, vY))                         # Eq(X,Y)
    le_xy = N.modus_ponens(h, equipotence_implique_inf_egal("F", x, y))     # X ≤ Y
    le_yx = N.modus_ponens(h, equipotence_implique_inf_egal_inverse(x, y))  # Y ≤ X
    conj = conjonction_intro(le_xy, le_yx)                   # X≤Y et Y≤X
    return N.loi_deduction(equipotent(vX, vY), conj)         # Eq(X,Y) ⇒ (X≤Y et Y≤X)


# ═══════════════════════════════════════════════════════════════════════════════
# (3)  Eq(X, X') ⇒ ((X ≤ Y) ⇒ (X' ≤ Y))   —   invariance du membre GAUCHE
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_invariant_gauche(x="X", xp="Xp", y="Y"):
    """⊢ Eq(X, X') ⇒ ((X ≤ Y) ⇒ (X' ≤ Y)).   (remplacement gauche par équipotent.)

    De Eq(X,X') on tire X' ≤ X (1, equipotence_implique_inf_egal_inverse au couple
    (X,X')).  Sous X≤Y : (X'≤X et X≤Y) donne X'≤Y (inf_egal_transitive au triplet
    (X',X,Y)).  On décharge X≤Y puis Eq(X,X')."""
    vX, vXp, vY = var(x), var(xp), var(y)
    hEq = N.assume(equipotent(vX, vXp))                      # Eq(X,X')
    xp_le_x = N.modus_ponens(hEq,
        equipotence_implique_inf_egal_inverse(x, xp))        # X' ≤ X   [sous Eq(X,X')]
    hle = N.assume(inf_egal_card(vX, vY))                    # X ≤ Y
    trans = inf_egal_transitive("F", "G", xp, x, y)          # (X'≤X et X≤Y) ⇒ X'≤Y
    xp_le_y = N.modus_ponens(conjonction_intro(xp_le_x, hle), trans)  # X' ≤ Y
    inner = N.loi_deduction(inf_egal_card(vX, vY), xp_le_y)  # (X≤Y) ⇒ (X'≤Y)  [sous Eq]
    return N.loi_deduction(equipotent(vX, vXp), inner)       # Eq(X,X') ⇒ ((X≤Y)⇒(X'≤Y))


# ═══════════════════════════════════════════════════════════════════════════════
# (4)  Eq(Y, Y') ⇒ ((X ≤ Y) ⇒ (X ≤ Y'))   —   invariance du membre DROIT
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_invariant_droite(x="X", y="Y", yp="Yp"):
    """⊢ Eq(Y, Y') ⇒ ((X ≤ Y) ⇒ (X ≤ Y')).   (remplacement droit par équipotent.)

    De Eq(Y,Y') on tire Y ≤ Y' (equipotence_implique_inf_egal au couple (Y,Y')).
    Sous X≤Y : (X≤Y et Y≤Y') donne X≤Y' (inf_egal_transitive au triplet (X,Y,Y'))."""
    vX, vY, vYp = var(x), var(y), var(yp)
    hEq = N.assume(equipotent(vY, vYp))                      # Eq(Y,Y')
    y_le_yp = N.modus_ponens(hEq,
        equipotence_implique_inf_egal("F", y, yp))           # Y ≤ Y'   [sous Eq(Y,Y')]
    hle = N.assume(inf_egal_card(vX, vY))                    # X ≤ Y
    trans = inf_egal_transitive("F", "G", x, y, yp)          # (X≤Y et Y≤Y') ⇒ X≤Y'
    x_le_yp = N.modus_ponens(conjonction_intro(hle, y_le_yp), trans)  # X ≤ Y'
    inner = N.loi_deduction(inf_egal_card(vX, vY), x_le_yp)  # (X≤Y) ⇒ (X≤Y')  [sous Eq]
    return N.loi_deduction(equipotent(vY, vYp), inner)       # Eq(Y,Y') ⇒ ((X≤Y)⇒(X≤Y'))


# ═══════════════════════════════════════════════════════════════════════════════
# (5)  INVARIANCE PLEINE :
#      (Eq(X,X') et Eq(Y,Y')) ⇒ ((X ≤ Y) ⇒ (X' ≤ Y'))
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_invariant_equipotence(x="X", xp="Xp", y="Y", yp="Yp"):
    """⊢ (Eq(X, X') et Eq(Y, Y')) ⇒ ((X ≤ Y) ⇒ (X' ≤ Y')).

    🎯 COMPATIBILITÉ de l'ordre cardinal avec l'équipotence (E.III.3.2).  Compose les
    invariances (3) et (4) : sous Eq(X,X') et Eq(Y,Y') et X≤Y, on a d'abord X≤Y'
    (par (4), invariance droite avec Eq(Y,Y')), puis X'≤Y' (par (3), invariance
    gauche avec Eq(X,X'), appliquée à X≤Y')."""
    vX, vXp, vY, vYp = var(x), var(xp), var(y), var(yp)
    hEqX = N.assume(equipotent(vX, vXp))                     # Eq(X,X')
    hEqY = N.assume(equipotent(vY, vYp))                     # Eq(Y,Y')
    hle = N.assume(inf_egal_card(vX, vY))                    # X ≤ Y
    # X ≤ Y'   (invariance droite : Eq(Y,Y') puis X≤Y ⇒ X≤Y')
    droite = inf_egal_invariant_droite(x, y, yp)             # Eq(Y,Y')⇒((X≤Y)⇒(X≤Y'))
    x_le_yp = N.modus_ponens(hle, N.modus_ponens(hEqY, droite))      # X ≤ Y'
    # X' ≤ Y'  (invariance gauche : Eq(X,X') puis X≤Y' ⇒ X'≤Y')
    gauche = inf_egal_invariant_gauche(x, xp, yp)            # Eq(X,X')⇒((X≤Y')⇒(X'≤Y'))
    xp_le_yp = N.modus_ponens(x_le_yp, N.modus_ponens(hEqX, gauche))  # X' ≤ Y'
    inner = N.loi_deduction(inf_egal_card(vX, vY), xp_le_yp)  # (X≤Y)⇒(X'≤Y')  [sous les 2 Eq]
    # décharge des deux équipotences sous forme de conjonction unique
    conj = et(equipotent(vX, vXp), equipotent(vY, vYp))
    h2 = N.assume(conj)
    inner_chargee = N.loi_deduction(equipotent(vX, vXp),
                      N.loi_deduction(equipotent(vY, vYp), inner))
    inner2 = N.modus_ponens(conjonction_elim_droite(h2),
              N.modus_ponens(conjonction_elim_gauche(h2), inner_chargee))
    return N.loi_deduction(conj, inner2)


# ═══════════════════════════════════════════════════════════════════════════════
# (6)-(7)  FORMES ÉQUIVALENCE (⇔) : Eq(X,Y) ⇒ ((X≤Z) ⇔ (Y≤Z)),  etc.
#          Plus fortes que (3)/(4) : les deux sens du remplacement à la fois.
# ═══════════════════════════════════════════════════════════════════════════════
def inf_egal_equivalence_gauche(x="X", y="Y", z="Z"):
    """⊢ Eq(X, Y) ⇒ ((X ≤ Z) ⇔ (Y ≤ Z)).   (le membre GAUCHE de ≤ ne compte qu'à
    équipotence près — forme ⇔, plus forte que l'implication (3)).

    Sens ⇒ : Eq(X,Y) donne (via (3) au couple (X,Y))  (X≤Z) ⇒ (Y≤Z).
    Sens ⇐ : Eq(Y,X) (symétrie de Eq(X,Y)) donne (via (3) au couple (Y,X))
             (Y≤Z) ⇒ (X≤Z).  On assemble l'équivalence sous Eq(X,Y)."""
    vX, vY = var(x), var(y)
    h = N.assume(equipotent(vX, vY))                         # Eq(X,Y)
    # (X≤Z) ⇒ (Y≤Z)
    fwd = N.modus_ponens(h, inf_egal_invariant_gauche(x, y, z))   # (X≤Z)⇒(Y≤Z)
    # Eq(Y,X) via symétrie, puis (Y≤Z) ⇒ (X≤Z)
    eq_yx = N.modus_ponens(h, equipotence_symetrique("F", x, y))  # Eq(Y,X)
    bwd = N.modus_ponens(eq_yx, inf_egal_invariant_gauche(y, x, z))   # (Y≤Z)⇒(X≤Z)
    equiv = conjonction_intro(fwd, bwd)                      # (X≤Z) ⇔ (Y≤Z)
    return N.loi_deduction(equipotent(vX, vY), equiv)        # Eq(X,Y) ⇒ ((X≤Z)⇔(Y≤Z))


def inf_egal_equivalence_droite(z="Z", x="X", y="Y"):
    """⊢ Eq(X, Y) ⇒ ((Z ≤ X) ⇔ (Z ≤ Y)).   (le membre DROIT de ≤ ne compte qu'à
    équipotence près — forme ⇔, plus forte que l'implication (4)).

    Sens ⇒ : Eq(X,Y) donne (via (4))  (Z≤X) ⇒ (Z≤Y).
    Sens ⇐ : Eq(Y,X) (symétrie) donne (via (4))  (Z≤Y) ⇒ (Z≤X)."""
    vX, vY = var(x), var(y)
    h = N.assume(equipotent(vX, vY))                         # Eq(X,Y)
    fwd = N.modus_ponens(h, inf_egal_invariant_droite(z, x, y))   # (Z≤X)⇒(Z≤Y)
    eq_yx = N.modus_ponens(h, equipotence_symetrique("F", x, y))  # Eq(Y,X)
    bwd = N.modus_ponens(eq_yx, inf_egal_invariant_droite(z, y, x))   # (Z≤Y)⇒(Z≤X)
    equiv = conjonction_intro(fwd, bwd)                      # (Z≤X) ⇔ (Z≤Y)
    return N.loi_deduction(equipotent(vX, vY), equiv)        # Eq(X,Y) ⇒ ((Z≤X)⇔(Z≤Y))


__all__ = [
    "equipotence_implique_inf_egal_inverse",
    "equipotents_mutuellement_inf_egal",
    "inf_egal_invariant_gauche",
    "inf_egal_invariant_droite",
    "inf_egal_invariant_equipotence",
    "inf_egal_equivalence_gauche",
    "inf_egal_equivalence_droite",
]
