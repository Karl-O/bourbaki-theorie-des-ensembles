"""§III.1.4 — C58 (E III.5) : x ≤ y ⇔ (x < y ou x = y), instance cardinale. CLOS.

Bourbaki (E III.5 L.7-9) : « La relation x ≤ y est équivalente à "x < y ou
x = y" ; les relations "x ≤ y et y < z", "x < y et y ≤ z" entraînent x < z. »

Ce module DÉRIVE la PREMIÈRE partie (l'équivalence) pour l'ordre des cardinaux
du dépôt, où l'ordre strict est DÉFINITIONNEL :  x < y := (x ≤ y et x ≠ y)
(inf_strict_card).  Route (équivalente à celle du livre, qui invoque C24) :

  (⇒)  sous x≤y, tiers exclu sur x=y : si x=y, injection droite ; sinon
       (x≤y et ¬(x=y)) EST x<y (définition), injection gauche ; cas().
  (⇐)  par cas() : x<y ⇒ x≤y (élimination de conjonction) ; x=y ⇒ x≤y
       (Leibniz S6 sur x≤x, réflexivité inf_egal_reflexif, CLOS).

La SECONDE partie (transitivités mixtes) est DÉRIVÉE ici aussi
(`c58_trans_gauche`, `c58_trans_droite`, E III.5 L.8-15) : route exacte du livre —
x≤z par transitivité de ≤ (inf_egal_transitive_general, close), et x≠z car x=z
entraînerait, via l'antisymétrie cardinale (inf_egal_antisymetrique_card =
Cantor–Bernstein, close), l'égalité contraire à la partie stricte de l'hypothèse.
L'antisymétrie portant des gardes est_cardinal, ces deux théorèmes sont clos
MODULO { card(y),card(z) } (resp. { card(x),card(y) }) — résidus honnêtes.

Partie 1 : THÉORÈME CLOS, 0 hypothèse. theorie_ensembles = 22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, ou, non, egal, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    syllogisme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    tiers_exclu, cas, conjonction_intro, conjonction_elim_gauche,
    conjonction_elim_droite, equivalence_avant, equivalence_arriere,
    contraposition, instancie)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    inf_egal_reflexif)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_transitive_general, inf_egal_antisymetrique_card)


def c58_enonce(x: str = "x58", y: str = "y58"):
    """L'énoncé-cible :  ( x ≤ y ) ⟺ ( x < y  ou  x = y )."""
    vx, vy = var(x), var(y)
    return equiv(inf_egal_card(vx, vy),
                 ou(inf_strict_card(vx, vy), egal(vx, vy)))


# @livre Ch.III §1.4 Crit.58 | E III.5 L.7-9 | PDF p.108  (partie 1, l'équivalence — DÉRIVÉE ici ; partie 2 [transitivités mixtes] à part)
# @livre Ch.III §1.4 Demo.- | E III.5 L.10-15 | PDF p.108  (démo de la partie 1 ; la route du dépôt [tiers exclu + Leibniz S6] est équivalente à celle du livre [C24])
def c58_ordre_strict(x: str = "x58", y: str = "y58"):
    """🎯 ⊢ ( x ≤ y ) ⟺ ( x < y  ou  x = y ).   (THÉORÈME CLOS, 0 hyp.)

    Conclusion ÉGALE LITTÉRALEMENT c58_enonce(x, y)."""
    vx, vy = var(x), var(y)
    A = inf_egal_card(vx, vy)                      # x ≤ y
    Eq = egal(vx, vy)                              # x = y
    Lt = inf_strict_card(vx, vy)                   # x < y  (== et(A, ¬Eq) littéral)
    assert Lt == et(A, non(Eq)), "inf_strict_card n'est plus définitionnel ?"
    B = ou(Lt, Eq)

    # ── (⇒)  A ⇒ B ───────────────────────────────────────────────────────────
    h = N.assume(A)                                # x ≤ y                [à décharger]
    te = tiers_exclu(Eq)                           # ⊢ Eq ∨ ¬Eq
    # cas Eq : Eq ⇒ (Eq ∨ Lt) ⇒ (Lt ∨ Eq)
    branche_eq = syllogisme(N.s2(Eq, Lt), N.s3(Eq, Lt))        # ⊢ Eq ⇒ B
    # cas ¬Eq : sous h, (A et ¬Eq) EST Lt ; injection gauche
    h_ne = N.assume(non(Eq))                       # ¬Eq                  [à décharger]
    lt = conjonction_intro(h, h_ne)                # {A, ¬Eq} ⊢ Lt   (littéralement)
    b_g = N.modus_ponens(lt, N.s2(Lt, Eq))         # {A, ¬Eq} ⊢ B
    branche_ne = N.loi_deduction(non(Eq), b_g)     # {A} ⊢ ¬Eq ⇒ B
    b_de_a = cas(te, branche_eq, branche_ne)       # {A} ⊢ B
    imp_ab = N.loi_deduction(A, b_de_a)            # ⊢ A ⇒ B

    # ── (⇐)  B ⇒ A ───────────────────────────────────────────────────────────
    # cas Lt : x<y ⇒ x≤y  (élimination gauche de la conjonction définitionnelle)
    h_lt = N.assume(Lt)
    branche_lt = N.loi_deduction(Lt, conjonction_elim_gauche(h_lt))   # ⊢ Lt ⇒ A
    # cas Eq : x=y ⇒ x≤y  (Leibniz sur x≤·, depuis x≤x réflexif CLOS)
    refl = inf_egal_reflexif(x)                    # ⊢ x ≤ x   (CLOS)
    leib = N.s6(vx, vy, "w58", inf_egal_card(vx, var("w58")))  # (x=y) ⇒ (x≤x ⇔ x≤y)
    h_eq = N.assume(Eq)
    eqv = N.modus_ponens(h_eq, leib)               # {Eq} ⊢ (x≤x ⇔ x≤y)
    a_de_eq = N.modus_ponens(refl, equivalence_avant(eqv))     # {Eq} ⊢ A
    branche_eq2 = N.loi_deduction(Eq, a_de_eq)     # ⊢ Eq ⇒ A
    h_b = N.assume(B)
    a_de_b = cas(h_b, branche_lt, branche_eq2)     # {B} ⊢ A
    imp_ba = N.loi_deduction(B, a_de_b)            # ⊢ B ⇒ A

    # ── équivalence ──────────────────────────────────────────────────────────
    res = conjonction_intro(imp_ab, imp_ba)        # ⊢ A ⟺ B
    assert res.conclusion == c58_enonce(x, y), "C58 : conclusion ≠ énoncé"
    assert not res.hypotheses, "C58 : hypothèses non déchargées"
    return res                                     # CLOS, 0 hyp


def _trans(u, v, w):
    """⊢ ( u≤v et v≤w ) ⇒ u≤w   (transitivité de ≤, aux TERMES)."""
    g = inf_egal_transitive_general("Xtr", "Ytr", "Ztr")
    return instancie(instancie(instancie(g, u), v), w)


def _antisym(u, v):
    """⊢ ( u≤v et v≤u et card(u) et card(v) ) ⇒ u=v   (antisymétrie cardinale, aux TERMES)."""
    g = inf_egal_antisymetrique_card("uas", "vas")
    return instancie(instancie(g, u), v)


# @livre Ch.III §1.4 Crit.58 | E III.5 L.8-9 | PDF p.108  (partie 2 : transitivités mixtes)
# @livre Ch.III §1.4 Demo.- | E III.5 L.10-15 | PDF p.108  (démo partie 2 : « chacune entraîne x≤z par transitivité ; x=z entraînerait x=y=z, contraire à l'hypothèse »)
def c58_trans_gauche(x: str = "x58", y: str = "y58", z: str = "z58"):
    """🎯 { card(y), card(z) } ⊢ ( x≤y et y<z ) ⇒ x<z   (C58 partie 2, 1ᵉ relation).

    Route livre (instance cardinale) : x≤z par transitivité(x≤y, y≤z) ; x≠z car
    x=z donnerait z≤y (Leibniz sur x≤y) donc, avec y≤z, y=z par antisymétrie —
    contraire à y<z.  Contraposée : ¬(y=z) ⇒ ¬(x=z)."""
    vx, vy, vz = var(x), var(y), var(z)
    le_xy = inf_egal_card(vx, vy)
    lt_yz = inf_strict_card(vy, vz)                 # = et(y≤z, ¬(y=z))
    hyp = et(le_xy, lt_yz)
    card_y = N.assume(est_cardinal(vy))
    card_z = N.assume(est_cardinal(vz))

    h = N.assume(hyp)
    h_xy = conjonction_elim_gauche(h)               # x≤y
    h_ltyz = conjonction_elim_droite(h)             # y<z
    h_yz = conjonction_elim_gauche(h_ltyz)          # y≤z
    y_ne_z = conjonction_elim_droite(h_ltyz)        # ¬(y=z)

    le_xz = N.modus_ponens(conjonction_intro(h_xy, h_yz), _trans(vx, vy, vz))  # x≤z

    # x=z ⇒ y=z : (x=z) donne z≤y (Leibniz x↦z dans ·≤y), puis antisym(y,z)
    h_eq_xz = N.assume(egal(vx, vz))
    leib = N.s6(vx, vz, "w58t", inf_egal_card(var("w58t"), vy))   # (x=z) ⇒ (x≤y ⇔ z≤y)
    le_zy = N.modus_ponens(h_xy, equivalence_avant(N.modus_ponens(h_eq_xz, leib)))  # z≤y
    eq_yz = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_intro(h_yz, le_zy),
                                            card_y), card_z),
        _antisym(vy, vz))                           # y=z
    imp_xz_yz = N.loi_deduction(egal(vx, vz), eq_yz)             # (x=z) ⇒ (y=z)
    x_ne_z = N.modus_ponens(y_ne_z, contraposition(imp_xz_yz))  # ¬(x=z)

    lt_xz = conjonction_intro(le_xz, x_ne_z)        # x<z (== et(x≤z, ¬(x=z)))
    assert lt_xz.conclusion == inf_strict_card(vx, vz), "x<z non définitionnel ?"
    res = N.loi_deduction(hyp, lt_xz)               # (x≤y et y<z) ⇒ x<z
    assert res.hypotheses == frozenset({est_cardinal(vy), est_cardinal(vz)}), \
        "C58 g : hypothèses ≠ {card(y),card(z)}"
    return res


# @livre Ch.III §1.4 Crit.58 | E III.5 L.8-9 | PDF p.108  (partie 2 : transitivités mixtes)
# @livre Ch.III §1.4 Demo.- | E III.5 L.10-15 | PDF p.108
def c58_trans_droite(x: str = "x58", y: str = "y58", z: str = "z58"):
    """🎯 { card(x), card(y) } ⊢ ( x<y et y≤z ) ⇒ x<z   (C58 partie 2, 2ᵉ relation).

    Symétrique de c58_trans_gauche : x≤z par transitivité ; x≠z car x=z donnerait
    y≤x (Leibniz z↦x dans y≤·), donc, avec x≤y, x=y par antisymétrie — contraire
    à x<y.  Contraposée : ¬(x=y) ⇒ ¬(x=z)."""
    vx, vy, vz = var(x), var(y), var(z)
    lt_xy = inf_strict_card(vx, vy)                 # = et(x≤y, ¬(x=y))
    le_yz = inf_egal_card(vy, vz)
    hyp = et(lt_xy, le_yz)
    card_x = N.assume(est_cardinal(vx))
    card_y = N.assume(est_cardinal(vy))

    h = N.assume(hyp)
    h_ltxy = conjonction_elim_gauche(h)             # x<y
    h_xy = conjonction_elim_gauche(h_ltxy)          # x≤y
    x_ne_y = conjonction_elim_droite(h_ltxy)        # ¬(x=y)
    h_yz = conjonction_elim_droite(h)               # y≤z

    le_xz = N.modus_ponens(conjonction_intro(h_xy, h_yz), _trans(vx, vy, vz))  # x≤z

    # x=z ⇒ x=y : (x=z) donne y≤x (Leibniz z↦x dans y≤·), puis antisym(x,y)
    h_eq_xz = N.assume(egal(vx, vz))
    leib = N.s6(vx, vz, "w58t", inf_egal_card(vy, var("w58t")))   # (x=z) ⇒ (y≤x ⇔ y≤z)
    le_yx = N.modus_ponens(h_yz, equivalence_arriere(N.modus_ponens(h_eq_xz, leib)))  # y≤x
    eq_xy = N.modus_ponens(
        conjonction_intro(conjonction_intro(conjonction_intro(h_xy, le_yx),
                                            card_x), card_y),
        _antisym(vx, vy))                           # x=y
    imp_xz_xy = N.loi_deduction(egal(vx, vz), eq_xy)            # (x=z) ⇒ (x=y)
    x_ne_z = N.modus_ponens(x_ne_y, contraposition(imp_xz_xy))  # ¬(x=z)

    lt_xz = conjonction_intro(le_xz, x_ne_z)        # x<z
    assert lt_xz.conclusion == inf_strict_card(vx, vz), "x<z non définitionnel ?"
    res = N.loi_deduction(hyp, lt_xz)               # (x<y et y≤z) ⇒ x<z
    assert res.hypotheses == frozenset({est_cardinal(vx), est_cardinal(vy)}), \
        "C58 d : hypothèses ≠ {card(x),card(y)}"
    return res


__all__ = ["c58_enonce", "c58_ordre_strict",
           "c58_trans_gauche", "c58_trans_droite"]
