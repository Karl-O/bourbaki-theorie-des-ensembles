"""Chapitre III §2 — Ensembles bien ordonnés : définitions + théorèmes DIRECTS.

Tous les résultats sont CERTIFIÉS par le noyau abrégé (type Theoreme opaque).
Une relation R{x,y} = fonction Python (Terme, Terme) → Formule (pattern §II.6 / §III.1).
R est notée ≤ : R{a,b} = a≤b.

Théorèmes (E.III.2.1) :
 - bien_ordonne_est_ordonne        : E bien ordonné ⟹ E ordonné par R
 - ensemble_est_segment            : ⊢ E est un segment de E
 - vide_est_segment                : ⊢ ∅ est un segment de E
 - segment_inclus                  : S segment de E ⟹ S⊂E
 - intersection_segments_segment   : A,B segments de E ⟹ A∩B segment de E
 - reunion_segments_segment        : A,B segments de E ⟹ A∪B segment de E

REPORTÉ honnêtement (infrastructure absente — voir rapport) : Prop. 1-4,
Lemmes 1-4, Théorème 1 (Zermelo), Théorème 2 (Zorn), Théorème 3, et les
critères C59/C60 (récurrence / définition par récurrence transfinie).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, et, ou, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               projection_gauche, projection_droite,
                               equivalence_avant, equivalence_arriere)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion, _instance_intersection


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


# ── §III.2.1, Définition 1 — un ensemble bien ordonné est ordonné ─────────────
# @livre Ch.III §2.1 Def.1 | E III.15 L.30-32 | PDF p.118
def bien_ordonne_est_ordonne(R, e="E"):
    """⊢ est_bien_ordonne(R,E) ⇒ est_relation_ordre_dans(R,E).

    La Définition 1 (E.III.2.1) est une conjonction « E ordonné  et  toute
    partie non vide a un plus petit élément » ; la projection gauche donne
    « E ordonné »."""
    ve = _terme(e)
    hyp = E.est_bien_ordonne(R, ve)
    H = N.assume(hyp)
    return N.loi_deduction(hyp, conjonction_elim_gauche(H))


# ── §III.2.1, Définition 2 — segments triviaux et clôture ─────────────────────
# @livre Ch.III §2.1 Def.2 | E III.16 L.8-13 | PDF p.119
def ensemble_est_segment(R, e="E", x="x", y="y"):
    """⊢ E est un segment de E   (E.III.2.1 : « E lui-même est un segment de E »).

    S=E : E⊂E (réflexivité de ⊂) ; et le corps ((x∈E et y∈E et y≤x)⇒y∈E) tient
    car y∈E est la deuxième composante de la prémisse (projection)."""
    ve = _terme(e)
    vx, vy = var(x), var(y)
    # (1)  E ⊂ E
    sub = N.generalisation("z", _a_implique_a(appartient(var("z"), ve)))
    # (2)  (∀x)(∀y)(((x∈E et y∈E) et y≤x) ⇒ y∈E)
    premisse = et(et(appartient(vx, ve), appartient(vy, ve)), R(vy, vx))
    Hp = N.assume(premisse)
    y_in = projection_droite(appartient(vx, ve), appartient(vy, ve))   # (x∈E et y∈E)⇒y∈E
    concl = N.modus_ponens(conjonction_elim_gauche(Hp), y_in)          # y∈E
    body = N.loi_deduction(premisse, concl)
    body = N.generalisation(x, N.generalisation(y, body))
    return conjonction_intro(sub, body)


def _a_implique_a(f):
    """⊢ f ⇒ f."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
    return a_implique_a(f)


# @livre Ch.III §2.1 Def.2 | E III.16 L.8-13 | PDF p.119
def vide_est_segment(R, e="E", x="x", y="y"):
    """⊢ ∅ est un segment de E   (E.III.2.1 : « l'ensemble vide est un segment de E »).

    S=∅ : ∅⊂E (ex falso depuis ¬(z∈∅)) ; et le corps tient car la prémisse
    contient x∈∅, fausse, donc l'implication est vraie (ex falso)."""
    ve = _terme(e)
    vx, vy = var(x), var(y)
    vz = var("z")
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)
    # (1)  ∅ ⊂ E  : (∀z)(z∈∅ ⇒ z∈E).  De ⊢¬(z∈∅), S2 → ¬(z∈∅)∨(z∈E) = (z∈∅⇒z∈E).
    not_z = instancie(ax_vide, vz)                                     # ¬(z∈∅)
    z_imp = N.modus_ponens(not_z, N.s2(not_z.conclusion, appartient(vz, ve)))
    sub = N.generalisation("z", z_imp)                                # ∅⊂E
    # (2)  corps : ((x∈∅ et y∈E) et y≤x) ⇒ y∈∅.  Ex falso depuis ¬(x∈∅).
    premisse = et(et(appartient(vx, E.VIDE), appartient(vy, ve)), R(vy, vx))
    Hp = N.assume(premisse)
    x_in_vide = conjonction_elim_gauche(conjonction_elim_gauche(Hp))  # x∈∅
    not_x = instancie(ax_vide, vx)                                    # ¬(x∈∅)
    # ex falso : de ⊢¬(x∈∅), S2 donne ¬(x∈∅)∨(y∈∅) = (x∈∅)⇒(y∈∅) ; MP avec x∈∅.
    x_imp_y = N.modus_ponens(not_x, N.s2(not_x.conclusion, appartient(vy, E.VIDE)))
    faux = N.modus_ponens(x_in_vide, x_imp_y)                         # y∈∅
    body = N.loi_deduction(premisse, faux)
    body = N.generalisation(x, N.generalisation(y, body))
    return conjonction_intro(sub, body)


# @livre Ch.III §2.1 Def.2 | E III.16 L.8-9 | PDF p.119
def segment_inclus(R, S="S", e="E", x="x", y="y"):
    """⊢ est_segment(S,R,E) ⇒ S⊂E   (la première composante de la Définition 2)."""
    vS, ve = _terme(S), _terme(e)
    hyp = E.est_segment(vS, R, ve, x, y)
    H = N.assume(hyp)
    return N.loi_deduction(hyp, conjonction_elim_gauche(H))


# ── §III.2.1 — « toute intersection / réunion de segments est un segment » ────
# @livre Ch.III §2.1 Def.2 | E III.16 L.10-13 | PDF p.119
def intersection_segments_segment(R, A="A", B="B", e="E", x="x", y="y"):
    """⊢ (est_segment(A,R,E) et est_segment(B,R,E)) ⇒ est_segment(A∩B,R,E).

    (E.III.2.1 : « toute intersection ou réunion de segments de E est un segment
    de E ».)"""
    vA, vB, ve = _terme(A), _terme(B), _terme(e)
    vx, vy = var(x), var(y)
    AinterB = E.intersection(vA, vB)
    hyp = et(E.est_segment(vA, R, ve, x, y), E.est_segment(vB, R, ve, x, y))
    H = N.assume(hyp)
    segA, segB = conjonction_elim_gauche(H), conjonction_elim_droite(H)
    subA, bodyA = conjonction_elim_gauche(segA), conjonction_elim_droite(segA)
    subB, bodyB = conjonction_elim_gauche(segB), conjonction_elim_droite(segB)

    # (1)  A∩B ⊂ E  : z∈A∩B ⇒ z∈A ⇒ z∈E
    vz = var("z")
    memb = _instance_intersection(vA, vB, vz)                  # z∈A∩B ⇔ (z∈A et z∈B)
    z_in_A = syllogisme(equivalence_avant(memb),
                        projection_gauche(appartient(vz, vA), appartient(vz, vB)))  # z∈A∩B⇒z∈A
    incA = instancie(subA, vz)                                 # z∈A⇒z∈E
    sub = N.generalisation("z", syllogisme(z_in_A, incA))      # A∩B⊂E

    # (2)  corps : ((x∈A∩B et y∈E) et y≤x) ⇒ y∈A∩B
    premisse = et(et(appartient(vx, AinterB), appartient(vy, ve)), R(vy, vx))
    Hp = N.assume(premisse)
    x_in_AB = conjonction_elim_gauche(conjonction_elim_gauche(Hp))  # x∈A∩B
    y_in_E = conjonction_elim_droite(conjonction_elim_gauche(Hp))   # y∈E
    yx = conjonction_elim_droite(Hp)                               # y≤x
    memx = _instance_intersection(vA, vB, vx)                     # x∈A∩B ⇔ (x∈A et x∈B)
    x_A_B = N.modus_ponens(x_in_AB, equivalence_avant(memx))      # x∈A et x∈B
    x_in_A = projection_gauche(appartient(vx, vA), appartient(vx, vB))
    x_in_A = N.modus_ponens(x_A_B, x_in_A)                       # x∈A
    x_in_B = N.modus_ponens(x_A_B, projection_droite(appartient(vx, vA), appartient(vx, vB)))  # x∈B
    # y∈A et y∈B : appliquer bodyA, bodyB en (x,y) avec les prémisses prouvées
    y_in_A = _force_premisse(bodyA, vx, vy, x_in_A, y_in_E, yx)
    y_in_B = _force_premisse(bodyB, vx, vy, x_in_B, y_in_E, yx)
    y_in_AB = N.modus_ponens(conjonction_intro(y_in_A, y_in_B),
                             equivalence_arriere(_instance_intersection(vA, vB, vy)))  # y∈A∩B
    body = N.loi_deduction(premisse, y_in_AB)
    body = N.generalisation(x, N.generalisation(y, body))
    concl = conjonction_intro(sub, body)
    return N.loi_deduction(hyp, concl)


# @livre Ch.III §2.1 Def.2 | E III.16 L.10-13 | PDF p.119
def reunion_segments_segment(R, A="A", B="B", e="E", x="x", y="y"):
    """⊢ (est_segment(A,R,E) et est_segment(B,R,E)) ⇒ est_segment(A∪B,R,E).

    (E.III.2.1 : « toute réunion de segments de E est un segment de E ».)"""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import cas
    vA, vB, ve = _terme(A), _terme(B), _terme(e)
    vx, vy = var(x), var(y)
    AunionB = E.reunion(vA, vB)
    hyp = et(E.est_segment(vA, R, ve, x, y), E.est_segment(vB, R, ve, x, y))
    H = N.assume(hyp)
    segA, segB = conjonction_elim_gauche(H), conjonction_elim_droite(H)
    subA, bodyA = conjonction_elim_gauche(segA), conjonction_elim_droite(segA)
    subB, bodyB = conjonction_elim_gauche(segB), conjonction_elim_droite(segB)

    # (1)  A∪B ⊂ E  : z∈A∪B ⇒ (z∈A ou z∈B), chacun ⇒ z∈E
    vz = var("z")
    memb = _instance_reunion(vA, vB, vz)                       # z∈A∪B ⇔ (z∈A ou z∈B)
    incA = instancie(subA, vz)                                 # z∈A⇒z∈E
    incB = instancie(subB, vz)                                 # z∈B⇒z∈E
    z_disj = N.assume(ou(appartient(vz, vA), appartient(vz, vB)))
    z_in_E = cas(z_disj, incA, incB)                           # (sous hyp disj) z∈E
    z_in_E = N.loi_deduction(ou(appartient(vz, vA), appartient(vz, vB)), z_in_E)
    sub = N.generalisation("z", syllogisme(equivalence_avant(memb), z_in_E))  # A∪B⊂E

    # (2)  corps : ((x∈A∪B et y∈E) et y≤x) ⇒ y∈A∪B
    premisse = et(et(appartient(vx, AunionB), appartient(vy, ve)), R(vy, vx))
    Hp = N.assume(premisse)
    x_in_AB = conjonction_elim_gauche(conjonction_elim_gauche(Hp))  # x∈A∪B
    y_in_E = conjonction_elim_droite(conjonction_elim_gauche(Hp))   # y∈E
    yx = conjonction_elim_droite(Hp)                               # y≤x
    x_disj = N.modus_ponens(x_in_AB, equivalence_avant(_instance_reunion(vA, vB, vx)))  # x∈A ou x∈B
    s2A = N.s2(appartient(vy, vA), appartient(vy, vB))            # y∈A ⇒ (y∈A ou y∈B)
    s2B = syllogisme(N.s2(appartient(vy, vB), appartient(vy, vA)),
                     N.s3(appartient(vy, vB), appartient(vy, vA)))  # y∈B ⇒ (y∈A ou y∈B)
    # cas x∈A : bodyA donne y∈A ; cas x∈B : bodyB donne y∈B
    case_A = N.assume(appartient(vx, vA))
    yA = _force_premisse(bodyA, vx, vy, case_A, y_in_E, yx)        # y∈A
    yAB_a = N.modus_ponens(yA, s2A)                               # y∈A∪B
    case_A_imp = N.loi_deduction(appartient(vx, vA), yAB_a)
    case_B = N.assume(appartient(vx, vB))
    yB = _force_premisse(bodyB, vx, vy, case_B, y_in_E, yx)        # y∈B
    yAB_b = N.modus_ponens(yB, s2B)                               # y∈A∪B
    case_B_imp = N.loi_deduction(appartient(vx, vB), yAB_b)
    y_in_AunionB0 = cas(x_disj, case_A_imp, case_B_imp)           # y∈A ou y∈B  (membre droit réunion)
    y_in_AB = N.modus_ponens(y_in_AunionB0,
                             equivalence_arriere(_instance_reunion(vA, vB, vy)))  # y∈A∪B
    body = N.loi_deduction(premisse, y_in_AB)
    body = N.generalisation(x, N.generalisation(y, body))
    concl = conjonction_intro(sub, body)
    return N.loi_deduction(hyp, concl)


def _force_premisse(body_seg, vx, vy, thm_x_in, thm_y_in_E, thm_yx):
    """De body_seg = (∀x)(∀y)(((x∈S et y∈E) et y≤x)⇒y∈S) et des théorèmes
    ⊢x∈S, ⊢y∈E, ⊢y≤x, déduire ⊢y∈S."""
    inst = instancie(instancie(body_seg, vx), vy)   # ((x∈S et y∈E) et y≤x)⇒y∈S
    premisse = conjonction_intro(conjonction_intro(thm_x_in, thm_y_in_E), thm_yx)
    return N.modus_ponens(premisse, inst)


__all__ = ["bien_ordonne_est_ordonne", "ensemble_est_segment", "vide_est_segment",
           "segment_inclus", "intersection_segments_segment", "reunion_segments_segment"]
