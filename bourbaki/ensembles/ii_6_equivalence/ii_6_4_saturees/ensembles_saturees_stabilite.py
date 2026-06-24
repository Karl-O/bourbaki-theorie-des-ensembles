"""§II.6.4 — Stabilité des parties saturées par réunion et intersection (E II.43-44).

Module NEUF (vague II — saturation).  On NE MODIFIE AUCUN fichier existant ; on
RECOLLE des lemmes DÉJÀ CLOS (modulo hypothèses) et les axiomes de la théorie des
ensembles (`theorie_ensembles()` reste à 22 axiomes — AUCUN axiome neuf).

ÉNONCÉ (Bourbaki, E.II.43, §II.6 n°4 « Parties saturées », dernier alinéa) :

  « Si (X_ι)_{ι∈I} est une famille de parties saturées de E, les ensembles
    ⋃_{ι∈I} X_ι et ⋂_{ι∈I} X_ι sont saturés (II, p. 25, prop. 3 et 4). »

On formalise ici le CAS BINAIRE A, B — fidèle comme cas particulier I = {1, 2} de
la propriété de famille (la réf. « prop. 3 et 4 » de E.II.4 est précisément la
spécialisation binaire) :

  `reunion_de_saturees_est_saturee`        {A saturée, B saturée}
        ⊢ est_saturee( A∪B, G )
  `intersection_de_saturees_est_saturee`   {A saturée, B saturée}
        ⊢ est_saturee( A∩B, G )

où est_saturee(C, G) = (∀x)(∀y)( (x∈C et (x,y)∈G) ⇒ y∈C )  (prédicat E.est_saturee,
forme dépliée, liants x, y — REPRODUITE à l'identique de `cible_sature_partie_saturee`
qui écrit E.est_saturee(prB, vg, prB, x="x")).

STRATÉGIE (calquée sur les modules clos de ii_6_4_saturees).  On déplie
est_saturee(C, G) et on prouve le corps instancié en deux points universels x, y.
Sous (x∈C et (x,y)∈G) :

  RÉUNION (C = A∪B).  x∈A∪B ⇒ (x∈A ou x∈B)  [membership AXIOME_REUNION].
    • Cas x∈A : est_saturee(A) instanciée en (x,y) appliquée à (x∈A et (x,y)∈G)
      donne y∈A ; intro réunion (S2) ⇒ y∈A∪B.
    • Cas x∈B : idem ⇒ y∈B ; intro réunion ⇒ y∈A∪B.
    `cas` (élimination de ∨) ⇒ y∈A∪B.

  INTERSECTION (C = A∩B).  x∈A∩B ⇒ (x∈A et x∈B)  [membership AXIOME_INTER].
    est_saturee(A) ⇒ y∈A ; est_saturee(B) ⇒ y∈B ; conjonction + intro intersection
    ⇒ y∈A∩B.

Puis loi_deduction (décharge l'antécédent x∈C et (x,y)∈G) et double généralisation
sur y, x — qui reconstruit EXACTEMENT pourtout("x", pourtout("y", …)) = la forme
canonique de E.est_saturee.

HYPOTHÈSES HONNÊTES (load-bearing, exactement dans le séquent — rien postulé, aucune
tautologie, conclusion ∉ hypothèses) :
  • est_saturee(A, G)  — consommée dans la branche/le côté « A » ;
  • est_saturee(B, G)  — consommée dans la branche/le côté « B ».
Aucune des deux n'est la conclusion (qui porte sur A∪B, resp. A∩B).  Les liants x, y
de la généralisation ne figurent dans AUCUNE hypothèse (les est_saturee sont closes),
donc la généralisation est licite.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, et, impl, appartient)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (
    _instance_reunion, _instance_intersection)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── instances de membership (axiomes de theorie_ensembles, 22 ax. inchangée) ──
def _mem_reunion(a, b, z):
    """⊢ (z ∈ A∪B) ⇔ (z∈A ou z∈B)  (instance de AXIOME_REUNION)."""
    return _instance_reunion(a, b, z)


def _mem_inter(a, b, z):
    """⊢ (z ∈ A∩B) ⇔ (z∈A et z∈B)  (instance de AXIOME_INTER)."""
    return _instance_intersection(a, b, z)


def cible_reunion_saturee(a="A", b="B", g="G"):
    """Cible Bourbaki : est_saturee( A∪B, G )  (forme dépliée, liants x, y).

    Renvoie (∀x)(∀y)((x∈A∪B et (x,y)∈G) ⇒ y∈A∪B), construite EXACTEMENT comme
    cible_sature_partie_saturee : E.est_saturee(C, G, C, x="x") avec C = A∪B."""
    va, vb, vg = _t(a), _t(b), _t(g)
    c = E.reunion(va, vb)
    return E.est_saturee(c, vg, c, x="x")


def cible_intersection_saturee(a="A", b="B", g="G"):
    """Cible Bourbaki : est_saturee( A∩B, G )  (forme dépliée, liants x, y)."""
    va, vb, vg = _t(a), _t(b), _t(g)
    c = E.intersection(va, vb)
    return E.est_saturee(c, vg, c, x="x")


def reunion_de_saturees_est_saturee(a="A", b="B", g="G"):
    """{est_saturee(A,G), est_saturee(B,G)} ⊢ est_saturee( A∪B, G )
    (E.II.43, cas binaire ; clos mod. hyp.).

    « Si A et B sont saturées pour R, A∪B l'est. »  Cas particulier I = {1,2} de la
    stabilité d'une famille de parties saturées par réunion (E.II.43, réf. prop. 3
    de E.II.4).  Preuve : membership de la réunion (AXIOME_REUNION) + preuve par cas
    sur x∈A ou x∈B, chaque branche consommant la saturation correspondante (cf.
    en-tête).  Clos modulo {A saturée pour R, B saturée pour R}."""
    va, vb, vg = _t(a), _t(b), _t(g)
    vx, vy = var("x"), var("y")
    union = E.reunion(va, vb)

    # hypothèses honnêtes : A et B saturées pour R (forme canonique E.est_saturee)
    h_satA = N.assume(E.est_saturee(va, vg, va, x="x"))    # (∀x)(∀y)((x∈A et (x,y)∈G)⇒y∈A)
    h_satB = N.assume(E.est_saturee(vb, vg, vb, x="x"))

    # antécédent du corps instancié en (x, y) : (x∈A∪B et (x,y)∈G)
    antec = et(appartient(vx, union), appartient(E.couple(vx, vy), vg))
    h_ant = N.assume(antec)
    x_in_U = conjonction_elim_gauche(h_ant)                # x∈A∪B
    xy_G = conjonction_elim_droite(h_ant)                  # (x,y)∈G

    # x∈A∪B ⇒ (x∈A ou x∈B)
    disj = N.modus_ponens(x_in_U, equivalence_avant(_mem_reunion(va, vb, vx)))

    # intro réunion sur y : y∈A ⇒ y∈A∪B   et   y∈B ⇒ y∈A∪B
    y_in_U_from_A = equivalence_arriere(_mem_reunion(va, vb, vy))   # (y∈A ou y∈B) ⇒ y∈A∪B
    yA_or = N.s2(appartient(vy, va), appartient(vy, vb))           # y∈A ⇒ (y∈A ou y∈B)
    yB_or = syllogisme(N.s2(appartient(vy, vb), appartient(vy, va)),
                       N.s3(appartient(vy, vb), appartient(vy, va)))  # y∈B ⇒ (y∈A ou y∈B)

    # branche x∈A : (x∈A et (x,y)∈G) ⇒ y∈A ⇒ y∈A∪B
    h_xA = N.assume(appartient(vx, va))
    yA = N.modus_ponens(conjonction_intro(h_xA, xy_G),
                        instancie(instancie(h_satA, vx), vy))        # y∈A
    yU_A = N.modus_ponens(N.modus_ponens(yA, yA_or), y_in_U_from_A)   # y∈A∪B
    brA = N.loi_deduction(appartient(vx, va), yU_A)                  # (x∈A) ⇒ y∈A∪B

    # branche x∈B : (x∈B et (x,y)∈G) ⇒ y∈B ⇒ y∈A∪B
    h_xB = N.assume(appartient(vx, vb))
    yB = N.modus_ponens(conjonction_intro(h_xB, xy_G),
                        instancie(instancie(h_satB, vx), vy))        # y∈B
    yU_B = N.modus_ponens(N.modus_ponens(yB, yB_or), y_in_U_from_A)   # y∈A∪B
    brB = N.loi_deduction(appartient(vx, vb), yU_B)                  # (x∈B) ⇒ y∈A∪B

    y_in_U = cas(disj, brA, brB)                           # y∈A∪B
    body_imp = N.loi_deduction(antec, y_in_U)              # (x∈A∪B et (x,y)∈G) ⇒ y∈A∪B
    return N.generalisation("x", N.generalisation("y", body_imp))


def intersection_de_saturees_est_saturee(a="A", b="B", g="G"):
    """{est_saturee(A,G), est_saturee(B,G)} ⊢ est_saturee( A∩B, G )
    (E.II.43, cas binaire ; clos mod. hyp.).

    « Si A et B sont saturées pour R, A∩B l'est. »  Cas particulier I = {1,2} de la
    stabilité d'une famille de parties saturées par intersection (E.II.43, réf.
    prop. 4 de E.II.4).  Preuve : membership de l'intersection (AXIOME_INTER) +
    application des DEUX saturations puis recollement par conjonction (cf. en-tête).
    Clos modulo {A saturée pour R, B saturée pour R}."""
    va, vb, vg = _t(a), _t(b), _t(g)
    vx, vy = var("x"), var("y")
    inter = E.intersection(va, vb)

    h_satA = N.assume(E.est_saturee(va, vg, va, x="x"))
    h_satB = N.assume(E.est_saturee(vb, vg, vb, x="x"))

    antec = et(appartient(vx, inter), appartient(E.couple(vx, vy), vg))
    h_ant = N.assume(antec)
    x_in_I = conjonction_elim_gauche(h_ant)                # x∈A∩B
    xy_G = conjonction_elim_droite(h_ant)                  # (x,y)∈G

    # x∈A∩B ⇒ (x∈A et x∈B)
    conj = N.modus_ponens(x_in_I, equivalence_avant(_mem_inter(va, vb, vx)))
    x_in_A = conjonction_elim_gauche(conj)                 # x∈A
    x_in_B = conjonction_elim_droite(conj)                 # x∈B

    # y∈A (saturation A) et y∈B (saturation B)
    yA = N.modus_ponens(conjonction_intro(x_in_A, xy_G),
                        instancie(instancie(h_satA, vx), vy))        # y∈A
    yB = N.modus_ponens(conjonction_intro(x_in_B, xy_G),
                        instancie(instancie(h_satB, vx), vy))        # y∈B

    # (y∈A et y∈B) ⇒ y∈A∩B
    y_in_I = N.modus_ponens(conjonction_intro(yA, yB),
                            equivalence_arriere(_mem_inter(va, vb, vy)))   # y∈A∩B
    body_imp = N.loi_deduction(antec, y_in_I)              # (x∈A∩B et (x,y)∈G) ⇒ y∈A∩B
    return N.generalisation("x", N.generalisation("y", body_imp))


__all__ = [
    "cible_reunion_saturee",
    "cible_intersection_saturee",
    "reunion_de_saturees_est_saturee",
    "intersection_de_saturees_est_saturee",
]
