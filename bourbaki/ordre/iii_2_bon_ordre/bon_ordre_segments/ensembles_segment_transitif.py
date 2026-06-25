"""Chapitre III §2 — Transitivité des segments (E.III.2.1, Définition 2).

THÉORÈME `segment_de_segment_est_segment` :

    { est_segment(S, R, E),  est_segment(T, R, S) }  ⊢  est_segment(T, R, E)

« Tout segment T d'un segment S de E est lui-même un segment de E. »  On le donne
sous forme de SÉQUENT : conclusion = est_segment(T,R,E) exactement, avec pour seules
hypothèses non déchargées les deux énoncés « S segment de E » et « T segment de S »
(jamais la conclusion, jamais d'hypothèse parasite).  La forme implication fermée
⊢ (est_segment(S,R,E) et est_segment(T,R,S)) ⇒ est_segment(T,R,E) s'en déduit en une
ligne par loi_deduction — voir le commentaire en fin de fonction.

──────────────────────────────────────────────────────────────────────────────
STRATÉGIE
──────────────────────────────────────────────────────────────────────────────
Rappel (E.III.2.1) :  est_segment(A, R, E) = A⊂E  et
    (∀x)(∀y)( ((x∈A et y∈E) et y≤x) ⇒ y∈A ).

On éclate les deux hypothèses en leurs composantes (inclusion + clôture) :
  est_segment(S,R,E) → S⊂E,  clos_S = (∀x,y)(((x∈S et y∈E) et y≤x) ⇒ y∈S)
  est_segment(T,R,S) → T⊂S,  clos_T = (∀x,y)(((x∈T et y∈S) et y≤x) ⇒ y∈T)

Composante 1 (inclusion T⊂E) : transitivité de ⊂ sur (T⊂S, S⊂E).

Composante 2 (clôture de T dans E) : on assume la prémisse ((x∈T et y∈E) et y≤x)
et l'on veut y∈T.
  (a)  x∈T  et  T⊂S            →  x∈S
  (b)  clos_S appliqué à (x∈S, y∈E, y≤x)  →  y∈S
  (c)  clos_T appliqué à (x∈T, y∈S, y≤x)  →  y∈T          (← le but)

Tout est CERTIFIÉ par le noyau abrégé (primitives N.* uniquement ; type Theoreme
opaque).  R{x,y} = fonction Python (Terme, Terme) → Formule (pattern §II.6/§III.1).
R notée ≤.  theorie_ensembles inchangé (= 22 axiomes).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, et, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    inclusion_transitive)


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _force_premisse(body_seg, vx, vy, thm_x_in, thm_y_in, thm_yx):
    """De body_seg = (∀x)(∀y)(((x∈A et y∈B) et y≤x) ⇒ y∈A) et des théorèmes
    ⊢x∈A, ⊢y∈B, ⊢y≤x, déduire ⊢y∈A.  (Motif §III.2.1 — instancie×2 puis MP.)"""
    inst = instancie(instancie(body_seg, vx), vy)   # ((x∈A et y∈B) et y≤x) ⇒ y∈A
    premisse = conjonction_intro(conjonction_intro(thm_x_in, thm_y_in), thm_yx)
    return N.modus_ponens(premisse, inst)


# @livre Ch.III §2.1 Def.2 | E III.16 L.10-13 | PDF p.119
def segment_de_segment_est_segment(R, S="S", T="T", e="E", x="x", y="y"):
    """{ est_segment(S,R,E), est_segment(T,R,S) } ⊢ est_segment(T,R,E).

    Tout segment T d'un segment S de E est un segment de E (E.III.2.1, Déf. 2).
    Séquent : conclusion = est_segment(T,R,E), hypothèses = exactement les deux
    énoncés de segment.  (Décharge → implication fermée : voir fin de fonction.)"""
    vS, vT, ve = _terme(S), _terme(T), _terme(e)
    vx, vy = var(x), var(y)

    # ── Hypothèses (deux assume distincts → séquent à exactement 2 hypothèses) ─
    hyp_S = E.est_segment(vS, R, ve, x, y)             # est_segment(S,R,E)
    hyp_T = E.est_segment(vT, R, vS, x, y)             # est_segment(T,R,S)
    segS = N.assume(hyp_S)
    segT = N.assume(hyp_T)
    subS = conjonction_elim_gauche(segS)               # S⊂E
    closS = conjonction_elim_droite(segS)              # clôture de S dans E
    subT = conjonction_elim_gauche(segT)               # T⊂S
    closT = conjonction_elim_droite(segT)              # clôture de T dans S

    # ── Composante 1 — T ⊂ E  (transitivité de l'inclusion) ───────────────────
    trans_incl = inclusion_transitive(T, S, e)         # ((T⊂S) et (S⊂E)) ⇒ (T⊂E)
    sub = N.modus_ponens(conjonction_intro(subT, subS), trans_incl)   # T⊂E

    # ── Composante 2 — clôture de T dans E ────────────────────────────────────
    # corps :  ((x∈T et y∈E) et y≤x) ⇒ y∈T
    premisse = et(et(appartient(vx, vT), appartient(vy, ve)), R(vy, vx))
    Hp = N.assume(premisse)
    x_in_T = conjonction_elim_gauche(conjonction_elim_gauche(Hp))   # x∈T
    y_in_E = conjonction_elim_droite(conjonction_elim_gauche(Hp))   # y∈E
    yx = conjonction_elim_droite(Hp)                                # y≤x
    # (a)  x∈T  et  T⊂S  →  x∈S
    x_in_S = N.modus_ponens(x_in_T, instancie(subT, vx))           # x∈S
    # (b)  clos_S à (x∈S, y∈E, y≤x)  →  y∈S
    y_in_S = _force_premisse(closS, vx, vy, x_in_S, y_in_E, yx)    # y∈S
    # (c)  clos_T à (x∈T, y∈S, y≤x)  →  y∈T
    y_in_T = _force_premisse(closT, vx, vy, x_in_T, y_in_S, yx)    # y∈T
    body = N.loi_deduction(premisse, y_in_T)
    body = N.generalisation(x, N.generalisation(y, body))         # (∀x)(∀y)(…⇒y∈T)

    # ── Conclusion — est_segment(T,R,E)  (séquent, hypothèses non déchargées) ──
    # Forme implication fermée éventuelle (décharge des deux hypothèses) :
    #     concl = conjonction_intro(sub, body)
    #     return N.loi_deduction(hyp_S, N.loi_deduction(hyp_T, concl))
    return conjonction_intro(sub, body)                # est_segment(T,R,E)


__all__ = ["segment_de_segment_est_segment"]
