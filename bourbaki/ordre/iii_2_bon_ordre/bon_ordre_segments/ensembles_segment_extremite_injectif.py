"""§III.2.1 — PROPOSITION 2 (E III.15) : STRICTITÉ / INJECTIVITÉ de x ↦ S_x.

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉ BOURBAKI (E III.15-16, §2 n°1 « Segments », Proposition 2).

    « L'ensemble E* des segments d'un ensemble bien ordonné E est bien ordonné par
    inclusion ; l'application x ↦ S_x est un isomorphisme de l'ensemble bien
    ordonné E sur l'ensemble des segments de E distincts de E. »
    Démonstration : « si x∈E et y∈E, la relation x≤y entraîne S_x ⊂ S_y et que
    x<y entraîne S_x ≠ S_y. »

Ce module formalise précisément le cœur de cette démonstration : pour x<y (i.e.
x≤y avec x≠y) le segment S_x est STRICTEMENT inclus dans S_y, donc x ↦ S_x est
injective / strictement croissante.

Le VRAI segment initial strict d'extrémité t est (E.III.2.1)

    seg(E,R,t) := segment_extremite(R, E, t) = { u∈E | R{u,t} et u≠t },

caractérisé par AXIOME_SEGMENT_EXTREMITE (déjà dans theorie_ensembles=22, RIEN ajouté).

────────────────────────────────────────────────────────────────────────────────
STRICTITÉ = INCLUSION LARGE + TÉMOIN D'ÉCART.

Le noyau n'a PAS de primitive `inclus_strict`.  La strictité S_x ⊊ S_y s'EXPRIME
donc, de façon honnête et disponible, par la conjonction :

    « inclusion large »  S_x ⊂ S_y        ET        « témoin d'écart »  x∈S_y et x∉S_x.

Le témoin x certifie que l'inclusion est PROPRE : x sépare S_y de S_x (x∈S_y, x∉S_x).

────────────────────────────────────────────────────────────────────────────────
STRATÉGIE — CONJUGUER DEUX THÉORÈMES DÉJÀ CLOS (rien n'est reprouvé ici).

  mono = seg_strict_monotone_de_bon_ordre(R, E, x, y)   (paquet lemme4_segments)
            { est_bien_ordonne(R,E),  R{x,y} } ⊢ seg(E,R,x) ⊂ seg(E,R,y).
  tem  = seg_strict_propre(R, E, x, y)                  (ce paquet bon_ordre_segments)
            { x∈E,  R{x,y},  x≠y } ⊢ ( x∈seg(E,R,y)  et  ¬(x∈seg(E,R,x)) ).
  res  = conjonction_intro(mono, tem).

Les deux briques lisent R via la MÊME convention de graphe (R{x,y} := (x,y)∈R,
via _R_de / _Rgraphe identiques), donc l'hypothèse R{x,y} COÏNCIDE LITTÉRALEMENT
et FUSIONNE.  Les 4 hypothèses du résultat sont EXACTEMENT les antécédents Bourbaki
{ bon ordre,  x∈E,  x≤y,  x≠y } — sans aucune parasite.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (theorie=22, jamais postulé, jamais tautologie) :

  ✅ CONDITIONNEL (4 hypothèses load-bearing HONNÊTES — les antécédents Bourbaki) :
     • segment_extremite_strictement_croissant(R,E,x,y) :
          { est_bien_ordonne(R,E),  x∈E,  R{x,y},  x≠y }
              ⊢ ( seg(E,R,x) ⊂ seg(E,R,y)
                  et ( x∈seg(E,R,y) et ¬(x∈seg(E,R,x)) ) ).
       🎯 STRICTITÉ de x ↦ S_x : inclusion large S_x⊂S_y PLUS témoin d'écart
       x∈S_y, x∉S_x.  Clos modulo ces 4 hypothèses honnêtes.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la preuve est la pure
CONJONCTION de deux théorèmes déjà clos.  🚫 jamais tautologie : la conclusion
(inclusion + témoin) n'est aucune des 4 hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, appartient, inclus,
)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_lemme_1_segments import (
    seg_strict_monotone_de_bon_ordre,
)
from bourbaki.ordre.iii_2_bon_ordre.bon_ordre_segments.ensembles_segment_strict_propre import (
    seg_strict_propre,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PROPOSITION 2 — STRICTITÉ de x ↦ S_x : S_x ⊊ S_y pour x<y.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.1 Prop.2 | E III.16 L.21-30 | PDF p.119
def segment_extremite_strictement_croissant(R="R", E_="E", x="x", y="y"):
    """⊢ { est_bien_ordonne(R,E),  x∈E,  R{x,y},  x≠y }
            ⊢ ( seg(E,R,x) ⊂ seg(E,R,y)
                et ( x∈seg(E,R,y) et ¬(x∈seg(E,R,x)) ) ).

    🎯 PROPOSITION 2 (E III.15) — x ↦ S_x est STRICTEMENT croissante / injective :
    pour x<y (x≤y, x≠y) le segment S_x est STRICTEMENT inclus dans S_y.

    La strictité S_x ⊊ S_y est EXPRIMÉE (faute de primitive inclus_strict) par
    « inclusion large S_x⊂S_y ET témoin d'écart (x∈S_y et x∉S_x) ».

    PREUVE = pure conjonction de deux théorèmes DÉJÀ CLOS (rien n'est reprouvé) :
      • mono = seg_strict_monotone_de_bon_ordre(R,E,x,y) : seg(E,R,x)⊂seg(E,R,y)
        sous { est_bien_ordonne(R,E), R{x,y} } ;
      • tem  = seg_strict_propre(R,E,x,y) : (x∈seg(E,R,y) et ¬(x∈seg(E,R,x)))
        sous { x∈E, R{x,y}, x≠y }.
      conjonction_intro(mono, tem).  L'hypothèse R{x,y} (même convention de graphe
      dans les deux briques) FUSIONNE : 4 hypothèses au total, exactement les
      antécédents Bourbaki.

    SEULES hypothèses : est_bien_ordonne(R,E), x∈E, R{x,y}, x≠y — HONNÊTES (les
    antécédents de la Proposition 2).  NON vacueux : la conclusion (inclusion +
    témoin) n'est aucune des 4 hypothèses."""
    vx, vy = _t(x), _t(y)
    mono = seg_strict_monotone_de_bon_ordre(R=R, a=E_, t=vx, s=vy)  # seg(x)⊂seg(y)
    tem = seg_strict_propre(R=R, E_=E_, x=vx, y=vy)                 # x∈S_y et ¬(x∈S_x)
    res = conjonction_intro(mono, tem)                             # la conjonction visée
    assert res.conclusion == segment_extremite_strictement_croissant_cible(R, E_, x, y), \
        "conclusion ≠ (seg(x)⊂seg(y) et (x∈seg(y) et ¬(x∈seg(x))))"
    return res


def segment_extremite_strictement_croissant_cible(R="R", E_="E", x="x", y="y"):
    """ÉNONCÉ de la conclusion de segment_extremite_strictement_croissant (test miroir) :

        ( seg(E,R,x) ⊂ seg(E,R,y)
          et ( x∈seg(E,R,y) et ¬(x∈seg(E,R,x)) ) )   [seg = segment_extremite]."""
    vx, vy = _t(x), _t(y)
    Sx, Sy = seg(R, E_, vx), seg(R, E_, vy)
    return et(inclus(Sx, Sy),
              et(appartient(vx, Sy), non(appartient(vx, Sx))))


__all__ = [
    "segment_extremite_strictement_croissant",
    "segment_extremite_strictement_croissant_cible",
]
