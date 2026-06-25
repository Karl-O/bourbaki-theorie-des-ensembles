"""§III.2.1 — PROPOSITION 2 (E III.15), SENS LARGE : x≤y ⟹ S_x ⊂ S_y.

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉ BOURBAKI (E III.15-16, §2 n°1 « Segments », Proposition 2).

    « L'ensemble E* des segments d'un ensemble bien ordonné E est bien ordonné par
    inclusion ; l'application x ↦ S_x est un isomorphisme de l'ensemble bien
    ordonné E sur l'ensemble des segments de E distincts de E. »
    Démonstration : « si x∈E et y∈E, la relation x≤y entraîne S_x ⊂ S_y et que
    x<y entraîne S_x ≠ S_y. »

Ce module formalise le PREMIER membre de cette démonstration — le SENS LARGE
(monotonie) de l'application x ↦ S_x : pour x≤y le segment S_x est inclus (au sens
large) dans S_y.  Le sens strict x<y ⟹ S_x ≠ S_y est traité à part
(ensembles_segment_extremite_injectif : STRICTITÉ / injectivité).

Le VRAI segment initial strict d'extrémité t est (E.III.2.1)

    seg(E,R,t) := segment_extremite(R, E, t) = { u∈E | R{u,t} et u≠t },

caractérisé par AXIOME_SEGMENT_EXTREMITE (déjà dans theorie_ensembles=22, RIEN ajouté).

────────────────────────────────────────────────────────────────────────────────
RÉ-EXPOSITION III.2 D'UN THÉORÈME DÉJÀ CLOS EN AVAL.

Le contenu mathématique du sens large est DÉJÀ établi, sous forme CONDITIONNELLE,
par une brique qui vit dans le paquet cardinaux (arc ordinaux/segments) :

  seg_strict_monotone_de_bon_ordre(R,E,x,y)            (paquet lemme4_segments)
        { est_bien_ordonne(R,E),  R{x,y} } ⊢ seg(E,R,x) ⊂ seg(E,R,y).

Ce module n'en REPROUVE RIEN : il se contente de RÉ-EXPOSER ce résultat à sa place
logique (§III.2 « Segments ») sous la forme CLOSE attendue par Bourbaki, en
DÉCHARGEANT ses deux antécédents en implications imbriquées (double loi_deduction) :

    ⊢ est_bien_ordonne(R,E) ⇒ ( R{x,y} ⇒ inclus(seg(E,R,x), seg(E,R,y)) ).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (theorie=22, jamais postulé, jamais tautologie) :

  ✅ CLOS — 0 hypothèse pendante (les deux antécédents Bourbaki déchargés) :
     • segment_extremite_monotone(R,E,x,y) :
          ⊢ est_bien_ordonne(R,E)
              ⇒ ( R{x,y} ⇒ inclus(seg(E,R,x), seg(E,R,y)) ).
       🎯 SENS LARGE de la Proposition 2 : x≤y ⟹ S_x ⊂ S_y, exposé en théorème
       NOMMÉ III.2, CLOS (les antécédents bon ordre et x≤y sont des implications,
       non des hypothèses pendantes).

⚠️ ANTI-PARASITE.  L'énoncé NE met PAS x∈E ni y∈E : la construction de seg ne
consomme que R{x,y} + l'ordre.  Les appartenances seraient des hypothèses PARASITES.
Les deux SEULS antécédents sont est_bien_ordonne(R,E) et R{x,y} — exactement ceux
de la brique amont.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la preuve est une pure DOUBLE
DÉCHARGE (loi_deduction) d'un théorème déjà clos.  🚫 jamais tautologie : la
conclusion finale (l'inclusion) n'est aucune des deux formules déchargées.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, impl, appartient, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_lemme_1_segments import (
    seg_strict_monotone_de_bon_ordre,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg, _R_de,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PROPOSITION 2 — SENS LARGE : x≤y ⟹ S_x ⊂ S_y  (théorème NOMMÉ III.2, CLOS).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.1 Prop.2 | E III.16 L.21-30 | PDF p.119
def segment_extremite_monotone(R="R", E_="E", x="x", y="y"):
    """⊢ est_bien_ordonne(R,E)
            ⇒ ( R{x,y} ⇒ inclus(seg(E,R,x), seg(E,R,y)) ).        [CLOS, 0 hyp]

    🎯 PROPOSITION 2 (E III.15) — SENS LARGE de x ↦ S_x : la relation x≤y entraîne
    S_x ⊂ S_y.  Ré-exposition III.2, sous forme CLOSE, d'un théorème déjà clos en aval
    (seg_strict_monotone_de_bon_ordre, paquet lemme4_segments).  RIEN n'est reprouvé.

    PREUVE = DOUBLE DÉCHARGE (deux loi_deduction) du théorème conditionnel amont :
      mono  = seg_strict_monotone_de_bon_ordre(R,E,x,y)
                  { est_bien_ordonne(R,E), R{x,y} } ⊢ seg(E,R,x) ⊂ seg(E,R,y) ;
      inner = loi_deduction( R{x,y}, mono )
                  { est_bien_ordonne(R,E) } ⊢ ( R{x,y} ⇒ seg(x)⊂seg(y) ) ;
      res   = loi_deduction( est_bien_ordonne(R,E), inner )
                  ⊢ est_bien_ordonne(R,E) ⇒ ( R{x,y} ⇒ seg(x)⊂seg(y) ).   CLOS.

    ANTI-PARASITE : pas de x∈E, y∈E (non consommés par seg) ; les deux SEULS
    antécédents sont le bon ordre et R{x,y}.  NON vacueux : la conclusion (l'inclusion)
    n'est aucune des deux formules déchargées."""
    Rf = _R_de(R)
    vx, vy = _t(x), _t(y)

    # ── théorème conditionnel amont (déjà clos modulo ses 2 hypothèses)
    mono = seg_strict_monotone_de_bon_ordre(R=R, a=E_, t=vx, s=vy)  # seg(x)⊂seg(y)
    assert mono.conclusion == inclus(seg(R, E_, vx), seg(R, E_, vy)), \
        "brique amont : conclusion ≠ inclus(seg(x), seg(y))"

    # ── les DEUX formules-hypothèses à décharger (reconstruites ET vérifiées
    #    présentes dans mono.hypotheses : aucun mismatch de liant ne passe).
    bo = E.est_bien_ordonne(Rf, _t(E_))                 # est_bien_ordonne(R,E)
    rxy = Rf(vx, vy)                                    # R{x,y} := (x,y)∈R
    assert mono.hypotheses == frozenset({bo, rxy}), \
        "brique amont : hypothèses ≠ {est_bien_ordonne(R,E), R{x,y}}"

    # ── double décharge : R{x,y} d'abord (implication interne), puis le bon ordre.
    inner = N.loi_deduction(rxy, mono)                  # { bo } ⊢ ( R{x,y} ⇒ incl )
    res = N.loi_deduction(bo, inner)                    # ⊢ bo ⇒ ( R{x,y} ⇒ incl )

    assert res.conclusion == segment_extremite_monotone_cible(R, E_, x, y), \
        "conclusion ≠ ( bo ⇒ ( R{x,y} ⇒ inclus(seg(x), seg(y)) ) )"
    assert res.est_clos, "le théorème devrait être CLOS (0 hypothèse pendante)"
    return res


def segment_extremite_monotone_cible(R="R", E_="E", x="x", y="y"):
    """ÉNONCÉ de la conclusion de segment_extremite_monotone (test miroir) :

        est_bien_ordonne(R,E)
            ⇒ ( R{x,y} ⇒ inclus(seg(E,R,x), seg(E,R,y)) )   [seg = segment_extremite]."""
    Rf = _R_de(R)
    vx, vy = _t(x), _t(y)
    bo = E.est_bien_ordonne(Rf, _t(E_))
    rxy = Rf(vx, vy)
    return impl(bo, impl(rxy, inclus(seg(R, E_, vx), seg(R, E_, vy))))


__all__ = [
    "segment_extremite_monotone",
    "segment_extremite_monotone_cible",
]
