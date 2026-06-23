"""§III — PONT de liant-valeur pour `compatible_ordre` (outil de raccord du cluster iso).

Depuis que `compatible_ordre` construit f(x) avec le liant-valeur « j » (lettre fraîche,
sans capture), les preuves iso/trichotomie écrites en « y » (via valeur_dans_graphe /
AXIOME_DOM / composition_valeur, tous en « y ») se désynchronisent.  Plutôt que de
threader « j » dans tous les helpers projet-entier, on PONTE au niveau d'un théorème
`compatible_ordre(f,S,R,R')` ENTIER : on convertit son liant-valeur j↔y, sur les
VARIABLES PLAINES x,y de quantification (donc SANS imbrication de τ_y → pas de capture
'@0', contrairement à un pont sur une valeur f(t) où t contient lui-même un τ_y).

`reecrire` : réécriture Leibniz S6 d'un terme dans une formule.
`pont_compatible` : bridge le liant-valeur d'un théorème dont la conclusion est
    exactement `compatible_ordre(f,S,R,R',x,y)` (forme ∀x∀y).

theorie_ensembles() = 22 (alpha_tau primitive justifiée, pas un axiome).
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, et, equiv, impl, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant, instancie
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_j_egal_y, valeur_y_egal_j


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def reecrire(thm, eq_thm, contexte, hole="hpb0"):
    """Réécrit a→b dans la formule de `thm` via S6, où eq_thm ⊢ a=b et `contexte(trou)`
    reconstruit la formule de thm avec a remplacé par le trou.  ⊢ thm.conclusion[a:=b]."""
    a, b = eq_thm.conclusion.termes
    eqv = N.modus_ponens(eq_thm, N.s6(a, b, hole, contexte(var(hole))))   # F[a] ⇔ F[b]
    return N.modus_ponens(thm, equivalence_avant(eqv))                    # F[b]


def pont_compatible(thm, f, S, R, Rp, x="x", y="y", sens="j2y"):
    """Bridge le liant-valeur d'un théorème de conclusion `compatible_ordre(f,S,R,R',x,y)`.

    `thm` : ⊢ … compatible_ordre(f,S,R,R')  (forme ∀x∀y, corps
        impl(x∈S∧y∈S, equiv(R{x,y}, R'{f(x),f(y)}))) avec liant-valeur `sens[0]`.
    `sens` : "j2y" (j→y) ou "y2j" (y→j).  R, R' : relations (Terme,Terme)→Formule.
    Retourne ⊢ … même conclusion avec le liant-valeur converti, MÊMES hypothèses."""
    vf, vS = _t(f), _t(S)
    vx, vy = var(x), var(y)
    xyS = et(appartient(vx, vS), appartient(vy, vS))
    if sens == "j2y":
        b_src, b_dst, eqfn = "j", "y", valeur_j_egal_y
    elif sens == "y2j":
        b_src, b_dst, eqfn = "y", "j", valeur_y_egal_j
    else:
        raise ValueError(f"sens inconnu : {sens!r}")
    fy_src = E.valeur(vf, vy, b=b_src)
    fx_dst = E.valeur(vf, vx, b=b_dst)
    body = instancie(instancie(thm, vx), vy)                  # corps[b_src], x,y plaines
    body = reecrire(body, eqfn(vf, vx),
                    lambda h: impl(xyS, equiv(R(vx, vy), Rp(h, fy_src))))
    body = reecrire(body, eqfn(vf, vy),
                    lambda h: impl(xyS, equiv(R(vx, vy), Rp(fx_dst, h))))
    return N.generalisation(x, N.generalisation(y, body))     # corps[b_dst], ∀x∀y


__all__ = ["reecrire", "pont_compatible"]
