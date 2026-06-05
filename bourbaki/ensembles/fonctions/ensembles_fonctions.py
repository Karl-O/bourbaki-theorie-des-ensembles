"""§II.3.4 — Fonctions : graphe fonctionnel, valeur f(x), caractérisation C46.

Théorèmes (sous hypothèses « F fonctionnel » et « x dans le domaine ») :
  (x, f(x)) ∈ F   et   ((x,y) ∈ F) ⇔ (y = f(x)).
La valeur f(x):=τy((x,y)∈F) est « le » correspondant grâce à existe_temoin
(qui donne (x,f(x))∈F) et à l'unicité fonctionnelle.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, appartient, existe
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, equivalence_avant, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def valeur_dans_graphe(f="F", x="x"):
    """{(∃y)((x,y)∈F)} ⊢ (x, f(x)) ∈ F.   (f, x : noms OU termes ; x dans le domaine.)"""
    vF, vx, vy = _t(f), _t(x), var("y")
    r = appartient(E.couple(vx, vy), vF)               # (x,y)∈F
    dom_hyp = N.assume(existe("y", r))                 # (∃y)((x,y)∈F)
    return N.modus_ponens(dom_hyp, N.existe_temoin(r, "y"))   # (x, f(x))∈F


def valeur_caracterisation(f="F", x="x"):
    """{F fonctionnel, (∃y)((x,y)∈F)} ⊢ ((x,y) ∈ F) ⇔ (y = f(x)).   (C46 ; f,x noms ou termes.)"""
    vF, vx, vy = _t(f), _t(x), var("y")
    fx = E.valeur(vF, vx)
    xfx = valeur_dans_graphe(f, x)                     # (x, f(x))∈F   [hyp : domaine]
    hfunc = N.assume(E.est_fonctionnel(vF))            # F fonctionnel
    inst = instancie(instancie(instancie(hfunc, vx), vy), fx)   # ((x,y)∈F et (x,f(x))∈F)⇒y=f(x)
    # ⇒ : (x,y)∈F ⇒ y=f(x)
    hxy = N.assume(appartient(E.couple(vx, vy), vF))
    fwd = N.loi_deduction(appartient(E.couple(vx, vy), vF),
                          N.modus_ponens(conjonction_intro(hxy, xfx), inst))
    # ⇐ : y=f(x) ⇒ (x,y)∈F   (réécriture f(x)→y dans (x,f(x))∈F)
    hyfx = N.assume(egal(vy, fx))
    fxy = N.modus_ponens(hyfx, symetrie(vy, fx))       # f(x)=y
    xy_in = N.modus_ponens(xfx, equivalence_avant(N.modus_ponens(
        fxy, N.s6(fx, vy, "w", appartient(E.couple(vx, var("w")), vF)))))
    bwd = N.loi_deduction(egal(vy, fx), xy_in)
    return conjonction_intro(fwd, bwd)


__all__ = ["valeur_dans_graphe", "valeur_caracterisation"]
