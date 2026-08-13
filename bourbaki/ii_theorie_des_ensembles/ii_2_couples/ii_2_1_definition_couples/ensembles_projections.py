"""§II.2 — Projections : pr₁(x,y)=x et pr₂(x,y)=y  (Bourbaki « on a évidemment… »).

Repose sur l'identité τx(x=a)=a (immédiate via `existe_temoin` : (∃x)(x=a) ⇒
(τx(x=a)|x)(x=a), et (∃x)(x=a) tient par S5+réflexivité), sur la Proposition 1,
et sur S7 (congruence de τ sous équivalence universelle).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, existe, tau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes


# @livre Ch.II §2.1 Lem.- | E II.7 L.17-21 | PDF p.58
def tau_egal(a="a", x="x"):
    """⊢ τx(x=a) = a.   (le τ d'une relation équivalente à x=a vaut a.)"""
    va, vx = var(a), var(x)
    ex = N.modus_ponens(N.reflexivite(va), N.s5(egal(vx, va), va, x))   # (∃x)(x=a)
    return N.modus_ponens(ex, N.existe_temoin(egal(vx, va), x))         # τx(x=a)=a


# @livre Ch.II §2.1 Def.- | E II.7 L.17-29 | PDF p.58
def projection_premiere(u="u", v="v"):
    """⊢ pr₁((u,v)) = u.   (u, v distincts de x, y.)"""
    vu, vv, vx, vy = var(u), var(v), var("x"), var("y")
    cuv = E.couple(vu, vv)
    R = existe("y", egal(cuv, E.couple(vx, vy)))            # corps de pr₁((u,v)), lié par x
    # F : R ⇒ (x=u)
    dur = couple_egal_implique_composantes(u, v, "x", "y")  # ((u,v)=(x,y)) ⇒ (u=x et v=y)
    heq = N.assume(egal(cuv, E.couple(vx, vy)))
    xu = N.modus_ponens(conjonction_elim_gauche(N.modus_ponens(heq, dur)), symetrie(vu, vx))
    inner = N.loi_deduction(egal(cuv, E.couple(vx, vy)), xu)   # ((u,v)=(x,y)) ⇒ (x=u)
    F = existe_elimination(inner, "y")                        # R ⇒ (x=u)
    # B : (x=u) ⇒ R
    hxu = N.assume(egal(vx, vu))
    uv_xv = N.modus_ponens(N.modus_ponens(hxu, symetrie(vx, vu)),
                           congruence_terme(vu, vx, E.couple(var("w"), vv)))  # (u,v)=(x,v)
    Rx = N.modus_ponens(uv_xv, N.s5(egal(cuv, E.couple(vx, vy)), vv, "y"))    # (∃y)((u,v)=(x,y))
    B = N.loi_deduction(egal(vx, vu), Rx)                     # (x=u) ⇒ R
    gen = N.generalisation("x", conjonction_intro(F, B))      # (∀x)(R ⇔ (x=u))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vx, vu), "x"))  # τx(R) = τx(x=u)
    return composer_egalites(tau_eq, tau_egal(u, "x"))        # pr₁((u,v)) = u


# @livre Ch.II §2.1 Def.- | E II.7 L.17-29 | PDF p.58
def projection_seconde(u="u", v="v"):
    """⊢ pr₂((u,v)) = v.   (u, v distincts de x, y.)"""
    vu, vv, vx, vy = var(u), var(v), var("x"), var("y")
    cuv = E.couple(vu, vv)
    R = existe("x", egal(cuv, E.couple(vx, vy)))            # corps de pr₂((u,v)), lié par y
    dur = couple_egal_implique_composantes(u, v, "x", "y")  # ((u,v)=(x,y)) ⇒ (u=x et v=y)
    heq = N.assume(egal(cuv, E.couple(vx, vy)))
    yv = N.modus_ponens(conjonction_elim_droite(N.modus_ponens(heq, dur)), symetrie(vv, vy))
    inner = N.loi_deduction(egal(cuv, E.couple(vx, vy)), yv)   # ((u,v)=(x,y)) ⇒ (y=v)
    F = existe_elimination(inner, "x")                        # R ⇒ (y=v)
    hyv = N.assume(egal(vy, vv))
    uv_uy = N.modus_ponens(N.modus_ponens(hyv, symetrie(vy, vv)),
                           congruence_terme(vv, vy, E.couple(vu, var("w"))))  # (u,v)=(u,y)
    Ry = N.modus_ponens(uv_uy, N.s5(egal(cuv, E.couple(vx, vy)), vu, "x"))    # (∃x)((u,v)=(x,y))
    B = N.loi_deduction(egal(vy, vv), Ry)                     # (y=v) ⇒ R
    gen = N.generalisation("y", conjonction_intro(F, B))      # (∀y)(R ⇔ (y=v))
    tau_eq = N.modus_ponens(gen, N.s7(R, egal(vy, vv), "y"))  # τy(R) = τy(y=v)
    return composer_egalites(tau_eq, tau_egal(v, "y"))        # pr₂((u,v)) = v


__all__ = ["tau_egal", "projection_premiere", "projection_seconde"]
