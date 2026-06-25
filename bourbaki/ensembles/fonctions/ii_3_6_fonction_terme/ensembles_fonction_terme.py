"""§II.3.6 — Définition d'une fonction par un terme (Critère C54, E.II.46).

La fonction x↦T (x∈A, T∈C) a pour graphe
    F := {w | (∃x)(∃y)(w=(x,y) et x∈A et y=T)}.
Critère C54 : R := « x∈A et y=T » admet F pour graphe par rapport à x,y ;
ce graphe est FONCTIONNEL ; sa première projection est A, sa seconde est
B = {T | x∈A} (II, p.6).

On certifie ici (toolbox abrégée) :
  - `membre_graphe_terme`  ⊢ ((u,v)∈F) ⇔ (u∈A et v=T[u])   (réduction du graphe,
        via Prop. 1 et l'élimination des témoins x,y) ;
  - `graphe_terme_fonctionnel`  ⊢ F est fonctionnel   (le cœur de C54 :
        (u,v)∈F et (u,v')∈F entraîne v=v', par unicité de la valeur T[u]).

NB : x, y sont les liants du corps (donc l'assemblage de F ne contient ni x ni y,
fidèle à C54). u, v, v' sont des lettres-paramètres distinctes de x, y, w.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient, existe, subst_t, libres_t, libres_f
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, instanciation_en_x)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import couple_egal_implique_composantes


def _inst_axiome(a, t, w, x="x", y="y"):
    """⊢ (W∈F) ⇔ (∃x)(∃y)(W=(x,y) et (x∈A et y=T)).   (instance de l'axiome C54.)"""
    th = E.theorie_graphe_terme(a, t, x, y, "w")
    ax = N.axiome(th, E.axiome_graphe_terme(a, t, x, y, "w"))   # (∀w)(...)
    return instancie(ax, w)


# @livre Ch.II §3.6 Crit.54 | E II.15 L.31-35 | PDF p.66
def membre_graphe_terme(a="A", t=None, u="u", v="v", x="x", y="y"):
    """⊢ ((u,v) ∈ F) ⇔ (u∈A et v=T[u]),   F = graphe_terme(A,T).

    T[u] = (u|x)T.  Réduit l'appartenance au graphe (∃-définie) à la condition
    explicite « u∈A et v=valeur du terme en u »  (via Prop. 1 + élim. des témoins).
    """
    vA = var(a) if isinstance(a, str) else a
    vu, vv, vx, vy = var(u), var(v), var(x), var(y)
    if t is None:
        t = E.valeur(var("F"), vx)        # défaut sans intérêt ; appels réels passent T
    Tu = subst_t(vu, x, t)                # T[u]
    cuv = E.couple(vu, vv)
    inst = _inst_axiome(vA, t, cuv, x, y)            # ((u,v)∈F) ⇔ (∃x)(∃y) body
    body = et(et(egal(cuv, E.couple(vx, vy)), appartient(vx, vA)), egal(vy, t))

    # ── ⇒ : (∃x)(∃y) body  ⇒  (u∈A et v=T[u]) ──────────────────────────────────
    hb = N.assume(body)
    eqcpl = conjonction_elim_gauche(conjonction_elim_gauche(hb))   # (u,v)=(x,y)
    xA = conjonction_elim_droite(conjonction_elim_gauche(hb))      # x∈A
    yT = conjonction_elim_droite(hb)                               # y=T
    comps = N.modus_ponens(eqcpl, couple_egal_implique_composantes(u, v, x, y))  # u=x et v=y
    ux = conjonction_elim_gauche(comps)                            # u=x
    vy_eq = conjonction_elim_droite(comps)                         # v=y
    # u∈A : de x∈A et u=x (Leibniz)
    uA = N.modus_ponens(xA, equivalence_arriere(N.modus_ponens(
        ux, N.s6(vu, vx, "w", appartient(var("w"), vA)))))         # u∈A
    # v=T[u] : v=y, y=T (=T(x)), et T(x)=T(u) car u=x
    from bourbaki.logique.i_1_termes_relations.formule import _fraiche
    hole = _fraiche(libres_t(t) | libres_t(vu) | libres_t(vx) | {x, u, v})
    Thole = subst_t(var(hole), x, t)                               # T avec trou frais (x↦hole)
    xu = N.modus_ponens(ux, symetrie(vu, vx))                      # x=u
    Tx_Tu = N.modus_ponens(xu, congruence_terme(vx, vu, Thole, hole))  # (x=u)⇒(T(x)=T(u))
    v_eq_Tu = composer_egalites(vy_eq, composer_egalites(yT, Tx_Tu))   # v=y=T(x)=T(u)
    conc_av = conjonction_intro(uA, v_eq_Tu)                       # u∈A et v=T[u]
    avant = existe_elimination(existe_elimination(
        N.loi_deduction(body, conc_av), y), x)                     # (∃x)(∃y)body ⇒ conc

    # ── ⇐ : (u∈A et v=T[u])  ⇒  (∃x)(∃y) body ──────────────────────────────────
    hc = N.assume(et(appartient(vu, vA), egal(vv, Tu)))
    # témoins x:=u, y:=v.  (u|x)(v|y)body = ((u,v)=(u,v) et (u∈A et v=T[u]))
    refl = N.reflexivite(cuv)                                      # (u,v)=(u,v)
    wit = conjonction_intro(conjonction_intro(refl, conjonction_elim_gauche(hc)),
                            conjonction_elim_droite(hc))           # = (u|x)(v|y)body
    # (v|y)body, puis (∃y), puis (u|x), puis (∃x)
    from bourbaki.logique.i_1_termes_relations.formule import subst_f
    body_uy = subst_f(vu, x, body)            # (u|x)body
    ex_y = N.modus_ponens(wit, N.s5(body_uy, vv, y))              # (∃y)(u|x)body
    ex_xy = N.modus_ponens(ex_y, N.s5(existe(y, body), vu, x))    # (∃x)(∃y)body
    arriere = N.loi_deduction(et(appartient(vu, vA), egal(vv, Tu)), ex_xy)

    eq_ex = conjonction_intro(avant, arriere)                     # (∃x)(∃y)body ⇔ conc
    return equivalence_transitivite(inst, eq_ex)                  # ((u,v)∈F) ⇔ (u∈A et v=T[u])


# @livre Ch.II §3.6 Crit.54 | E II.15 L.31-35 | PDF p.66
def graphe_terme_fonctionnel(a="A", t=None, x="x", y="y"):
    """⊢ F est fonctionnel,   F = graphe_terme(A,T).   (Critère C54, cœur.)

    Forme : ⊢ (∀u)(∀v)(∀v')(((u,v)∈F et (u,v')∈F) ⇒ v=v').
    Preuve : (u,v)∈F ⇒ v=T[u] et (u,v')∈F ⇒ v'=T[u] (lemme), donc v=v'."""
    vA = var(a) if isinstance(a, str) else a
    vx = var(x)
    if t is None:
        t = E.valeur(var("F"), vx)
    u, v, vp = "u", "v", "z"          # liants u, v, z (= ceux de est_fonctionnel)
    vu, vv, vvp = var(u), var(v), var(vp)
    Tu = subst_t(vu, x, t)                       # T[u]
    F = E.graphe_terme(vA, t, x)

    lem_v = membre_graphe_terme(vA, t, u, v, x, y)      # ((u,v)∈F) ⇔ (u∈A et v=T[u])
    lem_vp = membre_graphe_terme(vA, t, u, vp, x, y)    # ((u,v')∈F) ⇔ (u∈A et v'=T[u])

    ante = et(appartient(E.couple(vu, vv), F), appartient(E.couple(vu, vvp), F))
    h = N.assume(ante)
    v_Tu = conjonction_elim_droite(N.modus_ponens(conjonction_elim_gauche(h),
                                                  equivalence_avant(lem_v)))    # v=T[u]
    vp_Tu = conjonction_elim_droite(N.modus_ponens(conjonction_elim_droite(h),
                                                   equivalence_avant(lem_vp)))  # v'=T[u]
    v_vp = composer_egalites(v_Tu, N.modus_ponens(vp_Tu, symetrie(vvp, Tu)))    # v=T[u]=v'
    inner = N.loi_deduction(ante, v_vp)          # (((u,v)∈F et (u,v')∈F)) ⇒ v=v'
    return N.generalisation(u, N.generalisation(v, N.generalisation(vp, inner)))


__all__ = ["membre_graphe_terme", "graphe_terme_fonctionnel"]
