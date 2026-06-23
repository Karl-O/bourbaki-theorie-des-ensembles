"""§II.3.7 — Composée de deux fonctions : Proposition 6.

⊢ (F fonctionnel et G fonctionnel) ⇒ (G∘F fonctionnel).
Donc si f:A→B et g:B→C sont des applications, g∘f est une application de A dans C
(la totalité du domaine est l'autre moitié, immédiate via dom(G∘F)).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, appartient, existe, subst_f, Terme
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import couple_composee, _inst_composee
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_fonctions import valeur_dans_graphe, valeur_caracterisation


def _tc(t):
    return t if isinstance(t, Terme) else var(t)


def composee_fonctionnelle(g="G", f="F"):
    """⊢ ((F fonctionnel) et (G fonctionnel)) ⇒ (G∘F fonctionnel).   (Proposition 6, E.II.46.)"""
    vG, vF = _tc(g), _tc(f)
    u, v, z, vy, vyp = var("u"), var("v"), var("z"), var("y"), var("yp")
    comp = E.composee(vG, vF)
    hfg = N.assume(et(E.est_fonctionnel(vF), E.est_fonctionnel(vG)))
    hF, hG = conjonction_elim_gauche(hfg), conjonction_elim_droite(hfg)
    h = N.assume(et(appartient(E.couple(u, v), comp), appartient(E.couple(u, z), comp)))

    # décomposer les deux appartenances (témoins y et yp distincts via alpha)
    ex1 = N.modus_ponens(conjonction_elim_gauche(h),
                         equivalence_avant(couple_composee(g, f, "u", "v")))   # (∃y)((u,y)∈F et (y,v)∈G)
    phi2 = et(appartient(E.couple(u, vy), vF), appartient(E.couple(vy, z), vG))
    c2 = equivalence_transitivite(couple_composee(g, f, "u", "z"),
                                  alpha_existe("y", "yp", phi2))
    ex2 = N.modus_ponens(conjonction_elim_droite(h), equivalence_avant(c2))    # (∃yp)((u,yp)∈F et (yp,z)∈G)

    body1 = et(appartient(E.couple(u, vy), vF), appartient(E.couple(vy, v), vG))
    body2 = et(appartient(E.couple(u, vyp), vF), appartient(E.couple(vyp, z), vG))
    hb1, hb2 = N.assume(body1), N.assume(body2)
    y_eq_yp = N.modus_ponens(                                                  # y = yp  (F fonctionnel)
        conjonction_intro(conjonction_elim_gauche(hb1), conjonction_elim_gauche(hb2)),
        instancie(instancie(instancie(hF, u), vy), vyp))
    ypv = N.modus_ponens(conjonction_elim_droite(hb1), equivalence_avant(      # (yp,v)∈G
        N.modus_ponens(y_eq_yp, N.s6(vy, vyp, "t", appartient(E.couple(var("t"), v), vG)))))
    v_eq_z = N.modus_ponens(                                                   # v = z  (G fonctionnel)
        conjonction_intro(ypv, conjonction_elim_droite(hb2)),
        instancie(instancie(instancie(hG, vyp), v), z))

    # éliminer les deux existentiels
    elim2 = N.modus_ponens(ex2, existe_elimination(N.loi_deduction(body2, v_eq_z), "yp"))
    vz = N.modus_ponens(ex1, existe_elimination(N.loi_deduction(body1, elim2), "y"))
    imp = N.loi_deduction(h.conclusion, vz)                                    # (… et …) ⇒ v=z
    gen = N.generalisation("u", N.generalisation("v", N.generalisation("z", imp)))
    return N.loi_deduction(et(E.est_fonctionnel(vF), E.est_fonctionnel(vG)), gen)


def composee_intro(vG, vF, t1, t2, w, thm_fw, thm_wg):
    """De ⊢(t1,w)∈F et ⊢(w,t2)∈G, déduire ⊢ (t1,t2) ∈ G∘F   (introduction dans la composée)."""
    vy, vp, vr = var("y"), var("p"), var("r")
    inst = _inst_composee(vG, vF, E.couple(t1, t2))
    inner = et(appartient(E.couple(t1, vy), vF), appartient(E.couple(vy, t2), vG))
    ex_y = N.modus_ponens(conjonction_intro(thm_fw, thm_wg), N.s5(inner, w, "y"))   # (∃y)(...)
    body = et(egal(E.couple(t1, t2), E.couple(vp, vr)),
              existe("y", et(appartient(E.couple(vp, vy), vF), appartient(E.couple(vy, vr), vG))))
    wit = conjonction_intro(N.reflexivite(E.couple(t1, t2)), ex_y)
    gbody = subst_f(t1, "p", body)
    full = N.modus_ponens(N.modus_ponens(wit, N.s5(gbody, t2, "r")),
                          N.s5(existe("r", body), t1, "p"))
    return N.modus_ponens(full, equivalence_arriere(inst))


def composition_valeur(g="G", f="F", x="x"):
    """⊢ (g∘f)(x) = g(f(x))   sous {F fonctionnel, G fonctionnel, x∈dom F, f(x)∈dom G}.

    Verrou clé : la valeur d'une composée au niveau des fonctions. (E.II.16, x↦g(f(x)).)"""
    vG, vF, vx, vy = _tc(g), _tc(f), _tc(x), var("y")   # g,f,x acceptent un TERME composé
    comp = E.composee(vG, vF)
    fx = E.valeur(vF, vx)
    gfx = E.valeur(vG, fx)                              # g(f(x))
    gof = E.valeur(comp, vx)                            # (g∘f)(x)
    in_comp = composee_intro(vG, vF, vx, gfx, fx,       # (x, g(f(x))) ∈ G∘F  [hyps x∈domF, f(x)∈domG]
                             valeur_dans_graphe(vF, vx), valeur_dans_graphe(vG, fx))
    vc = valeur_caracterisation(comp, vx)              # ((x,y)∈comp ⇔ y=(g∘f)(x)) [hyps comp func, comp dom]
    vc_gfx = instancie(N.generalisation("y", vc), gfx)  # ((x,g(f(x)))∈comp ⇔ g(f(x))=(g∘f)(x))
    eq = N.modus_ponens(in_comp, equivalence_avant(vc_gfx))   # g(f(x))=(g∘f)(x)
    # cut de l'hypothèse « (∃y)(x,y)∈comp » (dérivée de in_comp)
    comp_dom = N.modus_ponens(in_comp, N.s5(appartient(E.couple(vx, vy), comp), gfx, "y"))
    eq1 = N.modus_ponens(comp_dom, N.loi_deduction(existe("y", appartient(E.couple(vx, vy), comp)), eq))
    # cut de l'hypothèse « comp fonctionnel » (via Proposition 6)
    comp_func = N.modus_ponens(conjonction_intro(N.assume(E.est_fonctionnel(vF)),
                                                 N.assume(E.est_fonctionnel(vG))),
                               composee_fonctionnelle(g, f))
    eq2 = N.modus_ponens(comp_func, N.loi_deduction(E.est_fonctionnel(comp), eq1))
    return N.modus_ponens(eq2, symetrie(gfx, gof))      # (g∘f)(x) = g(f(x))


__all__ = ["composee_fonctionnelle", "composee_intro", "composition_valeur"]
