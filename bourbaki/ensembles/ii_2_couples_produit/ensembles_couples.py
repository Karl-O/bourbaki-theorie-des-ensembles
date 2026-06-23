"""§II.2 — injectivité des paires et Proposition 1 (sens difficile).

Lemmes d'injectivité (tous certifiés par le noyau abrégé), puis la Proposition 1
de Bourbaki (E.II.30) : (x,y)=(x',y') ⇒ (x=x' et y=y'), avec (x,y):={{x},{x,y}}.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, ou, appartient, impl


def _T(v):
    """Coercion nom→terme : accepte un Terme ou un nom de variable."""
    return v if isinstance(v, Terme) else var(v)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (_instance_paire, appartient_singleton,
                                 appartient_paire_gauche, appartient_paire_droite)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, cas)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import couple_egal_si_composantes


# ── Lemmes d'appartenance / injectivité ───────────────────────────────────────
def singleton_membre(a, c):
    """⊢ (a ∈ {c}) ⇔ (a = c).   ({c} = {c,c}, axiome de la paire + idempotence ∨.)"""
    eq = egal(a, c)
    inst = _instance_paire(c, c, a)                    # (a∈{c,c}) ⇔ (a=c ∨ a=c)
    idem = conjonction_intro(N.s1(eq), N.s2(eq, eq))   # (a=c ∨ a=c) ⇔ (a=c)
    return equivalence_transitivite(inst, idem)        # (a∈{c}) ⇔ (a=c)


def singleton_injectif(x="x", xp="xp"):
    """⊢ ({x} = {x'}) ⇒ (x = x').   (x, x' : noms OU termes.)"""
    vx, vxp = _T(x), _T(xp)
    sx, sxp = E.singleton(vx), E.singleton(vxp)
    h = N.assume(egal(sx, sxp))
    leib = N.s6(sx, sxp, "w", appartient(vx, var("w")))   # (Sx=Sx')⇒((x∈Sx)⇔(x∈Sx'))
    equ = N.modus_ponens(h, leib)
    x_dans_sxp = N.modus_ponens(membre_paire_gauche(vx, vx), equivalence_avant(equ))  # x∈{x'}
    eq = N.modus_ponens(x_dans_sxp, equivalence_avant(singleton_membre(vx, vxp)))  # x=x'
    return N.loi_deduction(egal(sx, sxp), eq)


def singleton_egale_paire(c="c", a="a", b="b"):
    """⊢ ({c} = {a,b}) ⇒ (a=c et b=c).   (c, a, b : noms OU termes.)"""
    vc, va, vb = _T(c), _T(a), _T(b)
    sc, p = E.singleton(vc), E.paire(va, vb)
    h = N.assume(egal(sc, p))

    def coord(membre_thm, t):                          # t∈{a,b} ⊢ → t=c
        leib = N.s6(sc, p, "w", appartient(t, var("w")))   # (Sc=P)⇒((t∈Sc)⇔(t∈P))
        equ = N.modus_ponens(h, leib)
        t_dans_sc = N.modus_ponens(membre_thm, equivalence_arriere(equ))  # t∈{c}
        return N.modus_ponens(t_dans_sc, equivalence_avant(singleton_membre(t, vc)))

    eqa = coord(membre_paire_gauche(va, vb), va)       # a=c
    eqb = coord(membre_paire_droite(va, vb), vb)       # b=c
    return N.loi_deduction(egal(sc, p), conjonction_intro(eqa, eqb))


# ── Appartenance à une paire de TERMES quelconques ────────────────────────────
def membre_paire_gauche(t, u):
    """⊢ t ∈ {t, u}  (t, u termes quelconques)."""
    c = _instance_paire(t, u, t)                       # (t∈{t,u}) ⇔ (t=t ∨ t=u)
    ortt = N.modus_ponens(N.reflexivite(t), N.s2(egal(t, t), egal(t, u)))
    return N.modus_ponens(ortt, equivalence_arriere(c))


def membre_paire_droite(t, u):
    """⊢ u ∈ {t, u}  (t, u termes quelconques)."""
    c = _instance_paire(t, u, u)                       # (u∈{t,u}) ⇔ (u=t ∨ u=u)
    uu = N.modus_ponens(N.reflexivite(u), N.s2(egal(u, u), egal(u, t)))   # u=u ∨ u=t
    oru = N.modus_ponens(uu, N.s3(egal(u, u), egal(u, t)))                # u=t ∨ u=u
    return N.modus_ponens(oru, equivalence_arriere(c))


# ── Cancellation des paires : {a,b}={a,c} ⇒ b=c ───────────────────────────────
def paire_cancellation(ta, tb, tc):
    """⊢ ({a,b} = {a,c}) ⇒ (b = c)  (a, b, c termes ; coordonnée commune à gauche)."""
    pab, pac = E.paire(ta, tb), E.paire(ta, tc)
    h = N.assume(egal(pab, pac))
    # b ∈ {a,b} → b ∈ {a,c} → (b=a ∨ b=c)
    leib_b = N.modus_ponens(h, N.s6(pab, pac, "w", appartient(tb, var("w"))))
    b_in_ac = N.modus_ponens(membre_paire_droite(ta, tb), equivalence_avant(leib_b))
    disj_b = N.modus_ponens(b_in_ac, equivalence_avant(_instance_paire(ta, tc, tb)))
    # c ∈ {a,c} → c ∈ {a,b} → (c=a ∨ c=b)
    leib_c = N.modus_ponens(h, N.s6(pab, pac, "w", appartient(tc, var("w"))))
    c_in_ab = N.modus_ponens(membre_paire_droite(ta, tc), equivalence_arriere(leib_c))
    disj_c = N.modus_ponens(c_in_ab, equivalence_avant(_instance_paire(ta, tb, tc)))
    # cas interne : sous (b=a), de (c=a ∨ c=b) conclure (b=c)
    hba = N.assume(egal(tb, ta))                       # b=a
    a_eq_c = N.modus_ponens(N.assume(egal(tc, ta)), symetrie(tc, ta))   # {c=a} ⊢ a=c
    br_ca = N.loi_deduction(egal(tc, ta), composer_egalites(hba, a_eq_c))   # (c=a)⇒(b=c)
    br_cb = symetrie(tc, tb)                            # (c=b)⇒(b=c)
    sous_ba = N.loi_deduction(egal(tb, ta), cas(disj_c, br_ca, br_cb))      # (b=a)⇒(b=c)
    # cas externe : (b=a ∨ b=c)
    br_bc = a_implique_a(egal(tb, tc))                 # (b=c)⇒(b=c)
    return N.loi_deduction(egal(pab, pac), cas(disj_b, sous_ba, br_bc))


# ── Proposition 1, sens difficile ─────────────────────────────────────────────
def couple_egal_implique_composantes(x="x", y="y", xp="xp", yp="yp"):
    """⊢ ((x,y)=(x',y')) ⇒ (x=x' et y=y').  (sens difficile de la Proposition 1 ; noms OU termes.)"""
    vx, vy, vxp, vyp = _T(x), _T(y), _T(xp), _T(yp)
    w = var("w")
    cx, cxy = E.singleton(vx), E.paire(vx, vy)
    cxp, cxpyp = E.singleton(vxp), E.paire(vxp, vyp)
    gauche, droite = E.couple(vx, vy), E.couple(vxp, vyp)   # {{x},{x,y}}, {{x'},{x',y'}}
    h = N.assume(egal(gauche, droite))

    # ── x = x' ─────────────────────────────────────────────────────────────────
    cx_dans_g = membre_paire_gauche(cx, cxy)               # {x} ∈ gauche
    leib = N.modus_ponens(h, N.s6(gauche, droite, "w", appartient(cx, w)))
    cx_dans_d = N.modus_ponens(cx_dans_g, equivalence_avant(leib))   # {x} ∈ droite
    disj = N.modus_ponens(cx_dans_d,
                          equivalence_avant(_instance_paire(cxp, cxpyp, cx)))  # {x}={x'} ∨ {x}={x',y'}
    br1 = singleton_injectif(x, xp)                        # ({x}={x'}) ⇒ (x=x')
    hb = N.assume(egal(cx, cxpyp))                         # {x}={x',y'}
    xpx = conjonction_elim_gauche(N.modus_ponens(hb, singleton_egale_paire(x, xp, yp)))  # x'=x
    br2 = N.loi_deduction(egal(cx, cxpyp), N.modus_ponens(xpx, symetrie(vxp, vx)))  # ⇒ x=x'
    x_eq = cas(disj, br1, br2)                             # {h} ⊢ x=x'

    # ── {x,y} = {x',y'} ──────────────────────────────────────────────────────
    cx_eq = N.modus_ponens(x_eq, congruence_terme(vx, vxp, E.singleton(w)))   # {x}={x'}
    # réécrire la 1ʳᵉ coordonnée de `droite` : {x'} ↦ {x}
    rp_eq_r = N.modus_ponens(cx_eq, congruence_terme(cx, cxp, E.paire(w, cxpyp)))
    r_eq_rp = N.modus_ponens(rp_eq_r, symetrie(E.paire(cx, cxpyp), droite))    # droite = {{x},{x',y'}}
    g_eq_rp = composer_egalites(h, r_eq_rp)                # {{x},{x,y}} = {{x},{x',y'}}
    cxy_eq = N.modus_ponens(g_eq_rp, paire_cancellation(cx, cxy, cxpyp))       # {x,y}={x',y'}

    # ── y = y' ─────────────────────────────────────────────────────────────────
    xp_eq_x = N.modus_ponens(x_eq, symetrie(vx, vxp))      # x'=x
    cxpyp_eq = N.modus_ponens(xp_eq_x, congruence_terme(vxp, vx, E.paire(w, vyp)))  # {x',y'}={x,y'}
    cxy_eq2 = composer_egalites(cxy_eq, cxpyp_eq)          # {x,y}={x,y'}
    y_eq = N.modus_ponens(cxy_eq2, paire_cancellation(vx, vy, vyp))            # y=y'

    return N.loi_deduction(egal(gauche, droite), conjonction_intro(x_eq, y_eq))


def proposition_1(x="x", y="y", xp="xp", yp="yp"):
    """⊢ ((x,y)=(x',y')) ⇔ (x=x' et y=y').  (Proposition 1, E.II.30 — énoncé complet.)"""
    dur = couple_egal_implique_composantes(x, y, xp, yp)   # ⇒
    facile = couple_egal_si_composantes(x, y, xp, yp)      # ⇐
    return conjonction_intro(dur, facile)                  # ⇔


__all__ = ["singleton_membre", "singleton_injectif", "singleton_egale_paire",
           "membre_paire_gauche", "membre_paire_droite", "paire_cancellation",
           "couple_egal_implique_composantes", "proposition_1"]
