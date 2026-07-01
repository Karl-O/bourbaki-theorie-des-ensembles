"""§II.5.2 — PROPOSITION 2 (E II.31, n° 2), CAS SURJECTIF (2°) — forme
rétraction/section, au niveau des GRAPHES fonctionnels.

ÉNONCÉ (E II.31, Prop. 2, 2°).  u : E'→E injective, v : F→F' surjective ⟹ la fonction
f ↦ v∘f∘u de 𝓕(E;F) dans 𝓕(E';F') est SURJECTIVE.
PREUVE de Bourbaki : « soit r' une rétraction de u, s' une section de v ; pour toute
g : E'→F', on a v∘(s'∘g∘r')∘u = (v∘s')∘g∘(r'∘u) = g », donc f := s'∘g∘r' est un
antécédent de g.

CE QU'ON FORMALISE ICI (2°, honnête et CLOS).  La surjectivité est une EXISTENCE :
il faut EXHIBER un antécédent f.  On le CONSTRUIT comme graphe-terme
    f := graphe_terme(E, s'(g(r'(x))), 'x')     (donc f(x) = s'(g(r'(x))) sur E),
et on prouve que c'est une application E→F dont la conjuguée v∘f∘u vaut g
ponctuellement.  Contrairement au cas 1° (∀ sur des f donnés, cf.
`ensembles_conjugaison_prop2_ii5`), 2° exige de CONSTRUIRE et d'ÉVALUER un objet : on
évalue f au point u(x') (un point-τ), ce qui rerencontre le VERROU-τ.  On le LÈVE
grâce au liant paramétrable de `valeur(·,·,b=…)` (« levée du verrou liant valeur ») :
le terme définissant f emploie des liants FRAIS (r'→'c', g→'b', s'→'a') distincts du
liant interne 'y' de graphe_terme_valeur / valeur_caracterisation, ce qui évite la
capture (v→'d', u→'y' par défaut).  Ainsi graphe_terme_valeur donne f(u(x'))=s'(g(r'(u(x')))),
puis r'(u(x'))=x' (rétraction) et v(s'(y'))=y' (section) donnent v(f(u(x')))=g(x').

CONCLUSION (CLOSE, curryfiée sous 6 hypothèses fidèles : u:E'→E, r' rétraction de u
[action r'∘u=Id], s':F'→F section de v [action v∘s'=Id], g:E'→F') :
    ⊢ (H₀ ⇒ … ⇒ H₅ ⇒ (∃f)( f fonctionnel ∧ dom f=E ∧ (∀x∈E)f(x)∈F
                              ∧ (∀x'∈E') v(f(u(x')))=g(x') ))
soit « il existe une application f : E→F dont la conjuguée v∘f∘u égale g » — la
surjectivité de f ↦ v∘f∘u.  Rien postulé ; theorie_ensembles INCHANGÉE (22 axiomes).
Restent REPORTÉS : l'OBJET-conjugaison lui-même, et le passage aux hypothèses
« u injective / v surjective » (⟹ rétraction/section) — pour la rétraction voir
[[bourbaki-verrou-tau-contournement]] (`retraction_construite_par_tau`, action).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, pourtout, existe)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie, equivalence_avant)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme)
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur, graphe_terme_domaine)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _defs(g, u, rp, sp, v, e, ep, f_set, fp):
    """Termes/constructeurs partagés (liants FRAIS pour éviter la capture-τ)."""
    vg, vu, vrp, vsp, vv = _t(g), _t(u), _t(rp), _t(sp), _t(v)
    vE, vEp, vF, vFp = _t(e), _t(ep), _t(f_set), _t(fp)
    Rp = lambda pt: E.valeur(vrp, pt, b="c")            # r'(pt)
    G = lambda pt: E.valeur(vg, pt, b="b")              # g(pt)
    Sp = lambda pt: E.valeur(vsp, pt, b="a")            # s'(pt)
    U = lambda pt: E.valeur(vu, pt)                     # u(pt)   (liant « y » défaut)
    Vv = lambda pt: E.valeur(vv, pt, b="d")             # v(pt)
    T = lambda pt: Sp(G(Rp(pt)))                        # s'(g(r'(pt)))
    witness = E.graphe_terme(vE, T(var("x")), "x")      # f := x ↦ s'(g(r'(x)))
    return (vg, vu, vrp, vsp, vv, vE, vEp, vF, vFp, Rp, G, Sp, U, Vv, T, witness)


def _hyps(vu, vrp, vg, vsp, vv, vE, vEp, vF, vFp, Rp, G, Sp, U, Vv):
    """Les 6 hypothèses ORDONNÉES (u:E'→E ; r' rétr. de u ; r':E→E' ; s' sect. de v ;
    s':F'→F ; g:E'→F')."""
    x, xp, yp = var("x"), var("xp"), var("yp")
    return [
        pourtout("xp", impl(appartient(xp, vEp), appartient(U(xp), vE))),          # u:E'→E
        pourtout("xp", impl(appartient(xp, vEp), egal(Rp(U(xp)), xp))),            # r'∘u=Id
        pourtout("x", impl(appartient(x, vE), appartient(Rp(x), vEp))),            # r':E→E'
        pourtout("yp", impl(appartient(yp, vFp), egal(Vv(Sp(yp)), yp))),           # v∘s'=Id
        pourtout("yp", impl(appartient(yp, vFp), appartient(Sp(yp), vF))),         # s':F'→F
        pourtout("xp", impl(appartient(xp, vEp), appartient(G(xp), vFp))),         # g:E'→F'
    ]


def _corps(fterm, vg, vu, vv, vE, vEp, vF):
    """Corps de l'existentielle : f application E→F de conjuguée g (liant valeurs 'xv')."""
    xv, xp = var("xv"), var("xp")
    return et(et(et(
        E.est_fonctionnel(fterm),
        egal(E.dom(fterm), vE)),
        pourtout("xv", impl(appartient(xv, vE), appartient(E.valeur(fterm, xv), vF)))),
        pourtout("xp", impl(appartient(xp, vEp),
                            egal(E.valeur(vv, E.valeur(fterm, E.valeur(vu, xp)), b="d"),
                                 E.valeur(vg, xp, b="b")))))


# @livre Ch.II §5.2 Prop.2 | E II.31 L.41-44 | PDF p.82
def prop2_conjugaison_surjective(g="g", u="u", rp="rp", sp="sp", v="v",
                                 e="E", ep="Ep", f_set="F", fp="Fp"):
    """⊢ (H₀ ⇒ … ⇒ H₅ ⇒ (∃f)(f:E→F ∧ v∘f∘u = g)).   (PROPOSITION 2, cas 2° surjectif.)

    Antécédent CONSTRUIT f := graphe_terme(E, s'(g(r'(x))), 'x').  Verrou-τ levé par
    liants frais dans le terme définissant f (cf. docstring de module)."""
    (vg, vu, vrp, vsp, vv, vE, vEp, vF, vFp, Rp, G, Sp, U, Vv, T, witness) = _defs(
        g, u, rp, sp, v, e, ep, f_set, fp)
    x, xv, xp = var("x"), var("xv"), var("xp")

    (H_u, H_ret, H_rpt, H_sec, H_spt, H_gt) = _hyps(
        vu, vrp, vg, vsp, vv, vE, vEp, vF, vFp, Rp, G, Sp, U, Vv)
    h_u, h_ret, h_rpt = N.assume(H_u), N.assume(H_ret), N.assume(H_rpt)
    h_sec, h_spt, h_gt = N.assume(H_sec), N.assume(H_spt), N.assume(H_gt)

    # f(p) = s'(g(r'(p)))  généralisé : (∀p)(p∈E ⇒ f(p)=T(p))
    gtv = graphe_terme_valeur(vE, T(var("x")), "p", "x", "y")   # {p∈E} ⊢ f(p)=T(p)
    gtv_gen = N.generalisation("p", N.loi_deduction(appartient(var("p"), vE), gtv))

    # ── (∀x'∈E') v(f(u(x'))) = g(x')  (la conjuguée vaut g) ──────────────────────
    hxp = N.assume(appartient(xp, vEp))
    ux_in_E = N.modus_ponens(hxp, instancie(h_u, xp))                  # u(x')∈E
    fval = N.modus_ponens(ux_in_E, instancie(gtv_gen, U(xp)))          # f(u(x'))=s'(g(r'(u(x'))))
    rux = N.modus_ponens(hxp, instancie(h_ret, xp))                    # r'(u(x'))=x'
    # congruences r'(u(x'))→x' sous g(·) puis s'(·) : f(u(x')) = s'(g(x'))
    cong_g = N.modus_ponens(rux, congruence_terme(Rp(U(xp)), xp, E.valeur(vg, var("w"), b="b")))
    cong_s = N.modus_ponens(cong_g, congruence_terme(
        G(Rp(U(xp))), G(xp), E.valeur(vsp, var("w"), b="a")))
    fu_eq = composer_egalites(fval, cong_s)                           # f(u(x')) = s'(g(x'))
    # v(f(u(x'))) = v(s'(g(x'))) = g(x')
    cong_v = N.modus_ponens(fu_eq, congruence_terme(
        E.valeur(witness, U(xp)), Sp(G(xp)), E.valeur(vv, var("w"), b="d")))
    gx_in_Fp = N.modus_ponens(hxp, instancie(h_gt, xp))               # g(x')∈F'
    sec_at_gx = N.modus_ponens(gx_in_Fp, instancie(h_sec, G(xp)))     # v(s'(g(x')))=g(x')
    conj_at_xp = composer_egalites(cong_v, sec_at_gx)                 # v(f(u(x')))=g(x')
    CONJ = N.generalisation("xp", N.loi_deduction(appartient(xp, vEp), conj_at_xp))

    # ── (∀x∈E) f(x)∈F  (f est à valeurs dans F) ─────────────────────────────────
    hxv = N.assume(appartient(xv, vE))
    fvalx = N.modus_ponens(hxv, instancie(gtv_gen, xv))              # f(x)=s'(g(r'(x)))
    rpx = N.modus_ponens(hxv, instancie(h_rpt, xv))                  # r'(x)∈E'
    grpx = N.modus_ponens(rpx, instancie(h_gt, Rp(xv)))             # g(r'(x))∈F'
    sgrpx = N.modus_ponens(grpx, instancie(h_spt, G(Rp(xv))))       # s'(g(r'(x)))∈F
    # réécriture f(x)∈F via f(x)=s'(g(r'(x)))  (Leibniz S6)
    Tx, fx = T(xv), E.valeur(witness, xv)
    leib = N.s6(Tx, fx, "w", appartient(var("w"), vF))
    Tx_eq_fx = N.modus_ponens(fvalx, symetrie(fx, Tx))              # s'(g(r'(x)))=f(x)
    fx_in_F = N.modus_ponens(sgrpx, equivalence_avant(N.modus_ponens(Tx_eq_fx, leib)))
    VALUES = N.generalisation("xv", N.loi_deduction(appartient(xv, vE), fx_in_F))

    # f fonctionnel et dom f = E  (graphe_terme, clos)
    gtf = graphe_terme_fonctionnel(vE, T(var("x")), "x", "y")        # est_fonctionnel(f)
    gtd = graphe_terme_domaine(vE, T(var("x")), "x", "y", "z")       # dom f = E

    # ∃f : le corps pour le témoin f = graphe_terme(...)
    conj = conjonction_intro(conjonction_intro(conjonction_intro(gtf, gtd), VALUES), CONJ)
    ex = N.modus_ponens(conj, N.s5(_corps(var("f"), vg, vu, vv, vE, vEp, vF), witness, "f"))

    resultat = ex
    for H in (H_gt, H_spt, H_sec, H_rpt, H_ret, H_u):
        resultat = N.loi_deduction(H, resultat)
    return resultat


def cible_prop2_conjugaison_surjective(g="g", u="u", rp="rp", sp="sp", v="v",
                                       e="E", ep="Ep", f_set="F", fp="Fp"):
    """Conclusion EXACTE attendue de `prop2_conjugaison_surjective` (pour les tests)."""
    (vg, vu, vrp, vsp, vv, vE, vEp, vF, vFp, Rp, G, Sp, U, Vv, T, witness) = _defs(
        g, u, rp, sp, v, e, ep, f_set, fp)
    hyps = _hyps(vu, vrp, vg, vsp, vv, vE, vEp, vF, vFp, Rp, G, Sp, U, Vv)
    concl = existe("f", _corps(var("f"), vg, vu, vv, vE, vEp, vF))
    for H in reversed(hyps):
        concl = impl(H, concl)
    return concl


__all__ = ["prop2_conjugaison_surjective", "cible_prop2_conjugaison_surjective"]
