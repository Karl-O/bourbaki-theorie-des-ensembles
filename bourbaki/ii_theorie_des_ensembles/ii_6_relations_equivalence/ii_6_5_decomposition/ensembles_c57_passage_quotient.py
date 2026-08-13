"""§II.6.5 C57 — l'application déduite par passage au quotient EXISTE.

────────────────────────────────────────────────────────────────────────────────
« Lorsque f est compatible avec R, on la met sous la forme h∘p, h : E/R → F
étant uniquement déterminée » (E II.44, critère C57).  L'existence de h était
REPORTÉE dans tout le projet (cf. application_deduite_quotient) ; elle est
établie ici SANS axiome du choix, par le TÉMOIN CANONIQUE τ de Bourbaki
(motif `section_construite_par_tau`, E II.18) :

    s(t) := τz( t = p(z) )                    témoin canonique de la classe t
    H    := graphe_terme( Q, f(s(t)), t )     (kit C54 — CONSTRUIT, pas postulé)

  { f compatible : (∀x)(∀y)( R{x,y} ⇒ f(x)=f(y) ),
    caractérisation : (∀x)(∀y)( p(x)=p(y) ⇔ R{x,y} ),  p(x)∈Q }
      ⊢  H( p(x) )  =  f(x)                     — « f = H∘p », au point.

Deux étages : (1) c57_valeur_au_temoin ⊢ f(s(p(x)))=f(x) — la valeur de f ne
dépend que de la CLASSE et le témoin canonique la réalise ; (2) c57_application
_deduite emballe en graphe par le kit C54 (relais noms→termes : le point p(x)
est un τ, il ne traverse pas les liants internes du kit ; on prouve au NOM
« ptq » puis on généralise-instancie).
⚠️ LIANT « y » OBLIGATOIRE dans le kit C54 dès que le terme contient
valeur(·,·) : valeur(F,x) EST τy((x,y)∈F), donc l'existentielle de domaine
(∃y)((u,y)∈F) doit garder « y » — passer y="yq" casse la décharge (piège
diagnostiqué le 3 août : ce n'est PAS une limite du kit, c'est un mauvais
choix de liant).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, tau, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def section_canonique(p, e, t="t", z="zq"):
    """s(t) := τz( z∈E et t = p(z) )  — témoin canonique PRIS DANS E.

    ⚠️ La garde « z∈E » est INDISPENSABLE (leçon du 4 août 2026) : sans elle,
    s(t) peut tomber hors de E et la caractérisation du quotient devient
    insatisfiable — cf. l'avertissement en tête de module."""
    return tau(z, et(appartient(var(z), _t(e)),
                     egal(var(t), E.valeur(_t(p), var(z)))))


def graphe_deduit(f, p, quot, e, t="t", z="zq"):
    """H := graphe_terme( Q, f(s(t)), t )  — l'application déduite CONSTRUITE."""
    return E.graphe_terme(_t(quot),
                          E.valeur(_t(f), section_canonique(p, e, t, z)), t)


def hyp_compatible(f, R, x="xq", y="yq"):
    """(∀x)(∀y)( R{x,y} ⇒ f(x) = f(y) )  — « f est compatible avec R » (E II.44)."""
    vf, vx, vy = _t(f), var(x), var(y)
    return pourtout(x, pourtout(y, impl(R(vx, vy),
                                        egal(E.valeur(vf, vx), E.valeur(vf, vy)))))


def hyp_quotient_caracterise(p, R, e, x="xq", y="yq"):
    """(∀x)(∀y)( (x∈E et y∈E) ⇒ ( p(x)=p(y) ⇔ R{x,y} ) )  — GARDÉE PAR E.

    ⚠️ LA GARDE EST OBLIGATOIRE.  Sans elle l'hypothèse est INSATISFIABLE pour
    tout graphe p de domaine E : hors du domaine, p(x)=τy((x,y)∈p) porte sur
    une relation identiquement fausse, donc S7 identifie TOUS ces p(x) entre
    eux — on aurait p(x)=p(y) sans R{x,y}.  (Diagnostic du 4 août 2026 ; même
    famille de piège que l'incohérence de l'intersection : une hypothèse
    « honnête » mais insatisfiable rend tous les théorèmes qui la portent
    VACUEUX.)"""
    vp, vE, vx, vy = _t(p), _t(e), var(x), var(y)
    return pourtout(x, pourtout(y, impl(
        et(appartient(vx, vE), appartient(vy, vE)),
        _equiv(egal(E.valeur(vp, vx), E.valeur(vp, vy)), R(vx, vy)))))


def _equiv(a, b):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    return equiv(a, b)


# @livre Ch.II §6.5 Crit.C57 | E II.44 L.22-27 | PDF p.95  (C57, CŒUR : la valeur de f au témoin canonique de la classe redonne f(x) — sans axiome du choix, section GARDÉE par E)
def c57_valeur_au_temoin(f="f", p="P", e="Eq", R=None, x="xq", z="zq"):
    """{ f compatible, p caractérise R SUR E, x∈E } ⊢ f( s(p(x)) ) = f(x),
    s(t) := τz( z∈E et t = p(z) ) — témoin canonique PRIS DANS E.

    Preuve : x lui-même est témoin (x∈E et p(x)=p(x)), donc le témoin
    canonique en est un aussi (existe_temoin) — ce qui donne À LA FOIS
    s(p(x))∈E et p(x)=p(s(p(x))).  La caractérisation GARDÉE s'applique alors
    (ses gardes sont x∈E et s(p(x))∈E, cette dernière venant du témoin : c'est
    exactement pourquoi la section doit être gardée), d'où R{x,s(p(x))} puis
    f(x)=f(s(p(x))) par compatibilité."""
    if R is None:
        R = lambda u, v: appartient(E.couple(u, v), var("GR"))
    vf, vp, vE, vx = _t(f), _t(p), _t(e), var(x)
    px = E.valeur(vp, vx)
    s_px = tau(z, et(appartient(var(z), vE), egal(px, E.valeur(vp, var(z)))))
    hcomp = N.assume(hyp_compatible(vf, R))
    hcar = N.assume(hyp_quotient_caracterise(vp, R, vE))
    hx = N.assume(appartient(vx, vE))

    Rz = et(appartient(var(z), vE), egal(px, E.valeur(vp, var(z))))
    ex = N.modus_ponens(conjonction_intro(hx, N.reflexivite(px)),
                        N.s5(Rz, vx, z))                       # (∃z)(z∈E et p(x)=p(z))
    both = N.modus_ponens(ex, N.existe_temoin(Rz, z))
    s_in_E = conjonction_elim_gauche(both)                     # s(p(x)) ∈ E
    p_eq = conjonction_elim_droite(both)                       # p(x)=p(s(p(x)))
    car_inst = N.modus_ponens(conjonction_intro(hx, s_in_E),
                              instancie(instancie(hcar, vx), s_px))
    r_xs = N.modus_ponens(p_eq, equivalence_avant(car_inst))
    f_eq = N.modus_ponens(r_xs, instancie(instancie(hcomp, vx), s_px))
    res = N.modus_ponens(f_eq, symetrie(E.valeur(vf, vx), E.valeur(vf, s_px)))
    assert res.conclusion == egal(E.valeur(vf, s_px), E.valeur(vf, vx)),         "c57_valeur_au_temoin : ≠ f(s(p(x)))=f(x)"
    assert set(res.hypotheses) == {hcomp.conclusion, hcar.conclusion,
                                   hx.conclusion}, "c57_valeur_au_temoin : hyps ≠ 3"
    return res


# @livre Ch.II §6.5 Crit.C57 | E II.44 L.22-27 | PDF p.95  (C57 : l'application déduite H EXISTE — graphe CONSTRUIT par le kit C54 sur le témoin canonique gardé — et vérifie H(p(x))=f(x))
def c57_application_deduite(f="f", p="P", quot="Q", e="Eq", R=None, x="xq",
                            t="t", z="zq"):
    """{ f compatible, p caractérise R SUR E, x∈E, p(x)∈Q } ⊢ H( p(x) ) = f(x).

    H = graphe_deduit(f,p,Q,E) est un GRAPHE CONSTRUIT (kit C54) : l'existence
    de l'application déduite n'est plus reportée.  C'est « f = H∘p » au point,
    forme exigée par les consommateurs (III.7 Prop. 6 1°, décompositions…).
    ⚠️ Les hypothèses sont GARDÉES par E — voir hyp_quotient_caracterise."""
    if R is None:
        R = lambda u, v: appartient(E.couple(u, v), var("GR"))
    vf, vp, vQ, vE, vx = _t(f), _t(p), _t(quot), _t(e), var(x)
    H = graphe_deduit(vf, vp, vQ, vE, t, z)
    px = E.valeur(vp, vx)
    hpx = N.assume(appartient(px, vQ))

    # (1) H(p(x)) = f(s(p(x)))   — kit C54 au NOM « ptq », puis noms→termes
    T = E.valeur(vf, section_canonique(vp, vE, t, z))
    val_nom = graphe_terme_valeur(vQ, T, "ptq", t, "y")
    gen = N.generalisation("ptq", N.loi_deduction(
        appartient(var("ptq"), vQ), val_nom))
    val = N.modus_ponens(hpx, instancie(gen, px))
    # (2) f(s(p(x))) = f(x)      — le cœur gardé (3 hyps honnêtes)
    res = composer_egalites(val, c57_valeur_au_temoin(vf, vp, vE, R, x, z))
    cible = egal(E.valeur(H, px), E.valeur(vf, vx))
    assert res.conclusion == cible, "c57_application_deduite : ≠ H(p(x))=f(x)"
    assert len(res.hypotheses) == 4, "c57_application_deduite : hyps ≠ 4"
    return res


def hyp_factorise(h, p, f, e, x="xu"):
    """(∀x)( x∈E ⇒ H(p(x)) = f(x) )  — « H factorise f à travers p », au point."""
    vh, vp, vf, vE, vx = _t(h), _t(p), _t(f), _t(e), var(x)
    return pourtout(x, impl(appartient(vx, vE),
                            egal(E.valeur(vh, E.valeur(vp, vx)),
                                 E.valeur(vf, vx))))


def hyp_p_surjective(p, e, quot, t="tu", x="xu"):
    """(∀t)( t∈Q ⇒ (∃x)( x∈E et t = p(x) ) )  — p est surjective de E sur Q."""
    vp, vE, vQ, vt, vx = _t(p), _t(e), _t(quot), var(t), var(x)
    return pourtout(t, impl(appartient(vt, vQ), existe(x, et(
        appartient(vx, vE), egal(vt, E.valeur(vp, vx))))))


def motif_final(vh, vhp, vt):
    """La conclusion ponctuelle : H(t) = H'(t)."""
    return egal(E.valeur(vh, vt), E.valeur(vhp, vt))


def _arriere(thm):
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_arriere,
    )
    return equivalence_arriere(thm)


# @livre Ch.II §6.5 Crit.C57 | E II.44 L.22-27 | PDF p.95  (C57, « ET UNE SEULE » : deux applications déduites de la même f coïncident sur le quotient — p étant surjective)
def c57_unicite(h="Hq", hp="Hpq", p="P", f="f", e="Eq", quot="Q",
                t="tu", x="xu"):
    """{ H factorise f, H' factorise f, p surjective } ⊢ (∀t)(t∈Q ⇒ H(t)=H'(t)).

    L'UNICITÉ de l'application déduite (E II.44) : sous t∈Q, la surjectivité
    de p donne t=p(x) avec x∈E ; les deux factorisations valent alors f(x) en
    ce point, et Leibniz (t=p(x)) transporte l'égalité en t.  Motif
    `coincidence_sur_quotient` (C57, II.44), ici pour des GRAPHES NUS."""
    vh, vhp, vp, vf = _t(h), _t(hp), _t(p), _t(f)
    vE, vQ = _t(e), _t(quot)
    vt, vx = var(t), var(x)

    h1 = N.assume(hyp_factorise(vh, vp, vf, vE, x))
    h2 = N.assume(hyp_factorise(vhp, vp, vf, vE, x))
    hs = N.assume(hyp_p_surjective(vp, vE, vQ, t, x))

    corps = et(appartient(vx, vE), egal(vt, E.valeur(vp, vx)))
    hb = N.assume(corps)
    xE = conjonction_elim_gauche(hb)
    e1 = N.modus_ponens(xE, instancie(h1, vx))          # H(p(x)) = f(x)
    e2 = N.modus_ponens(xE, instancie(h2, vx))          # H'(p(x)) = f(x)
    at_px = composer_egalites(e1, N.modus_ponens(e2, symetrie(
        E.valeur(vhp, E.valeur(vp, vx)), E.valeur(vf, vx))))
    #     H(p(x)) = H'(p(x))
    motif = egal(E.valeur(vh, var("w6t")), E.valeur(vhp, var("w6t")))
    at_t = N.modus_ponens(at_px, _arriere(N.modus_ponens(
        conjonction_elim_droite(hb),
        N.s6(vt, E.valeur(vp, vx), "w6t", motif))))
    ex = N.modus_ponens(N.assume(appartient(vt, vQ)), instancie(hs, vt))
    res = N.generalisation(t, N.loi_deduction(appartient(vt, vQ), N.modus_ponens(
        ex, existe_elimination(N.loi_deduction(corps, at_t), x))))
    assert res.conclusion == pourtout(t, impl(appartient(vt, vQ), motif_final(
        vh, vhp, vt))), "c57_unicite : ≠ coïncidence sur Q"
    assert len(res.hypotheses) == 3, "c57_unicite : hyps ≠ 3"
    return res

