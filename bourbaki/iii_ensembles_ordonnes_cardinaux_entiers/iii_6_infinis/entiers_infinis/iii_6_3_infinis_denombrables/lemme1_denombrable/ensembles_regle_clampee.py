# -*- coding: utf-8 -*-
"""§III.6.3 — K6a : LA RÈGLE CLAMPÉE (la borne V déchargée par tiers exclu).

🎯 CIBLES :

    clamp_E(t) := τ_z( (t∈E ∧ z=t) ∨ (¬(t∈E) ∧ z=x0) )      [le rabatteur]

    clamp_dans_E      :  { x0∈E }  ⊢  clamp_E(t) ∈ E
    regle_clampee_bornee :  { x0∈E }
        ⊢ regle_dans_V( T_{S_c, x0}, E )     où  S_c(t) = clamp_E(u(t))

LE VERROU V-BORNE : l'itération C63-vraie exige (∀p)(T(p)∈V) — pour une règle
S(t)=u(t) brute, T(p) est du bruit-τ hors-domaine et AUCUN ensemble V ne
convient.  Le CLAMP rabat toute valeur dans E : les deux disjoints de son τ
forcent z∈E (z=t sous t∈E, z=x0 sinon), et le TIERS EXCLU garantit qu'un
témoin existe TOUJOURS — d'où (∀p)(T(p)∈E), dérivable sous x0∈E seul.
Comme S_c est un callable opaque, T_{S_c,x0} = regle_iteration_vraie(S_c, x0)
telle quelle : les τ-évaluations de R8' (t_iter_en_vide, valeur_succ)
s'appliquent SANS modification ; l'équation au successeur donnera
g(n+1) = clamp_E(u(g(n))) = u(g(n)) dès que u(g(n))∈E (clamp_eval, K6b).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, non, tau, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_arriere, cas,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_N import (
    regle_iteration_vraie,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def tiers_exclu(A):
    """⊢ A ∨ ¬A   (a_implique_a encode ¬A∨A ; S3 commute)."""
    return N.modus_ponens(a_implique_a(A), N.s3(non(A), A))


def clamp_E(t, e, x0, zname="zcl"):
    """Le TERME rabatteur : τ_z( (t∈E ∧ z=t) ∨ (¬(t∈E) ∧ z=x0) )."""
    vt, ve, vx0, vz = _t(t), _t(e), _t(x0), var(zname)
    return tau(zname, ou(et(appartient(vt, ve), egal(vz, vt)),
                         et(non(appartient(vt, ve)), egal(vz, vx0))))


def regle_clampee(u, x0, e, zname="zcl", yname="ycl"):
    """T_{S_c, x0} := regle_iteration_vraie(S_c, x0) avec S_c(t)=clamp_E(u(t))."""
    vu, vx0, ve = _t(u), _t(x0), _t(e)

    def S_c(t):
        return clamp_E(E.valeur(vu, t), ve, vx0, zname)

    return regle_iteration_vraie(S_c, vx0, yname), S_c


def clamp_dans_E(t, e, x0, zname="zcl"):
    """{ x0∈E } ⊢ clamp_E(t) ∈ E                              [1 hyp honnête].

    Tiers exclu sur t∈E fournit TOUJOURS un témoin (t ou x0) au τ ;
    existe_temoin donne la condition au τ, dont les DEUX disjoints forcent
    l'appartenance à E (Leibniz depuis t∈E resp. x0∈E)."""
    vt, ve, vx0 = _t(t), _t(e), _t(x0)
    C = clamp_E(vt, ve, vx0, zname)
    cond = C.args[0]
    vz = var(zname)
    tE = appartient(vt, ve)
    gauche_f = et(tE, egal(vz, vt))
    droite_f = et(non(tE), egal(vz, vx0))

    h_x0 = N.assume(appartient(vx0, ve))                    # x0∈E     [HONNÊTE]

    # (∃z)cond — par tiers exclu sur t∈E
    h_a = N.assume(tE)
    dA = N.modus_ponens(conjonction_intro(h_a, N.reflexivite(vt)),
                        N.s2(et(tE, egal(vt, vt)), et(non(tE), egal(vt, vx0))))
    exA = N.modus_ponens(dA, N.s5(cond, vt, zname))
    impA = N.loi_deduction(tE, exA)
    h_b = N.assume(non(tE))
    dB0 = N.modus_ponens(conjonction_intro(h_b, N.reflexivite(vx0)),
                         N.s2(et(non(tE), egal(vx0, vx0)), et(tE, egal(vx0, vt))))
    dB = N.modus_ponens(dB0, N.s3(et(non(tE), egal(vx0, vx0)),
                                  et(tE, egal(vx0, vt))))
    exB = N.modus_ponens(dB, N.s5(cond, vx0, zname))
    impB = N.loi_deduction(non(tE), exB)
    ex = cas(tiers_exclu(tE), impA, impB)                   # (∃z)cond

    # cond(τ), puis par cas : les deux disjoints forcent C∈E
    cd = N.modus_ponens(ex, N.existe_temoin(cond, zname))
    gT = et(tE, egal(C, vt))
    dT = et(non(tE), egal(C, vx0))
    h_g = N.assume(gT)
    c_in_A = N.modus_ponens(conjonction_elim_gauche(h_g), equivalence_arriere(
        N.modus_ponens(conjonction_elim_droite(h_g),
                       N.s6(C, vt, "wcl", appartient(var("wcl"), ve)))))
    h_d = N.assume(dT)
    c_in_B = N.modus_ponens(h_x0, equivalence_arriere(
        N.modus_ponens(conjonction_elim_droite(h_d),
                       N.s6(C, vx0, "wcl", appartient(var("wcl"), ve)))))
    res = cas(cd, N.loi_deduction(gT, c_in_A), N.loi_deduction(dT, c_in_B))
    assert res.conclusion == appartient(C, ve), "clamp_dans_E : forme"
    assert list(res.hypotheses) == [appartient(vx0, ve)], "clamp_dans_E : hyps"
    return res


def regle_clampee_bornee(u, x0, e, zname="zcl", yname="ycl", p="pgv"):
    """🎯 K6a : { x0∈E } ⊢ regle_dans_V( T_{S_c,x0}, E )     [1 hyp honnête].

    Le même argument un niveau au-dessus : tiers exclu sur p=∅, les deux
    disjoints du τ de T forcent y∈E (y=x0, ou y=clamp∈E par clamp_dans_E)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import terme_plus_grand
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
    vu, vx0, ve, vp = _t(u), _t(x0), _t(e), var(p)
    T, S_c = regle_clampee(u, x0, e, zname, yname)
    Tp = T(vp)
    cond = Tp.args[0]
    pv = egal(vp, E.VIDE)
    # les sorties, RECONSTRUITES par les mêmes builders que la règle (et() est
    # encodé : jamais d'extraction structurelle — leçon des builders)
    prev = E.valeur(vp, terme_plus_grand(inf_egal_card, E.dom(vp), "m", "x"))
    ARG = E.valeur(vu, prev)                                # u(p(M))
    Sc_terme = S_c(prev)                                    # clamp_E(u(p(M)))

    h_x0 = N.assume(appartient(vx0, ve))                    # x0∈E     [HONNÊTE]
    h_a = N.assume(pv)
    dA = N.modus_ponens(conjonction_intro(h_a, N.reflexivite(vx0)),
                        N.s2(et(pv, egal(vx0, vx0)),
                             et(non(pv), egal(vx0, Sc_terme))))
    exA = N.modus_ponens(dA, N.s5(cond, vx0, Tp.lieur))
    impA = N.loi_deduction(pv, exA)
    h_b = N.assume(non(pv))
    dB0 = N.modus_ponens(conjonction_intro(h_b, N.reflexivite(Sc_terme)),
                         N.s2(et(non(pv), egal(Sc_terme, Sc_terme)),
                              et(pv, egal(Sc_terme, vx0))))
    dB = N.modus_ponens(dB0, N.s3(et(non(pv), egal(Sc_terme, Sc_terme)),
                                  et(pv, egal(Sc_terme, vx0))))
    exB = N.modus_ponens(dB, N.s5(cond, Sc_terme, Tp.lieur))
    impB = N.loi_deduction(non(pv), exB)
    ex = cas(tiers_exclu(pv), impA, impB)                   # (∃y)cond

    cd = N.modus_ponens(ex, N.existe_temoin(cond, Tp.lieur))
    gT = et(pv, egal(Tp, vx0))
    dT = et(non(pv), egal(Tp, Sc_terme))
    h_g = N.assume(gT)
    t_in_A = N.modus_ponens(h_x0, equivalence_arriere(
        N.modus_ponens(conjonction_elim_droite(h_g),
                       N.s6(Tp, vx0, "wcl", appartient(var("wcl"), ve)))))
    h_d = N.assume(dT)
    cl_in = clamp_dans_E(ARG, ve, vx0, zname)               # {x0∈E} clamp∈E
    t_in_B = N.modus_ponens(cl_in, equivalence_arriere(
        N.modus_ponens(conjonction_elim_droite(h_d),
                       N.s6(Tp, Sc_terme, "wcl", appartient(var("wcl"), ve)))))
    t_in = cas(cd, N.loi_deduction(gT, t_in_A), N.loi_deduction(dT, t_in_B))
    res = N.generalisation(p, t_in)
    assert res.conclusion == regle_dans_V(T, ve, p), "regle_clampee_bornee : forme"
    assert list(res.hypotheses) == [appartient(vx0, ve)], "regle_clampee_bornee : hyps"
    return res


__all__ = ["tiers_exclu", "clamp_E", "regle_clampee", "clamp_dans_E",
           "regle_clampee_bornee"]
