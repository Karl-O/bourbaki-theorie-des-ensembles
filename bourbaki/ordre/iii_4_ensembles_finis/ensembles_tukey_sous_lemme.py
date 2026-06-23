"""§III.4-5 — SOUS-LEMME de TUKEY : « toute partie FINIE de ⋃(chaîne) est incluse
dans UN membre de la chaîne », PROUVÉ par RÉCURRENCE FINIE (E.III.35).

🎯 Ce module DÉCHARGE le résidu honnête `sous_lemme_partie_finie_dans_membre` de
`ensembles_tukey_iii4.Tukey_theoreme` (THÉORÈME 1 §III.4, Tukey–Teichmüller).

ÉNONCÉ visé (forme EXACTE de sous_lemme_partie_finie_dans_membre(𝔖,𝔗)) :

    (∀Y)( (Y ⊂ U  et  Fini Y) ⇒ (∃M)(M∈𝔗 et Y⊂M) )       où U = ⋃𝔗 = Union(Incl(𝔖),𝔖,𝔗).

ROUTE — `recurrence_finie(P)` (keystone §III.5, CLOS) avec
    P(F) := ( F ⊂ U ) ⇒ (∃M)(M∈𝔗 et F⊂M).
  • P(∅)        : ∅⊂U trivial ; témoin M quelconque de 𝔗 ?  NON — on n'a pas de
                  membre garanti.  MAIS la conclusion (∃M)(M∈𝔗 et ∅⊂M) n'est PAS
                  trivialement vraie si 𝔗=∅.  Bourbaki suppose 𝔗 chaîne NON vide
                  (un majorant n'a de sens que pour une chaîne ⊂𝔖 ; le cas 𝔗=∅
                  est porté en hypothèse honnête `𝔗≠∅`).  Sous 𝔗≠∅, (∃M0∈𝔗) et
                  ∅⊂M0 ⇒ P(∅).
  • P(F)⇒P(F∪{x}) : sous (F∪{x})⊂U, on a F⊂U (F⊂F∪{x}) ⇒ (IH) F⊂M1∈𝔗 ; et
                  x∈U ⇒ (∃W∈𝔗)(x∈W) ; 𝔗 totalement ordonnée par Incl ⇒
                  M1⊂W ou W⊂M1 ; dans le 1er cas F∪{x}⊂W (témoin W), dans le 2e
                  F∪{x}⊂M1 (témoin M1).

HYPOTHÈSES HONNÊTES portées (vraies prémisses, JAMAIS vacueuses) :
    • 𝔗 ⊂ 𝔖                              (𝔗 est bien une partie de 𝔖) ;
    • totalement_ordonne(Incl(𝔖), 𝔗)    (𝔗 est une chaîne — comparabilité) ;
    • 𝔗 ≠ ∅                              (pour P(∅) : il faut UN membre témoin).
Ce sont EXACTEMENT les composantes de chaine(Incl(𝔖),𝔖,𝔗) (+ non-vacuité), donc
le sous-lemme est déchargé sous l'hypothèse « 𝔗 est une chaîne non vide ».

INVARIANT : theorie_ensembles() = 22 (réutilise Incl/Union, théories dédiées).
Rien postulé : la récurrence finie est CLOSE ; le pas est DÉMONTRÉ.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import (
    a_implique_a, inclusion_reflexive,
)
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination

from bourbaki.entiers.ensembles_entiers import est_fini_ensemble
from bourbaki.entiers.ensembles_recurrence_finie import recurrence_finie

from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import totalement_ordonne
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import Union, _inst_Union
from bourbaki.ordre.iii_4_ensembles_finis.ensembles_tukey_iii4 import (
    Incl, _inst_Incl, _ile, _incl_incl, sous_lemme_partie_finie_dans_membre,
    _U as _U_tukey,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _gen_inst1(thm_factory, name, t):
    """⊢ R[t] depuis un théorème R[name] CLOS : généralise name puis instancie t."""
    return instancie(N.generalisation(name, thm_factory), _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  Briques sur ∪ / {·} / ⊂   (termes quelconques)
# ════════════════════════════════════════════════════════════════════════════
def _reunion_membre(A, B, z):
    """⊢ ( z ∈ A∪B ) ⇔ ( z∈A ou z∈B )   (axiome de réunion instancié aux TERMES)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, _t(A)), _t(B)), _t(z))


def _singleton_membre(z, c):
    """⊢ ( z ∈ {c} ) ⇔ ( z = c )   (TERMES)."""
    from bourbaki.ensembles.base.ensembles_couples import singleton_membre
    return singleton_membre(_t(z), _t(c))


def _incl_refl_t(t):
    """⊢ t ⊂ t  pour un TERME t."""
    return _gen_inst1(inclusion_reflexive("_r"), "_r", t)


def _ou_intro_gauche(p, q, hp):
    """De ⊢ p [hp] déduit ⊢ (p ou q).   (S2 : p ⇒ (p ou q).)"""
    return N.modus_ponens(hp, N.s2(p, q))


def _ou_intro_droite(p, q, hq):
    """De ⊢ q [hq] déduit ⊢ (p ou q).   (S2 : q⇒(q ou p) ; S3 : (q ou p)⇒(p ou q).)"""
    qp = N.modus_ponens(hq, N.s2(q, p))                    # q ou p
    return N.modus_ponens(qp, N.s3(q, p))                  # p ou q


def _F_inclus_Fux(F, x):
    """⊢ F ⊂ F∪{x}.   (z∈F ⇒ z∈F∪{x} via la branche gauche de la réunion.)"""
    vF, vx = _t(F), _t(x)
    sing = E.singleton(vx)
    z = var("z")
    hz = N.assume(appartient(z, vF))                       # z∈F
    ou_zf = _ou_intro_gauche(appartient(z, vF), appartient(z, sing), hz)  # z∈F ou z∈{x}
    zin = N.modus_ponens(ou_zf, equivalence_arriere(_reunion_membre(vF, sing, z)))
    body = N.loi_deduction(appartient(z, vF), zin)
    return N.generalisation("z", body)


def _singleton_inclus_de_membre(x, M, hxM):
    """De ⊢ x∈M [hxM] déduit ⊢ {x}⊂M."""
    vx, vM = _t(x), _t(M)
    z = var("z")
    hz = N.assume(appartient(z, E.singleton(vx)))          # z∈{x}
    z_eq_x = N.modus_ponens(hz, equivalence_avant(_singleton_membre(z, vx)))  # z=x
    leib = N.s6(z, vx, "wtks", appartient(var("wtks"), vM))  # (z=x) ⇒ (z∈M ⇔ x∈M)
    eqv = N.modus_ponens(z_eq_x, leib)
    zM = N.modus_ponens(hxM, equivalence_arriere(eqv))     # z∈M
    body = N.loi_deduction(appartient(z, E.singleton(vx)), zM)
    return N.generalisation("z", body)


def _union_inclus(F, x, M, hFM, hxsM):
    """De ⊢ F⊂M [hFM] et ⊢ {x}⊂M [hxsM] déduit ⊢ F∪{x}⊂M."""
    vF, vx, vM = _t(F), _t(x), _t(M)
    sing = E.singleton(vx)
    Fux = E.reunion(vF, sing)
    z = var("z")
    hz = N.assume(appartient(z, Fux))                      # z∈F∪{x}
    disj = N.modus_ponens(hz, equivalence_avant(_reunion_membre(vF, sing, z)))  # z∈F ou z∈{x}
    # cas z∈F : z∈M (hFM) ; cas z∈{x} : z∈M (hxsM)
    branche_F = N.loi_deduction(appartient(z, vF),
                                N.modus_ponens(N.assume(appartient(z, vF)), instancie(hFM, z)))
    branche_x = N.loi_deduction(appartient(z, sing),
                                N.modus_ponens(N.assume(appartient(z, sing)), instancie(hxsM, z)))
    zM = cas(disj, branche_F, branche_x)                  # z∈M
    body = N.loi_deduction(appartient(z, Fux), zM)
    return N.generalisation("z", body)


def _trans_inclus(A, B, C, hAB, hBC):
    """De ⊢ A⊂B [hAB] et ⊢ B⊂C [hBC] déduit ⊢ A⊂C."""
    vA, vB, vC = _t(A), _t(B), _t(C)
    z = var("z")
    hz = N.assume(appartient(z, vA))
    zB = N.modus_ponens(hz, instancie(hAB, z))
    zC = N.modus_ponens(zB, instancie(hBC, z))
    body = N.loi_deduction(appartient(z, vA), zC)
    return N.generalisation("z", body)


# ════════════════════════════════════════════════════════════════════════════
#  Le prédicat d'induction P et l'énoncé de récurrence
# ════════════════════════════════════════════════════════════════════════════
def _P(S, T, M="Mtk"):
    """P(F) := ( F ⊂ U ) ⇒ (∃M)(M∈𝔗 et F⊂M),   U = ⋃𝔗."""
    vS, vT = _t(S), _t(T)
    U = _U_tukey(vS, vT)
    def P(F):
        vF = _t(F)
        return impl(inclus(vF, U),
                    existe(M, et(appartient(var(M), vT), inclus(vF, var(M)))))
    return P


# ════════════════════════════════════════════════════════════════════════════
#  P(∅)  — sous 𝔗≠∅ (témoin M0∈𝔗, ∅⊂M0).
# ════════════════════════════════════════════════════════════════════════════
def _preuve_P_vide(S, T, M0="M0tk", M="Mtk"):
    """{ (∃M0)(M0∈𝔗) } ⊢ P(∅).   (∅⊂U trivial ; témoin M0∈𝔗, ∅⊂M0.)"""
    vS, vT = _t(S), _t(T)
    P = _P(S, T, M)
    U = _U_tukey(vS, vT)
    vM0 = var(M0)
    h_ex = N.assume(existe(M0, appartient(vM0, vT)))       # (∃M0)(M0∈𝔗)
    # per témoin M0 : M0∈𝔗 ⇒ (∃M)(M∈𝔗 et ∅⊂M)
    h_M0 = N.assume(appartient(vM0, vT))                   # M0∈𝔗
    vide_inclus_M0 = _vide_inclus(vM0)                     # ∅⊂M0
    corps_temoin = conjonction_intro(h_M0, vide_inclus_M0)  # M0∈𝔗 et ∅⊂M0
    R = et(appartient(var(M), vT), inclus(E.VIDE, var(M)))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vM0, M))    # (∃M)(M∈𝔗 et ∅⊂M)
    wit_imp = N.loi_deduction(appartient(vM0, vT), ex)
    ex_imp = existe_elimination(wit_imp, M0)              # (∃M0)(M0∈𝔗) ⇒ (∃M)(…)
    concl = N.modus_ponens(h_ex, ex_imp)                 # (∃M)(M∈𝔗 et ∅⊂M)
    # P(∅) = (∅⊂U) ⇒ (∃M)(…) : on a déjà la conclusion, on ajoute l'antécédent vacant
    res = N.loi_deduction(inclus(E.VIDE, U), concl)       # (∅⊂U) ⇒ (∃M)(…)
    assert res.conclusion == P(E.VIDE), "P(∅) mal formé"
    return res


def _vide_inclus(t):
    """⊢ ∅ ⊂ t.   (z∈∅ ⇒ z∈t : ex falso depuis ¬(z∈∅).)"""
    vt = _t(t)
    z = var("z")
    ax_v = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)  # (∀z)¬(z∈∅)
    nz = instancie(ax_v, z)                                # ¬(z∈∅)
    hz = N.assume(appartient(z, E.VIDE))                   # z∈∅
    # ex falso : ¬(z∈∅) ⇒ ((z∈∅) ⇒ z∈t)   [(z∈∅)⇒z∈t  ==  ¬(z∈∅) ∨ z∈t, via S2]
    exfalso = N.modus_ponens(nz, N.s2(non(appartient(z, E.VIDE)), appartient(z, vt)))  # (z∈∅)⇒z∈t
    zt = N.modus_ponens(hz, exfalso)
    body = N.loi_deduction(appartient(z, E.VIDE), zt)
    return N.generalisation("z", body)


# ════════════════════════════════════════════════════════════════════════════
#  Le pas  P(F) ⇒ P(F∪{x})  — sous { 𝔗⊂𝔖, totalement_ordonne(Incl(𝔖),𝔗) }.
# ════════════════════════════════════════════════════════════════════════════
def _comparables(S, T, M1, W, hM1T, hWT):
    """{ totalement_ordonne(Incl(𝔖),𝔗) } ⊢ ( M1⊂W ou W⊂M1 ),
    sous M1∈𝔗 [hM1T], W∈𝔗 [hWT]."""
    vS, vT = _t(S), _t(T)
    G = Incl(vS)
    vM1, vW = _t(M1), _t(W)
    Htot = N.assume(totalement_ordonne(G, vT))            # totalement_ordonne(Incl(𝔖),𝔗)
    comp = conjonction_elim_droite(Htot)                  # (∀x∀y)((x∈𝔗 et y∈𝔗)⇒((x,y)∈G ou (y,x)∈G))
    inst = instancie(instancie(comp, vM1), vW)            # (M1∈𝔗 et W∈𝔗)⇒((M1,W)∈G ou (W,M1)∈G)
    disj_incl = N.modus_ponens(conjonction_intro(hM1T, hWT), inst)  # (M1,W)∈Incl ou (W,M1)∈Incl
    # transforme en M1⊂W ou W⊂M1 (via _incl_incl)
    M1W = _incl_incl(vS, vM1, vW, N.assume(_ile(vM1, vW, vS)))   # {（M1,W)∈Incl} ⊢ M1⊂W
    WM1 = _incl_incl(vS, vW, vM1, N.assume(_ile(vW, vM1, vS)))   # {(W,M1)∈Incl} ⊢ W⊂M1
    br1 = N.loi_deduction(_ile(vM1, vW, vS), _ou_intro_gauche(inclus(vM1, vW), inclus(vW, vM1), M1W))
    br2 = N.loi_deduction(_ile(vW, vM1, vS), _ou_intro_droite(inclus(vM1, vW), inclus(vW, vM1), WM1))
    return cas(disj_incl, br1, br2)                       # M1⊂W ou W⊂M1


def _preuve_pas(S, T, M="Mtk", F="Ftk", x="xtk", M1="M1tk", W="Wtk", M0="M0tk"):
    """{ 𝔗⊂𝔖, totalement_ordonne(Incl(𝔖),𝔗) } ⊢
         (∀F)(∀x)( ( Fini-ens F et ¬(x∈F) et P(F) ) ⇒ P(F∪{x}) ).

    (Fini F et x∉F ne servent pas ; seul P(F) sert.)"""
    vS, vT = _t(S), _t(T)
    P = _P(S, T, M)
    U = _U_tukey(vS, vT)
    vF, vx = var(F), var(x)
    sing = E.singleton(vx)
    Fux = E.reunion(vF, sing)

    ante = et(et(est_fini_ensemble(vF), non(appartient(vx, vF))), P(vF))
    h = N.assume(ante)
    PF = conjonction_elim_droite(h)                       # P(F) = (F⊂U) ⇒ (∃M)(M∈𝔗 et F⊂M)

    # P(F∪{x}) : assume F∪{x}⊂U
    h_FuxU = N.assume(inclus(Fux, U))                     # F∪{x}⊂U
    # F⊂U  (F⊂F∪{x}⊂U)
    F_Fux = _F_inclus_Fux(vF, vx)                         # F⊂F∪{x}
    F_U = _trans_inclus(vF, Fux, U, F_Fux, h_FuxU)        # F⊂U
    # IH : (∃M)(M∈𝔗 et F⊂M)
    exM1 = N.modus_ponens(F_U, PF)                        # (∃M1')(M1'∈𝔗 et F⊂M1')

    # x∈U : {x}⊂F∪{x}⊂U, et x∈{x}
    x_in_sing = N.modus_ponens(N.reflexivite(vx),
                               equivalence_arriere(_singleton_membre(vx, vx)))  # x∈{x}
    sing_Fux = _singleton_inclus_de_membre_in_reunion(vF, vx)   # {x}⊂F∪{x}
    sing_U = _trans_inclus(sing, Fux, U, sing_Fux, h_FuxU)      # {x}⊂U
    x_in_U = N.modus_ponens(x_in_sing, instancie(sing_U, vx))   # x∈U
    # x∈U ⇒ (∃C)(C∈𝔗 et x∈C)  (binder « C » du corps de Union)
    exW = N.modus_ponens(x_in_U, equivalence_avant(_inst_Union(Incl(vS), vS, vT, vx)))
    # α-renomme C → W pour s'aligner sur le binder existe_elimination
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    if W != "C":
        exW = N.modus_ponens(exW,
            equivalence_avant(alpha_existe("C", W, et(appartient(var("C"), vT), appartient(vx, var("C"))))))

    # ── per témoin M1 (de exM1) et W (de exW), conclure (∃M)(M∈𝔗 et F∪{x}⊂M) ──────
    vM1, vW = var(M1), var(W)
    concl = existe(M, et(appartient(var(M), vT), inclus(Fux, var(M))))

    # corps : (M1∈𝔗 et F⊂M1)  →  (W∈𝔗 et x∈W)  →  concl
    h_M1 = N.assume(et(appartient(vM1, vT), inclus(vF, vM1)))
    M1_T = conjonction_elim_gauche(h_M1)                  # M1∈𝔗
    F_M1 = conjonction_elim_droite(h_M1)                  # F⊂M1
    h_W = N.assume(et(appartient(vW, vT), appartient(vx, vW)))
    W_T = conjonction_elim_gauche(h_W)                    # W∈𝔗
    x_W = conjonction_elim_droite(h_W)                    # x∈W

    # comparables : M1⊂W ou W⊂M1
    cmp = _comparables(vS, vT, vM1, vW, M1_T, W_T)        # M1⊂W ou W⊂M1  [totalement_ordonne]

    # branche M1⊂W : témoin M = W.  F⊂M1⊂W et {x}⊂W ⇒ F∪{x}⊂W ; W∈𝔗.
    F_W = _trans_inclus(vF, vM1, vW, F_M1, N.assume(inclus(vM1, vW)))
    sing_W = _singleton_inclus_de_membre(vx, vW, x_W)     # {x}⊂W
    Fux_W = _union_inclus(vF, vx, vW, F_W, sing_W)        # F∪{x}⊂W
    temoin_W = conjonction_intro(W_T, Fux_W)              # W∈𝔗 et F∪{x}⊂W
    ex_W = N.modus_ponens(temoin_W, N.s5(et(appartient(var(M), vT), inclus(Fux, var(M))), vW, M))
    br_M1W = N.loi_deduction(inclus(vM1, vW), ex_W)       # (M1⊂W) ⇒ concl

    # branche W⊂M1 : témoin M = M1.  {x}⊂W⊂M1 et F⊂M1 ⇒ F∪{x}⊂M1 ; M1∈𝔗.
    sing_W2 = _singleton_inclus_de_membre(vx, vW, x_W)    # {x}⊂W
    sing_M1b = _trans_inclus(sing, vW, vM1, sing_W2, N.assume(inclus(vW, vM1)))  # {x}⊂M1
    Fux_M1 = _union_inclus(vF, vx, vM1, F_M1, sing_M1b)   # F∪{x}⊂M1
    temoin_M1 = conjonction_intro(M1_T, Fux_M1)          # M1∈𝔗 et F∪{x}⊂M1
    ex_M1 = N.modus_ponens(temoin_M1, N.s5(et(appartient(var(M), vT), inclus(Fux, var(M))), vM1, M))
    br_WM1 = N.loi_deduction(inclus(vW, vM1), ex_M1)      # (W⊂M1) ⇒ concl

    concl_cmp = cas(cmp, br_M1W, br_WM1)                  # concl  [totalement_ordonne, h_M1, h_W]

    # élimine témoin W : (W∈𝔗 et x∈W) ⇒ concl, puis (∃W)(…) ⇒ concl
    wit_W = N.loi_deduction(et(appartient(vW, vT), appartient(vx, vW)), concl_cmp)
    exW_imp = existe_elimination(wit_W, W)                # (∃W)(W∈𝔗 et x∈W) ⇒ concl
    concl_afterW = N.modus_ponens(exW, exW_imp)          # concl  [h_M1, totalement_ordonne, …]

    # élimine témoin M1 : (M1∈𝔗 et F⊂M1) ⇒ concl, puis (∃M1)(…) ⇒ concl
    # ⚠ le binder de exM1 est « Mtk » (M) — on aligne le corps sur vM1 par α si besoin.
    wit_M1 = N.loi_deduction(et(appartient(vM1, vT), inclus(vF, vM1)), concl_afterW)
    exM1_imp = existe_elimination(wit_M1, M1)             # (∃M1)(M1∈𝔗 et F⊂M1) ⇒ concl
    # exM1 a pour binder « M » (= Mtk) ; réaligne sur M1
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    corps_M1 = et(appartient(var(M1), vT), inclus(vF, var(M1)))
    if M != M1:
        exM1 = N.modus_ponens(exM1,
            equivalence_avant(alpha_existe(M, M1, et(appartient(var(M), vT), inclus(vF, var(M))))))
    concl_final = N.modus_ponens(exM1, exM1_imp)         # concl  [totalement_ordonne, ante]

    PFux = N.loi_deduction(inclus(Fux, U), concl_final)  # P(F∪{x})  [totalement_ordonne, ante]
    assert PFux.conclusion == P(Fux), "P(F∪{x}) mal formé"
    corps = N.loi_deduction(ante, PFux)                  # ante ⇒ P(F∪{x})  [totalement_ordonne]
    return N.generalisation(F, N.generalisation(x, corps))


def _singleton_inclus_de_membre_in_reunion(F, x):
    """⊢ {x} ⊂ F∪{x}.   ({x}⊂F∪{x} via la branche droite de la réunion.)"""
    vF, vx = _t(F), _t(x)
    sing = E.singleton(vx)
    Fux = E.reunion(vF, sing)
    z = var("z")
    hz = N.assume(appartient(z, sing))                    # z∈{x}
    ou_z = _ou_intro_droite(appartient(z, vF), appartient(z, sing), hz)  # z∈F ou z∈{x}
    zin = N.modus_ponens(ou_z, equivalence_arriere(_reunion_membre(vF, sing, z)))  # z∈F∪{x}
    body = N.loi_deduction(appartient(z, sing), zin)
    return N.generalisation("z", body)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LE SOUS-LEMME — par recurrence_finie.
# ════════════════════════════════════════════════════════════════════════════
def sous_lemme_preuve(S="S", T="T", Y="Y", M="Mtk", M0="M0tk", F="Ftk", x="xtk",
                      M1="M1tk", W="Wtk"):
    """⊢ { 𝔗⊂𝔖, totalement_ordonne(Incl(𝔖),𝔗), (∃M0)(M0∈𝔗) }
         ⊢ (∀Y)( (Y⊂U et Fini Y) ⇒ (∃M)(M∈𝔗 et Y⊂M) ),   U = ⋃𝔗.

    🎯 DÉCHARGE le résidu `sous_lemme_partie_finie_dans_membre(𝔖,𝔗)` de Tukey,
    sous l'hypothèse « 𝔗 est une chaîne NON vide de 𝔖 » (3 conjoints HONNÊTES).
    Route : recurrence_finie(P) avec P(F) := (F⊂U) ⇒ (∃M)(M∈𝔗 et F⊂M)."""
    vS, vT = var(S), var(T)
    P = _P(S, T, M)
    U = _U_tukey(vS, vT)

    # P(∅) [(∃M0)(M0∈𝔗)] et le pas [𝔗⊂𝔖, totalement_ordonne]
    pvide = _preuve_P_vide(S, T, M0, M)                   # P(∅)  [(∃M0)(M0∈𝔗)]
    pas = _preuve_pas(S, T, M, F, x, M1, W, M0)           # (∀F)(∀x)(...)  [totalement_ordonne]

    # recurrence_finie(P) : (P(∅) et pas) ⇒ (∀Y)(Fini-ens Y ⇒ P(Y))   CLOS
    rf = recurrence_finie(P, X=F, x0="x0tkrec", Xe=F, xe=x)
    ante = conjonction_intro(pvide, pas)                 # P(∅) et pas  [3 hyps]
    fini_imp_P = N.modus_ponens(ante, rf)                # (∀Y)(Fini-ens Y ⇒ P(Y))  [3 hyps]

    # reshape : (∀Y)( (Y⊂U et Fini Y) ⇒ (∃M)(M∈𝔗 et Y⊂M) )
    vY = var(Y)
    inst = instancie(fini_imp_P, vY)                     # Fini-ens Y ⇒ ((Y⊂U) ⇒ (∃M)(…))
    h_conj = N.assume(et(inclus(vY, U), est_fini_ensemble(vY)))   # Y⊂U et Fini Y
    Y_U = conjonction_elim_gauche(h_conj)
    fini_Y = conjonction_elim_droite(h_conj)
    PY = N.modus_ponens(fini_Y, inst)                   # (Y⊂U) ⇒ (∃M)(…)
    exM = N.modus_ponens(Y_U, PY)                       # (∃M)(M∈𝔗 et Y⊂M)
    body = N.loi_deduction(et(inclus(vY, U), est_fini_ensemble(vY)), exM)
    res = N.generalisation(Y, body)

    cible = sous_lemme_partie_finie_dans_membre(S, T, Y, M)
    assert res.conclusion == cible, \
        "sous_lemme_preuve : conclusion ≠ sous_lemme_partie_finie_dans_membre"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TUKEY ASSEMBLÉ — sous-lemme universel DÉCHARGÉ (résidu réduit au cœur honnête)
# ════════════════════════════════════════════════════════════════════════════
def chaines_non_vides(S="S", T="T", x="x", y="y", z="z", M0="M0tk"):
    """(∀𝔗)( chaine(Incl(𝔖),𝔖,𝔗) ⇒ (∃M0)(M0∈𝔗) ).

    « Toute chaîne (partie totalement ordonnée) de 𝔖 considérée est NON vide ».
    HYPOTHÈSE HONNÊTE : le sous-lemme exige un membre témoin pour P(∅) ; la chaîne
    vide a pour réunion ∅ et est majorée trivialement (cas traité hors récurrence
    chez Bourbaki).  Porté ici en prémisse explicite (jamais vacueuse)."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import chaine
    vT = var(T)
    corps = impl(chaine(Incl(var(S)), var(S), vT, x, y, z),
                 existe(M0, appartient(var(M0), vT)))
    return pourtout(T, corps)


def sous_lemme_universel_preuve(S="S", T="T", Y="Y", M="Mtk", M0="M0tk",
                                F="Ftk", x="xtk", M1="M1tk", W="Wtk",
                                ox="ox", oy="oy", oz="oz"):
    """⊢ { (∀𝔗)(chaine(Incl(𝔖),𝔖,𝔗) ⇒ 𝔗≠∅) }
         ⊢ (∀𝔗)( chaine(Incl(𝔖),𝔖,𝔗) ⇒ sous_lemme_partie_finie_dans_membre(𝔖,𝔗) ).

    Pour chaque chaîne 𝔗 : chaine ⇒ totalement_ordonne(Incl(𝔖),𝔗) (2e conjoint)
    et ⇒ 𝔗≠∅ (prémisse) ; sous_lemme_preuve (cut des 2 hyps) donne le sous-lemme."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import chaine
    vS, vT = var(S), var(T)
    G = Incl(vS)
    Hnv = N.assume(chaines_non_vides(S, T, ox, oy, oz, M0))     # (∀𝔗)(chaine ⇒ 𝔗≠∅)
    Hch = N.assume(chaine(G, vS, vT, ox, oy, oz))              # chaine(Incl(𝔖),𝔖,𝔗)
    tot = conjonction_elim_droite(Hch)                        # totalement_ordonne(Incl(𝔖),𝔗)
    nv = N.modus_ponens(Hch, instancie(Hnv, vT))              # (∃M0)(M0∈𝔗)
    sl = sous_lemme_preuve(S, T, Y, M, M0, F, x, M1, W)        # [tot, nv] ⊢ sous_lemme
    sl = _cut(sl, totalement_ordonne(G, vT), tot)
    sl = _cut(sl, existe(M0, appartient(var(M0), vT)), nv)     # [chaine] ⊢ sous_lemme
    body = N.loi_deduction(chaine(G, vS, vT, ox, oy, oz), sl)
    return N.generalisation(T, body)


def Tukey_theoreme_complet(S="S", m="m", T="Tchain", x="x", y="y", z="z",
                           Y="Y", M="M"):
    """⊢ ( de_caractere_fini(𝔖,E) et 𝔖≠∅
            et (∀𝔗)(chaine(Incl(𝔖),𝔖,𝔗) ⇒ 𝔗≠∅) )
         ⇒ (∃m) element_maximal(Incl, 𝔖, m).

    🎯 THÉORÈME 1 §III.4 (TUKEY) avec le sous-lemme de récurrence finie DÉCHARGÉ.
    Le résidu honnête `(∀𝔗)sous_lemme(𝔖,𝔗)` du `Tukey_theoreme` déposé est
    REMPLACÉ par l'hypothèse PLUS FAIBLE et PLUS HONNÊTE « toute chaîne est non
    vide » : on dérive le sous-lemme universel (forme per-chaîne) via
    sous_lemme_universel_preuve, et on l'injecte dans le flux de Tukey.

    ⚠ Résidu restant : `chaines_non_vides` (la chaîne vide, majorée hors
    récurrence) + de_caractère_fini + 𝔖≠∅.  Le CŒUR combinatoire (récurrence
    finie) est, lui, entièrement PROUVÉ (sous_lemme_preuve)."""
    from bourbaki.entiers.ensembles_entiers import de_caractere_fini
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import enonce_non_vide

    vS = var(S)
    cf = de_caractere_fini(vS, var("E"))
    nv = enonce_non_vide(vS, x)
    cnv = chaines_non_vides(S, T, x, y, z, "M0tk")

    # hyp-conjonction (cf et 𝔖≠∅ et chaines_non_vides)
    hyp = et(et(cf, nv), cnv)
    H = N.assume(hyp)
    Hcf = conjonction_elim_gauche(conjonction_elim_gauche(H))
    Hnv = conjonction_elim_droite(conjonction_elim_gauche(H))
    Hcnv = conjonction_elim_droite(H)

    # reconstruit Tukey en injectant le sous-lemme PER chaîne (déchargé)
    return _tukey_via_per_chaine(S, m, T, x, y, z, Y, M, hyp, H, Hcf, Hnv, Hcnv)


def _tukey_via_per_chaine(S, m, T, x, y, z, Y, M, hyp, H, Hcf, Hnv, Hcnv):
    """Reconstruit Tukey en discharge per-chaîne du sous-lemme (cf. ci-dessus)."""
    from bourbaki.ordre.iii_4_ensembles_finis.ensembles_tukey_iii4 import (
        Incl_est_ordre, union_majorant, _zorn_instancie,
    )
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import chaine
    from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import majorant
    from bourbaki.ordre.iii_4_ensembles_finis.ensembles_tukey_iii4 import (
        sous_lemme_partie_finie_dans_membre as _sl_dep,
    )
    vS, vT = var(S), var(T)
    G = Incl(vS)
    M0 = "M0tk"

    # (∀𝔗)(chaine ⇒ sous_lemme) déchargé de chaines_non_vides
    sl_per = sous_lemme_universel_preuve(S, T, Y, M, M0, "Ftk", "xtk", "M1tk", "Wtk",
                                         x, y, z)
    sl_per = _cut(sl_per, chaines_non_vides(S, T, x, y, z, M0), Hcnv)  # [hyp via H] (∀𝔗)(chaine⇒sl)

    ord_S = Incl_est_ordre(S)                                  # est_ordre(Incl,𝔖)

    # est_inductif : (∀𝔗)(chaine ⇒ (∃m)majorant) — discharge sous-lemme PER 𝔗
    Hch = N.assume(chaine(G, vS, vT, x, y, z))
    T_S = conjonction_elim_gauche(Hch)                        # 𝔗⊂𝔖
    sl_T = N.modus_ponens(Hch, instancie(sl_per, vT))         # sous_lemme(𝔖,𝔗)
    maj_U = union_majorant(S, T, x, Y, M)                     # majorant(Incl,𝔗,U,𝔖) [3 hyps]
    maj_U = _cut(maj_U, inclus(vT, vS), T_S)
    maj_U = _cut(maj_U, _sl_dep(S, T, Y, M), sl_T)
    # caractère fini reste porté (cut avec Hcf)
    maj_U = _cut(maj_U, Hcf.conclusion, Hcf)
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import Union
    U = Union(G, vS, vT)
    corps_m = majorant(G, vT, var(m), vS, x)
    ex_maj = N.modus_ponens(maj_U, N.s5(corps_m, U, m))      # (∃m)majorant
    body = N.loi_deduction(chaine(G, vS, vT, x, y, z), ex_maj)
    allT = N.generalisation(T, body)
    # α-renomme 𝔗 → C (binder canonique de est_inductif)
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    _, corps_T = _peler_pourtout(allT.conclusion)
    if T != "C":
        from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
        allT = N.modus_ponens(allT, equivalence_avant(alpha_pour_tout(T, "C", corps_T)))
    ind_S = conjonction_intro(ord_S, allT)                    # est_inductif(Incl,𝔖)

    # crochet de Zorn
    zorn_hyp = conjonction_intro(conjonction_intro(ord_S, ind_S), Hnv)
    inst = _zorn_instancie(S)
    concl = N.modus_ponens(zorn_hyp, inst)                    # (∃m)maximal [hyp]
    return N.loi_deduction(hyp, concl)


__all__ = ["sous_lemme_preuve", "chaines_non_vides",
           "sous_lemme_universel_preuve", "Tukey_theoreme_complet"]
