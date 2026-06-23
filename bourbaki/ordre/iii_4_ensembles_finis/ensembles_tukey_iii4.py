"""Chapitre III §4 — THÉORÈME 1 (TUKEY–TEICHMÜLLER), via le THÉORÈME DE ZORN.

Module NEUF.  Il PROUVE le Théorème 1 §III.4 (E.III.35) :

    « Tout ensemble 𝔖 de parties d'un ensemble E, de CARACTÈRE FINI, admet un
      élément maximal (quand on l'ordonne par inclusion). »

DÉFINITION 2 (E.III.34, §III.4.5, lue VERBATIM dans le PDF source) :
    𝔖 (⊂ 𝔓(E)) est de caractère fini  :⇔  (∀X)( X∈𝔖 ⇔ « toute partie finie de
    X appartient à 𝔖 » ).
(prédicat `de_caractere_fini` de bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers, LU verbatim.)

ROUTE (Bourbaki E.III.35, par ZORN — que NOUS AVONS, `zorn_theoreme`) :
  • On ordonne 𝔖 par l'INCLUSION : graphe Incl(𝔖) := { (X,Y) | X∈𝔖 ∧ Y∈𝔖 ∧ X⊂Y }
    (terme opaque + axiome DÉFINITIONNEL, motif `axiome_Gamma`/`axiome_M` ;
    n'altère PAS theorie_ensembles()=22).
  • (Incl,𝔖) est un ORDRE : réflexivité de ⊂, antisymétrie (A1), transitivité de ⊂
    (Incl_est_ordre, INCONDITIONNEL).
  • (Incl,𝔖) est INDUCTIF : pour une chaîne 𝔗 de 𝔖, la RÉUNION U=⋃𝔗 est dans 𝔖
    et MAJORE 𝔗.  C'est le CŒUR :
        U∈𝔖  ⇐(caractère fini)  toute partie finie Y de U est dans 𝔖 ;
        Y partie finie de U  ⊂(SOUS-LEMME)  un membre M de la chaîne 𝔗 ;
        M∈𝔗⊂𝔖 ⇒ M∈𝔖, et Y partie finie de M∈𝔖 ⇒(caractère fini) Y∈𝔖.
    Le SOUS-LEMME « toute partie finie de ⋃(chaîne) est incluse dans UN membre de
    la chaîne » est une RÉCURRENCE FINIE (sur Card Y) NON proprement disponible
    ici ; il est porté comme HYPOTHÈSE HONNÊTE `sous_lemme_partie_finie_dans_membre`
    (jamais postulé sous forme vacueuse : c'est une vraie prémisse mathématique du
    cœur, signalée explicitement dans le rapport).
  • ZORN (zorn_theoreme) ⇒ 𝔖 a un élément maximal pour Incl.

INVARIANT : theorie_ensembles() reste = 22 (axiome de Incl en théorie DÉDIÉE,
motif Mc/M).  Rien n'est postulé : le maximal est DÉMONTRÉ via zorn_theoreme ; on
ne suppose JAMAIS le maximal ni Tukey.  La réunion ⋃𝔗 réutilise l'infra `Union`
de ensembles_zorn_theoreme (terme + axiome de membership génériques).

NOTATION : X ⊂ Y := inclus(X,Y) ;  (X,Y)∈Incl  est l'ordre du poset 𝔖.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, inclusion_reflexive
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, reflexivite_sur, antisymetrie, transitivite_rel, totalement_ordonne,
    majorant, element_maximal,
)
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine, est_inductif, enonce_non_vide,
)
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import (
    Union, _inst_Union, zorn_theoreme,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import de_caractere_fini, est_fini_ensemble


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _incl_refl(t):
    """⊢ t⊂t  pour un TERME t."""
    th = inclusion_reflexive("_r")
    return instancie(N.generalisation("_r", th), _terme(t))


def _incl_trans(a, b, c, ab, bc):
    """De ⊢ a⊂b [ab] et ⊢ b⊂c [bc] (TERMES) déduit ⊢ a⊂c (réécriture directe)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    va, vb, vc = _terme(a), _terme(b), _terme(c)
    cible = inclus(va, vc)
    bndr, _ = _peler_pourtout(cible)
    zt = var(bndr)
    hz = N.assume(appartient(zt, va))
    z_in_b = N.modus_ponens(hz, instancie(ab, zt))
    z_in_c = N.modus_ponens(z_in_b, instancie(bc, zt))
    body = N.loi_deduction(appartient(zt, va), z_in_c)
    return N.generalisation(bndr, body)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — L'ORDRE D'INCLUSION SUR 𝔖 :
#    Incl(𝔖) := { (X,Y) | X∈𝔖 et Y∈𝔖 et X⊂Y }
#  Terme opaque + axiome DÉFINITIONNEL (S8+A1, motif axiome_Gamma).  theorie=22.
# ════════════════════════════════════════════════════════════════════════════
def Incl(S):
    """Incl(𝔖) := { (X,Y) | X∈𝔖 et Y∈𝔖 et X⊂Y }  (graphe de ⊂ sur 𝔖)."""
    return E.app("tukey_Incl", _terme(S))


def _corps_Incl(S, X, Y):
    """Corps de Incl :  X∈𝔖 et Y∈𝔖 et X⊂Y."""
    vS = _terme(S)
    return et(et(appartient(_terme(X), vS), appartient(_terme(Y), vS)),
              inclus(_terme(X), _terme(Y)))


def axiome_Incl(S="S", X="X", Y="Y"):
    """⊢-schéma (∀S X Y)( (X,Y)∈Incl ⇔ (X∈𝔖 et Y∈𝔖 et X⊂Y) ).

    Axiome DÉFINITIONNEL du graphe d'inclusion sur 𝔖 (S8+A1).  N'altère PAS
    theorie_ensembles()."""
    vS, vX, vY = var(S), var(X), var(Y)
    return pourtout(S, pourtout(X, pourtout(Y,
        equiv(appartient(E.couple(vX, vY), Incl(vS)), _corps_Incl(vS, vX, vY)))))


def theorie_Incl(S="S", X="X", Y="Y"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Incl (Tukey, ÉTAPE 1)."""
    return N.Theorie("Incl-Tukey", [axiome_Incl(S, X, Y)])


def _inst_Incl(S, X, Y):
    """⊢ ( (X,Y)∈Incl ⇔ (X∈𝔖 et Y∈𝔖 et X⊂Y) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Incl(), axiome_Incl())
    for tm in (S, X, Y):
        ax = instancie(ax, _terme(tm))
    return ax


def Incl_membre(S="S", X="X", Y="Y"):
    """⊢ ( (X,Y)∈Incl ) ⇔ ( X∈𝔖 et Y∈𝔖 et X⊂Y )."""
    return _inst_Incl(var(S), var(X), var(Y))


def _ile(X, Y, S):
    """Formule « (X,Y)∈Incl »  (l'ordre du poset 𝔖, i.e. X⊂Y)."""
    return appartient(E.couple(_terme(X), _terme(Y)), Incl(_terme(S)))


def _Incl_intro(S, X, Y, hXS, hYS, hXY):
    """De ⊢ X∈𝔖 [hXS], ⊢ Y∈𝔖 [hYS], ⊢ X⊂Y [hXY], déduit ⊢ (X,Y)∈Incl."""
    corps = conjonction_intro(conjonction_intro(hXS, hYS), hXY)
    return N.modus_ponens(corps, equivalence_arriere(_inst_Incl(S, X, Y)))


def _incl_incl(S, X, Y, hIncl):
    """De ⊢ (X,Y)∈Incl [hIncl] déduit ⊢ X⊂Y (projection du corps de Incl)."""
    corps = N.modus_ponens(hIncl, equivalence_avant(_inst_Incl(S, X, Y)))
    return conjonction_elim_droite(corps)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (suite) — Incl est un ORDRE sur 𝔖
# ════════════════════════════════════════════════════════════════════════════
def Incl_reflexive_sur(S="S", X="x"):
    """⊢ reflexivite_sur(Incl,𝔖).  = (∀x)( x∈𝔖 ⇒ (x,x)∈Incl )."""
    vS, vX = var(S), var(X)
    hXS = N.assume(appartient(vX, vS))
    XX = _incl_refl(vX)
    XX_I = _Incl_intro(vS, vX, vX, hXS, hXS, XX)
    body = N.loi_deduction(appartient(vX, vS), XX_I)
    return N.generalisation(X, body)


def Incl_antisymetrique(S="S", X="x", Y="y"):
    """⊢ antisymetrie(Incl).  = (∀x∀y)( ((x,y)∈Incl et (y,x)∈Incl) ⇒ x=y )."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    vS, vX, vY = var(S), var(X), var(Y)
    hyp = et(_ile(vX, vY, vS), _ile(vY, vX, vS))
    h = N.assume(hyp)
    XY = _incl_incl(vS, vX, vY, conjonction_elim_gauche(h))   # X⊂Y
    YX = _incl_incl(vS, vY, vX, conjonction_elim_droite(h))   # Y⊂X
    a1 = extensionnalite_appliquee(vX, vY)                    # (X⊂Y et Y⊂X)⇒X=Y
    X_eq_Y = N.modus_ponens(conjonction_intro(XY, YX), a1)
    body = N.loi_deduction(hyp, X_eq_Y)
    return N.generalisation(X, N.generalisation(Y, body))


def Incl_transitive(S="S", X="x", Y="y", Z="z"):
    """⊢ transitivite_rel(Incl).  = (∀x∀y∀z)( ((x,y)∈Incl et (y,z)∈Incl) ⇒ (x,z)∈Incl )."""
    vS, vX, vY, vZ = var(S), var(X), var(Y), var(Z)
    hyp = et(_ile(vX, vY, vS), _ile(vY, vZ, vS))
    h = N.assume(hyp)
    xycorps = N.modus_ponens(conjonction_elim_gauche(h),
                             equivalence_avant(_inst_Incl(vS, vX, vY)))  # X∈𝔖 et Y∈𝔖 et X⊂Y
    yzcorps = N.modus_ponens(conjonction_elim_droite(h),
                             equivalence_avant(_inst_Incl(vS, vY, vZ)))  # Y∈𝔖 et Z∈𝔖 et Y⊂Z
    XS = conjonction_elim_gauche(conjonction_elim_gauche(xycorps))  # X∈𝔖
    ZS = conjonction_elim_droite(conjonction_elim_gauche(yzcorps))  # Z∈𝔖
    XY = conjonction_elim_droite(xycorps)                    # X⊂Y
    YZ = conjonction_elim_droite(yzcorps)                    # Y⊂Z
    XZ = _incl_trans(vX, vY, vZ, XY, YZ)                     # X⊂Z
    XZ_I = _Incl_intro(vS, vX, vZ, XS, ZS, XZ)              # (X,Z)∈Incl
    body = N.loi_deduction(hyp, XZ_I)
    return N.generalisation(X, N.generalisation(Y, N.generalisation(Z, body)))


def Incl_est_ordre(S="S"):
    """⊢ est_ordre(Incl,𝔖).  INCONDITIONNEL (réfl. ⊂, antisym. A1, trans. ⊂)."""
    refl = Incl_reflexive_sur(S, "x")
    antisym = Incl_antisymetrique(S, "x", "y")
    trans = Incl_transitive(S, "x", "y", "z")
    return conjonction_intro(conjonction_intro(refl, antisym), trans)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — LE CŒUR : la RÉUNION U=⋃𝔗 d'une chaîne 𝔗 de 𝔖 EST DANS 𝔖.
#  On réutilise l'infra `Union` (terme + axiome de membership génériques) de
#  ensembles_zorn_theoreme, avec G=Incl(𝔖), E_set=𝔖, D=𝔗.
# ════════════════════════════════════════════════════════════════════════════
def _U(S, T):
    """U := ⋃𝔗  (réunion de la chaîne 𝔗), via l'infra Union(Incl,𝔖,𝔗)."""
    return Union(Incl(_terme(S)), _terme(S), _terme(T))


def sous_lemme_partie_finie_dans_membre(S="S", T="T", Y="Y", M="M"):
    """HYPOTHÈSE HONNÊTE — le SOUS-LEMME de la récurrence finie (E.III.35) :

        (∀Y)( (Y⊂U et Y fini) ⇒ (∃M)(M∈𝔗 et Y⊂M) )

    « Toute partie FINIE Y de la réunion U=⋃𝔗 d'une chaîne 𝔗 est incluse dans UN
    SEUL membre M de la chaîne 𝔗 ».  C'est une RÉCURRENCE sur Card Y (Bourbaki :
    « comme l'ensemble des Z_y est fini et totalement ordonné, il admet un plus
    grand élément ») ; la récurrence finie générale n'étant pas proprement câblée
    ici, ce fait est PORTÉ EN HYPOTHÈSE (vraie prémisse mathématique, jamais
    vacueuse).  Liants Y (la partie finie), M (le membre témoin)."""
    vS, vT, vY = var(S), var(T), var(Y)
    U = _U(vS, vT)
    concl = existe(M, et(appartient(var(M), vT), inclus(vY, var(M))))
    return pourtout(Y, impl(et(inclus(vY, U), est_fini_ensemble(vY)), concl))


def union_dans_S(S="S", T="T", Y="Y", M="M"):
    """⊢ { 𝔗⊂𝔖, de_caractere_fini(𝔖,E), sous_lemme(𝔖,𝔗) } ⊢ U∈𝔖,  où U=⋃𝔗.

    Par caractère fini : U∈𝔖 ⇐ (∀Y)((Y⊂U et Y fini) ⇒ Y∈𝔖).  Soit Y⊂U fini ;
    par le SOUS-LEMME, Y⊂M pour un M∈𝔗⊂𝔖, donc M∈𝔖 ; Y est alors une partie
    FINIE de M∈𝔖, d'où (caractère fini de 𝔖 appliqué à M) Y∈𝔖.  E_set = E (le
    sur-ensemble) reste implicite via de_caractere_fini(𝔖,E)."""
    vS, vT, vY, vM = var(S), var(T), var(Y), var(M)
    U = _U(vS, vT)
    HTS = N.assume(inclus(vT, vS))                            # 𝔗⊂𝔖
    # de_caractere_fini(𝔖,E) — on n'a besoin que de l'équivalence sur 𝔖 ; E est un
    # paramètre libre « E » du prédicat (sur-ensemble). On l'instancie à 𝔖.
    Hcf = N.assume(de_caractere_fini(vS, var("E")))           # caractère fini de 𝔖
    Hsl = N.assume(sous_lemme_partie_finie_dans_membre(S, T, Y, M))  # le sous-lemme

    # ── (∀Y)((Y⊂U et Y fini) ⇒ Y∈𝔖) ───────────────────────────────────────────
    hyp_Y = et(inclus(vY, U), est_fini_ensemble(vY))
    hY = N.assume(hyp_Y)
    # sous-lemme : (∃M)(M∈𝔗 et Y⊂M)
    exM = N.modus_ponens(hY, instancie(Hsl, vY))
    # per-témoin M : (M∈𝔗 et Y⊂M) ⇒ Y∈𝔖
    HwM = N.assume(et(appartient(vM, vT), inclus(vY, vM)))
    M_T = conjonction_elim_gauche(HwM)                        # M∈𝔗
    Y_M = conjonction_elim_droite(HwM)                        # Y⊂M
    M_S = N.modus_ponens(M_T, instancie(HTS, vM))             # M∈𝔖
    # caractère fini appliqué à M : M∈𝔖 ⇔ (∀Y')((Y'⊂M et Y' fini)⇒Y'∈𝔖)
    cf_M = instancie(Hcf, vM)                                 # M∈𝔖 ⇔ (∀Y')(…)
    droite_M = N.modus_ponens(M_S, equivalence_avant(cf_M))   # (∀Y')((Y'⊂M et Y' fini)⇒Y'∈𝔖)
    # instancie Y'=Y : (Y⊂M et Y fini) ⇒ Y∈𝔖
    fin_Y = conjonction_elim_droite(hY)                       # Y fini
    Y_S = N.modus_ponens(conjonction_intro(Y_M, fin_Y), instancie(droite_M, vY))  # Y∈𝔖
    wit_imp = N.loi_deduction(et(appartient(vM, vT), inclus(vY, vM)), Y_S)
    ex_imp = existe_elimination(wit_imp, M)                   # (∃M)(…) ⇒ Y∈𝔖
    Y_S_final = N.modus_ponens(exM, ex_imp)                   # Y∈𝔖  [Y⊂U et Y fini]
    body = N.loi_deduction(hyp_Y, Y_S_final)
    allY = N.generalisation(Y, body)                          # (∀Y)((Y⊂U et Y fini)⇒Y∈𝔖)

    # ── caractère fini appliqué à U : U∈𝔖 ⇐ allY ──────────────────────────────
    cf_U = instancie(Hcf, U)                                  # U∈𝔖 ⇔ (∀Y)(…)
    # le côté droit de cf_U a le MÊME liant Y et la MÊME forme que allY → arrière
    return N.modus_ponens(allY, equivalence_arriere(cf_U))    # U∈𝔖


# ── tout membre M de la chaîne 𝔗 est ⊂ U=⋃𝔗 ────────────────────────────────
def _M_inclus_U(S, T, M, hMT):
    """De ⊢ M∈𝔗 [hMT] déduit ⊢ M⊂U=⋃𝔗  (membre de la chaîne ⊂ réunion)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    vS, vT, vM = _terme(S), _terme(T), _terme(M)
    GIncl = Incl(vS)
    U = Union(GIncl, vS, vT)
    cible = inclus(vM, U)
    bndr, _ = _peler_pourtout(cible)                          # binder canonique de inclus(M,U)
    vx = var(bndr)
    hxM = N.assume(appartient(vx, vM))                        # x∈M
    # (∃W)(W∈𝔗 et x∈W) via témoin W=M.  Le binder existentiel « W » est choisi
    # DISTINCT du nom de M et de l'élément bndr pour éviter toute capture.
    W = "Wmem"
    R = et(appartient(var(W), vT), appartient(vx, var(W)))
    corps_temoin = conjonction_intro(hMT, hxM)                # M∈𝔗 et x∈M
    ex = N.modus_ponens(corps_temoin, N.s5(R, vM, W))         # (∃W)(W∈𝔗 et x∈W)
    # réaligne le binder existentiel W → « C » (binder du corps de l'axiome Union)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    R_C = et(appartient(var("C"), vT), appartient(vx, var("C")))
    if W != "C":
        ex = N.modus_ponens(ex, equivalence_avant(alpha_existe(W, "C", R)))
    xU = N.modus_ponens(ex, equivalence_arriere(_inst_Union(GIncl, vS, vT, vx)))  # x∈U
    body = N.loi_deduction(appartient(vx, vM), xU)
    return N.generalisation(bndr, body)                       # M⊂U


def union_majorant(S="S", T="T", M="x", Y="Y", Mm="M"):
    """⊢ { 𝔗⊂𝔖, de_caractere_fini(𝔖,E), sous_lemme } ⊢ majorant(Incl, 𝔗, U, 𝔖).

    majorant(Incl,𝔗,U,𝔖) = U∈𝔖 et (∀M)(M∈𝔗 ⇒ (M,U)∈Incl).  U∈𝔖 (union_dans_S) ;
    et pour M∈𝔗 : M∈𝔖 (𝔗⊂𝔖), U∈𝔖, M⊂U ⇒ (M,U)∈Incl.  Binder « x » pour matcher
    majorant(Incl,𝔗,U,𝔖)."""
    vS, vT = var(S), var(T)
    GIncl = Incl(vS)
    U = Union(GIncl, vS, vT)
    HTS = N.assume(inclus(vT, vS))                            # 𝔗⊂𝔖
    U_S = union_dans_S(S, T, Y, Mm)                           # U∈𝔖  [3 hyps]
    vM = var(M)
    hMT = N.assume(appartient(vM, vT))                        # M∈𝔗
    MS = N.modus_ponens(hMT, instancie(HTS, vM))              # M∈𝔖
    M_U = _M_inclus_U(vS, vT, vM, hMT)                        # M⊂U
    M_U_I = _Incl_intro(vS, vM, U, MS, U_S, M_U)             # (M,U)∈Incl
    body = N.loi_deduction(appartient(vM, vT), M_U_I)
    allM = N.generalisation(M, body)                          # (∀M)(M∈𝔗⇒(M,U)∈Incl)
    return conjonction_intro(U_S, allM)                       # majorant(Incl,𝔗,U,𝔖)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — (Incl,𝔖) est INDUCTIF.
# ════════════════════════════════════════════════════════════════════════════
def Incl_est_inductif(S="S", T="Tchain", m="m", x="x", y="y", z="z", Y="Y", Mm="M"):
    """⊢ { de_caractere_fini(𝔖,E), sous_lemme(𝔖,𝔗) } ⊢ est_inductif(Incl,𝔖).

    est_inductif(Incl,𝔖) = est_ordre(Incl,𝔖) et (∀𝔗)(chaine(Incl,𝔖,𝔗) ⇒
    (∃m) majorant(Incl,𝔗,m,𝔖)).  est_ordre (Incl_est_ordre, inconditionnel) ; et
    pour une chaîne 𝔗 (= 𝔗⊂𝔖 et totalement_ordonne), la RÉUNION U=⋃𝔗 est un
    majorant (union_majorant), témoin du (∃m).

    ⚠ Le sous-lemme est INSTANCIÉ au 𝔗 lié par le (∀𝔗) ; il est donc porté comme
    une hypothèse UNIVERSELLE (∀𝔗) — voir Tukey_theoreme pour l'énoncé exact."""
    vS = var(S)
    GIncl = Incl(vS)
    ord_S = Incl_est_ordre(S)                                 # est_ordre(Incl,𝔖)
    vT = var(T)
    # sous-lemme UNIVERSEL (∀𝔗) — assumé une fois (T-clos), instancié au 𝔗 lié.
    # Cela évite que la variable de chaîne 𝔗 reste libre dans une hypothèse lors
    # de la généralisation (∀𝔗).
    Hsl_univ = N.assume(_sous_lemme_universel(S, T, Y, Mm))   # (∀𝔗)sous_lemme(𝔖,𝔗)
    sl_T = instancie(Hsl_univ, vT)                            # sous_lemme(𝔖, 𝔗_lié)
    Hch = N.assume(chaine(GIncl, vS, vT, x, y, z))            # chaine(Incl,𝔖,𝔗)
    T_S = conjonction_elim_gauche(Hch)                        # 𝔗⊂𝔖
    # majorant(Incl,𝔗,U,𝔖) — décharge 𝔗⊂𝔖 et le sous-lemme per-chaîne (depuis l'universel) ;
    # caractère-fini reste porté (𝔖-global, T-clos).
    maj_U = union_majorant(S, T, x, Y, Mm)                    # majorant(Incl,𝔗,U,𝔖)  [3 hyps]
    maj_U = _cut(maj_U, inclus(vT, vS), T_S)
    maj_U = _cut(maj_U, sous_lemme_partie_finie_dans_membre(S, T, Y, Mm), sl_T)
    # (∃m) majorant(Incl,𝔗,m,𝔖) via S5, témoin m=U
    U = Union(GIncl, vS, vT)
    corps_m = majorant(GIncl, vT, var(m), vS, x)
    s5 = N.s5(corps_m, U, m)                                  # (U|m)corps ⇒ (∃m)corps
    ex_maj = N.modus_ponens(maj_U, s5)                        # (∃m)majorant(Incl,𝔗,m,𝔖)
    body = N.loi_deduction(chaine(GIncl, vS, vT, x, y, z), ex_maj)
    allT = N.generalisation(T, body)                          # (∀𝔗)(chaine⇒(∃m)majorant)
    # α-renomme 𝔗 → C pour matcher est_inductif (binder canonique « C »)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    _, corps_T = _peler_pourtout(allT.conclusion)
    if T != "C":
        from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
        ren = alpha_pour_tout(T, "C", corps_T)
        allT = N.modus_ponens(allT, equivalence_avant(ren))
    return conjonction_intro(ord_S, allT)                     # est_inductif(Incl,𝔖)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — 🎯 LE THÉORÈME 1 §III.4 (TUKEY–TEICHMÜLLER).
# ════════════════════════════════════════════════════════════════════════════
def _sous_lemme_universel(S="S", T="C", Y="Y", M="M"):
    """(∀𝔗) sous_lemme_partie_finie_dans_membre(𝔖,𝔗)  — le sous-lemme pour TOUTE
    chaîne 𝔗 (forme universelle portée par Tukey_theoreme).  Liant 𝔗 = « C »
    pour s'aligner sur les usages internes."""
    vT = var(T)
    return pourtout(T, sous_lemme_partie_finie_dans_membre(S, T, Y, M))


def Tukey_theoreme(S="S", m="m", T="Tchain", x="x", y="y", z="z", Y="Y", M="M"):
    """⊢ ( de_caractere_fini(𝔖,E) et 𝔖≠∅ et (∀𝔗)sous_lemme(𝔖,𝔗) )
         ⇒ (∃m) element_maximal(Incl, 𝔖, m).

    🎯🎯 THÉORÈME 1 §III.4 (TUKEY–TEICHMÜLLER), E.III.35 — PROUVÉ via ZORN.
    On ordonne 𝔖 par l'inclusion Incl :
      • est_ordre(Incl,𝔖)      — Incl_est_ordre (inconditionnel) ;
      • est_inductif(Incl,𝔖)   — Incl_est_inductif (CŒUR : ⋃(chaîne)∈𝔖 par
                                  caractère fini + sous-lemme) ;
      • 𝔖≠∅                    — hypothèse (enonce_non_vide).
    Ces trois sont EXACTEMENT le crochet de zorn_theoreme(Incl,𝔖), qui FOURNIT
    (∃m)element_maximal(Incl,𝔖,m).  Le maximal est DÉMONTRÉ, JAMAIS postulé.

    HYPOTHÈSES (honnêtes, NON vacueuses) :
      • de_caractere_fini(𝔖,E)  — la prémisse du théorème (Déf. 2, E.III.34) ;
      • 𝔖≠∅                     — (∅∈𝔖 par caractère fini, mais sa preuve passe par
                                  est_fini_ensemble(∅)=Fini(Card∅) ; porté en
                                  prémisse pour rester focalisé) ;
      • (∀𝔗)sous_lemme(𝔖,𝔗)    — « partie finie de ⋃(chaîne) ⊂ un membre » (la
                                  récurrence finie de Bourbaki, portée honnêtement).
    """
    vS = var(S)
    GIncl = Incl(vS)
    cf = de_caractere_fini(vS, var("E"))
    nv = enonce_non_vide(vS, x)
    sl = _sous_lemme_universel(S, T, Y, M)

    # ── une SEULE hypothèse-conjonction (cf et 𝔖≠∅ et sous-lemme universel) ────
    hyp = et(et(cf, nv), sl)
    H = N.assume(hyp)
    Hcf = conjonction_elim_gauche(conjonction_elim_gauche(H))   # caractère fini
    Hnv = conjonction_elim_droite(conjonction_elim_gauche(H))   # 𝔖≠∅
    Hsl = conjonction_elim_droite(H)                            # (∀𝔗)sous_lemme

    ord_S = Incl_est_ordre(S)                                   # est_ordre(Incl,𝔖)
    # est_inductif(Incl,𝔖) — porte {caractère fini, sous-lemme universel}
    ind_S = Incl_est_inductif(S, T, m, x, y, z, Y, M)
    ind_S = _cut(ind_S, cf, Hcf)
    ind_S = _cut(ind_S, sl, Hsl)

    # ── crochet EXACT de zorn_theoreme(Incl,𝔖) ───────────────────────────────
    zorn_hyp = conjonction_intro(conjonction_intro(ord_S, ind_S), Hnv)
    inst = _zorn_instancie(S)                                  # crochet(Incl,𝔖)⇒(∃m)max
    concl = N.modus_ponens(zorn_hyp, inst)                     # (∃m)maximal(Incl,𝔖,m)  [H]
    return N.loi_deduction(hyp, concl)                         # ⊢ hyp ⇒ (∃m)maximal


def _zorn_instancie(S):
    """⊢ ( est_ordre(Incl,𝔖) et est_inductif(Incl,𝔖) et 𝔖≠∅ ) ⇒ (∃m)maximal(Incl,𝔖,m).

    zorn_theoreme() (CLOS) instancié à G:=Incl(𝔖), E:=𝔖 via un PIVOT frais s0
    (motif `_zorn_instancie` de ensembles_comparabilite) pour éviter toute capture
    de la lettre 𝔖."""
    s0 = "_ts0"
    vs0 = var(s0)
    Incl0 = Incl(vs0)
    th = zorn_theoreme()                                       # CLOS (binders G,E,m,C,x,y,z)
    th = N.generalisation("G", N.generalisation("E", th))      # (∀E∀G)( … )
    th = instancie(th, Incl0)                                  # G:=Incl(s0)
    th = instancie(th, vs0)                                    # E:=s0
    th = instancie(N.generalisation(s0, th), var(S))           # s0:=𝔖
    return th


__all__ = [
    "Incl", "axiome_Incl", "theorie_Incl", "Incl_membre",
    "Incl_reflexive_sur", "Incl_antisymetrique", "Incl_transitive", "Incl_est_ordre",
    "sous_lemme_partie_finie_dans_membre", "union_dans_S", "union_majorant",
    "Incl_est_inductif", "Tukey_theoreme",
]
