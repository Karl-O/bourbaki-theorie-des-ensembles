"""§III.4 — PARTIES FINIES D'ENSEMBLES ORDONNÉS (Proposition 3 et corollaires).

🎯 PROPOSITION 3 (E III.34) — VERBATIM :
   « Soit E un ensemble préordonné filtrant à droite (resp. un ensemble ordonné
   réticulé, resp. un ensemble totalement ordonné). Toute partie finie non vide de
   E est majorée (resp. admet une borne supérieure et une borne inférieure, resp.
   admet un plus grand et un plus petit élément). »
   Démonstration Bourbaki : récurrence sur le nombre n d'éléments de la partie.

   COROLLAIRE 1 — Tout ensemble fini totalement ordonné est bien ordonné et admet
                  un plus grand élément.
   COROLLAIRE 2 — Tout ensemble ordonné fini admet un élément maximal.

────────────────────────────────────────────────────────────────────────────────
ROUTE — `recurrence_finie(P)` (§III.5, keystone CLOS, 0 hyp) :
    P(X) := ( X⊂E et ¬(X=∅) ) ⇒ (∃m)(<conclusion sur la partie X>).
  Base ∅ : X=∅ ⇒ l'antécédent ¬(X=∅) est faux ⇒ implication vraie (vacuous-guard).
  Pas X∪{x} : on suppose X⊂E, x∉X, P(X), et l'on prouve P(X∪{x}).
    • si X=∅ : X∪{x}={x}, et x est le plus grand élément (resp. majorant, …) de {x} ;
    • si X≠∅ : P(X) fournit l'objet m pour X ; on le combine avec x via la propriété
      structurelle de E (totalité : comparer m et x ; le plus grand des deux convient).

Ce module traite la VARIANTE TOTALEMENT ORDONNÉE de la Prop 3 (plus grand élément)
et le Corollaire 1 (qui en découle en X:=E). theorie=22, aucun postulat.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
    equivalence_transitivite,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.ordre.ensembles_ordre_relation import (
    est_ordre, totalement_ordonne, plus_grand_element, majorant,
    element_maximal, _couple_dans,
)
from bourbaki.entiers.ensembles_recurrence_finie import (
    recurrence_finie, recurrence_finie_enonce,
)
from bourbaki.entiers.ensembles_entiers import est_fini_ensemble
from bourbaki.ensembles.ensembles_theoremes import _instance_reunion
from bourbaki.ensembles.base.ensembles_couples import singleton_membre


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_ZPG = "zpgT"   # bound variable name used UNIFORMLY in plus_grand_element here


def _pge(G, A, m):
    """plus_grand_element avec liant interne FIXÉ à _ZPG (évite la capture du point x)."""
    return plus_grand_element(G, _t(A), _t(m), x=_ZPG)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  MEMBERSHIP X∪{x} :  z ∈ X∪{x}  ⇔  (z∈X  ou  z=x)
# ════════════════════════════════════════════════════════════════════════════
def _membre_union_singleton(z, X, x):
    """⊢ ( z ∈ X∪{x} ) ⇔ ( z∈X ou z=x ).

    AXIOME_REUNION : z∈X∪{x} ⇔ (z∈X ou z∈{x}) ; singleton_membre : z∈{x} ⇔ z=x."""
    vz, vX, vx = _t(z), _t(X), _t(x)
    sing = E.singleton(vx)
    runi = _instance_reunion(vX, sing, vz)                 # z∈X∪{x} ⇔ (z∈X ou z∈{x})
    smem = singleton_membre(vz, vx)                        # z∈{x} ⇔ z=x
    A = appartient(vz, vX)
    Bs = appartient(vz, sing)
    Be = egal(vz, vx)
    # ⇒ : (z∈X ou z∈{x}) ⇒ (z∈X ou z=x)
    hdisj = N.assume(ou(A, Bs))
    casA = N.s2(A, Be)                                    # A ⇒ (A ou z=x)
    casB = N.loi_deduction(Bs, _ou_droite(A, N.modus_ponens(N.assume(Bs), equivalence_avant(smem))))
    fwd = N.loi_deduction(ou(A, Bs), cas(hdisj, casA, casB))
    # ⇐ : (z∈X ou z=x) ⇒ (z∈X ou z∈{x})
    hdisj2 = N.assume(ou(A, Be))
    casA2 = N.s2(A, Bs)                                   # A ⇒ (A ou z∈{x})
    casB2 = N.loi_deduction(Be, _ou_droite(A, N.modus_ponens(N.assume(Be), equivalence_arriere(smem))))
    bwd = N.loi_deduction(ou(A, Be), cas(hdisj2, casA2, casB2))
    equiv2 = conjonction_intro(fwd, bwd)                   # (z∈X ou z∈{x}) ⇔ (z∈X ou z=x)
    return equivalence_transitivite(runi, equiv2)


def _ou_droite(A, thmB):
    """De ⊢ B, déduit ⊢ (A ou B).   (introduction droite de ∨, via S2+S3.)"""
    B = thmB.conclusion
    return N.modus_ponens(N.modus_ponens(thmB, N.s2(B, A)), N.s3(B, A))  # B⇒(B ou A)⇒(A ou B)


# ════════════════════════════════════════════════════════════════════════════
#  PRÉDICAT P pour la variante TOTALEMENT ORDONNÉE (plus grand élément)
# ════════════════════════════════════════════════════════════════════════════
def _P_plus_grand(G, E_set, m="m_pgf"):
    """P(X) := ( X⊂E et ¬(X=∅) ) ⇒ (∃m)( plus_grand_element(G,X,m) )."""
    vE = _t(E_set)
    def P(X):
        vX = _t(X)
        garde = et(inclus(vX, vE), non(egal(vX, E.VIDE)))
        concl = existe(m, _pge(G, vX, var(m)))
        return impl(garde, concl)
    return P


# ════════════════════════════════════════════════════════════════════════════
#  Briques : décomposer est_ordre / totalement_ordonne en réfl/antisym/trans/total
# ════════════════════════════════════════════════════════════════════════════
def _decompose_total(htot, G, E_set, x="x", y="y", z="z"):
    """De htot : ⊢ totalement_ordonne(G,E), renvoie (refl, antisym, trans, comp)
    où chacun est une preuve du conjoint correspondant."""
    ord_ = conjonction_elim_gauche(htot)                  # est_ordre(G,E)
    comp = conjonction_elim_droite(htot)                  # comparables
    refl = conjonction_elim_gauche(conjonction_elim_gauche(ord_))   # reflexivite_sur
    antisym = conjonction_elim_droite(conjonction_elim_gauche(ord_))
    trans = conjonction_elim_droite(ord_)
    return refl, antisym, trans, comp


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 3 (variante totalement ordonnée — plus grand élément)
# ════════════════════════════════════════════════════════════════════════════
def prop3_total_enonce(G, E_set, X="Xpgt", m="m_pgf"):
    """⊢-cible : ( totalement_ordonne(G,E) ) ⇒
        (∀X)( ( est_fini_ensemble(X) et X⊂E et ¬(X=∅) )
              ⇒ (∃m)( plus_grand_element(G,X,m) ) ).

    « Toute partie finie non vide d'un ensemble totalement ordonné admet un plus
    grand élément. »  (Prop. 3 §III.4, variante totale.)"""
    vE = _t(E_set)
    vX = var(X)
    corps = impl(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))),
                 existe(m, _pge(G, vX, var(m))))
    return impl(totalement_ordonne(G, E_set), pourtout(X, corps))


def _preuve_pas_total(G, E_set, htot, P, X="Xrec", x="xrec", z="zpgT", m="m_pgf"):
    """{ htot } ⊢ _pas_ensemble(P)  pour P = _P_plus_grand(G,E).

    P(X) := (X⊂E et ¬(X=∅)) ⇒ (∃m)(plus_grand_element(G,X,m)).
    Le pas : (Fini-ens X et ¬(x∈X) et P(X)) ⇒ P(X∪{x})."""
    from bourbaki.entiers.ensembles_recurrence_finie import _pas_ensemble
    vE = _t(E_set)
    vX, vx, vz = var(X), var(x), var(z)
    Xux = E.reunion(vX, E.singleton(vx))
    refl, antisym, trans, comp = _decompose_total(htot, G, E_set)

    # hyp du pas : Fini-ens X et ¬(x∈X) et P(X)
    hpas = N.assume(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)))
    hPX = conjonction_elim_droite(hpas)                   # P(X) : (X⊂E et ¬(X=∅)) ⇒ (∃m)pge(X,m)

    # but : P(X∪{x}) = (X∪{x}⊂E et ¬(X∪{x}=∅)) ⇒ (∃m)pge(X∪{x},m)
    garde = et(inclus(Xux, vE), non(egal(Xux, E.VIDE)))
    hgarde = N.assume(garde)
    Xux_sub_E = conjonction_elim_gauche(hgarde)           # X∪{x} ⊂ E

    # x ∈ X∪{x}  (via membership) ; x ∈ E
    mem_x = _membre_union_singleton(vx, vX, vx)           # x∈X∪{x} ⇔ (x∈X ou x=x)
    x_in_Xux = N.modus_ponens(
        _ou_droite(appartient(vx, vX), N.reflexivite(vx)),   # (x∈X ou x=x)
        equivalence_arriere(mem_x))                       # x∈X∪{x}
    x_in_E = N.modus_ponens(x_in_Xux, instancie(Xux_sub_E, vx))   # x∈E

    # X⊂E  : X ⊂ X∪{x} ⊂ E.  (liant "z" pour coïncider avec l'encodage de inclus.)
    vz2 = var("z")
    hzX = N.assume(appartient(vz2, vX))
    z_in_Xux = N.modus_ponens(
        N.modus_ponens(hzX, N.s2(appartient(vz2, vX), egal(vz2, vx))),
        equivalence_arriere(_membre_union_singleton(vz2, vX, vx)))
    z_in_E = N.modus_ponens(z_in_Xux, instancie(Xux_sub_E, vz2))
    X_sub_E = N.generalisation("z", N.loi_deduction(appartient(vz2, vX), z_in_E))   # X⊂E

    # ── cas A : X = ∅ ──  →  X∪{x} = {x}, x plus grand de {x} ; mais on travaille avec
    #    X∪{x} directement.  On montre que x est le plus grand élément de X∪{x} en
    #    utilisant que tout élément z∈X∪{x} est soit dans X (impossible si X=∅, mais on
    #    n'a pas besoin de discriminer : voir cas B' général ci-dessous).
    #
    # On évite la disjonction X=∅/X≠∅ par tiers exclu sur ¬(X=∅) : on prouve P(X∪{x})
    # par CAS sur  (X=∅)  ou  ¬(X=∅).
    from bourbaki.logique.tactiques.tactiques_abrege2 import tiers_exclu
    te = tiers_exclu(egal(vX, E.VIDE))                    # (X=∅) ou ¬(X=∅)

    # ── helper : (z,t)∈G transport via Leibniz pour z=x etc. déjà géré inline ──────
    def refl_en(t_in_E, t):
        return N.modus_ponens(t_in_E, instancie(refl, t))

    # ============ CAS A : X = ∅  ============================================
    hXvide = N.assume(egal(vX, E.VIDE))
    # x est le plus grand : x∈X∪{x} (déjà) et ∀z(z∈X∪{x} ⇒ (z,x)∈G).
    # Pour z∈X∪{x} : (z∈X ou z=x).  z∈X ⇒ z∈∅ (Leibniz X↦∅) ⇒ faux ; z=x ⇒ (z,x)∈G refl.
    hz_in = N.assume(appartient(vz, Xux))
    disj_z = N.modus_ponens(hz_in, equivalence_avant(_membre_union_singleton(vz, vX, vx)))  # z∈X ou z=x
    #   sous-cas z∈X : contradiction via X=∅
    hzX2 = N.assume(appartient(vz, vX))
    #   X=∅ ⇒ (z∈X ⇔ z∈∅) ; z∈∅ faux
    leibV = N.s6(vX, E.VIDE, "wv", appartient(vz, var("wv")))   # (X=∅)⇒(z∈X ⇔ z∈∅)
    z_in_vide = N.modus_ponens(hzX2, equivalence_avant(N.modus_ponens(hXvide, leibV)))  # z∈∅
    nz_vide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)   # ¬(z∈∅)
    falso = N.modus_ponens(z_in_vide, N.modus_ponens(nz_vide, N.s2(non(appartient(vz, E.VIDE)), _couple_dans(vz, vx, G))))
    # falso : (z,x)∈G  (ex falso : de z∈∅ et ¬(z∈∅))
    casA_zX = N.loi_deduction(appartient(vz, vX), falso)  # z∈X ⇒ (z,x)∈G
    #   sous-cas z=x : (z,x)∈G via réfl (x,x)∈G transporté
    hzx = N.assume(egal(vz, vx))
    xx_G = refl_en(x_in_E, vx)                            # (x,x)∈G
    leib_zx = N.s6(vx, vz, "wzx", _couple_dans(var("wzx"), vx, G))   # (x=z)⇒((x,x)∈G⇔(z,x)∈G)
    x_eq_z = N.modus_ponens(hzx, symetrie(vz, vx))        # x=z
    zx_G = N.modus_ponens(xx_G, equivalence_avant(N.modus_ponens(x_eq_z, leib_zx)))  # (z,x)∈G
    casA_zx = N.loi_deduction(egal(vz, vx), zx_G)         # z=x ⇒ (z,x)∈G
    zx_final_A = cas(disj_z, casA_zX, casA_zx)            # (z,x)∈G  (sous z∈X∪{x})
    maj_body_A = N.generalisation(z, N.loi_deduction(appartient(vz, Xux), zx_final_A))
    pge_x_A = conjonction_intro(x_in_Xux, maj_body_A)     # plus_grand_element(G, X∪{x}, x)
    ex_A = N.modus_ponens(pge_x_A, N.s5(_pge(G, Xux, var(m)), vx, m))   # (∃m)pge(X∪{x},m)
    casA = N.loi_deduction(egal(vX, E.VIDE), ex_A)        # (X=∅) ⇒ (∃m)pge(X∪{x},m)

    # ============ CAS B : X ≠ ∅  ============================================
    hXnonvide = N.assume(non(egal(vX, E.VIDE)))
    # P(X) appliqué : antécédent (X⊂E et ¬(X=∅))
    ante_PX = conjonction_intro(X_sub_E, hXnonvide)
    ex_mX = N.modus_ponens(ante_PX, hPX)                 # (∃m)pge(X,m)
    # élimination du témoin m : on prouve (∃m')pge(X∪{x},m') à partir de pge(X,m)
    hpgeX = N.assume(_pge(G, vX, var(m)))   # pge(X,m) : m∈X et ∀z(z∈X⇒(z,m)∈G)
    vm = var(m)
    m_in_X = conjonction_elim_gauche(hpgeX)
    m_maj_X = conjonction_elim_droite(hpgeX)             # ∀z(z∈X⇒(z,m)∈G)
    m_in_Xux = N.modus_ponens(
        N.modus_ponens(m_in_X, N.s2(appartient(vm, vX), egal(vm, vx))),
        equivalence_arriere(_membre_union_singleton(vm, vX, vx)))   # m∈X∪{x}
    m_in_E = N.modus_ponens(m_in_X, instancie(X_sub_E, vm))   # m∈E
    # comparer m et x : (m,x)∈G ou (x,m)∈G
    comp_mx = N.modus_ponens(conjonction_intro(m_in_E, x_in_E),
                             instancie(instancie(comp, vm), vx))    # (m,x)∈G ou (x,m)∈G

    #   --- sous-cas (m,x)∈G : x est le plus grand de X∪{x} ---
    hmx = N.assume(_couple_dans(vm, vx, G))              # (m,x)∈G
    #   ∀z∈X∪{x} : (z,x)∈G.   z∈X ⇒ (z,m)∈G puis trans avec (m,x) ; z=x ⇒ réfl.
    hz_in_B1 = N.assume(appartient(vz, Xux))
    disj_zB1 = N.modus_ponens(hz_in_B1, equivalence_avant(_membre_union_singleton(vz, vX, vx)))
    #     z∈X
    hzX_B1 = N.assume(appartient(vz, vX))
    zm_G = N.modus_ponens(hzX_B1, instancie(m_maj_X, vz))    # (z,m)∈G
    trans_inst = instancie(instancie(instancie(trans, vz), vm), vx)   # ((z,m)∈G et (m,x)∈G)⇒(z,x)∈G
    zx_G_B1 = N.modus_ponens(conjonction_intro(zm_G, hmx), trans_inst)   # (z,x)∈G
    casB1_zX = N.loi_deduction(appartient(vz, vX), zx_G_B1)
    #     z=x
    hzx_B1 = N.assume(egal(vz, vx))
    xxG = refl_en(x_in_E, vx)
    x_eq_z_B1 = N.modus_ponens(hzx_B1, symetrie(vz, vx))
    zxG_B1 = N.modus_ponens(xxG, equivalence_avant(N.modus_ponens(x_eq_z_B1, N.s6(vx, vz, "wb1", _couple_dans(var("wb1"), vx, G)))))
    casB1_zx = N.loi_deduction(egal(vz, vx), zxG_B1)
    zx_final_B1 = cas(disj_zB1, casB1_zX, casB1_zx)
    maj_body_B1 = N.generalisation(z, N.loi_deduction(appartient(vz, Xux), zx_final_B1))
    pge_x_B1 = conjonction_intro(x_in_Xux, maj_body_B1)     # pge(G,X∪{x},x)
    ex_B1 = N.modus_ponens(pge_x_B1, N.s5(_pge(G, Xux, var(m)), vx, m))   # (∃m)pge(X∪{x},m)
    casB1 = N.loi_deduction(_couple_dans(vm, vx, G), ex_B1)

    #   --- sous-cas (x,m)∈G : m est le plus grand de X∪{x} ---
    hxm = N.assume(_couple_dans(vx, vm, G))             # (x,m)∈G
    hz_in_B2 = N.assume(appartient(vz, Xux))
    disj_zB2 = N.modus_ponens(hz_in_B2, equivalence_avant(_membre_union_singleton(vz, vX, vx)))
    #     z∈X ⇒ (z,m)∈G
    hzX_B2 = N.assume(appartient(vz, vX))
    zmG_B2 = N.modus_ponens(hzX_B2, instancie(m_maj_X, vz))
    casB2_zX = N.loi_deduction(appartient(vz, vX), zmG_B2)
    #     z=x ⇒ (z,m)∈G via (x,m)∈G + Leibniz x↦z
    hzx_B2 = N.assume(egal(vz, vx))
    x_eq_z_B2 = N.modus_ponens(hzx_B2, symetrie(vz, vx))
    zmG_B2b = N.modus_ponens(hxm, equivalence_avant(N.modus_ponens(x_eq_z_B2, N.s6(vx, vz, "wb2", _couple_dans(var("wb2"), vm, G)))))
    casB2_zx = N.loi_deduction(egal(vz, vx), zmG_B2b)
    zm_final_B2 = cas(disj_zB2, casB2_zX, casB2_zx)
    maj_body_B2 = N.generalisation(z, N.loi_deduction(appartient(vz, Xux), zm_final_B2))
    pge_m_B2 = conjonction_intro(m_in_Xux, maj_body_B2)
    ex_B2 = N.modus_ponens(pge_m_B2, N.s5(_pge(G, Xux, var(m)), vm, m))   # (∃m')pge(X∪{x},m')
    casB2 = N.loi_deduction(_couple_dans(vx, vm, G), ex_B2)

    ex_from_pgeX = cas(comp_mx, casB1, casB2)            # (∃m)pge(X∪{x},m)  (sous pge(X,m))
    imp_pgeX = N.loi_deduction(_pge(G, vX, var(m)), ex_from_pgeX)
    ex_B = N.modus_ponens(ex_mX, existe_elimination(imp_pgeX, m))   # (∃m)pge(X∪{x},m)  (sous ¬(X=∅))
    casB = N.loi_deduction(non(egal(vX, E.VIDE)), ex_B)

    # ── combine A/B par tiers exclu ─────────────────────────────────────────────
    ex_total = cas(te, casA, casB)                       # (∃m)pge(X∪{x},m)  (sous garde)
    PXux = N.loi_deduction(garde, ex_total)              # P(X∪{x})
    corps = N.loi_deduction(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)), PXux)
    res = N.generalisation(X, N.generalisation(x, corps))
    assert res.conclusion == _pas_ensemble(P, X, x), "pas mal formé"
    return res


def prop3_total(G="Gpgt", E_set="Epgt", X="Xpgt", m="m_pgf"):
    """🎯 ⊢ prop3_total_enonce(G,E).   (Prop. 3 §III.4, variante totalement ordonnée.)

    Toute partie FINIE non vide d'un ensemble TOTALEMENT ORDONNÉ admet un plus grand
    élément.  Via `recurrence_finie` : P(X):=(X⊂E et ¬(X=∅))⇒(∃m)pge(G,X,m) ; base ∅
    vacuous (¬(X=∅) faux), pas par comparaison du plus grand de X avec le point ajouté."""
    vE = _t(E_set)
    htot = N.assume(totalement_ordonne(G, E_set))
    P = _P_plus_grand(G, E_set, m)

    # P(∅) : antécédent (∅⊂E et ¬(∅=∅)) faux car ¬(∅=∅) faux ⇒ implication triviale
    hP0_ante = N.assume(et(inclus(E.VIDE, vE), non(egal(E.VIDE, E.VIDE))))
    n_refl = conjonction_elim_droite(hP0_ante)           # ¬(∅=∅)
    refl0 = N.reflexivite(E.VIDE)                        # ∅=∅
    from bourbaki.ensembles import ensembles_abrege as _E
    concl0 = existe(m, _pge(G, E.VIDE, var(m)))
    falso0 = N.modus_ponens(refl0, N.modus_ponens(n_refl, N.s2(non(egal(E.VIDE, E.VIDE)), concl0)))
    P0 = N.loi_deduction(et(inclus(E.VIDE, vE), non(egal(E.VIDE, E.VIDE))), falso0)   # P(∅)
    assert P0.conclusion == P(E.VIDE), "P(∅) mal formé"

    pas = _preuve_pas_total(G, E_set, htot, P, m=m)      # _pas_ensemble(P)  [htot]

    # recurrence_finie(P) : (P(∅) et pas) ⇒ (∀X)(Fini-ens X ⇒ P(X))
    rf = recurrence_finie(P)
    premisse = et(P(E.VIDE), pas.conclusion)
    fini_imp_PX = N.modus_ponens(conjonction_intro(P0, pas), rf)   # (∀X)(Fini-ens X ⇒ P(X))  [htot]

    # spécialise : (Fini-ens X et X⊂E et ¬(X=∅)) ⇒ (∃m)pge(G,X,m)
    vX = var(X)
    inst = instancie(fini_imp_PX, vX)                    # Fini-ens X ⇒ P(X)
    hfin = N.assume(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))))
    fini_ens_X = conjonction_elim_gauche(conjonction_elim_gauche(hfin))
    X_sub = conjonction_elim_droite(conjonction_elim_gauche(hfin))
    X_nv = conjonction_elim_droite(hfin)
    PX = N.modus_ponens(fini_ens_X, inst)               # P(X) = (X⊂E et ¬(X=∅))⇒(∃m)pge
    ex_m = N.modus_ponens(conjonction_intro(X_sub, X_nv), PX)
    corps = N.loi_deduction(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))), ex_m)
    concl = N.generalisation(X, corps)
    res = N.loi_deduction(totalement_ordonne(G, E_set), concl)
    assert res.conclusion == prop3_total_enonce(G, E_set, X, m), "conclusion ≠ énoncé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 — un ensemble fini totalement ordonné admet un plus grand élément
# ════════════════════════════════════════════════════════════════════════════
def cor1_total_enonce(G, E_set, m="m_pgf"):
    """⊢-cible : ( totalement_ordonne(G,E) et est_fini_ensemble(E) et ¬(E=∅) )
        ⇒ (∃m)( plus_grand_element(G,E,m) ).

    « Tout ensemble fini totalement ordonné (non vide) admet un plus grand élément. »
    (Cor. 1 §III.4 — partie « plus grand élément ».)"""
    vE = _t(E_set)
    return impl(et(et(totalement_ordonne(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))),
                existe(m, _pge(G, vE, var(m))))


def cor1_total(G="Gpgt", E_set="Epgt", m="m_pgf"):
    """🎯 ⊢ cor1_total_enonce(G,E).   (Cor. 1 §III.4, partie plus grand élément.)

    Application directe de prop3_total à la partie X := E (E⊂E par inclusion réflexive)."""
    vE = _t(E_set)
    h = N.assume(et(et(totalement_ordonne(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))))
    htot = conjonction_elim_gauche(conjonction_elim_gauche(h))
    hfin = conjonction_elim_droite(conjonction_elim_gauche(h))
    hnv = conjonction_elim_droite(h)
    # prop3_total appliqué : totalement_ordonne ⇒ (∀X)((Fini-ens X et X⊂E et ¬(X=∅))⇒(∃m)pge)
    p3 = prop3_total(G, E_set, "XcorE", m)
    forall_X = N.modus_ponens(htot, p3)
    inst_E = instancie(forall_X, vE)                    # (Fini-ens E et E⊂E et ¬(E=∅))⇒(∃m)pge(G,E,m)
    # E⊂E
    E_sub_E = _inclus_refl_via(vE)
    ex = N.modus_ponens(conjonction_intro(conjonction_intro(hfin, E_sub_E), hnv), inst_E)
    res = N.loi_deduction(et(et(totalement_ordonne(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))), ex)
    assert res.conclusion == cor1_total_enonce(G, E_set, m), "conclusion ≠ énoncé cor1"
    return res


def _inclus_refl_via(t):
    vz = var("z")
    body = N.loi_deduction(appartient(vz, t), N.assume(appartient(vz, t)))   # z∈t⇒z∈t
    return N.generalisation("z", body)                   # t⊂t


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 3 (variante FILTRANTE à droite — majorant dans E)
# ════════════════════════════════════════════════════════════════════════════
_ZMJ = "zmjf"   # liant fixe de majorant ici


def _maj(G, A, m, E_set):
    """majorant(G,A,m,E) avec liant interne FIXÉ à _ZMJ (évite la capture du point)."""
    return majorant(G, _t(A), _t(m), _t(E_set), x=_ZMJ)


def _filtrant_droite_G(G, E_set, x="xfd", y="yfd", z="zfd"):
    """est_filtrant_droite pour la relation de graphe R(a,b):=(a,b)∈G."""
    R = lambda a, b: _couple_dans(a, b, G)
    return E.est_filtrant_droite(R, _t(E_set), x, y, z)


def _P_majorant(G, E_set, m="m_mjf"):
    """P(X) := ( X⊂E et ¬(X=∅) ) ⇒ (∃m)( majorant(G,X,m,E) )."""
    vE = _t(E_set)
    def P(X):
        vX = _t(X)
        garde = et(inclus(vX, vE), non(egal(vX, E.VIDE)))
        return impl(garde, existe(m, _maj(G, vX, var(m), vE)))
    return P


def prop3_filtrant_enonce(G, E_set, X="Xmjt", m="m_mjf"):
    """⊢-cible : ( est_ordre(G,E) et est_filtrant_droite_G(G,E) ) ⇒
        (∀X)( ( est_fini_ensemble(X) et X⊂E et ¬(X=∅) )
              ⇒ (∃m)( majorant(G,X,m,E) ) ).

    « Toute partie finie non vide d'un ensemble ordonné filtrant à droite est
    majorée. »  (Prop. 3 §III.4, variante filtrante.)"""
    vE = _t(E_set)
    vX = var(X)
    corps = impl(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))),
                 existe(m, _maj(G, vX, var(m), vE)))
    return impl(et(est_ordre(G, E_set), _filtrant_droite_G(G, E_set)),
                pourtout(X, corps))


def _preuve_pas_filtrant(G, E_set, hord, hfilt, P, X="Xrec", x="xrec", m="m_mjf"):
    """{ hord, hfilt } ⊢ _pas_ensemble(P)  pour P = _P_majorant(G,E)."""
    from bourbaki.entiers.ensembles_recurrence_finie import _pas_ensemble
    vE = _t(E_set)
    vX, vx = var(X), var(x)
    Xux = E.reunion(vX, E.singleton(vx))
    # décompose est_ordre
    refl = conjonction_elim_gauche(conjonction_elim_gauche(hord))
    trans = conjonction_elim_droite(hord)

    hpas = N.assume(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)))
    hPX = conjonction_elim_droite(hpas)                   # P(X)
    garde = et(inclus(Xux, vE), non(egal(Xux, E.VIDE)))
    hgarde = N.assume(garde)
    Xux_sub_E = conjonction_elim_gauche(hgarde)           # X∪{x} ⊂ E

    # x ∈ X∪{x} ; x∈E
    mem_x = _membre_union_singleton(vx, vX, vx)
    x_in_Xux = N.modus_ponens(_ou_droite(appartient(vx, vX), N.reflexivite(vx)),
                              equivalence_arriere(mem_x))
    x_in_E = N.modus_ponens(x_in_Xux, instancie(Xux_sub_E, vx))
    # X⊂E (liant "z")
    vz2 = var("z")
    hzX = N.assume(appartient(vz2, vX))
    z_in_Xux = N.modus_ponens(N.modus_ponens(hzX, N.s2(appartient(vz2, vX), egal(vz2, vx))),
                              equivalence_arriere(_membre_union_singleton(vz2, vX, vx)))
    z_in_E = N.modus_ponens(z_in_Xux, instancie(Xux_sub_E, vz2))
    X_sub_E = N.generalisation("z", N.loi_deduction(appartient(vz2, vX), z_in_E))

    # tiers exclu sur ¬(X=∅)
    from bourbaki.logique.tactiques.tactiques_abrege2 import tiers_exclu
    te = tiers_exclu(egal(vX, E.VIDE))
    va = var(_ZMJ)   # liant du majorant : on raisonne sur a := _ZMJ

    # ============ CAS A : X=∅ — x est un majorant de X∪{x} dans E ============
    hXvide = N.assume(egal(vX, E.VIDE))
    # majorant(G,X∪{x},x,E) = x∈E et (∀a)(a∈X∪{x} ⇒ (a,x)∈G)
    ha_in = N.assume(appartient(va, Xux))
    disj_a = N.modus_ponens(ha_in, equivalence_avant(_membre_union_singleton(va, vX, vx)))
    #   a∈X : contradiction (X=∅)
    haX = N.assume(appartient(va, vX))
    leibV = N.s6(vX, E.VIDE, "wv", appartient(va, var("wv")))
    a_in_vide = N.modus_ponens(haX, equivalence_avant(N.modus_ponens(hXvide, leibV)))
    nv = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), va)
    falsoA = N.modus_ponens(a_in_vide, N.modus_ponens(nv, N.s2(non(appartient(va, E.VIDE)), _couple_dans(va, vx, G))))
    casA_aX = N.loi_deduction(appartient(va, vX), falsoA)
    #   a=x : (a,x)∈G via réfl (x,x)∈G
    hax = N.assume(egal(va, vx))
    xxG = N.modus_ponens(x_in_E, instancie(refl, vx))     # (x,x)∈G
    x_eq_a = N.modus_ponens(hax, symetrie(va, vx))
    axG = N.modus_ponens(xxG, equivalence_avant(N.modus_ponens(x_eq_a, N.s6(vx, va, "wax", _couple_dans(var("wax"), vx, G)))))
    casA_ax = N.loi_deduction(egal(va, vx), axG)
    ax_final_A = cas(disj_a, casA_aX, casA_ax)
    maj_body_A = N.generalisation(_ZMJ, N.loi_deduction(appartient(va, Xux), ax_final_A))
    majx_A = conjonction_intro(x_in_E, maj_body_A)        # majorant(G,X∪{x},x,E)
    exA = N.modus_ponens(majx_A, N.s5(_maj(G, Xux, var(m), vE), vx, m))
    casA = N.loi_deduction(egal(vX, E.VIDE), exA)

    # ============ CAS B : X≠∅ ============
    hXnv = N.assume(non(egal(vX, E.VIDE)))
    ex_mX = N.modus_ponens(conjonction_intro(X_sub_E, hXnv), hPX)   # (∃m)maj(X,m)
    vm = var(m)
    hmaj = N.assume(_maj(G, vX, vm, vE))                  # maj(X,m): m∈E et (∀a)(a∈X⇒(a,m)∈G)
    m_in_E = conjonction_elim_gauche(hmaj)
    m_maj = conjonction_elim_droite(hmaj)
    # filtrant : (m∈E et x∈E) ⇒ (∃z)(z∈E et (m,z)∈G et (x,z)∈G)
    filt_inst = instancie(instancie(hfilt, vm), vx)
    ex_z = N.modus_ponens(conjonction_intro(m_in_E, x_in_E), filt_inst)   # (∃z)(...)
    vw = var("zfd")
    hz = N.assume(et(et(appartient(vw, vE), _couple_dans(vm, vw, G)), _couple_dans(vx, vw, G)))
    w_in_E = conjonction_elim_gauche(conjonction_elim_gauche(hz))
    mw_G = conjonction_elim_droite(conjonction_elim_gauche(hz))
    xw_G = conjonction_elim_droite(hz)
    # z(=w) est un majorant de X∪{x} : ∀a∈X∪{x} (a,w)∈G
    ha_inB = N.assume(appartient(va, Xux))
    disj_aB = N.modus_ponens(ha_inB, equivalence_avant(_membre_union_singleton(va, vX, vx)))
    #   a∈X ⇒ (a,m)∈G puis trans (m,w) ⇒ (a,w)∈G
    haX_B = N.assume(appartient(va, vX))
    am_G = N.modus_ponens(haX_B, instancie(m_maj, va))
    trans_amw = instancie(instancie(instancie(trans, va), vm), vw)
    aw_G_B = N.modus_ponens(conjonction_intro(am_G, mw_G), trans_amw)
    casB_aX = N.loi_deduction(appartient(va, vX), aw_G_B)
    #   a=x ⇒ (a,w)∈G via (x,w)∈G + Leibniz x↦a
    hax_B = N.assume(egal(va, vx))
    x_eq_a_B = N.modus_ponens(hax_B, symetrie(va, vx))
    aw_G_Bb = N.modus_ponens(xw_G, equivalence_avant(N.modus_ponens(x_eq_a_B, N.s6(vx, va, "wxw", _couple_dans(var("wxw"), vw, G)))))
    casB_ax = N.loi_deduction(egal(va, vx), aw_G_Bb)
    aw_final = cas(disj_aB, casB_aX, casB_ax)
    maj_body_B = N.generalisation(_ZMJ, N.loi_deduction(appartient(va, Xux), aw_final))
    majw = conjonction_intro(w_in_E, maj_body_B)          # majorant(G,X∪{x},w,E)
    exB_w = N.modus_ponens(majw, N.s5(_maj(G, Xux, var(m), vE), vw, m))   # (∃m)maj(X∪{x},m)
    # éliminer le témoin z(=w) du filtrant
    imp_z = N.loi_deduction(et(et(appartient(vw, vE), _couple_dans(vm, vw, G)), _couple_dans(vx, vw, G)), exB_w)
    exB_fromZ = N.modus_ponens(ex_z, existe_elimination(imp_z, "zfd"))
    # éliminer le témoin m
    imp_m = N.loi_deduction(_maj(G, vX, vm, vE), exB_fromZ)
    exB = N.modus_ponens(ex_mX, existe_elimination(imp_m, m))
    casB = N.loi_deduction(non(egal(vX, E.VIDE)), exB)

    ex_total = cas(te, casA, casB)
    PXux = N.loi_deduction(garde, ex_total)
    corps = N.loi_deduction(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)), PXux)
    res = N.generalisation(X, N.generalisation(x, corps))
    assert res.conclusion == _pas_ensemble(P, X, x), "pas filtrant mal formé"
    return res


def prop3_filtrant(G="Gmjt", E_set="Emjt", X="Xmjt", m="m_mjf"):
    """🎯 ⊢ prop3_filtrant_enonce(G,E).   (Prop. 3 §III.4, variante filtrante à droite.)

    Toute partie FINIE non vide d'un ensemble ORDONNÉ FILTRANT à droite est majorée
    (admet un majorant DANS E).  Via `recurrence_finie` ; le pas combine le majorant m
    de X avec le point x par la propriété filtrante (z∈E majore m et x) + transitivité."""
    vE = _t(E_set)
    hyp_conj = N.assume(et(est_ordre(G, E_set), _filtrant_droite_G(G, E_set)))
    hord = conjonction_elim_gauche(hyp_conj)
    hfilt = conjonction_elim_droite(hyp_conj)
    P = _P_majorant(G, E_set, m)

    # P(∅) vacuous (¬(∅=∅) faux)
    concl0 = existe(m, _maj(G, E.VIDE, var(m), vE))
    n_refl = N.assume(et(inclus(E.VIDE, vE), non(egal(E.VIDE, E.VIDE))))
    nr = conjonction_elim_droite(n_refl)
    falso0 = N.modus_ponens(N.reflexivite(E.VIDE), N.modus_ponens(nr, N.s2(non(egal(E.VIDE, E.VIDE)), concl0)))
    P0 = N.loi_deduction(et(inclus(E.VIDE, vE), non(egal(E.VIDE, E.VIDE))), falso0)
    assert P0.conclusion == P(E.VIDE), "P(∅) filtrant mal formé"

    pas = _preuve_pas_filtrant(G, E_set, hord, hfilt, P, m=m)
    rf = recurrence_finie(P)
    fini_imp_PX = N.modus_ponens(conjonction_intro(P0, pas), rf)   # [hord, hfilt]

    vX = var(X)
    inst = instancie(fini_imp_PX, vX)
    hfin = N.assume(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))))
    fini_ens_X = conjonction_elim_gauche(conjonction_elim_gauche(hfin))
    X_sub = conjonction_elim_droite(conjonction_elim_gauche(hfin))
    X_nv = conjonction_elim_droite(hfin)
    PX = N.modus_ponens(fini_ens_X, inst)
    ex_m = N.modus_ponens(conjonction_intro(X_sub, X_nv), PX)
    corps = N.loi_deduction(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))), ex_m)
    concl = N.generalisation(X, corps)
    res = N.loi_deduction(et(est_ordre(G, E_set), _filtrant_droite_G(G, E_set)), concl)
    assert res.conclusion == prop3_filtrant_enonce(G, E_set, X, m), "conclusion ≠ énoncé filtrant"
    return res


__all__ = [
    "_membre_union_singleton",
    "_P_plus_grand",
    "prop3_total_enonce", "prop3_total",
    "cor1_total_enonce", "cor1_total",
    "prop3_filtrant_enonce", "prop3_filtrant",
]
