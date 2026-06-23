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
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
    equivalence_transitivite, contraposition,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, totalement_ordonne, plus_grand_element, majorant,
    element_maximal, _couple_dans,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_recurrence_finie import (
    recurrence_finie, recurrence_finie_enonce,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import _instance_reunion
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre


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
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_recurrence_finie import _pas_ensemble
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
    from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as _E
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
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_recurrence_finie import _pas_ensemble
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


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 2 §III.4 (E III.34) — TOUT ENSEMBLE ORDONNÉ FINI NON VIDE ADMET
#  UN ÉLÉMENT MAXIMAL.   (Variante PARTIELLEMENT ordonnée — preuve genuine.)
# ════════════════════════════════════════════════════════════════════════════
_ZEM = "zemf"   # liant fixe d'element_maximal ici (évite la capture du point x)


def _emax(G, A, m):
    """element_maximal(G,A,m) avec liant interne FIXÉ à _ZEM."""
    return element_maximal(G, _t(A), _t(m), x=_ZEM)


def _P_maximal(G, E_set, m="m_emf", a="a_emf"):
    """P(X) := X⊂E ⇒ (∀a)( a∈X ⇒ (∃m)( m∈X et (a,m)∈G et _emax(G,X,m) ) ).

    « Tout élément a d'une partie X (de E) est dominé par un élément maximal de X. »
    NOTE : pas de garde « ¬(X=∅) » — l'antécédent est seulement X⊂E (la quantif
    interne sur a∈X est triviale si X=∅, et le but du Cor 2 ré-injecte la non-vacuité
    via le témoin z∈E)."""
    vE = _t(E_set)
    def P(X):
        vX = _t(X)
        va, vm = var(a), var(m)
        concl = existe(m, et(et(appartient(vm, vX), _couple_dans(va, vm, G)),
                             _emax(G, vX, vm)))
        return impl(inclus(vX, vE),
                    pourtout(a, impl(appartient(va, vX), concl)))
    return P


def _emax_de_pourtout(G, A, m_in, corps_gen):
    """Assemble _emax(G,A,m) = et(m∈A, (∀_ZEM)(...)) depuis m_in (m∈A) et le corps généralisé."""
    return conjonction_intro(m_in, corps_gen)


def _preuve_pas_maximal(G, E_set, hord, P, X="Xrec", x="xrec",
                        m="m_emf", a="a_emf"):
    """{ hord:est_ordre(G,E) } ⊢ _pas_ensemble(P)  pour P = _P_maximal(G,E)."""
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_recurrence_finie import _pas_ensemble
    from bourbaki.logique.tactiques.tactiques_abrege2 import tiers_exclu, dne, dni
    vE = _t(E_set)
    vX, vx = var(X), var(x)
    va, vm = var(a), var(m)
    vt = var(_ZEM)
    Xux = E.reunion(vX, E.singleton(vx))

    # décompose est_ordre : refl, antisym, trans
    refl = conjonction_elim_gauche(conjonction_elim_gauche(hord))
    antisym = conjonction_elim_droite(conjonction_elim_gauche(hord))
    trans = conjonction_elim_droite(hord)

    hpas = N.assume(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)))
    hPX = conjonction_elim_droite(hpas)                   # P(X)

    # ── guard : X∪{x} ⊂ E ────────────────────────────────────────────────────
    hgarde = N.assume(inclus(Xux, vE))
    Xux_sub_E = hgarde
    # x∈X∪{x} ; x∈E
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
    # P(X) appliqué : (∀a)(a∈X ⇒ ∃m(m∈X et (a,m)∈G et emax(G,X,m)))
    PX_body = N.modus_ponens(X_sub_E, hPX)

    # but interne (sur le point a fixé dans X∪{x}) :
    #   GOAL(a) := (∃m)( m∈X∪{x} et (a,m)∈G et emax(G,X∪{x},m) )
    def GOAL(a_term):
        return existe(m, et(et(appartient(vm, Xux), _couple_dans(a_term, vm, G)),
                            _emax(G, Xux, vm)))

    # ─────────────────────────────────────────────────────────────────────────
    #  SOUS-LEMME 1 : si m∈X et emax(G,X,m) et ¬((m,x)∈G) alors emax(G,X∪{x},m).
    #  donné en arguments : pm_in_X (m∈X), pmax_X (emax(G,X,m)), pn_mx (¬(m,x)∈G)
    # ─────────────────────────────────────────────────────────────────────────
    def sublemme1(M, pM_in_X, pmax_X, pn_Mx):
        """M un TERME. ⊢ emax(G,X∪{x},M)  (sous les preuves données)."""
        vt = var(_ZEM)                                    # liant LOCAL (évite capture extérieure)
        emax_body_X = conjonction_elim_droite(pmax_X)     # (∀t)((t∈X et (M,t)∈G)⇒t=M)
        # M∈X∪{x}
        M_in_Xux = N.modus_ponens(
            N.modus_ponens(pM_in_X, N.s2(appartient(M, vX), egal(M, vx))),
            equivalence_arriere(_membre_union_singleton(M, vX, vx)))
        # corps : (t∈X∪{x} et (M,t)∈G) ⇒ t=M
        hbody = N.assume(et(appartient(vt, Xux), _couple_dans(M, vt, G)))
        t_in_Xux = conjonction_elim_gauche(hbody)
        Mt = conjonction_elim_droite(hbody)               # (M,t)∈G
        disj_t = N.modus_ponens(t_in_Xux, equivalence_avant(_membre_union_singleton(vt, vX, vx)))
        #  t∈X : emax_X(t) → t=M
        htX = N.assume(appartient(vt, vX))
        emax_t = instancie(emax_body_X, vt)               # (t∈X et (M,t)∈G)⇒t=M
        t_eq_M_X = N.modus_ponens(conjonction_intro(htX, Mt), emax_t)
        casX = N.loi_deduction(appartient(vt, vX), t_eq_M_X)
        #  t=x : (M,t)∈G=(M,x)∈G contradiction ¬((M,x)∈G) → ex falso egal(t,M)
        htx = N.assume(egal(vt, vx))
        #  transporte (M,t)∈G en (M,x)∈G via Leibniz t↦x
        Mx = N.modus_ponens(Mt, equivalence_avant(
            N.modus_ponens(htx, N.s6(vt, vx, "wsl1", _couple_dans(M, var("wsl1"), G)))))
        falso = N.modus_ponens(Mx, N.modus_ponens(pn_Mx,
                    N.s2(non(_couple_dans(M, vx, G)), egal(vt, M))))
        casx = N.loi_deduction(egal(vt, vx), falso)
        t_eq_M = cas(disj_t, casX, casx)
        corps_gen = N.generalisation(_ZEM,
            N.loi_deduction(et(appartient(vt, Xux), _couple_dans(M, vt, G)), t_eq_M))
        return conjonction_intro(M_in_Xux, corps_gen)     # emax(G,X∪{x},M)

    # ─────────────────────────────────────────────────────────────────────────
    #  SOUS-LEMME 2 : si m∈X, emax(G,X,m) et (m,x)∈G alors emax(G,X∪{x},x).
    # ─────────────────────────────────────────────────────────────────────────
    def sublemme2(M, pM_in_X, pmax_X, p_Mx):
        """M un TERME. ⊢ emax(G,X∪{x},x)  (sous les preuves données)."""
        vt = var(_ZEM)                                    # liant LOCAL
        emax_body_X = conjonction_elim_droite(pmax_X)     # (∀t)((t∈X et (M,t)∈G)⇒t=M)
        # x∈X∪{x} déjà : x_in_Xux
        hbody = N.assume(et(appartient(vt, Xux), _couple_dans(vx, vt, G)))
        t_in_Xux = conjonction_elim_gauche(hbody)
        xt = conjonction_elim_droite(hbody)               # (x,t)∈G
        disj_t = N.modus_ponens(t_in_Xux, equivalence_avant(_membre_union_singleton(vt, vX, vx)))
        #  t=x : egal(t,x) directement
        htx = N.assume(egal(vt, vx))
        casx = N.loi_deduction(egal(vt, vx), htx)         # t=x
        #  t∈X : (x,t)∈G et (M,x)∈G trans→(M,t)∈G ; emax_X(t)→t=M ;
        #        Leibniz t=M sur (x,t)→(x,M)∈G ; (x,M)∈G et (M,x)∈G antisym→x=M ;
        #        donc t=M=x → egal(t,x)
        htX = N.assume(appartient(vt, vX))
        trans_Mxt = instancie(instancie(instancie(trans, M), vx), vt)   # ((M,x)∈G et (x,t)∈G)⇒(M,t)∈G
        Mt = N.modus_ponens(conjonction_intro(p_Mx, xt), trans_Mxt)     # (M,t)∈G
        emax_t = instancie(emax_body_X, vt)               # (t∈X et (M,t)∈G)⇒t=M
        t_eq_M = N.modus_ponens(conjonction_intro(htX, Mt), emax_t)     # t=M
        # (x,M)∈G via Leibniz t↦M sur (x,t)∈G
        xM = N.modus_ponens(xt, equivalence_avant(
            N.modus_ponens(t_eq_M, N.s6(vt, M, "wsl2", _couple_dans(vx, var("wsl2"), G)))))
        # antisym : ((x,M)∈G et (M,x)∈G)⇒x=M
        antisym_xM = instancie(instancie(antisym, vx), M)
        x_eq_M = N.modus_ponens(conjonction_intro(xM, p_Mx), antisym_xM)  # x=M
        M_eq_x = N.modus_ponens(x_eq_M, symetrie(vx, M))                  # M=x
        # t=M et M=x → t=x
        t_eq_x = composer_egalites(t_eq_M, M_eq_x)         # t=x
        casX = N.loi_deduction(appartient(vt, vX), t_eq_x)
        t_eq_x_final = cas(disj_t, casX, casx)
        corps_gen = N.generalisation(_ZEM,
            N.loi_deduction(et(appartient(vt, Xux), _couple_dans(vx, vt, G)), t_eq_x_final))
        return conjonction_intro(x_in_Xux, corps_gen)     # emax(G,X∪{x},x)

    # ─────────────────────────────────────────────────────────────────────────
    #  Fixe a∈X∪{x}, prouve GOAL(a).
    # ─────────────────────────────────────────────────────────────────────────
    ha_in = N.assume(appartient(va, Xux))
    disj_a = N.modus_ponens(ha_in, equivalence_avant(_membre_union_singleton(va, vX, vx)))  # a∈X ou a=x

    # ══════ CAS a∈X ══════════════════════════════════════════════════════════
    haX = N.assume(appartient(va, vX))
    # P(X) à a : (∃m)(m∈X et (a,m)∈G et emax(G,X,m))
    ex_mX = N.modus_ponens(haX, instancie(PX_body, va))
    hwit = N.assume(et(et(appartient(vm, vX), _couple_dans(va, vm, G)), _emax(G, vX, vm)))
    m_in_X = conjonction_elim_gauche(conjonction_elim_gauche(hwit))
    am_G = conjonction_elim_droite(conjonction_elim_gauche(hwit))    # (a,m)∈G
    emax_X_m = conjonction_elim_droite(hwit)                         # emax(G,X,m)
    te_mx = tiers_exclu(_couple_dans(vm, vx, G))                     # (m,x)∈G ou ¬((m,x)∈G)
    #   (m,x)∈G : témoin x
    hmx = N.assume(_couple_dans(vm, vx, G))
    ax_G = N.modus_ponens(conjonction_intro(am_G, hmx),
                          instancie(instancie(instancie(trans, va), vm), vx))   # (a,x)∈G
    emax_Xux_x = sublemme2(vm, m_in_X, emax_X_m, hmx)
    wit_x = conjonction_intro(conjonction_intro(x_in_Xux, ax_G), emax_Xux_x)
    ex_x = N.modus_ponens(wit_x, N.s5(et(et(appartient(vm, Xux), _couple_dans(va, vm, G)), _emax(G, Xux, vm)), vx, m))
    casA_mx = N.loi_deduction(_couple_dans(vm, vx, G), ex_x)
    #   ¬((m,x)∈G) : témoin m
    hnmx = N.assume(non(_couple_dans(vm, vx, G)))
    emax_Xux_m = sublemme1(vm, m_in_X, emax_X_m, hnmx)
    m_in_Xux = N.modus_ponens(
        N.modus_ponens(m_in_X, N.s2(appartient(vm, vX), egal(vm, vx))),
        equivalence_arriere(_membre_union_singleton(vm, vX, vx)))
    wit_m = conjonction_intro(conjonction_intro(m_in_Xux, am_G), emax_Xux_m)
    ex_m = N.modus_ponens(wit_m, N.s5(et(et(appartient(vm, Xux), _couple_dans(va, vm, G)), _emax(G, Xux, vm)), vm, m))
    casA_nmx = N.loi_deduction(non(_couple_dans(vm, vx, G)), ex_m)
    goal_wit = cas(te_mx, casA_mx, casA_nmx)              # GOAL(a)  sous le témoin m
    imp_wit = N.loi_deduction(et(et(appartient(vm, vX), _couple_dans(va, vm, G)), _emax(G, vX, vm)), goal_wit)
    goal_aX = N.modus_ponens(ex_mX, existe_elimination(imp_wit, m))   # GOAL(a) sous a∈X
    casA = N.loi_deduction(appartient(va, vX), goal_aX)

    # ══════ CAS a=x ═══════════════════════════════════════════════════════════
    hax = N.assume(egal(va, vx))
    # On prouve GOAL(x) puis on transporte a↦x (Leibniz) — plus simple : prouver GOAL(a)
    # en transportant. On travaille directement avec a et le fait a=x.
    # tiers_exclu(_emax(G,X∪{x},x))
    te_emax = tiers_exclu(_emax(G, Xux, vx))
    #   --- emax(G,X∪{x},x) vrai : témoin x ---
    h_emax_x = N.assume(_emax(G, Xux, vx))
    xx_G = N.modus_ponens(x_in_E, instancie(refl, vx))   # (x,x)∈G
    # (a,x)∈G via a=x : Leibniz a↦x sur (x,x)∈G donne... on veut (a,x)∈G : Leibniz x↦a sur (x,x)→(a,x)
    x_eq_a = N.modus_ponens(hax, symetrie(va, vx))       # x=a
    ax_G_T = N.modus_ponens(xx_G, equivalence_avant(
        N.modus_ponens(x_eq_a, N.s6(vx, va, "wax1", _couple_dans(var("wax1"), vx, G)))))  # (a,x)∈G
    wit_T = conjonction_intro(conjonction_intro(x_in_Xux, ax_G_T), h_emax_x)
    ex_T = N.modus_ponens(wit_T, N.s5(et(et(appartient(vm, Xux), _couple_dans(va, vm, G)), _emax(G, Xux, vm)), vx, m))
    casX_true = N.loi_deduction(_emax(G, Xux, vx), ex_T)

    #   --- ¬emax(G,X∪{x},x) : x∈X∪{x} prouvable, donc ¬(∀t)Φ, donc (∃t)¬Φ ---
    h_n_emax = N.assume(non(_emax(G, Xux, vx)))
    #   _emax(G,Xux,x) = et(x∈Xux, pourtout(_ZEM, Φ)) où Φ(t)=impl(et(t∈Xux,(x,t)∈G),egal(t,x))
    Pc = appartient(vx, Xux)
    Qc = pourtout(_ZEM, impl(et(appartient(vt, Xux), _couple_dans(vx, vt, G)), egal(vt, vx)))
    # de ¬(P et Q) et ⊢P déduire ¬Q : via contraposition de (Q⇒(P et Q))
    imp_PetQ = N.loi_deduction(Qc, conjonction_intro(x_in_Xux, N.assume(Qc)))   # Q⇒(P et Q)
    nQ = N.modus_ponens(h_n_emax, contraposition(imp_PetQ))   # ¬Q = ¬(∀t)Φ
    #   ¬(∀t)Φ : pourtout(t,Φ)=non(existe(t,non Φ)), donc ¬(∀t)Φ = ¬¬(∃t)¬Φ → (∃t)¬Φ via dne
    Phi = impl(et(appartient(vt, Xux), _couple_dans(vx, vt, G)), egal(vt, vx))
    ex_nPhi_zem = N.modus_ponens(nQ, dne(existe(_ZEM, non(Phi))))   # (∃_ZEM)¬Φ
    #   α-renomme le témoin _ZEM → _TW (fresh) pour libérer _ZEM (réutilisé dans sublemme1)
    _TW = "twemf"
    vt = var(_TW)
    ex_nPhi = N.modus_ponens(ex_nPhi_zem, equivalence_avant(alpha_existe(_ZEM, _TW, non(Phi))))  # (∃_TW)¬Φ[_TW]
    #   élimine témoin t : ¬Φ(t)=¬(impl(A,B)), A=et(t∈Xux,(x,t)∈G), B=egal(t,x)
    Aimp = et(appartient(vt, Xux), _couple_dans(vx, vt, G))
    Bimp = egal(vt, vx)
    h_nphi = N.assume(non(impl(Aimp, Bimp)))
    #   A : ¬A ⇒ (A⇒B) [ex falso s2] ; contrapose ¬(A⇒B)⇒¬¬A ⇒ A
    exfalso_A = N.s2(Bimp, non(Aimp))                    # B... no: need ¬A⇒(A⇒B). (A⇒B)=ou(¬A,B); ¬A⇒(¬A ou B)
    nA_imp = N.s2(non(Aimp), Bimp)                       # ¬A ⇒ (¬A ou B) = ¬A⇒(A⇒B)
    getA = N.modus_ponens(N.modus_ponens(h_nphi, contraposition(nA_imp)), dne(Aimp))  # A
    #   ¬B : B⇒(A⇒B) [B⇒(¬A ou B)] contrapose
    nB_imp = syllogisme(N.s2(Bimp, non(Aimp)), N.s3(Bimp, non(Aimp)))  # B⇒ou(B,¬A)⇒ou(¬A,B) = B⇒(A⇒B)
    nB = N.modus_ponens(h_nphi, contraposition(nB_imp))  # ¬B = ¬egal(t,x)
    t_in_Xux = conjonction_elim_gauche(getA)
    xt_G = conjonction_elim_droite(getA)                 # (x,t)∈G
    #   t∈X ou t=x ; t=x ⇒ egal(t,x) contradicts ¬B → ex falso ; so t∈X
    disj_t2 = N.modus_ponens(t_in_Xux, equivalence_avant(_membre_union_singleton(vt, vX, vx)))
    #   pour produire GOAL(a) on a besoin de t∈X (avec (x,t)∈G). Construire t∈X par cas :
    #     t∈X → t∈X ; t=x → ex falso (¬egal(t,x)) → t∈X
    htX2 = N.assume(appartient(vt, vX))
    castX = N.loi_deduction(appartient(vt, vX), htX2)
    htx2 = N.assume(egal(vt, vx))
    falso_tX = N.modus_ponens(htx2, N.modus_ponens(nB, N.s2(non(egal(vt, vx)), appartient(vt, vX))))
    castx = N.loi_deduction(egal(vt, vx), falso_tX)
    t_in_X = cas(disj_t2, castX, castx)                  # t∈X
    #   P(X) à t : (∃m)(m∈X et (t,m)∈G et emax(G,X,m))
    ex_mt = N.modus_ponens(t_in_X, instancie(PX_body, vt))
    hwit2 = N.assume(et(et(appartient(vm, vX), _couple_dans(vt, vm, G)), _emax(G, vX, vm)))
    m_in_X2 = conjonction_elim_gauche(conjonction_elim_gauche(hwit2))
    tm_G = conjonction_elim_droite(conjonction_elim_gauche(hwit2))   # (t,m)∈G
    emax_X_m2 = conjonction_elim_droite(hwit2)
    # (x,m)∈G : (x,t)∈G + (t,m)∈G trans
    xm_G = N.modus_ponens(conjonction_intro(xt_G, tm_G),
                          instancie(instancie(instancie(trans, vx), vt), vm))   # (x,m)∈G
    te_mx2 = tiers_exclu(_couple_dans(vm, vx, G))
    #   (m,x)∈G : (x,m)∈G + (m,x)∈G antisym → x=m → m∈X but x∉X → ex falso
    hmx2 = N.assume(_couple_dans(vm, vx, G))
    antisym_xm = instancie(instancie(antisym, vx), vm)   # ((x,m)∈G et (m,x)∈G)⇒x=m
    x_eq_m = N.modus_ponens(conjonction_intro(xm_G, hmx2), antisym_xm)   # x=m
    # m∈X et x=m → x∈X (Leibniz m↦x : (m=x)⇒(m∈X⇔x∈X))
    m_eq_x = N.modus_ponens(x_eq_m, symetrie(vx, vm))    # m=x
    x_in_X = N.modus_ponens(m_in_X2, equivalence_avant(
        N.modus_ponens(m_eq_x, N.s6(vm, vx, "wmx", appartient(var("wmx"), vX)))))   # x∈X
    # contradiction avec ¬(x∈X) (hyp du pas)
    hnxX = conjonction_elim_droite(conjonction_elim_gauche(hpas))   # ¬(x∈X)
    GOALa = GOAL(va)
    falso_goal = N.modus_ponens(x_in_X, N.modus_ponens(hnxX, N.s2(non(appartient(vx, vX)), GOALa)))
    casmx2 = N.loi_deduction(_couple_dans(vm, vx, G), falso_goal)   # GOAL(a)
    #   ¬((m,x)∈G) : témoin m via sublemme1 ; (a,m)∈G : a=x donc (x,m)∈G transporté
    hnmx2 = N.assume(non(_couple_dans(vm, vx, G)))
    emax_Xux_m2 = sublemme1(vm, m_in_X2, emax_X_m2, hnmx2)
    m_in_Xux2 = N.modus_ponens(
        N.modus_ponens(m_in_X2, N.s2(appartient(vm, vX), egal(vm, vx))),
        equivalence_arriere(_membre_union_singleton(vm, vX, vx)))
    # (a,m)∈G : (x,m)∈G + a=x Leibniz x↦a
    am_G2 = N.modus_ponens(xm_G, equivalence_avant(
        N.modus_ponens(x_eq_a, N.s6(vx, va, "wax2", _couple_dans(var("wax2"), vm, G)))))   # (a,m)∈G
    wit_m2 = conjonction_intro(conjonction_intro(m_in_Xux2, am_G2), emax_Xux_m2)
    ex_m2 = N.modus_ponens(wit_m2, N.s5(et(et(appartient(vm, Xux), _couple_dans(va, vm, G)), _emax(G, Xux, vm)), vm, m))
    casnmx2 = N.loi_deduction(non(_couple_dans(vm, vx, G)), ex_m2)   # GOAL(a)
    goal_from_m = cas(te_mx2, casmx2, casnmx2)            # GOAL(a) sous témoin m
    imp_wit2 = N.loi_deduction(et(et(appartient(vm, vX), _couple_dans(vt, vm, G)), _emax(G, vX, vm)), goal_from_m)
    goal_from_t = N.modus_ponens(ex_mt, existe_elimination(imp_wit2, m))   # GOAL(a) sous témoin t
    imp_nphi = N.loi_deduction(non(impl(Aimp, Bimp)), goal_from_t)
    goal_neg = N.modus_ponens(ex_nPhi, existe_elimination(imp_nphi, _TW))   # GOAL(a) sous ¬emax(Xux,x)
    casX_false = N.loi_deduction(non(_emax(G, Xux, vx)), goal_neg)

    goal_ax = cas(te_emax, casX_true, casX_false)        # GOAL(a)  sous a=x
    casB = N.loi_deduction(egal(va, vx), goal_ax)

    # ── combine a∈X / a=x ────────────────────────────────────────────────────
    goal_a = cas(disj_a, casA, casB)                     # GOAL(a)  sous a∈X∪{x}
    body_a = N.generalisation(a, N.loi_deduction(appartient(va, Xux), goal_a))
    PXux = N.loi_deduction(inclus(Xux, vE), body_a)      # P(X∪{x})
    corps = N.loi_deduction(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)), PXux)
    res = N.generalisation(X, N.generalisation(x, corps))
    assert res.conclusion == _pas_ensemble(P, X, x), "pas maximal mal formé"
    return res


def cor2_enonce(G, E_set, m="m_emf"):
    """⊢-cible : ( est_ordre(G,E) et est_fini_ensemble(E) et ¬(E=∅) )
        ⇒ (∃m)( element_maximal(G,E,m) ).

    « Tout ensemble ordonné FINI non vide admet un élément maximal. »
    (Corollaire 2 §III.4, E III.34.)"""
    vE = _t(E_set)
    return impl(et(et(est_ordre(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))),
                existe(m, _emax(G, vE, var(m))))


def cor2_maximal(G="Gemf", E_set="Eemf", X="Xemf", m="m_emf"):
    """🎯 ⊢ cor2_enonce(G,E).   (Corollaire 2 §III.4 — élément maximal, ordre PARTIEL.)

    Via `recurrence_finie` sur P(X):=X⊂E⇒(∀a)(a∈X⇒(∃m)(m∈X et (a,m)∈G et emax(G,X,m))) :
    base ∅ (a∈∅ ex falso), pas par extension d'un maximal de X au point ajouté (tiers
    exclu sur (m,x)∈G + l'antisymétrie/transitivité de l'ordre).  À X:=E avec un témoin
    z∈E (non-vacuité) on obtient l'élément maximal."""
    vE = _t(E_set)
    hyp = N.assume(et(et(est_ordre(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))))
    hord = conjonction_elim_gauche(conjonction_elim_gauche(hyp))
    hfin = conjonction_elim_droite(conjonction_elim_gauche(hyp))
    hnv = conjonction_elim_droite(hyp)
    P = _P_maximal(G, E_set, m)
    va, vm = var("a_emf"), var(m)

    # ── P(∅) : ∅⊂E ⇒ (∀a)(a∈∅ ⇒ GOAL) ; a∈∅ ex falso ────────────────────────
    h0sub = N.assume(inclus(E.VIDE, vE))
    ha0 = N.assume(appartient(va, E.VIDE))
    nv0 = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), va)   # ¬(a∈∅)
    concl0 = existe(m, et(et(appartient(vm, E.VIDE), _couple_dans(va, vm, G)), _emax(G, E.VIDE, vm)))
    falso0 = N.modus_ponens(ha0, N.modus_ponens(nv0, N.s2(non(appartient(va, E.VIDE)), concl0)))
    body0 = N.generalisation("a_emf", N.loi_deduction(appartient(va, E.VIDE), falso0))
    P0 = N.loi_deduction(inclus(E.VIDE, vE), body0)
    assert P0.conclusion == P(E.VIDE), "P(∅) maximal mal formé"

    pas = _preuve_pas_maximal(G, E_set, hord, P, m=m)    # _pas_ensemble(P)  [hord]
    rf = recurrence_finie(P)
    fini_imp_PX = N.modus_ponens(conjonction_intro(P0, pas), rf)   # (∀X)(Fini-ens X ⇒ P(X))  [hord]

    # ── instancie à E : P(E) ; E⊂E ; (∀a)(a∈E ⇒ GOAL) ───────────────────────
    inst = instancie(fini_imp_PX, vE)                    # Fini-ens E ⇒ P(E)
    PE = N.modus_ponens(hfin, inst)                      # P(E) = (E⊂E ⇒ (∀a)(a∈E⇒GOAL))
    E_sub_E = _inclus_refl_via(vE)
    forall_a = N.modus_ponens(E_sub_E, PE)               # (∀a)(a∈E ⇒ ∃m(m∈E et (a,m)∈G et emax(G,E,m)))

    # ── non-vide : (∃z)(z∈E) ────────────────────────────────────────────────
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    ex_z = N.modus_ponens(hnv, equivalence_avant(non_vide_ssi_element(vE)))   # (∃z)(z∈E)
    vz = var("z")
    hz = N.assume(appartient(vz, vE))
    # instancie (∀a) en z
    inst_z = instancie(forall_a, vz)                     # z∈E ⇒ ∃m(m∈E et (z,m)∈G et emax(G,E,m))
    ex_m = N.modus_ponens(hz, inst_z)
    # élimine témoin m ; extrait emax(G,E,m) ; ∃-intro existe(m, _emax(G,E,m))
    hwit = N.assume(et(et(appartient(vm, vE), _couple_dans(vz, vm, G)), _emax(G, vE, vm)))
    emax_m = conjonction_elim_droite(hwit)               # _emax(G,E,m)
    ex_emax = N.modus_ponens(emax_m, N.s5(_emax(G, vE, vm), vm, m))   # (∃m)_emax(G,E,m)
    imp_wit = N.loi_deduction(et(et(appartient(vm, vE), _couple_dans(vz, vm, G)), _emax(G, vE, vm)), ex_emax)
    ex_from_z = N.modus_ponens(ex_m, existe_elimination(imp_wit, m))   # (∃m)_emax(G,E,m) sous z∈E
    imp_z = N.loi_deduction(appartient(vz, vE), ex_from_z)
    ex_final = N.modus_ponens(ex_z, existe_elimination(imp_z, "z"))    # (∃m)_emax(G,E,m)

    res = N.loi_deduction(et(et(est_ordre(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))), ex_final)
    assert res.conclusion == cor2_enonce(G, E_set, m), "conclusion ≠ énoncé cor2"
    return res


__all__ = [
    "_membre_union_singleton",
    "_P_plus_grand",
    "prop3_total_enonce", "prop3_total",
    "cor1_total_enonce", "cor1_total",
    "prop3_filtrant_enonce", "prop3_filtrant",
    "_emax", "_P_maximal", "_preuve_pas_maximal",
    "cor2_enonce", "cor2_maximal",
]
