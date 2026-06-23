"""§III.5 — PROPOSITION 6 (E III.38) et son socle « bien ordonné ».

🎯 PROPOSITION 6 (E III.38) — VERBATIM :
   « Pour tout ensemble fini E, totalement ordonné, ayant n éléments (n ≥ 1), il
   existe un isomorphisme et un seul de E sur l'intervalle [1,n]. »
   Démonstration Bourbaki : « Comme E et [1,n] sont bien ordonnés (III, p. 34,
   cor. 1), et ont même nombre d'éléments (prop. 5), la proposition résulte de
   III, p. 21, th. 3 et p. 31, cor. 2. »

La preuve de Bourbaki ROUTE par le Corollaire 1 §III.4 (« tout ensemble fini
totalement ordonné est bien ordonné ») PUIS le Théorème 3 §III.2 (isomorphisme
unique de bons ordres équipotents).  Ce module CLÔT le socle TRACTABLE :

  PART 1 — « tout ensemble fini totalement ordonné est bien ordonné », c.-à-d.
            TOUTE PARTIE FINIE NON VIDE d'un ensemble totalement ordonné admet
            un PLUS PETIT ÉLÉMENT.  (C'est exactement la moitié non triviale de
            « bien ordonné » ; l'autre — plus grand élément — est déjà close
            dans `ensembles_ordre_fini_iii4.cor1_total`.)

C'est le DUAL EXACT de `prop3_total`/`cor1_total` §III.4 (plus grand élément) :
on remplace partout `plus_grand_element(G,A,m)` (m∈A et ∀z(z∈A⇒(z,m)∈G)) par
`plus_petit_element(G,A,m)` (m∈A et ∀z(z∈A⇒(m,z)∈G)), et la comparaison du
témoin avec le point ajouté est inversée (on garde le PLUS PETIT des deux).

Route : `recurrence_finie(P)` avec
  P(X) := ( X⊂E et ¬(X=∅) ) ⇒ (∃m)( plus_petit_element(G,X,m) ).

theorie=22, aucun postulat.  Noyau INTACT.
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
    equivalence_transitivite, tiers_exclu,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie

from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    totalement_ordonne, plus_petit_element, _couple_dans,
)
from bourbaki.entiers.ensembles_recurrence_finie import recurrence_finie
from bourbaki.entiers.ensembles_entiers import est_fini_ensemble

# Réutilise les briques déjà déposées (membership X∪{x}, ∨-droite, décompo total).
from bourbaki.ordre.iii_4_ensembles_finis.ensembles_ordre_fini_iii4 import (
    _membre_union_singleton, _ou_droite, _decompose_total, _inclus_refl_via,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_ZPP = "zppT"   # liant interne FIXÉ de plus_petit_element ici (évite la capture du point x)


def _ppe(G, A, m):
    """plus_petit_element avec liant interne FIXÉ à _ZPP (évite la capture du point x)."""
    return plus_petit_element(G, _t(A), _t(m), x=_ZPP)


# ════════════════════════════════════════════════════════════════════════════
#  PRÉDICAT P pour le PLUS PETIT élément
# ════════════════════════════════════════════════════════════════════════════
def _P_plus_petit(G, E_set, m="m_ppf"):
    """P(X) := ( X⊂E et ¬(X=∅) ) ⇒ (∃m)( plus_petit_element(G,X,m) )."""
    vE = _t(E_set)
    def P(X):
        vX = _t(X)
        garde = et(inclus(vX, vE), non(egal(vX, E.VIDE)))
        concl = existe(m, _ppe(G, vX, var(m)))
        return impl(garde, concl)
    return P


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 3 (variante totalement ordonnée — PLUS PETIT élément)
# ════════════════════════════════════════════════════════════════════════════
def prop3_total_min_enonce(G, E_set, X="Xppt", m="m_ppf"):
    """⊢-cible : ( totalement_ordonne(G,E) ) ⇒
        (∀X)( ( est_fini_ensemble(X) et X⊂E et ¬(X=∅) )
              ⇒ (∃m)( plus_petit_element(G,X,m) ) ).

    « Toute partie finie non vide d'un ensemble totalement ordonné admet un plus
    petit élément. »  (Prop. 3 §III.4, variante totale, DUAL ; socle de Cor 1.)"""
    vE = _t(E_set)
    vX = var(X)
    corps = impl(et(et(est_fini_ensemble(vX), inclus(vX, vE)), non(egal(vX, E.VIDE))),
                 existe(m, _ppe(G, vX, var(m))))
    return impl(totalement_ordonne(G, E_set), pourtout(X, corps))


def _preuve_pas_total_min(G, E_set, htot, P, X="Xrec", x="xrec", z="zppT", m="m_ppf"):
    """{ htot } ⊢ _pas_ensemble(P)  pour P = _P_plus_petit(G,E).

    P(X) := (X⊂E et ¬(X=∅)) ⇒ (∃m)(plus_petit_element(G,X,m)).
    Le pas : (Fini-ens X et ¬(x∈X) et P(X)) ⇒ P(X∪{x})."""
    from bourbaki.entiers.ensembles_recurrence_finie import _pas_ensemble
    vE = _t(E_set)
    vX, vx, vz = var(X), var(x), var(z)
    Xux = E.reunion(vX, E.singleton(vx))
    refl, antisym, trans, comp = _decompose_total(htot, G, E_set)

    hpas = N.assume(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)))
    hPX = conjonction_elim_droite(hpas)                   # P(X)

    garde = et(inclus(Xux, vE), non(egal(Xux, E.VIDE)))
    hgarde = N.assume(garde)
    Xux_sub_E = conjonction_elim_gauche(hgarde)

    # x ∈ X∪{x}  ; x∈E
    mem_x = _membre_union_singleton(vx, vX, vx)
    x_in_Xux = N.modus_ponens(
        _ou_droite(appartient(vx, vX), N.reflexivite(vx)),
        equivalence_arriere(mem_x))
    x_in_E = N.modus_ponens(x_in_Xux, instancie(Xux_sub_E, vx))

    # X⊂E  (liant "z" pour coïncider avec l'encodage de inclus)
    vz2 = var("z")
    hzX = N.assume(appartient(vz2, vX))
    z_in_Xux = N.modus_ponens(
        N.modus_ponens(hzX, N.s2(appartient(vz2, vX), egal(vz2, vx))),
        equivalence_arriere(_membre_union_singleton(vz2, vX, vx)))
    z_in_E = N.modus_ponens(z_in_Xux, instancie(Xux_sub_E, vz2))
    X_sub_E = N.generalisation("z", N.loi_deduction(appartient(vz2, vX), z_in_E))

    te = tiers_exclu(egal(vX, E.VIDE))                    # (X=∅) ou ¬(X=∅)

    def refl_en(t_in_E, t):
        return N.modus_ponens(t_in_E, instancie(refl, t))

    # ============ CAS A : X = ∅  — x est le plus PETIT de X∪{x} ===============
    hXvide = N.assume(egal(vX, E.VIDE))
    hz_in = N.assume(appartient(vz, Xux))
    disj_z = N.modus_ponens(hz_in, equivalence_avant(_membre_union_singleton(vz, vX, vx)))  # z∈X ou z=x
    #   z∈X : contradiction X=∅  ⇒ ex falso (x,z)∈G
    hzX2 = N.assume(appartient(vz, vX))
    leibV = N.s6(vX, E.VIDE, "wv", appartient(vz, var("wv")))
    z_in_vide = N.modus_ponens(hzX2, equivalence_avant(N.modus_ponens(hXvide, leibV)))
    nz_vide = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)
    falso = N.modus_ponens(z_in_vide, N.modus_ponens(nz_vide, N.s2(non(appartient(vz, E.VIDE)), _couple_dans(vx, vz, G))))
    casA_zX = N.loi_deduction(appartient(vz, vX), falso)  # z∈X ⇒ (x,z)∈G
    #   z=x : (x,z)∈G via réfl (x,x)∈G transporté x↦z (2e composante)
    hzx = N.assume(egal(vz, vx))
    xx_G = refl_en(x_in_E, vx)                            # (x,x)∈G
    x_eq_z = N.modus_ponens(hzx, symetrie(vz, vx))        # x=z
    zx_G = N.modus_ponens(xx_G, equivalence_avant(N.modus_ponens(x_eq_z, N.s6(vx, vz, "wzx", _couple_dans(vx, var("wzx"), G)))))  # (x,z)∈G
    casA_zx = N.loi_deduction(egal(vz, vx), zx_G)
    xz_final_A = cas(disj_z, casA_zX, casA_zx)            # (x,z)∈G  (sous z∈X∪{x})
    min_body_A = N.generalisation(_ZPP, N.loi_deduction(appartient(vz, Xux), xz_final_A))
    ppe_x_A = conjonction_intro(x_in_Xux, min_body_A)     # plus_petit_element(G, X∪{x}, x)
    ex_A = N.modus_ponens(ppe_x_A, N.s5(_ppe(G, Xux, var(m)), vx, m))
    casA = N.loi_deduction(egal(vX, E.VIDE), ex_A)

    # ============ CAS B : X ≠ ∅  =============================================
    hXnonvide = N.assume(non(egal(vX, E.VIDE)))
    ante_PX = conjonction_intro(X_sub_E, hXnonvide)
    ex_mX = N.modus_ponens(ante_PX, hPX)                 # (∃m)ppe(X,m)
    hppeX = N.assume(_ppe(G, vX, var(m)))   # ppe(X,m): m∈X et ∀z(z∈X⇒(m,z)∈G)
    vm = var(m)
    m_in_X = conjonction_elim_gauche(hppeX)
    m_min_X = conjonction_elim_droite(hppeX)             # ∀z(z∈X⇒(m,z)∈G)
    m_in_Xux = N.modus_ponens(
        N.modus_ponens(m_in_X, N.s2(appartient(vm, vX), egal(vm, vx))),
        equivalence_arriere(_membre_union_singleton(vm, vX, vx)))
    m_in_E = N.modus_ponens(m_in_X, instancie(X_sub_E, vm))
    # comparer m et x : (m,x)∈G ou (x,m)∈G
    comp_mx = N.modus_ponens(conjonction_intro(m_in_E, x_in_E),
                             instancie(instancie(comp, vm), vx))    # (m,x)∈G ou (x,m)∈G

    #   --- sous-cas (m,x)∈G : m est le plus petit de X∪{x} ---
    hmx = N.assume(_couple_dans(vm, vx, G))              # (m,x)∈G
    hz_in_B1 = N.assume(appartient(vz, Xux))
    disj_zB1 = N.modus_ponens(hz_in_B1, equivalence_avant(_membre_union_singleton(vz, vX, vx)))
    #     z∈X ⇒ (m,z)∈G
    hzX_B1 = N.assume(appartient(vz, vX))
    mz_G = N.modus_ponens(hzX_B1, instancie(m_min_X, vz))    # (m,z)∈G
    casB1_zX = N.loi_deduction(appartient(vz, vX), mz_G)
    #     z=x ⇒ (m,z)∈G via (m,x)∈G + Leibniz x↦z (2e composante)
    hzx_B1 = N.assume(egal(vz, vx))
    x_eq_z_B1 = N.modus_ponens(hzx_B1, symetrie(vz, vx))     # x=z
    mz_G_B1 = N.modus_ponens(hmx, equivalence_avant(N.modus_ponens(x_eq_z_B1, N.s6(vx, vz, "wb1", _couple_dans(vm, var("wb1"), G)))))
    casB1_zx = N.loi_deduction(egal(vz, vx), mz_G_B1)
    mz_final_B1 = cas(disj_zB1, casB1_zX, casB1_zx)
    min_body_B1 = N.generalisation(_ZPP, N.loi_deduction(appartient(vz, Xux), mz_final_B1))
    ppe_m_B1 = conjonction_intro(m_in_Xux, min_body_B1)     # ppe(G,X∪{x},m)
    ex_B1 = N.modus_ponens(ppe_m_B1, N.s5(_ppe(G, Xux, var(m)), vm, m))
    casB1 = N.loi_deduction(_couple_dans(vm, vx, G), ex_B1)

    #   --- sous-cas (x,m)∈G : x est le plus petit de X∪{x} ---
    hxm = N.assume(_couple_dans(vx, vm, G))             # (x,m)∈G
    hz_in_B2 = N.assume(appartient(vz, Xux))
    disj_zB2 = N.modus_ponens(hz_in_B2, equivalence_avant(_membre_union_singleton(vz, vX, vx)))
    #     z∈X ⇒ (x,z)∈G via (x,m)∈G et (m,z)∈G + transitivité
    hzX_B2 = N.assume(appartient(vz, vX))
    mz_G_B2 = N.modus_ponens(hzX_B2, instancie(m_min_X, vz))    # (m,z)∈G
    trans_xmz = instancie(instancie(instancie(trans, vx), vm), vz)   # ((x,m)∈G et (m,z)∈G)⇒(x,z)∈G
    xz_G_B2 = N.modus_ponens(conjonction_intro(hxm, mz_G_B2), trans_xmz)   # (x,z)∈G
    casB2_zX = N.loi_deduction(appartient(vz, vX), xz_G_B2)
    #     z=x ⇒ (x,z)∈G via réfl (x,x)∈G transporté x↦z (2e composante)
    hzx_B2 = N.assume(egal(vz, vx))
    xxG_B2 = refl_en(x_in_E, vx)                            # (x,x)∈G
    x_eq_z_B2 = N.modus_ponens(hzx_B2, symetrie(vz, vx))    # x=z
    xz_G_B2b = N.modus_ponens(xxG_B2, equivalence_avant(N.modus_ponens(x_eq_z_B2, N.s6(vx, vz, "wb2", _couple_dans(vx, var("wb2"), G)))))
    casB2_zx = N.loi_deduction(egal(vz, vx), xz_G_B2b)
    xz_final_B2 = cas(disj_zB2, casB2_zX, casB2_zx)
    min_body_B2 = N.generalisation(_ZPP, N.loi_deduction(appartient(vz, Xux), xz_final_B2))
    ppe_x_B2 = conjonction_intro(x_in_Xux, min_body_B2)     # ppe(G,X∪{x},x)
    ex_B2 = N.modus_ponens(ppe_x_B2, N.s5(_ppe(G, Xux, var(m)), vx, m))
    casB2 = N.loi_deduction(_couple_dans(vx, vm, G), ex_B2)

    ex_from_ppeX = cas(comp_mx, casB1, casB2)            # (∃m)ppe(X∪{x},m)  (sous ppe(X,m))
    imp_ppeX = N.loi_deduction(_ppe(G, vX, var(m)), ex_from_ppeX)
    ex_B = N.modus_ponens(ex_mX, existe_elimination(imp_ppeX, m))
    casB = N.loi_deduction(non(egal(vX, E.VIDE)), ex_B)

    ex_total = cas(te, casA, casB)
    PXux = N.loi_deduction(garde, ex_total)
    corps = N.loi_deduction(et(et(est_fini_ensemble(vX), non(appartient(vx, vX))), P(vX)), PXux)
    res = N.generalisation(X, N.generalisation(x, corps))
    assert res.conclusion == _pas_ensemble(P, X, x), "pas min mal formé"
    return res


def prop3_total_min(G="Gppt", E_set="Eppt", X="Xppt", m="m_ppf"):
    """🎯 ⊢ prop3_total_min_enonce(G,E).   (Prop. 3 §III.4, variante totale, PLUS PETIT.)

    Toute partie FINIE non vide d'un ensemble TOTALEMENT ORDONNÉ admet un plus petit
    élément.  Via `recurrence_finie` ; base ∅ vacuous, pas par comparaison du plus
    petit de X avec le point ajouté (on garde le plus petit des deux)."""
    vE = _t(E_set)
    htot = N.assume(totalement_ordonne(G, E_set))
    P = _P_plus_petit(G, E_set, m)

    # P(∅) vacuous (¬(∅=∅) faux)
    hP0_ante = N.assume(et(inclus(E.VIDE, vE), non(egal(E.VIDE, E.VIDE))))
    n_refl = conjonction_elim_droite(hP0_ante)
    refl0 = N.reflexivite(E.VIDE)
    concl0 = existe(m, _ppe(G, E.VIDE, var(m)))
    falso0 = N.modus_ponens(refl0, N.modus_ponens(n_refl, N.s2(non(egal(E.VIDE, E.VIDE)), concl0)))
    P0 = N.loi_deduction(et(inclus(E.VIDE, vE), non(egal(E.VIDE, E.VIDE))), falso0)
    assert P0.conclusion == P(E.VIDE), "P(∅) min mal formé"

    pas = _preuve_pas_total_min(G, E_set, htot, P, m=m)
    rf = recurrence_finie(P)
    fini_imp_PX = N.modus_ponens(conjonction_intro(P0, pas), rf)   # [htot]

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
    res = N.loi_deduction(totalement_ordonne(G, E_set), concl)
    assert res.conclusion == prop3_total_min_enonce(G, E_set, X, m), "conclusion ≠ énoncé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 §III.4 — un ensemble fini totalement ordonné admet un PLUS PETIT
#  élément  (= la moitié « plus petit » du Cor 1 ; socle de « bien ordonné »).
# ════════════════════════════════════════════════════════════════════════════
def cor1_total_min_enonce(G, E_set, m="m_ppf"):
    """⊢-cible : ( totalement_ordonne(G,E) et est_fini_ensemble(E) et ¬(E=∅) )
        ⇒ (∃m)( plus_petit_element(G,E,m) ).

    « Tout ensemble fini totalement ordonné non vide admet un plus petit élément. »
    (Cor. 1 §III.4 — partie « plus petit élément ».)"""
    vE = _t(E_set)
    return impl(et(et(totalement_ordonne(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))),
                existe(m, _ppe(G, vE, var(m))))


def cor1_total_min(G="Gppt", E_set="Eppt", m="m_ppf"):
    """🎯 ⊢ cor1_total_min_enonce(G,E).   (Cor. 1 §III.4, partie plus petit élément.)

    Application directe de prop3_total_min à la partie X := E (E⊂E réflexif)."""
    vE = _t(E_set)
    h = N.assume(et(et(totalement_ordonne(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))))
    htot = conjonction_elim_gauche(conjonction_elim_gauche(h))
    hfin = conjonction_elim_droite(conjonction_elim_gauche(h))
    hnv = conjonction_elim_droite(h)
    p3 = prop3_total_min(G, E_set, "XcorEmin", m)
    forall_X = N.modus_ponens(htot, p3)
    inst_E = instancie(forall_X, vE)
    E_sub_E = _inclus_refl_via(vE)
    ex = N.modus_ponens(conjonction_intro(conjonction_intro(hfin, E_sub_E), hnv), inst_E)
    res = N.loi_deduction(et(et(totalement_ordonne(G, E_set), est_fini_ensemble(vE)), non(egal(vE, E.VIDE))), ex)
    assert res.conclusion == cor1_total_min_enonce(G, E_set, m), "conclusion ≠ énoncé cor1 min"
    return res


__all__ = [
    "prop3_total_min_enonce", "prop3_total_min",
    "cor1_total_min_enonce", "cor1_total_min",
]
