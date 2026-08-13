"""§III.7.6 Prop. 6, 1° — v est COMPATIBLE avec la relation de cohérence R.

────────────────────────────────────────────────────────────────────────────────
« Soit v l'application de G dans F qui coïncide avec u_α dans chaque E_α ;
l'hypothèse (23) entraîne que v est compatible avec la relation d'équivalence
R »  (E III.62).  C'est le CŒUR du 1° : une fois la compatibilité acquise, u
s'obtient par passage au quotient (II.44) et vérifie (24).

  { (23) au point : u_β(f_βα(x)) = u_α(x) pour α≤β,
    v coïncide    : v(x) = u_{λ(x)}(x) sur G,
    structure de la somme : x∈G ⇒ (λ(x)∈I et x∈E_{λ(x)}),  x∈G, y∈G }
      ⊢  R{x,y}  ⇒  v(x) = v(y)

R{x,y} = (∃γ)(γ∈I et γ≥λ(x) et γ≥λ(y) et f_{γλ(x)}(x)=f_{γλ(y)}(y)) — formule
EXPLICITE (relation_coherence_inductive), donc la compatibilité se DÉMONTRE :
sous le témoin γ, v(x) = u_{λx}(x) = u_γ(f_{γλx}(x)) = u_γ(f_{γλy}(y))
= u_{λy}(y) = v(y), les deux égalités du milieu étant (23) et la congruence.
⚠️ témoin de cohérence renommé « gc » (« g » est un nom trop courant).
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.fondations.ensembles_graphe_de import (
    graphe_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L, ensembles_limites_canoniques as C,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §7.6 Prop.6 | E III.62 L.26-29 | PDF p.165  (relation (23) « u_β∘f_βα = u_α pour α≤β », écrite au point)
def relation_23_au_point(uf, f, Efam, i, leq=None, a="ai", b="bi", x="xi"):
    """(∀a)(∀b)(∀x)( (a∈I et b∈I et a≤b et x∈E_a) ⇒ u_b(f_ba(x)) = u_a(x) )."""
    if leq is None:
        leq = C._gleq()
    vuf, vf, vE, vi = _t(uf), _t(f), _t(Efam), _t(i)
    va, vb, vx = var(a), var(b), var(x)
    fba = L.appl_ind(vf, vb, va)
    prem = et(et(et(appartient(va, vi), appartient(vb, vi)), leq(va, vb)),
              appartient(vx, E.valeur_famille(vE, va)))
    concl = egal(E.valeur(C.u_indice(vuf, vb), L.transition_valeur(fba, vx)),
                 E.valeur(C.u_indice(vuf, va), vx))
    return pourtout(a, pourtout(b, pourtout(x, impl(prem, concl))))


def hyp_v_coincide(v, uf, somme, x="xi"):
    """(∀x)( x∈G ⇒ v(x) = u_{λ(x)}(x) )  — « v coïncide avec u_α dans chaque E_α »
    (recollement, Prop. 8 E II.29 : hypothèse honnête, EXISTENCE de v reportée)."""
    vv, vuf, vG, vx = _t(v), _t(uf), _t(somme), var(x)
    lx = C.lambda_indice(vx)
    return pourtout(x, impl(appartient(vx, vG),
                            egal(E.valeur(graphe_de(vv), vx),
                                 E.valeur(C.u_indice(vuf, lx), vx))))


def hyp_structure_somme(Efam, i, somme, x="xi"):
    """(∀x)( x∈G ⇒ (λ(x)∈I et x∈E_{λ(x)}) )  — propriété caractéristique de G=∑E_α."""
    vE, vi, vG, vx = _t(Efam), _t(i), _t(somme), var(x)
    lx = C.lambda_indice(vx)
    return pourtout(x, impl(appartient(vx, vG),
                            et(appartient(lx, vi),
                               appartient(vx, E.valeur_famille(vE, lx)))))


# @livre Ch.III §7.6 Prop.6 | E III.62 L.29-30 | PDF p.165  (cœur du 1° : (23) entraîne que v est compatible avec la relation de cohérence R — l'obstacle à l'existence de u)
def compatible_v_coherence(v="v", uf="uf", f="f", Efam="E", i="I", somme=None,
                           leq=None, x="xi", y="yi"):
    """{ (23), v coïncide, structure de G, x∈G, y∈G } ⊢ ( R{x,y} ⇒ v(x)=v(y) )."""
    if leq is None:
        leq = C._gleq()
    vv, vuf, vf, vE, vi = _t(v), _t(uf), _t(f), _t(Efam), _t(i)
    vG = E.somme_famille(vE, vi) if somme is None else _t(somme)
    vx, vy, vg = var(x), var(y), var("gc")
    lx, ly = C.lambda_indice(vx), C.lambda_indice(vy)
    gv = graphe_de(vv)

    h23 = N.assume(relation_23_au_point(vuf, vf, vE, vi, leq))
    hv = N.assume(hyp_v_coincide(vv, vuf, vG))
    hs = N.assume(hyp_structure_somme(vE, vi, vG))
    hx, hy = N.assume(appartient(vx, vG)), N.assume(appartient(vy, vG))

    sx = N.modus_ponens(hx, instancie(hs, vx))         # λ(x)∈I et x∈E_{λ(x)}
    sy = N.modus_ponens(hy, instancie(hs, vy))
    vx_eq = N.modus_ponens(hx, instancie(hv, vx))      # v(x) = u_{λx}(x)
    vy_eq = N.modus_ponens(hy, instancie(hv, vy))      # v(y) = u_{λy}(y)

    R = C.relation_coherence_inductive(vf, leq, vi, vx, vy, g="gc")
    corps = R.sous[0]                                  # le corps sous (∃gc)
    hb = N.assume(corps)
    g_in = conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(hb)))                  # gc∈I
    le_x = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_gauche(hb)))                  # λ(x)≤gc
    le_y = conjonction_elim_droite(conjonction_elim_gauche(hb))   # λ(y)≤gc
    tr_eq = conjonction_elim_droite(hb)                # f_{gc,λx}(x)=f_{gc,λy}(y)

    def _e23(sz, le_z, lz, vz):
        """{…} ⊢ u_gc( f_{gc,λ(z)}(z) ) = u_{λ(z)}(z)   (instance de (23))."""
        prem = conjonction_intro(conjonction_intro(conjonction_intro(
            conjonction_elim_gauche(sz), g_in), le_z), conjonction_elim_droite(sz))
        return N.modus_ponens(prem, instancie(instancie(instancie(
            h23, lz), vg), vz))

    e_x = _e23(sx, le_x, lx, vx)
    e_y = _e23(sy, le_y, ly, vy)
    t_x = L.transition_valeur(L.appl_ind(vf, vg, lx), vx)   # f_{gc,λx}(x)
    t_y = L.transition_valeur(L.appl_ind(vf, vg, ly), vy)
    ug = C.u_indice(vuf, vg)
    cong = N.modus_ponens(tr_eq, congruence_terme(
        t_x, t_y, E.valeur(ug, var("w6c")), w="w6c"))  # u_gc(t_x) = u_gc(t_y)
    chain = composer_egalites(composer_egalites(composer_egalites(
        composer_egalites(vx_eq,
                          N.modus_ponens(e_x, symetrie(E.valeur(ug, t_x),
                                                       E.valeur(C.u_indice(vuf, lx), vx)))),
        cong), e_y),
        N.modus_ponens(vy_eq, symetrie(E.valeur(gv, vy),
                                       E.valeur(C.u_indice(vuf, ly), vy))))
    #     v(x) = u_{λx}(x) = u_gc(t_x) = u_gc(t_y) = u_{λy}(y) = v(y)
    res = N.loi_deduction(R, N.modus_ponens(N.assume(R), existe_elimination(
        N.loi_deduction(corps, chain), "gc")))
    assert res.conclusion == impl(R, egal(E.valeur(gv, vx), E.valeur(gv, vy))), \
        "compatible_v_coherence : ≠ (R{x,y} ⇒ v(x)=v(y))"
    assert set(res.hypotheses) == {h23.conclusion, hv.conclusion, hs.conclusion,
                                   hx.conclusion, hy.conclusion}, \
        "compatible_v_coherence : hyps"
    return res


__all__ = ["relation_23_au_point", "hyp_v_coincide", "hyp_structure_somme",
           "compatible_v_coherence"]
