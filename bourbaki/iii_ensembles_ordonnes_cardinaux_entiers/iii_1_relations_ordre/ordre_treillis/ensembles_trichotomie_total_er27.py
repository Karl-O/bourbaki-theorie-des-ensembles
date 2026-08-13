"""Résumé §2 (E.R.27 item 4) — trichotomie exclusive dans un ensemble totalement ordonné.

Bourbaki (E.R.27) : « x≤y ou y≤x (ou encore, soit x<y, soit x=y, soit x>y, ces
trois relations s'excluant mutuellement). »  (Fait général d'un ensemble TOTALEMENT
ordonné, pas propre aux cardinaux.)

ÉNONCÉ DÉRIVÉ (G graphe d'un ordre total sur E ; x<y := (x,y)∈G et x≠y) :

    ⊢ totalement_ordonne(G,E) ⇒ (∀u)(∀v)( (u∈E et v∈E) ⇒
          (  ( (u<v) ou (u=v) ou (v<u) )                         [EXHAUSTIVE]
             et ¬((u<v) et (u=v)) et ¬((u<v) et (v<u)) et ¬((u=v) et (v<u)) ) )  [EXCLUSIVE]

DÉMONSTRATION :
  · EXHAUSTIVE : par tiers-exclu sur (u=v).  Si u=v : disjonction par le milieu.
    Sinon : comparabilité (u,v)∈G ou (v,u)∈G [totalement_ordonne] ⇒ u<v ou v<u.
  · EXCLUSIVE :
      ¬(u<v et u=v) : u<v porte ¬(u=v), contredit u=v ;
      ¬(u<v et v<u) : (u,v)∈G et (v,u)∈G ⇒ u=v [antisymétrie], contredit ¬(u=v) ;
      ¬(u=v et v<u) : v<u porte ¬(v=u), et u=v ⇒ v=u [symétrie], contradiction.

theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, ou, non, egal, appartient, impl, pourtout, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    totalement_ordonne, antisymetrie)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cpl(a, b, G):
    return appartient(E.couple(_t(a), _t(b)), _t(G))


def _ex_falso(thm_a, thm_na, cible):
    """{⊢A}, {⊢¬A} ⟹ ⊢cible  (impl = ou(non,·) dans le noyau)."""
    imp = N.modus_ponens(thm_na, N.s2(non(thm_a.conclusion), cible))
    return N.modus_ponens(thm_a, imp)


def _neg(conj, thm_R_sous, thm_notR):
    """{conj ⊢ R}, {⊢¬R} ⟹ ⊢ ¬conj."""
    falso = _ex_falso(thm_R_sous, thm_notR, non(conj))     # {conj} ⊢ ¬conj
    return N.modus_ponens(N.loi_deduction(conj, falso), N.s1(non(conj)))


def _inj_gauche(A, B, thm_A):
    """{⊢A} ⟹ ⊢ A ou B."""
    return N.modus_ponens(thm_A, N.s2(A, B))


def _inj_droite(A, B, thm_B):
    """{⊢B} ⟹ ⊢ A ou B  (B⇒(B∨A)⇒(A∨B))."""
    return N.modus_ponens(N.modus_ponens(thm_B, N.s2(B, A)), N.s3(B, A))


def enonce_trichotomie_totale(G="G", E_set="E"):
    vG, vE = _t(G), _t(E_set)
    u, v = var("u"), var("v")
    lt = et(_cpl(u, v, vG), non(egal(u, v)))
    gt = et(_cpl(v, u, vG), non(egal(v, u)))
    eq = egal(u, v)
    exhaustive = ou(ou(lt, eq), gt)
    exclusive = et(et(non(et(lt, eq)), non(et(lt, gt))), non(et(eq, gt)))
    corps = impl(et(appartient(u, vE), appartient(v, vE)), et(exhaustive, exclusive))
    return impl(totalement_ordonne(vG, vE), pourtout("u", pourtout("v", corps)))


# @livre Ch.R §2 Prop.- | E.R.27 item 4 | PDF p.330  (trichotomie exclusive d'un ordre total — DÉRIVÉ)
# @livre Ch.R §2 Demo.- | E.R.27 item 4 | PDF p.330  (démo : tiers-exclu + comparabilité (exhaustive) ; antisymétrie+symétrie (exclusive))
def trichotomie_totale(G="G", E_set="E"):
    """🎯 ⊢ totalement_ordonne(G,E) ⇒ (∀u,v∈E)( trichotomie exclusive de u<v / u=v / v<u ).

    « Dans un ensemble totalement ordonné, exactement une des relations u<v, u=v, v<u
    est vraie » (E.R.27 item 4).  x<y := (x,y)∈G et x≠y."""
    vG, vE = _t(G), _t(E_set)
    u, v = var("u"), var("v")
    lt = et(_cpl(u, v, vG), non(egal(u, v)))
    gt = et(_cpl(v, u, vG), non(egal(v, u)))
    eq = egal(u, v)
    exhaustive = ou(ou(lt, eq), gt)

    h_tot = N.assume(totalement_ordonne(vG, vE))
    ordre = conjonction_elim_gauche(h_tot)                 # est_ordre(G,E)
    comp = conjonction_elim_droite(h_tot)                  # (∀x∀y)((x∈E et y∈E)⇒((x,y)∈G ou (y,x)∈G))
    antisym = conjonction_elim_droite(conjonction_elim_gauche(ordre))  # antisymetrie(G)

    h_uv = N.assume(et(appartient(u, vE), appartient(v, vE)))
    comp_uv = N.modus_ponens(h_uv, instancie(instancie(comp, u), v))    # (u,v)∈G ou (v,u)∈G
    antisym_uv = instancie(instancie(antisym, u), v)       # ((u,v)∈G et (v,u)∈G) ⇒ u=v

    # ── EXHAUSTIVE : ou(ou(lt,eq),gt) ─────────────────────────────────────────
    #  cas u=v : eq ⇒ (lt∨eq) ⇒ (lt∨eq)∨gt
    h_eq = N.assume(eq)
    exh_from_eq = _inj_gauche(ou(lt, eq), gt, _inj_droite(lt, eq, h_eq))
    imp_eq = N.loi_deduction(eq, exh_from_eq)              # (u=v) ⇒ exhaustive
    #  cas u≠v : comparabilité ⇒ lt ou gt
    h_ne = N.assume(non(eq))
    #   sous (u,v)∈G : lt = ((u,v)∈G et ¬(u=v)) ⇒ (lt∨eq)∨gt
    h_uvG = N.assume(_cpl(u, v, vG))
    lt_thm = conjonction_intro(h_uvG, h_ne)               # lt   [sous (u,v)∈G, u≠v]
    exh_from_uvG = _inj_gauche(ou(lt, eq), gt, _inj_gauche(lt, eq, lt_thm))
    imp_uvG = N.loi_deduction(_cpl(u, v, vG), exh_from_uvG)  # (u,v)∈G ⇒ exhaustive  [sous u≠v]
    #   sous (v,u)∈G : gt = ((v,u)∈G et ¬(v=u)) ; ¬(v=u) depuis ¬(u=v) par contraposée symétrie
    h_vuG = N.assume(_cpl(v, u, vG))
    #   ¬(v=u) : de (v=u)⇒(u=v) [symetrie] et ¬(u=v)
    nvu = _neg(egal(v, u), N.modus_ponens(N.assume(egal(v, u)), symetrie(v, u)), h_ne)  # ¬(v=u)
    gt_thm = conjonction_intro(h_vuG, nvu)                # gt   [sous (v,u)∈G, u≠v]
    exh_from_vuG = _inj_droite(ou(lt, eq), gt, gt_thm)
    imp_vuG = N.loi_deduction(_cpl(v, u, vG), exh_from_vuG)  # (v,u)∈G ⇒ exhaustive  [sous u≠v]
    exh_ne = cas(comp_uv, imp_uvG, imp_vuG)               # exhaustive   [sous u≠v]  (comp_uv sans u=v)
    imp_ne = N.loi_deduction(non(eq), exh_ne)             # (u≠v) ⇒ exhaustive
    exhaustive_thm = cas(tiers_exclu(eq), imp_eq, imp_ne)  # exhaustive

    # ── EXCLUSIVE ─────────────────────────────────────────────────────────────
    #  ¬(lt et eq) : lt donne ¬(u=v), eq donne u=v  → contradiction
    h_le = N.assume(et(lt, eq))
    R_eq = conjonction_elim_droite(h_le)                            # {lt∧eq} ⊢ (u=v)
    R_ne = conjonction_elim_droite(conjonction_elim_gauche(h_le))   # {lt∧eq} ⊢ ¬(u=v)
    falso_le = _ex_falso(R_eq, R_ne, non(et(lt, eq)))                # {lt∧eq} ⊢ ¬(lt∧eq)
    neg_lt_eq = N.modus_ponens(N.loi_deduction(et(lt, eq), falso_le), N.s1(non(et(lt, eq))))

    #  ¬(lt et gt) : (u,v)∈G et (v,u)∈G ⇒ u=v [antisym], contredit ¬(u=v) de lt
    h_lg = N.assume(et(lt, gt))
    uvG = conjonction_elim_gauche(conjonction_elim_gauche(h_lg))     # (u,v)∈G
    vuG = conjonction_elim_gauche(conjonction_elim_droite(h_lg))     # (v,u)∈G
    ne_lg = conjonction_elim_droite(conjonction_elim_gauche(h_lg))   # ¬(u=v)  (de lt)
    eq_lg = N.modus_ponens(conjonction_intro(uvG, vuG), antisym_uv)  # u=v
    falso_lg = _ex_falso(eq_lg, ne_lg, non(et(lt, gt)))              # {lt∧gt} ⊢ ¬(lt∧gt)
    neg_lt_gt = N.modus_ponens(N.loi_deduction(et(lt, gt), falso_lg), N.s1(non(et(lt, gt))))

    #  ¬(eq et gt) : eq=u=v ⇒ v=u [symetrie], contredit ¬(v=u) de gt
    h_eg = N.assume(et(eq, gt))
    eq_eg = conjonction_elim_gauche(h_eg)                            # u=v
    ne_vu = conjonction_elim_droite(conjonction_elim_droite(h_eg))   # ¬(v=u)  (de gt)
    vu_eg = N.modus_ponens(eq_eg, symetrie(u, v))                    # v=u
    falso_eg = _ex_falso(vu_eg, ne_vu, non(et(eq, gt)))             # {eq∧gt} ⊢ ¬(eq∧gt)
    neg_eq_gt = N.modus_ponens(N.loi_deduction(et(eq, gt), falso_eg), N.s1(non(et(eq, gt))))

    exclusive_thm = conjonction_intro(conjonction_intro(neg_lt_eq, neg_lt_gt), neg_eq_gt)

    corps = conjonction_intro(exhaustive_thm, exclusive_thm)         # [sous u∈E∧v∈E]
    inner = N.loi_deduction(et(appartient(u, vE), appartient(v, vE)), corps)
    gen = N.generalisation("u", N.generalisation("v", inner))
    res = N.loi_deduction(totalement_ordonne(vG, vE), gen)
    assert res.conclusion == enonce_trichotomie_totale(G, E_set), \
        "trichotomie_totale : conclusion ≠ énoncé attendu"
    return res


__all__ = ["enonce_trichotomie_totale", "trichotomie_totale"]
