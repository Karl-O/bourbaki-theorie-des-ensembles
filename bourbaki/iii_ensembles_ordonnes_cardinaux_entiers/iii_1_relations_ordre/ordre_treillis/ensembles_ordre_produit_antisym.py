"""§III.1.4 — L'ordre PRODUIT est une relation d'ORDRE (antisymétrie incluse).

Complète `ensembles_iii1_ordre_props.ordre_produit_est_preordre` (qui s'arrêtait au
PRÉORDRE, l'antisymétrie étant bloquée faute d'extensionnalité du produit).  Grâce à
`ensembles_extensionnalite_produit.extensionnalite_produit` (PART A), on PROUVE
l'antisymétrie sur le produit, donc l'ORDRE complet (E.III.1.4).

ÉNONCÉ.  Soit P := relation_ordre_produit(Rfam, I), R_ι := Rfam(ι).
  ordre_produit_est_ordre ⊢
     ( (∀ι)(ι∈I ⇒ ordre_transitif(R_ι))
       et (∀ι)(ι∈I ⇒ ordre_antisymetrique(R_ι))
       et (∀ι)(ι∈I ⇒ ordre_reflexif_implicite(R_ι)) )
     ⇒ ( transitivité(P) et antisymétrie_sur_produit(P) et réflexivité_implicite(P) ),
  antisymétrie_sur_produit(P) :=
     (∀x)(∀y)( (x∈∏ et y∈∏ et graphe(x) et graphe(y) et P{x,y} et P{y,x}) ⇒ x=y ).

ANTISYMÉTRIE (le point neuf).  De P{x,y} et P{y,x} : pour chaque ι∈I, R_ι{pr_ι x, pr_ι y}
et R_ι{pr_ι y, pr_ι x}, d'où pr_ι x = pr_ι y (antisymétrie de R_ι, hypothèse) ;
généraliser ⇒ (∀ι∈I) pr_ι x = pr_ι y ; par extensionnalite_produit (sous x,y∈∏ et
graphe x, graphe y) ⇒ x = y.  Transitivité / réflexivité implicite : POINTWISE
(comme ordre_produit_est_preordre).

HYPOTHÈSES HONNÊTES.  L'antécédent (per-factor transitivité/antisymétrie/réflexivité)
est l'hypothèse standard ; la clause d'antisymétrie est relativisée à ∏ (x,y∈∏, graphes)
— c'est l'ordre produit SUR LE PRODUIT (E.III.1.4 : relation « entre x=(x_ι), y=(y_ι) »,
i.e. sur ∏), et « graphe » est la prémisse honnête de extensionnalite_produit.  CLOS
(0 hyp) ; non vacuous (x=y ∉ son antécédent).

Binders : POINTS produit « xp,yp,zp » (≠ x,y,z,w, les binders internes de
graphe_egal_par_valeurs employé par extensionnalite_produit — collision interdite) ;
binders du FACTEUR « a,b,c » ; indice « i » ; projection-égalité « i ».
theorie_ensembles() reste à 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient, pourtout
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_extensionnalite_produit import (
    extensionnalite_produit)


def _t(v):
    return var(v) if isinstance(v, str) else v


# @livre Ch.III §1.4 Rem.- | E III.6 L.24-25 | PDF p.109
# (clause d'antisymétrie, relativisée à ∏, du « est une relation d'ordre » de l'ordre produit)
def antisymetrie_sur_produit(P, fam, I, x="xp", y="yp"):
    """(∀x)(∀y)( (x∈∏ et y∈∏ et graphe x et graphe y et P{x,y} et P{y,x}) ⇒ x=y ).

    Antisymétrie de l'ordre produit SUR le produit ∏=∏_{ι∈I} X_ι (fam=la famille (X_ι),
    I=indices).  Forme relativisée honnête (cf. docstring module)."""
    vx, vy = var(x), var(y)
    prod = E.produit_famille(_t(fam), _t(I))
    ante = et(et(et(et(et(
        appartient(vx, prod), appartient(vy, prod)),
        E.est_un_graphe(vx)), E.est_un_graphe(vy)),
        P(vx, vy)), P(vy, vx))
    return pourtout(x, pourtout(y, impl(ante, egal(vx, vy))))


# @livre Ch.III §1.4 Rem.- | E III.6 L.24-25 | PDF p.109
# (vérification complète — transitivité + antisymétrie sur ∏ + réflexivité implicite — du
#  « est une relation d'ordre entre x=(x_ι) et y=(y_ι), comme on le vérifie aisément »)
def ordre_produit_est_ordre(Rfam, fam, I="I", i="i", x="xp", y="yp", z="zp",
                            a="a", b="b", c="c"):
    """⊢ ( (∀ι)(ι∈I ⇒ ordre_transitif(R_ι)) et (∀ι)(ι∈I ⇒ ordre_antisymetrique(R_ι))
          et (∀ι)(ι∈I ⇒ ordre_reflexif_implicite(R_ι)) )
        ⇒ ( transitivité(P) et antisymétrie_sur_produit(P) et réflexivité_implicite(P) ),
       P := relation_ordre_produit(Rfam, I), R_ι := Rfam(ι)  (E.III.1.4).

    L'ordre produit est une relation d'ORDRE sur ∏ (PRÉORDRE + antisymétrie via
    extensionnalite_produit).  Rfam = ι↦R_ι ; fam = la famille (X_ι) du produit.
    Hypothèses honnêtes / non vacuous (voir docstring module).  CLOS."""
    vI = _t(I)
    vfam = _t(fam)
    vi = var(i)
    vx, vy, vz = var(x), var(y), var(z)
    P = V.relation_ordre_produit(Rfam, I, i)          # λ(x,y). (∀ι)(ι∈I ⇒ R_ι{pr_ι x, pr_ι y})
    R_i = Rfam(vi)
    prod = E.produit_famille(vfam, vI)

    # antécédent : transitivité, antisymétrie, réflexivité-implicite POINTWISE
    htr = pourtout(i, impl(appartient(vi, vI), E.ordre_transitif(R_i, a, b, c)))
    hanti = pourtout(i, impl(appartient(vi, vI), E.ordre_antisymetrique(R_i, a, b)))
    href = pourtout(i, impl(appartient(vi, vI), E.ordre_reflexif_implicite(R_i, a, b)))
    ante = et(et(htr, hanti), href)
    H = N.assume(ante)
    Htr = conjonction_elim_gauche(conjonction_elim_gauche(H))   # transitivité pointwise
    Hanti = conjonction_elim_droite(conjonction_elim_gauche(H)) # antisymétrie pointwise
    Href = conjonction_elim_droite(H)                           # réflexivité-implicite pointwise

    def pr(pt):
        return E.projection_indice(pt, vi)

    # ── (a) transitivité de P (pointwise, comme le préordre déposé) ───────────────
    hconj = N.assume(et(P(vx, vy), P(vy, vz)))
    Pxy = conjonction_elim_gauche(hconj)
    Pyz = conjonction_elim_droite(hconj)
    h_iI = N.assume(appartient(vi, vI))
    Rxy_i = N.modus_ponens(h_iI, instancie(Pxy, vi))
    Ryz_i = N.modus_ponens(h_iI, instancie(Pyz, vi))
    tr_i = N.modus_ponens(h_iI, instancie(Htr, vi))
    tr_proj = instancie(instancie(instancie(tr_i, pr(vx)), pr(vy)), pr(vz))
    Rxz_i = N.modus_ponens(conjonction_intro(Rxy_i, Ryz_i), tr_proj)
    tr_iI = N.loi_deduction(appartient(vi, vI), Rxz_i)
    Pxz = N.generalisation(i, tr_iI)
    tr_body = N.loi_deduction(et(P(vx, vy), P(vy, vz)), Pxz)
    trans_P = N.generalisation(x, N.generalisation(y, N.generalisation(z, tr_body)))

    # ── (b) ANTISYMÉTRIE sur ∏ : (x,y∈∏ et graphe x,y et P{x,y} et P{y,x}) ⇒ x=y ──
    cible_ante = et(et(et(et(et(
        appartient(vx, prod), appartient(vy, prod)),
        E.est_un_graphe(vx)), E.est_un_graphe(vy)),
        P(vx, vy)), P(vy, vx))
    Ha = N.assume(cible_ante)
    r1 = conjonction_elim_gauche(Ha)                  # (... et P{x,y})
    Pyx = conjonction_elim_droite(Ha)                 # P{y,x}
    Pxy_a = conjonction_elim_droite(r1)               # P{x,y}
    r2 = conjonction_elim_gauche(r1)                  # (... et graphe y)
    gy = conjonction_elim_droite(r2)                  # graphe y
    r3 = conjonction_elim_gauche(r2)                  # (... et graphe x)
    gx = conjonction_elim_droite(r3)                  # graphe x
    r4 = conjonction_elim_gauche(r3)                  # (x∈∏ et y∈∏)
    x_in = conjonction_elim_gauche(r4)                # x∈∏
    y_in = conjonction_elim_droite(r4)                # y∈∏

    # (∀ι)(ι∈I ⇒ pr_ι x = pr_ι y)  via antisymétrie de R_ι (binder « i »)
    h_iI2 = N.assume(appartient(vi, vI))
    Rxy_i2 = N.modus_ponens(h_iI2, instancie(Pxy_a, vi))   # R_ι{pr_ι x, pr_ι y}
    Ryx_i2 = N.modus_ponens(h_iI2, instancie(Pyx, vi))     # R_ι{pr_ι y, pr_ι x}
    anti_i = N.modus_ponens(h_iI2, instancie(Hanti, vi))   # ordre_antisymetrique(R_ι)
    anti_proj = instancie(instancie(anti_i, pr(vx)), pr(vy))  # (R_ι{pr x,pr y} et R_ι{pr y,pr x}) ⇒ pr x=pr y
    prx_eq_pry = N.modus_ponens(conjonction_intro(Rxy_i2, Ryx_i2), anti_proj)  # pr_ι x = pr_ι y
    proj_iI = N.loi_deduction(appartient(vi, vI), prx_eq_pry)  # ι∈I ⇒ pr_ι x=pr_ι y
    proj_eq = N.generalisation(i, proj_iI)            # (∀i)(i∈I ⇒ pr_i x=pr_i y)

    # extensionnalite_produit : (x∈∏ et y∈∏ et graphe x et graphe y
    #   et (∀i)(i∈I ⇒ pr_i x=pr_i y)) ⇒ x=y   (idx « i » = celui de proj_eq)
    ext = extensionnalite_produit(vfam, vI, vx, vy, i)
    hyp_ext = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        x_in, y_in), gx), gy), proj_eq)
    x_eq_y = N.modus_ponens(hyp_ext, ext)             # x = y
    anti_body = N.loi_deduction(cible_ante, x_eq_y)
    antisym_P = N.generalisation(x, N.generalisation(y, anti_body))

    # ── (c) réflexivité implicite de P : P{x,y} ⇒ (P{x,x} et P{y,y}) ──────────────
    hPxy = N.assume(P(vx, vy))
    h_iI3 = N.assume(appartient(vi, vI))
    Rxy_i3 = N.modus_ponens(h_iI3, instancie(hPxy, vi))
    ref_i = N.modus_ponens(h_iI3, instancie(Href, vi))
    ref_proj = instancie(instancie(ref_i, pr(vx)), pr(vy))
    RxxRyy_i = N.modus_ponens(Rxy_i3, ref_proj)
    Rxx_i = conjonction_elim_gauche(RxxRyy_i)
    Ryy_i = conjonction_elim_droite(RxxRyy_i)
    Pxx_iI = N.loi_deduction(appartient(vi, vI), Rxx_i)
    Pyy_iI = N.loi_deduction(appartient(vi, vI), Ryy_i)
    Pxx = N.generalisation(i, Pxx_iI)
    Pyy = N.generalisation(i, Pyy_iI)
    ref_body = N.loi_deduction(P(vx, vy), conjonction_intro(Pxx, Pyy))
    refimpl_P = N.generalisation(x, N.generalisation(y, ref_body))

    concl = conjonction_intro(conjonction_intro(trans_P, antisym_P), refimpl_P)
    return N.loi_deduction(ante, concl)


__all__ = ["antisymetrie_sur_produit", "ordre_produit_est_ordre"]
