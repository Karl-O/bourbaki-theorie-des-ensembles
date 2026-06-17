"""§III.1 — TRANSPORT des AXIOMES D'ORDRE : l'ordre INDUIT sur une partie et
l'ordre PRODUIT sont (à la convention « relation R{x,y} = fonction Python ») des
relations d'ordre / de préordre.  (E.III.1.1, Exemple 2 ; E.III.1.4.)

Pendant « niveau RELATION » (R : (Terme,Terme)↦Formule) des théorèmes de
`ensembles_ordre_relation.py` qui, eux, raisonnent sur le GRAPHE G (où
`ordre_induit_sur_partie` est DÉJÀ clos pour l'encodage graphe).  Ici les
hypothèses portent sur la RELATION R elle-même, comme dans `ensembles_ordre.py`
(ordre_oppose_est_ordre, …) et la définition `ordre_induit` / `ordre_produit`.

ÉNONCÉS (dérivés ; rien postulé, theorie=22) :

  (1) `ordre_induit_est_ordre`  ⊢ est_relation_ordre(R) ⇒ est_relation_ordre(R_E),
      où  R_E := ordre_induit(R, E)  =  λ(a,b). (R{a,b} et a∈E et b∈E)  (E.III.1.1,
      Exemple 2).  Les TROIS conditions transportent directement :
        • transitivité  : R{x,y}∧R{y,z}⇒R{x,z} (transitivité de R) ; x∈E, z∈E sont
          portés par les conjoints d'appartenance des deux hypothèses ;
        • antisymétrie  : R_E{x,y}∧R_E{y,x} contient R{x,y}∧R{y,x} ⇒ x=y (antisym R) ;
        • réflexivité implicite : R_E{x,y} ⇒ (R_E{x,x} et R_E{y,y}) — R{x,x}, R{y,y}
          viennent de ordre_reflexif_implicite(R) ; x∈E, y∈E sont déjà dans R_E{x,y}.
      THÉORÈME CLOS (0 hyp ; conclusion = l'implication énoncée).

  (2) `ordre_produit_est_preordre`  ⊢
        ( (∀ι)(ι∈I ⇒ ordre_transitif(R_ι))  et  (∀ι)(ι∈I ⇒ ordre_reflexif_implicite(R_ι)) )
            ⇒  est_relation_preordre(P),
      où  P := relation_ordre_produit(Rfam, I) ,  R_ι := Rfam(ι)  (E.III.1.4).  Les deux
      conditions du PRÉORDRE (transitivité, réflexivité implicite) transportent
      POINTWISE : pour chaque ι∈I, l'inégalité produit en ι EST l'inégalité du facteur
      R_ι en (pr_ι x, pr_ι y), et la propriété de R_ι s'y applique terme à terme.

      ⚠ L'ANTISYMÉTRIE n'est PAS incluse : au niveau produit elle exigerait
      l'EXTENSIONNALITÉ du produit « x = y ⟺ (∀ι∈I) pr_ι x = pr_ι y » (de
      pr_ι x = pr_ι y pour tout ι, conclure x=y), lemme NON disponible (cf. RÉSIDU
      explicite en docstring de la fonction).  Le préordre est exactement « ordre
      moins antisymétrie » (E.III.1.2) — les deux clauses qui transportent sans
      extensionnalité.  THÉORÈME CLOS sous ces deux SEULES hypothèses honnêtes.

──────────────────────────────────────────────────────────────────────────────
Binders : au niveau PRODUIT les points sont nommés « xp, yp, zp » (≠ a,b,c des
binders de ordre_transitif/_antisymetrique du FACTEUR) pour qu'aucune
instanciation de la propriété du facteur en (pr_ι xp, …) ne capture.  L'indice est
« i » (défaut de ordre_produit).  RIEN dans theorie_ensembles n'est touché (22).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, impl, appartient, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)


# ════════════════════════════════════════════════════════════════════════════
#  (1) L'ordre INDUIT sur une partie est une relation d'ordre  (E.III.1.1, Ex. 2)
# ════════════════════════════════════════════════════════════════════════════
def ordre_induit_est_ordre(R, e="E", x="xp", y="yp", z="zp"):
    """⊢ est_relation_ordre(R) ⇒ est_relation_ordre(ordre_induit(R, E)).

    R_E{a,b} := (R{a,b} et a∈E et b∈E).  Les trois conditions de la relation
    d'ordre se transportent à R_E (E.III.1.1, Exemple 2).  CLOS (0 hyp).

    R = relation (fonction (Terme,Terme)→Formule).  Si R est fournie sous forme
    « graphe » a≤b := (a,b)∈G, la conclusion est l'implication portant sur la
    relation induite λ(a,b).(((a,b)∈G et a∈E) et b∈E)."""
    ve = e if not isinstance(e, str) else var(e)
    vx, vy, vz = var(x), var(y), var(z)
    R_E = E.ordre_induit(R, ve)                       # λ(a,b). ((R{a,b} et a∈E) et b∈E)

    hyp = E.est_relation_ordre(R, x, y, z)
    H = N.assume(hyp)
    Htr = conjonction_elim_gauche(conjonction_elim_gauche(H))   # ordre_transitif(R)
    Has = conjonction_elim_droite(conjonction_elim_gauche(H))   # ordre_antisymetrique(R)
    Href = conjonction_elim_droite(H)                            # R{x,y}⇒(R{x,x} et R{y,y})

    # ── (a) transitivité de R_E : (R_E{x,y} et R_E{y,z}) ⇒ R_E{x,z} ──────────────
    hxy = N.assume(R_E(vx, vy))                       # (R{x,y} et x∈E) et y∈E
    hyz = N.assume(R_E(vy, vz))                       # (R{y,z} et y∈E) et z∈E
    Rxy = conjonction_elim_gauche(conjonction_elim_gauche(hxy))   # R{x,y}
    x_in = conjonction_elim_droite(conjonction_elim_gauche(hxy))  # x∈E
    Ryz = conjonction_elim_gauche(conjonction_elim_gauche(hyz))   # R{y,z}
    z_in = conjonction_elim_droite(hyz)                           # z∈E
    tr_i = instancie(instancie(instancie(Htr, vx), vy), vz)       # (R{x,y} et R{y,z})⇒R{x,z}
    Rxz = N.modus_ponens(conjonction_intro(Rxy, Ryz), tr_i)       # R{x,z}
    RE_xz = conjonction_intro(conjonction_intro(Rxz, x_in), z_in)  # R_E{x,z}
    tr_body = N.loi_deduction(R_E(vy, vz), RE_xz)                 # R_E{y,z}⇒R_E{x,z}
    tr_body = N.loi_deduction(R_E(vx, vy), tr_body)              # R_E{x,y}⇒(R_E{y,z}⇒R_E{x,z})
    # remettre en conjonction (R_E{x,y} et R_E{y,z})⇒R_E{x,z}
    hconj = N.assume(et(R_E(vx, vy), R_E(vy, vz)))
    tr_conj = N.modus_ponens(conjonction_elim_droite(hconj),
                             N.modus_ponens(conjonction_elim_gauche(hconj), tr_body))
    tr_conj = N.loi_deduction(et(R_E(vx, vy), R_E(vy, vz)), tr_conj)
    trans_RE = N.generalisation(x, N.generalisation(y, N.generalisation(z, tr_conj)))

    # ── (b) antisymétrie de R_E : (R_E{x,y} et R_E{y,x}) ⇒ x=y ────────────────────
    aconj = N.assume(et(R_E(vx, vy), R_E(vy, vx)))
    a_xy = conjonction_elim_gauche(aconj)             # R_E{x,y}
    a_yx = conjonction_elim_droite(aconj)             # R_E{y,x}
    aRxy = conjonction_elim_gauche(conjonction_elim_gauche(a_xy))   # R{x,y}
    aRyx = conjonction_elim_gauche(conjonction_elim_gauche(a_yx))   # R{y,x}
    as_i = instancie(instancie(Has, vx), vy)          # (R{x,y} et R{y,x})⇒x=y
    x_eq_y = N.modus_ponens(conjonction_intro(aRxy, aRyx), as_i)    # x=y
    as_body = N.loi_deduction(et(R_E(vx, vy), R_E(vy, vx)), x_eq_y)
    antisym_RE = N.generalisation(x, N.generalisation(y, as_body))

    # ── (c) réflexivité implicite : R_E{x,y} ⇒ (R_E{x,x} et R_E{y,y}) ─────────────
    rxy = N.assume(R_E(vx, vy))
    rRxy = conjonction_elim_gauche(conjonction_elim_gauche(rxy))   # R{x,y}
    rx_in = conjonction_elim_droite(conjonction_elim_gauche(rxy))  # x∈E
    ry_in = conjonction_elim_droite(rxy)                           # y∈E
    ref_i = instancie(instancie(Href, vx), vy)        # R{x,y}⇒(R{x,x} et R{y,y})
    RxxRyy = N.modus_ponens(rRxy, ref_i)              # R{x,x} et R{y,y}
    Rxx = conjonction_elim_gauche(RxxRyy)             # R{x,x}
    Ryy = conjonction_elim_droite(RxxRyy)             # R{y,y}
    RE_xx = conjonction_intro(conjonction_intro(Rxx, rx_in), rx_in)  # R_E{x,x}
    RE_yy = conjonction_intro(conjonction_intro(Ryy, ry_in), ry_in)  # R_E{y,y}
    ref_body = N.loi_deduction(R_E(vx, vy), conjonction_intro(RE_xx, RE_yy))
    refimpl_RE = N.generalisation(x, N.generalisation(y, ref_body))

    concl = conjonction_intro(conjonction_intro(trans_RE, antisym_RE), refimpl_RE)
    return N.loi_deduction(hyp, concl)


# ════════════════════════════════════════════════════════════════════════════
#  (2) L'ordre PRODUIT est une relation de PRÉORDRE  (E.III.1.4)
# ════════════════════════════════════════════════════════════════════════════
def ordre_produit_est_preordre(Rfam, I="I", i="i", x="xp", y="yp", z="zp",
                               a="a", b="b", c="c"):
    """⊢ ( (∀ι)(ι∈I ⇒ ordre_transitif(R_ι))  et  (∀ι)(ι∈I ⇒ ordre_reflexif_implicite(R_ι)) )
          ⇒  est_relation_preordre(relation_ordre_produit(Rfam, I)).

    P{x,y} := (∀ι)(ι∈I ⇒ R_ι{pr_ι x, pr_ι y}),  R_ι := Rfam(ι)  (ordre produit,
    E.III.1.4).  Les deux conditions du PRÉORDRE transportent POINTWISE :

      • transitivité de P : fixé ι∈I, P{x,y} et P{y,z} donnent R_ι{pr_ι x, pr_ι y}
        et R_ι{pr_ι y, pr_ι z} ; la transitivité de R_ι (hypothèse, instanciée aux
        projections) donne R_ι{pr_ι x, pr_ι z} ; généraliser ι ⇒ P{x,z} ;
      • réflexivité implicite de P : fixé ι∈I, P{x,y} donne R_ι{pr_ι x, pr_ι y} ;
        ordre_reflexif_implicite(R_ι) (instanciée) donne R_ι{pr_ι x, pr_ι x} et
        R_ι{pr_ι y, pr_ι y} ; généraliser ⇒ P{x,x} et P{y,y}.

    🔴 RÉSIDU EXPLICITE (frontière) : l'ANTISYMÉTRIE n'est PAS prouvée ici.  Au
    niveau produit elle se réduit, par antisymétrie de chaque R_ι, à
    « (∀ι∈I) pr_ι x = pr_ι y », puis exige l'EXTENSIONNALITÉ du produit
    (« projections toutes égales ⇒ points égaux »), lemme NON présent dans le
    dépôt.  Le théorème ci-dessous est donc HONNÊTEMENT un PRÉORDRE (E.III.1.2),
    sous les DEUX hypothèses pointwise.  CLOS (les deux hyps sont l'antécédent de
    l'implication ; aucune autre hypothèse résiduelle)."""
    vI = I if not isinstance(I, str) else var(I)
    vi = var(i)
    vx, vy, vz = var(x), var(y), var(z)
    P = V.relation_ordre_produit(Rfam, I, i)          # λ(x,y). (∀ι)(ι∈I ⇒ R_ι{pr_ι x, pr_ι y})
    R_i = Rfam(vi)

    # antécédent : transitivité ET réflexivité-implicite POINTWISE de la famille
    htr = pourtout(i, impl(appartient(vi, vI), E.ordre_transitif(R_i, a, b, c)))
    href = pourtout(i, impl(appartient(vi, vI), E.ordre_reflexif_implicite(R_i, a, b)))
    ante = et(htr, href)
    H = N.assume(ante)
    Htr = conjonction_elim_gauche(H)                  # (∀ι)(ι∈I ⇒ ordre_transitif(R_ι))
    Href = conjonction_elim_droite(H)                 # (∀ι)(ι∈I ⇒ ordre_reflexif_implicite(R_ι))

    # projections (pr_ι d'un point = valeur(point, ι))
    def pr(pt):
        return E.projection_indice(pt, vi)

    # ── (a) transitivité de P : (P{x,y} et P{y,z}) ⇒ P{x,z} ──────────────────────
    hconj = N.assume(et(P(vx, vy), P(vy, vz)))
    Pxy = conjonction_elim_gauche(hconj)              # (∀ι)(ι∈I ⇒ R_ι{pr_ι x, pr_ι y})
    Pyz = conjonction_elim_droite(hconj)              # (∀ι)(ι∈I ⇒ R_ι{pr_ι y, pr_ι z})
    # corps en ι : ι∈I ⇒ R_ι{pr_ι x, pr_ι z}
    h_iI = N.assume(appartient(vi, vI))
    Rxy_i = N.modus_ponens(h_iI, instancie(Pxy, vi))  # R_ι{pr_ι x, pr_ι y}
    Ryz_i = N.modus_ponens(h_iI, instancie(Pyz, vi))  # R_ι{pr_ι y, pr_ι z}
    tr_i = N.modus_ponens(h_iI, instancie(Htr, vi))   # ordre_transitif(R_ι)
    # ordre_transitif(R_ι) = (∀a)(∀b)(∀c)((R_ι{a,b} et R_ι{b,c})⇒R_ι{a,c})
    tr_proj = instancie(instancie(instancie(tr_i, pr(vx)), pr(vy)), pr(vz))
    Rxz_i = N.modus_ponens(conjonction_intro(Rxy_i, Ryz_i), tr_proj)   # R_ι{pr_ι x, pr_ι z}
    tr_iI = N.loi_deduction(appartient(vi, vI), Rxz_i)                 # ι∈I ⇒ R_ι{pr_ι x, pr_ι z}
    Pxz = N.generalisation(i, tr_iI)                  # P{x,z}
    tr_body = N.loi_deduction(et(P(vx, vy), P(vy, vz)), Pxz)
    trans_P = N.generalisation(x, N.generalisation(y, N.generalisation(z, tr_body)))

    # ── (b) réflexivité implicite de P : P{x,y} ⇒ (P{x,x} et P{y,y}) ──────────────
    hPxy = N.assume(P(vx, vy))
    h_iI2 = N.assume(appartient(vi, vI))
    Rxy_i2 = N.modus_ponens(h_iI2, instancie(hPxy, vi))   # R_ι{pr_ι x, pr_ι y}
    ref_i = N.modus_ponens(h_iI2, instancie(Href, vi))    # ordre_reflexif_implicite(R_ι)
    # ordre_reflexif_implicite(R_ι) = (∀a)(∀b)(R_ι{a,b}⇒(R_ι{a,a} et R_ι{b,b}))
    ref_proj = instancie(instancie(ref_i, pr(vx)), pr(vy))   # R_ι{pr_ι x,pr_ι y}⇒(R_ι{pr_ι x,pr_ι x} et R_ι{pr_ι y,pr_ι y})
    RxxRyy_i = N.modus_ponens(Rxy_i2, ref_proj)
    Rxx_i = conjonction_elim_gauche(RxxRyy_i)         # R_ι{pr_ι x, pr_ι x}
    Ryy_i = conjonction_elim_droite(RxxRyy_i)         # R_ι{pr_ι y, pr_ι y}
    Pxx_iI = N.loi_deduction(appartient(vi, vI), Rxx_i)    # ι∈I ⇒ R_ι{pr_ι x, pr_ι x}
    Pyy_iI = N.loi_deduction(appartient(vi, vI), Ryy_i)    # ι∈I ⇒ R_ι{pr_ι y, pr_ι y}
    Pxx = N.generalisation(i, Pxx_iI)                 # P{x,x}
    Pyy = N.generalisation(i, Pyy_iI)                 # P{y,y}
    ref_body = N.loi_deduction(P(vx, vy), conjonction_intro(Pxx, Pyy))
    refimpl_P = N.generalisation(x, N.generalisation(y, ref_body))

    concl = conjonction_intro(trans_P, refimpl_P)     # est_relation_preordre(P)
    return N.loi_deduction(ante, concl)


__all__ = ["ordre_induit_est_ordre", "ordre_produit_est_preordre"]
