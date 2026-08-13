"""§III.1 n°12 — PROPOSITION 12 (E.III.1.14) : critère de BORNE SUPÉRIEURE dans un
ensemble TOTALEMENT ordonné.

Énoncé Bourbaki (verbatim, E III.14) :

  « PROPOSITION 12. — Soient E un ensemble totalement ordonné, X une partie de E.
  Pour qu'un élément b ∈ E soit borne supérieure de X dans E, il faut et il suffit
  que : 1° b soit un majorant de X ; 2° pour tout c ∈ E tel que c < b, il existe
  x ∈ X tel que c < x ≤ b. »

Convention « graphe G » (ensembles_ordre_relation) : x≤y := (x,y)∈G ; ordre STRICT
codé inline comme dans le dépôt (cf. `_strict`) :
  c < b      :=  ((c,b)∈G et c≠b)
  c < x ≤ b  :=  ((c,x)∈G et c≠x et (x,b)∈G)

ÉNONCÉ FORMALISÉ (conditionnel-honnête) — CONCLUSION (cf. `borne_sup_critere_total`) :

  ⊢  borne_superieure(G,X,b,E) ⇔ ( majorant(G,X,b,E) et critère 2° )

  Hypothèses HONNÊTES (antécédents Bourbaki) : { totalement_ordonne(G,E), X⊂E, b∈E } ;
  la conclusion-équivalence ne figure PAS parmi les hypothèses.

NOTE DE FIDÉLITÉ (importante).  Le strict « c < x » du 2° est conservé (c≠x),
conformément au texte de Bourbaki.  L'omettre (coder « c < x » par « c ≤ x »)
rendrait l'équivalence FAUSSE et le sens ⇐ non prouvable : contre-exemple
E={0,1,2}, X={1}, b=2 — 2 majore {1} et tout c≤2 est « dépassé » par 1 (c≤1≤2),
pourtant sup{1}=1≠2.  Le < strict rétablit À LA FOIS la fidélité au PDF et la vérité
de l'énoncé.

STRATÉGIE (détaillée dans les docstrings de `_sens_directe` / `_sens_reciproque`).
conjonction_intro de deux loi_deduction (les deux sens).  Les deux raisonnements
combinent TOTALITÉ + ANTISYMÉTRIE comme le gabarit `maximal_est_plus_grand_si_total`
(E.III.1.12) : comparer par totalité, recoller par antisymétrie / réflexivité+Leibniz.
  ⇒ : 1° = projection gauche ; 2° par contraposée (si aucun x ne dépasse c, alors c
      majore X, donc b≤c≤b, antisym ⇒ b=c, contredit c≠b).
  ⇐ : b majore (1°) ; b ≤ tout majorant y (totalité + 2° en c:=y, antisym sur le
      témoin contredit y≠x).

theorie_ensembles INTANGIBLE = 22 : tout est DÉRIVÉ (primitives N.* du noyau LCF),
aucun axiome nouveau.  STATUT : CLOS sous les 3 hypothèses honnêtes.  (E.III.1.14,
Proposition 12.)
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu, equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    totalement_ordonne, majorant, borne_superieure, _couple_dans,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_treillis_props import (
    _ex_falso,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# liants internes FIXÉS (évitent toute capture du point courant) ────────────────
_XMAJ = "xs12"      # liant des prédicats majorant(...) ici
_YPP = "ys12"       # liant du « plus petit majorant » de borne_superieure ici
_CCRIT = "cs12"     # liant du ∀c du critère 2°
_XEX = "xe12"       # liant du ∃x du critère 2°


def _critere2(G, X, b, E_set):
    """Condition 2° (codage STRICT) : (∀c)( c<b ⇒ ∃x(x∈X et c<x≤b) ), avec
    c<b := ((c,b)∈G et c≠b) et c<x≤b := ((c,x)∈G et c≠x et (x,b)∈G)."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    vc, vx = var(_CCRIT), var(_XEX)
    c_lt_b = et(et(appartient(vc, vE), _couple_dans(vc, vb, G)), non(egal(vc, vb)))
    temoin = et(et(et(appartient(vx, vX), _couple_dans(vc, vx, G)), non(egal(vc, vx))),
                _couple_dans(vx, vb, G))
    return pourtout(_CCRIT, impl(c_lt_b, existe(_XEX, temoin)))


def _membre_droit(G, X, b, E_set):
    """Membre droit de l'équivalence : majorant(G,X,b,E) et critère 2°."""
    return et(majorant(G, X, _t(b), E_set, _XMAJ), _critere2(G, X, b, E_set))


def _bsup(G, X, b, E_set):
    """borne_superieure(G,X,b,E) avec liants internes FIXÉS (_XMAJ, _YPP)."""
    return borne_superieure(G, X, _t(b), E_set, _XMAJ, _YPP)


def _cible(G="Gs12", X="Xs12", b="bs12", E_set="Es12"):
    """Conclusion attendue : l'ÉQUIVALENCE de la Proposition 12."""
    return equiv(_bsup(G, X, b, E_set), _membre_droit(G, X, b, E_set))


# ════════════════════════════════════════════════════════════════════════════
#  SENS ⇒ :  borne_superieure(G,X,b,E)  ⇒  (1° et 2°)
# ════════════════════════════════════════════════════════════════════════════
def _sens_directe(G, X, b, E_set, comparables, refl_E, antisym, Hsub, Hb):
    """Sous {Htot, X⊂E, b∈E} : borne_superieure(G,X,b,E) ⇒ (majorant(G,X,b,E) et critère 2°)."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    Hbsup = N.assume(_bsup(G, X, b, E_set))               # maj(b) et (∀y)(maj(y)⇒(b,y)∈G)
    maj_b = conjonction_elim_gauche(Hbsup)                # majorant(G,X,b,E)   = 1°
    b_least = conjonction_elim_droite(Hbsup)              # (∀y)(maj(y)⇒(b,y)∈G)
    b_maj_body = conjonction_elim_droite(maj_b)           # (∀x)(x∈X⇒(x,b)∈G)
    # ── 2° : (∀c)( c<b ⇒ ∃x(x∈X et c<x≤b) ) ───────────────────────────────────
    vc, vx = var(_CCRIT), var(_XEX)
    c_lt_b = et(et(appartient(vc, vE), _couple_dans(vc, vb, G)), non(egal(vc, vb)))
    Hc = N.assume(c_lt_b)
    c_in_E = conjonction_elim_gauche(conjonction_elim_gauche(Hc))   # c∈E
    cb_G = conjonction_elim_droite(conjonction_elim_gauche(Hc))     # (c,b)∈G
    c_neq_b = conjonction_elim_droite(Hc)                          # c≠b
    temoin = et(et(et(appartient(vx, vX), _couple_dans(vc, vx, G)), non(egal(vc, vx))),
                _couple_dans(vx, vb, G))
    but = existe(_XEX, temoin)
    # tiers_exclu sur l'existence du témoin ; si oui trivial, si non ex falso
    disj = tiers_exclu(but)
    casA = N.loi_deduction(but, N.assume(but))            # (∃x …) ⇒ (∃x …)
    Hno = N.assume(non(but))                              # ¬(∃x …)
    # ¬∃ ⇒ c MAJORE X ⇒ (b,c)∈G ; avec (c,b)∈G antisym ⇒ b=c, contredit c≠b
    c_maj_X = _c_majore_X(G, X, b, E_set, comparables, refl_E, Hsub,
                          c_in_E, b_maj_body, Hno)        # (∀xx)(xx∈X⇒(xx,c)∈G)
    maj_c = conjonction_intro(c_in_E, c_maj_X)            # majorant(G,X,c,E)
    bc_G = N.modus_ponens(maj_c, instancie(b_least, vc))  # (b,c)∈G
    antisym_bc = instancie(instancie(antisym, vb), vc)    # ((b,c)∈G et (c,b)∈G)⇒b=c
    b_eq_c = N.modus_ponens(conjonction_intro(bc_G, cb_G), antisym_bc)   # b=c
    c_eq_b = N.modus_ponens(b_eq_c, symetrie(vb, vc))     # c=b
    contra = _ex_falso(c_eq_b, c_neq_b, but)              # (∃x …)  (ex falso : c=b et c≠b)
    casB = N.loi_deduction(non(but), contra)
    crit_imp = N.loi_deduction(c_lt_b, cas(disj, casA, casB))   # c<b ⇒ (∃x …)
    crit2 = N.generalisation(_CCRIT, crit_imp)           # critère 2°
    membre_droit = conjonction_intro(maj_b, crit2)
    return N.loi_deduction(_bsup(G, X, b, E_set), membre_droit)


def _c_majore_X(G, X, b, E_set, comparables, refl_E, Hsub, c_in_E, b_maj_body, Hno):
    """⊢ (∀xx)(xx∈X ⇒ (xx,c)∈G) (« c majore X ») sous {¬(∃témoin), c∈E, b majore X, X⊂E}.
    Pour xx∈X (donc xx∈E) : totalité ⇒ (c,xx)∈G ou (xx,c)∈G ; le 1er cas est traité par
    `_branche_c_le_xx`, le 2nd est trivial."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    vc, vxx = var(_CCRIT), var(_XMAJ)
    cible = _couple_dans(vxx, vc, G)                      # but : (xx,c)∈G
    Hxx = N.assume(appartient(vxx, vX))                  # xx∈X
    xx_in_E = N.modus_ponens(Hxx, instancie(Hsub, vxx))  # xx∈E
    xxb_G = N.modus_ponens(Hxx, instancie(b_maj_body, vxx))   # (xx,b)∈G   (b majore X)
    comp_cxx = instancie(instancie(comparables, vc), vxx)
    disj = N.modus_ponens(conjonction_intro(c_in_E, xx_in_E), comp_cxx)   # (c,xx)∈G ou (xx,c)∈G
    # cas (c,xx)∈G : helper ; cas (xx,c)∈G : trivial
    cas1 = N.loi_deduction(_couple_dans(vc, vxx, G), _branche_c_le_xx(
        G, X, b, E_set, refl_E, Hno, xx_in_E, xxb_G, Hxx, cible))
    cas2 = N.loi_deduction(cible, N.assume(cible))       # (xx,c)∈G ⇒ (xx,c)∈G
    body = N.loi_deduction(appartient(vxx, vX), cas(disj, cas1, cas2))   # xx∈X ⇒ (xx,c)∈G
    return N.generalisation(_XMAJ, body)


def _branche_c_le_xx(G, X, b, E_set, refl_E, Hno, xx_in_E, xxb_G, Hxx, cible):
    """Branche (c,xx)∈G du « c majore X » : produit (xx,c)∈G.  tiers_exclu sur c=xx :
    si c=xx, réflexivité (xx,xx)∈G transportée en (xx,c)∈G (Leibniz) ; si c≠xx, le
    quadruplet (xx∈X, (c,xx)∈G, c≠xx, (xx,b)∈G) est un témoin du ∃ ⇒ ex falso (¬∃)."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    vc, vxx, vx = var(_CCRIT), var(_XMAJ), var(_XEX)
    Hcxx = N.assume(_couple_dans(vc, vxx, G))            # (c,xx)∈G
    disj_eq = tiers_exclu(egal(vc, vxx))
    # branche c=xx : (xx,xx)∈G (réflexivité) → (xx,c)∈G  (Leibniz S6, 2e coord.)
    Heq = N.assume(egal(vc, vxx))                        # c=xx
    xx_eq_c = N.modus_ponens(Heq, symetrie(vc, vxx))     # xx=c
    xxxx = N.modus_ponens(xx_in_E, instancie(refl_E, vxx))   # (xx,xx)∈G
    leib = N.s6(vxx, vc, "ws12", _couple_dans(vxx, var("ws12"), G))   # (xx=c)⇒((xx,xx)∈G⇔(xx,c)∈G)
    xxc_eq = N.modus_ponens(xxxx, equivalence_avant(N.modus_ponens(xx_eq_c, leib)))   # (xx,c)∈G
    casEq = N.loi_deduction(egal(vc, vxx), xxc_eq)
    # branche c≠xx : (xx) est un témoin du ∃ → contredit ¬∃ → ex falso
    Hneq = N.assume(non(egal(vc, vxx)))                  # c≠xx
    temoin_thm = conjonction_intro(
        conjonction_intro(conjonction_intro(Hxx, Hcxx), Hneq), xxb_G)   # le témoin (xx)
    temoin_pat = et(et(et(appartient(vx, vX), _couple_dans(vc, vx, G)), non(egal(vc, vx))),
                    _couple_dans(vx, vb, G))
    ex_temoin = N.modus_ponens(temoin_thm, N.s5(temoin_pat, vxx, _XEX))   # (∃x témoin)
    contra = _ex_falso(ex_temoin, Hno, cible)            # (xx,c)∈G   (ex falso : ∃ et ¬∃)
    casNeq = N.loi_deduction(non(egal(vc, vxx)), contra)
    return cas(disj_eq, casEq, casNeq)                   # (xx,c)∈G   (porte Hcxx en hyp)


# ════════════════════════════════════════════════════════════════════════════
#  SENS ⇐ :  (1° et 2°)  ⇒  borne_superieure(G,X,b,E)
# ════════════════════════════════════════════════════════════════════════════
def _sens_reciproque(G, X, b, E_set, comparables, refl_E, antisym, Hb):
    """Sous {Htot, b∈E} : (majorant(G,X,b,E) et critère 2°) ⇒ borne_superieure(G,X,b,E)."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    b_in_E = Hb                                          # b∈E  (théorème hypothèse)
    Hrhs = N.assume(_membre_droit(G, X, b, E_set))       # maj(b) et critère 2°
    maj_b = conjonction_elim_gauche(Hrhs)                # majorant(G,X,b,E)
    crit2 = conjonction_elim_droite(Hrhs)               # (∀c)(c<b ⇒ ∃x …)

    # borne_superieure = maj_b et (∀y)(maj(y) ⇒ (b,y)∈G).  Reste le 2e conjonct.
    vy = var(_YPP)
    Hy = N.assume(majorant(G, X, vy, E_set, _XMAJ))      # y∈E et (∀x)(x∈X⇒(x,y)∈G)
    y_in_E = conjonction_elim_gauche(Hy)                 # y∈E
    y_maj_body = conjonction_elim_droite(Hy)            # (∀x)(x∈X⇒(x,y)∈G)
    cible = _couple_dans(vb, vy, G)                      # but : (b,y)∈G
    comp_by = instancie(instancie(comparables, vb), vy)
    disj = N.modus_ponens(conjonction_intro(b_in_E, y_in_E), comp_by)   # (b,y)∈G ou (y,b)∈G
    cas1 = N.loi_deduction(cible, N.assume(cible))       # (b,y)∈G ⇒ (b,y)∈G  (trivial)
    cas2 = N.loi_deduction(_couple_dans(vy, vb, G), _cas_y_le_b(
        G, X, b, E_set, refl_E, antisym, crit2, y_in_E, y_maj_body, cible, b_in_E))
    by_G = cas(disj, cas1, cas2)                         # (b,y)∈G   (sous {Hy, …})
    body = N.loi_deduction(majorant(G, X, vy, E_set, _XMAJ), by_G)   # maj(y)⇒(b,y)∈G
    plus_petit = N.generalisation(_YPP, body)            # (∀y)(maj(y)⇒(b,y)∈G)
    bsup = conjonction_intro(maj_b, plus_petit)          # borne_superieure(G,X,b,E)
    return N.loi_deduction(_membre_droit(G, X, b, E_set), bsup)


def _cas_y_le_b(G, X, b, E_set, refl_E, antisym, crit2, y_in_E, y_maj_body, cible, b_in_E):
    """Branche (y,b)∈G du « plus petit majorant » : produit (b,y)∈G.  tiers_exclu sur
    y=b : si y=b, réflexivité (b,b)∈G transportée en (b,y)∈G (Leibniz) ; si y≠b, le
    critère 2° en c:=y fournit un témoin contradictoire (cf. `_temoin_contradiction`).
    `b_in_E` = hypothèse honnête b∈E (passée, non ré-assumée)."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    vy = var(_YPP)
    Hyb = N.assume(_couple_dans(vy, vb, G))              # (y,b)∈G
    disj_eq = tiers_exclu(egal(vy, vb))
    # branche y=b : (b,b)∈G (réflexivité) → (b,y)∈G (Leibniz, b=y)
    Heq = N.assume(egal(vy, vb))                        # y=b
    b_eq_y = N.modus_ponens(Heq, symetrie(vy, vb))      # b=y
    bb = N.modus_ponens(b_in_E, instancie(refl_E, vb))  # (b,b)∈G
    leib = N.s6(vb, vy, "ws12", _couple_dans(vb, var("ws12"), G))   # (b=y)⇒((b,b)∈G⇔(b,y)∈G)
    by_eq = N.modus_ponens(bb, equivalence_avant(N.modus_ponens(b_eq_y, leib)))   # (b,y)∈G
    casEq = N.loi_deduction(egal(vy, vb), by_eq)
    # branche y≠b : critère 2° en y → témoin → antisym → contradiction y≠x
    Hneq = N.assume(non(egal(vy, vb)))                  # y≠b
    y_lt_b = conjonction_intro(conjonction_intro(y_in_E, Hyb), Hneq)   # y<b = (y∈E et (y,b)∈G et y≠b)
    crit_y = instancie(crit2, vy)                       # (y<b) ⇒ (∃x …)
    ex_x = N.modus_ponens(y_lt_b, crit_y)               # (∃x)(x∈X et (y,x)∈G et y≠x et (x,b)∈G)
    contra_x = _temoin_contradiction(G, X, b, E_set, antisym, y_maj_body, cible)
    by_from_ex = N.modus_ponens(ex_x, contra_x)         # (b,y)∈G   (∃-élimination)
    casNeq = N.loi_deduction(non(egal(vy, vb)), by_from_ex)
    return cas(disj_eq, casEq, casNeq)                  # (b,y)∈G


def _temoin_contradiction(G, X, b, E_set, antisym, y_maj_body, cible):
    """⊢ (∃x témoin) ⇒ (b,y)∈G, par ∃-élimination.  Témoin x : x∈X, (y,x)∈G, y≠x,
    (x,b)∈G.  y majore X ⇒ (x,y)∈G ; antisym((x,y),(y,x)) ⇒ x=y, contredit y≠x ⇒ ex falso."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)
    vy, vx = var(_YPP), var(_XEX)
    temoin = et(et(et(appartient(vx, vX), _couple_dans(vy, vx, G)), non(egal(vy, vx))),
                _couple_dans(vx, vb, G))
    Hw = N.assume(temoin)
    x_in_X = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(Hw)))  # x∈X
    yx_G = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(Hw)))    # (y,x)∈G
    y_neq_x = conjonction_elim_droite(conjonction_elim_gauche(Hw))                          # y≠x
    # y majore X : x∈X ⇒ (x,y)∈G
    xy_G = N.modus_ponens(x_in_X, instancie(y_maj_body, vx))   # (x,y)∈G
    # antisymétrie en (x,y) : ((x,y)∈G et (y,x)∈G) ⇒ x=y
    antisym_xy = instancie(instancie(antisym, vx), vy)
    x_eq_y = N.modus_ponens(conjonction_intro(xy_G, yx_G), antisym_xy)   # x=y
    y_eq_x = N.modus_ponens(x_eq_y, symetrie(vx, vy))    # y=x
    contra = _ex_falso(y_eq_x, y_neq_x, cible)           # (b,y)∈G   (ex falso : y=x et y≠x)
    sous = N.loi_deduction(temoin, contra)               # témoin ⇒ (b,y)∈G
    return existe_elimination(sous, _XEX)                # (∃x témoin) ⇒ (b,y)∈G


# ════════════════════════════════════════════════════════════════════════════
#  PROPOSITION 12 (E.III.1.14) — assemblage des deux sens
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §1.12 Prop.12 | E III.14 L.27-37 | PDF p.117
def borne_sup_critere_total(G="Gs12", X="Xs12", b="bs12", E_set="Es12",
                            x="xs12tot", y="ys12tot", z="zs12tot"):
    """🎯 { totalement_ordonne(G,E), X⊂E, b∈E }
            ⊢ ( borne_superieure(G,X,b,E)
                ⇔ ( majorant(G,X,b,E)
                    et (∀c)( (c∈E et (c,b)∈G et c≠b)
                             ⇒ (∃x)( x∈X et (c,x)∈G et c≠x et (x,b)∈G ) ) ) ).

    PROPOSITION 12 (E.III.1.14) : dans un ensemble TOTALEMENT ordonné, b est borne
    supérieure de X ssi b majore X et tout c < b est dépassé dans X (∃x∈X, c<x≤b).
    Preuve : conjonction des deux implications (loi_deduction chacune).  Le < est
    codé STRICT (c≠x) — fidèle au PDF et nécessaire à la vérité de l'énoncé."""
    vG, vX, vb, vE = _t(G), _t(X), _t(b), _t(E_set)

    # ── les TROIS hypothèses HONNÊTES ─────────────────────────────────────────
    Htot = N.assume(totalement_ordonne(G, E_set, x, y, z))   # est_ordre(G,E) et comparables
    Hsub = N.assume(inclus(vX, vE))                          # X⊂E
    Hb = N.assume(appartient(vb, vE))                        # b∈E

    # ── extraction des composantes de l'ordre total ───────────────────────────
    ord_part = conjonction_elim_gauche(Htot)                 # est_ordre(G,E)
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(ord_part))   # (∀t)(t∈E⇒(t,t)∈G)
    antisym = conjonction_elim_droite(conjonction_elim_gauche(ord_part)) # antisymetrie(G)
    comparables = conjonction_elim_droite(Htot)              # (∀x∀y)((x∈E et y∈E)⇒(…ou…))

    # ── les deux sens, puis conjonction = équivalence ─────────────────────────
    sens1 = _sens_directe(G, X, b, E_set, comparables, refl_E, antisym, Hsub, Hb)
    sens2 = _sens_reciproque(G, X, b, E_set, comparables, refl_E, antisym, Hb)
    return conjonction_intro(sens1, sens2)                   # équivalence (= et des 2 impl.)


__all__ = ["borne_sup_critere_total"]
