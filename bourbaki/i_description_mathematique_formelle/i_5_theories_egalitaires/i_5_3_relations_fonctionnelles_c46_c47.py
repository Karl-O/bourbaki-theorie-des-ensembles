"""Couche égalitaire — §I.5.3, critère C46 (« R fonctionnelle ⇔ x = τ_x(R) »).

Deux SCHÉMAS métathéoriques (critère C46 de chapitre I, comme C45 dans le fichier
voisin : réalisés en FONCTIONS PYTHON VÉRIFIABLES, jamais un `Theoreme`
schématique — pour chaque R concret elles émettent une dérivation du noyau) :

  1. `c46_avant(R, x, thm_fonc, ...)`  (C46, sens DIRECT, E.I.41 L.24-31) :
        d'un THÉORÈME CLOS  thm_fonc : ⊢ « R fonctionnelle en x »
        ( = ⊢ (∃x)R et relation_univoque_x(R) )
        produit  ⊢ R ⇔ (x = τ_x(R)).

  2. `c46_arriere(R, x, T, thm_R_equiv_T, ...)`  (C46, sens RÉCIPROQUE, E.I.41 L.32-36) :
        d'un THÉORÈME CLOS  ⊢ R ⇔ (x = T)  (T ne contenant pas x)
        produit  ⊢ « R fonctionnelle en x »  ( = ⊢ (∃x)R et relation_univoque_x(R) ).

ROUTE (VERBATIM du livre, E.I.41 L.24-36) :
  · Direct.  R ⇒ (x=τ_x(R)) par C45 (sens direct, univocité déchargée par thm_fonc).
    Sens inverse (x=τ_x(R)) ⇒ R : S6 donne (x=τ_x(R)) ⇒ (R ⇔ (τ_x(R)|x)R) ; le
    témoin canonique (τ_x(R)|x)R est un théorème (car (∃x)R l'est, via existe_temoin),
    donc sous x=τ_x(R), R est vraie.  conjonction_intro des deux sens = l'équivalence.
  · Réciproque.  R univoque par C45 (sens réciproque, c45_arriere, depuis R⇒(x=T)).
    (T|x)R ⇔ (T=T) [instance de R⇔(x=T) en x:=T] et T=T (réflexivité) donnent (T|x)R,
    puis (∃x)R par S5.  conjonction_intro((∃x)R, univocité) = « R fonctionnelle ».

FRONTIÈRE DE CONFIANCE : primitives `N.*` (s5, s6, existe_temoin, reflexivite,
generalisation, instancie, loi_deduction) + tactiques certifiées + C45.  Aucune
fabrication de `Theoreme`, aucun axiome ajouté (theorie_ensembles reste = 22).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, tau, impl, et, subst_f, libres_f, libres_t, existe, equiv,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_3_relations_fonctionnelles_c45 import (
    relation_univoque_x, relation_fonctionnelle_en_x, c45_avant, c45_arriere,
    _deux_fraiches,
)


# @livre Ch.I §5.3 Crit.46 | E I.41 L.24-27 | PDF p.41
# @livre Ch.I §5.3 Demo.- | E I.41 L.28-31 | PDF p.41  (démo du sens DIRECT de C46 — DÉRIVÉE)
def c46_avant(R, x: str, thm_fonc, y: str | None = None, z: str | None = None):
    """C46, sens DIRECT (E.I.41 L.24-31) — schéma métathéorique vérifiable :

        d'un THÉORÈME CLOS  thm_fonc : ⊢ relation_fonctionnelle_en_x(R, x)
        ( = ⊢ (∃x)R et relation_univoque_x(R) ),
        produit  ⊢ R ⇔ (x = τ_x(R)),  CLOS.

    y, z sont les MÊMES lettres fraîches ayant servi à bâtir thm_fonc (l'univocité
    en dépend structurellement) ; par défaut on les recalcule comme relation_
    univoque_x (fraîcheur sur libres_f(R) ∪ {x})."""
    fonc_cible = relation_fonctionnelle_en_x(R, x, y, z)
    if not thm_fonc.est_clos or thm_fonc.conclusion != fonc_cible:
        raise ValueError(
            "thm_fonc doit être un théorème CLOS ⊢ « R fonctionnelle en x » "
            "(mêmes lettres fraîches y, z que relation_fonctionnelle_en_x)")

    ex_R = conjonction_elim_gauche(thm_fonc)              # ⊢ (∃x)R
    uni = conjonction_elim_droite(thm_fonc)              # ⊢ relation_univoque_x(R)

    t = tau(x, R)                                        # τ_x(R)
    witness = subst_f(t, x, R)                           # (τ_x(R)|x)R

    # ── sens R ⇒ (x=τ_x(R)) : C45 direct, univocité DÉCHARGÉE par uni ──
    c45 = c45_avant(R, x, y, z)                          # { univoque } ⊢ R ⇒ (x=τ_x(R))
    fwd = N.modus_ponens(uni, N.loi_deduction(uni.conclusion, c45))   # ⊢ R ⇒ (x=τ_x(R))

    # ── sens (x=τ_x(R)) ⇒ R : S6 + témoin canonique ──
    leib = N.s6(var(x), t, "w", subst_f(var("w"), x, R))  # (x=τ) ⇒ ( R ⇔ (τ|x)R )
    h = N.assume(egal(var(x), t))                         # { x=τ_x(R) }
    equiv_R_wit = N.modus_ponens(h, leib)                 # R ⇔ (τ|x)R
    wit = N.modus_ponens(ex_R, N.existe_temoin(R, x))     # ⊢ (τ_x(R)|x)R
    R_true = N.modus_ponens(wit, equivalence_arriere(equiv_R_wit))    # R
    back = N.loi_deduction(egal(var(x), t), R_true)       # ⊢ (x=τ_x(R)) ⇒ R

    res = conjonction_intro(fwd, back)                    # ⊢ R ⇔ (x=τ_x(R))
    assert res.conclusion == equiv(R, egal(var(x), t)), \
        "c46_avant : conclusion ≠ ( R ⇔ (x=τ_x(R)) )"
    assert res.est_clos, "c46_avant : devrait être clos (thm_fonc est clos)"
    return res


# @livre Ch.I §5.3 Demo.- | E I.41 L.32-36 | PDF p.41  (démo du sens RÉCIPROQUE de C46 — DÉRIVÉE)
def c46_arriere(R, x: str, T, thm_R_equiv_T, y: str | None = None,
                z: str | None = None):
    """C46, sens RÉCIPROQUE (E.I.41 L.32-36) — schéma métathéorique vérifiable :

        d'un THÉORÈME CLOS  thm_R_equiv_T : ⊢ R ⇔ (x = T)  (T ne contenant pas x),
        produit  ⊢ relation_fonctionnelle_en_x(R, x)
                   = ⊢ (∃x)R et relation_univoque_x(R),  CLOS.

    Route livre : R univoque par C45 réciproque (c45_arriere depuis R⇒(x=T)) ;
    (T|x)R ⇔ (T=T) (instance de R⇔(x=T) en x:=T) et T=T donnent (T|x)R, d'où (∃x)R."""
    if x in libres_t(T):
        raise ValueError("C46 réciproque : le terme T ne doit pas contenir x")
    R_equiv_xeqT = equiv(R, egal(var(x), T))
    if not thm_R_equiv_T.est_clos or thm_R_equiv_T.conclusion != R_equiv_xeqT:
        raise ValueError("thm_R_equiv_T doit être CLOS de conclusion ( R ⇔ (x=T) )")

    # lettres fraîches communes (évitent aussi libres_t(T)) → assertion déterministe
    interdits = libres_f(R) | {x} | libres_t(T)
    if y is None or z is None:
        fy, fz = _deux_fraiches(interdits)
        y = y or fy
        z = z or fz

    # ── univocité : C45 réciproque depuis R ⇒ (x=T) ──
    R_imp_T = equivalence_avant(thm_R_equiv_T)           # ⊢ R ⇒ (x=T)
    uni = c45_arriere(R, x, T, R_imp_T, y, z)            # ⊢ relation_univoque_x(R)

    # ── (∃x)R : (T|x)R ⇔ (T=T)  [thm en x:=T]  et  T=T  donnent (T|x)R, puis S5 ──
    gen_x = N.generalisation(x, thm_R_equiv_T)           # (∀x)( R ⇔ (x=T) )   (clos)
    inst_T = instancie(gen_x, T)                         # (T|x)R ⇔ (T=T)      ((T|x)(x=T)=(T=T), x∉T)
    TxR = N.modus_ponens(N.reflexivite(T), equivalence_arriere(inst_T))   # ⊢ (T|x)R
    ex_R = N.modus_ponens(TxR, N.s5(R, T, x))            # ⊢ (∃x)R

    res = conjonction_intro(ex_R, uni)                   # ⊢ (∃x)R et univoque
    assert res.conclusion == relation_fonctionnelle_en_x(R, x, y, z), \
        "c46_arriere : conclusion ≠ « R fonctionnelle en x »"
    assert res.est_clos, "c46_arriere : devrait être clos (thm_R_equiv_T est clos)"
    return res


# @livre Ch.I §5.3 Crit.47 | E I.42 L.5-8 | PDF p.42
# @livre Ch.I §5.3 Demo.- | E I.42 L.9-13 | PDF p.42  (démo de C47 — DÉRIVÉE, route noyau équivalente)
def c47_equivalence(R, x: str, S, thm_fonc, y: str | None = None,
                    z: str | None = None):
    """C47 (E.I.42 L.5-13) — schéma métathéorique vérifiable :

        Données : x non constante de 𝒯 ; R, S deux relations (Formules, x libre) ;
        un THÉORÈME CLOS  thm_fonc : ⊢ « R fonctionnelle en x »
        ( = ⊢ (∃x)R et relation_univoque_x(R) ).
        Produit :  ⊢ S{τ_x(R)}  ⇔  (∃x)( R{x} et S{x} ),  CLOS.

    LIVRE (E.I.42 L.9-13) : de C46+C43, (R et S{x}) ⇔ (R et S{τ_x(R)}) ; S{τ_x(R)}
    ne contenant pas x, C33 donne (∃x)(R et S{τ}) ⇔ (S{τ} et (∃x)R) ; et (∃x)R est
    vraie (R fonctionnelle).  ROUTE NOYAU équivalente (mêmes ingrédients, sans
    reconstruire C43/C33) : on prouve les DEUX sens de l'équivalence —
      · S{τ} ⇒ (∃x)(R et S) : le témoin (τ|x)R est un théorème [(∃x)R + existe_temoin],
        donc (τ|x)(R et S) = ((τ|x)R et S{τ}) est vrai sous S{τ} ; S5 donne (∃x)(R et S) ;
      · (∃x)(R et S) ⇒ S{τ} : sous (R et S{x}), R ⇒ (x=τ) [C46] puis Leibniz S6 donnent
        S{x} ⇔ S{τ}, d'où S{τ} ; existe_elimination (x ∉ S{τ}) décharge le ∃.
    conjonction_intro des deux sens = l'équivalence.  theorie=22, tout par N.*."""
    t = tau(x, R)                                        # τ_x(R)
    S_tau = subst_f(t, x, S)                             # S{τ_x(R)}   ((τ|x)S, x∉ après subst)
    R_et_S = et(R, S)                                    # R{x} et S{x}
    exists_RS = existe(x, R_et_S)                        # (∃x)( R et S )

    # R fonctionnelle → (∃x)R, R ⇔ (x=τ), témoin (τ|x)R
    ex_R = conjonction_elim_gauche(thm_fonc)             # ⊢ (∃x)R
    equiv_R = c46_avant(R, x, thm_fonc, y, z)            # ⊢ R ⇔ (x=τ_x(R))
    R_imp_tau = equivalence_avant(equiv_R)               # ⊢ R ⇒ (x=τ_x(R))
    witness = N.modus_ponens(ex_R, N.existe_temoin(R, x))  # ⊢ (τ_x(R)|x)R

    # ── sens S{τ} ⇒ (∃x)( R et S ) ──
    hS = N.assume(S_tau)                                 # { S{τ} }
    conj_tau = conjonction_intro(witness, hS)            # ⊢ (τ|x)R et S{τ}  = (τ|x)(R et S)
    ex_RS = N.modus_ponens(conj_tau, N.s5(R_et_S, t, x))  # ⊢ (∃x)( R et S )
    fwd = N.loi_deduction(S_tau, ex_RS)                  # ⊢ S{τ} ⇒ (∃x)(R et S)

    # ── sens (∃x)( R et S ) ⇒ S{τ} ──
    hRS = N.assume(R_et_S)                               # { R et S{x} }
    r = conjonction_elim_gauche(hRS)                     # R{x}
    s_x = conjonction_elim_droite(hRS)                   # S{x} (= S)
    x_eq_tau = N.modus_ponens(r, R_imp_tau)              # x = τ_x(R)
    leib = N.s6(var(x), t, "w", subst_f(var("w"), x, S))  # (x=τ) ⇒ ( S{x} ⇔ S{τ} )
    s_tau = N.modus_ponens(s_x, equivalence_avant(N.modus_ponens(x_eq_tau, leib)))  # S{τ}
    back = existe_elimination(N.loi_deduction(R_et_S, s_tau), x)   # ⊢ (∃x)(R et S) ⇒ S{τ}

    res = conjonction_intro(fwd, back)                   # ⊢ S{τ} ⇔ (∃x)( R et S )
    assert res.conclusion == equiv(S_tau, exists_RS), \
        "c47_equivalence : conclusion ≠ ( S{τ_x(R)} ⇔ (∃x)(R et S) )"
    assert res.est_clos, "c47_equivalence : devrait être clos (thm_fonc est clos)"
    return res


__all__ = ["c46_avant", "c46_arriere", "c47_equivalence"]
