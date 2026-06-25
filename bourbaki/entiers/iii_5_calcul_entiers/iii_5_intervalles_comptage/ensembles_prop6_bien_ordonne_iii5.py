"""§III.5 — PROPOSITION 6 (E III.38), socle « bien ordonné ».

🎯 CIBLES de ce module :

  (A) partie_finie_est_finie :
        ( X⊂E et est_fini_ensemble(E) ) ⇒ est_fini_ensemble(X)
      « Toute partie d'un ensemble fini est finie » (Cor. 1 §III.4.2), CLOS,
      INCONDITIONNEL (via fini_downward gardé + Prop. 2 close).

  (B) fini_total_est_bien_ordonne :
        ( totalement_ordonne(G,E) et est_fini_ensemble(E) )
        ⇒ est_bien_ordonne_graphe(G, E)
      « Tout ensemble FINI TOTALEMENT ORDONNÉ est BIEN ORDONNÉ » — la moitié
      « en particulier bien ordonné » de la Prop. 6 §III.5.

⚠️ NOTE D'HONNÊTETÉ sur (B).  La définition GRAPHE du bien-ordre exige le facteur
ORDRE sous la forme `est_relation_ordre_dans(R_G, E)` (E.III.1.1) :
    est_relation_ordre(R_G)  ∧  est_reflexive_dans_ordre(R_G, E)
où est_relation_ordre = transitif ∧ antisym ∧ reflexif_IMPLICITE, et
est_reflexive_dans_ordre = (∀x)((x,x)∈G ⇔ x∈E).  Or le PRÉDICAT du projet
`totalement_ordonne(G,E)` = est_ordre(G,E) ∧ comparables, avec
est_ordre = reflexivite_SUR(G,E) ∧ antisym ∧ trans.  est_ordre ne contient NI la
réflexivité IMPLICITE ((x,y)∈G ⇒ (x,x)∈G), NI le sens « ⇒ » de la réflexivité
DANS ((x,x)∈G ⇒ x∈E) — qui réclamerait G⊂E×E, non encodé dans `totalement_ordonne`.
Ces deux clauses NE SONT PAS dérivables de `totalement_ordonne` seul (pas de G⊂E×E).

Le facteur ORDRE est donc PRIS EN HYPOTHÈSE explicite, sous EXACTEMENT la forme
attendue `est_relation_ordre_dans(R_G, E)` (= « E est ordonné par G » au sens
Bourbaki, ce que tout ensemble totalement ordonné fournit).  La partie SUBSTANTIELLE
non triviale — l'existence d'un plus petit élément pour toute partie non vide d'un
FINI totalement ordonné — est, elle, PROUVÉE INCONDITIONNELLEMENT (via
prop3_total_min + partie_finie_est_finie).

theorie=22, rien postulé.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination

from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble, est_fini
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal

from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    totalement_ordonne, plus_petit_element, _couple_dans,
)
from bourbaki.ordre.iii_4_ensembles_finis.ensembles_ordre_fini_iii4 import _decompose_total
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zermelo import est_bien_ordonne_graphe, R_de

from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop6_fini_interval_iii5 import (
    prop3_total_min, _ppe, _ZPP,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import (
    partie_inf_egal_card, _pont_inf_egal_card,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import fini_downward_garde_thm
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import fini_downward


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _decharge_par_conclusion(thm, preuve):
    """Décharge de `thm` l'hypothèse ÉGALE à `preuve.conclusion`."""
    cible = preuve.conclusion
    assert cible in thm.hypotheses, "la conclusion de la preuve n'est pas une hyp de thm"
    return _cut(thm, cible, preuve)


# ════════════════════════════════════════════════════════════════════════════
#  (A) LEMME — « toute partie d'un ensemble fini est finie »  (Cor. 1 §III.4.2)
# ════════════════════════════════════════════════════════════════════════════
def partie_finie_est_finie_enonce(X, Eens):
    """⊢-cible : ( X⊂E et est_fini_ensemble(E) ) ⇒ est_fini_ensemble(X)."""
    vX, vE = _t(X), _t(Eens)
    return impl(et(inclus(vX, vE), est_fini_ensemble(vE)), est_fini_ensemble(vX))


def partie_finie_est_finie(X="Xpf", Eens="Epf", xfd="xfd"):
    """🎯 ⊢ ( X⊂E et est_fini_ensemble(E) ) ⇒ est_fini_ensemble(X).   (Cor. 1 §III.4.2.)

    « Toute partie d'un ensemble fini est finie. »  INCONDITIONNEL.

    Chaîne :
      1. X⊂E ⇒ X≤E                       [partie_inf_egal_card] ;
      2. X≤E ⇒ Card X≤Card E             [_pont_inf_egal_card] ;
      3. (∀x)fini_downward(Card X,x)     [fini_downward_garde_thm, hyps
         est_cardinal(Card X) (card_est_un_cardinal) + predecesseur_fini_universel
         (Prop. 2 close) DÉCHARGÉES] ;  instancié à x:=Card E :
         (Card X≤Card E et Fini(Card E)) ⇒ Fini(Card X).
    est_fini_ensemble(·) = Fini(Card ·) ; conclusion = est_fini_ensemble(X)."""
    vX, vE = _t(X), _t(Eens)
    cX, cE = cardinal(vX), cardinal(vE)

    le_XE = partie_inf_egal_card(vX, vE)                 # (X⊂E)⇒(X≤E)          CLOS
    pont = _pont_inf_egal_card(vX, vE)                   # (X≤E)⇒(Card X≤Card E) CLOS

    fdg = fini_downward_garde_thm(cX, xfd)              # (∀x)fini_downward(Card X,x)
                                                         #   [est_cardinal(Card X), pfu]
    fdg = _decharge_par_conclusion(fdg, predecesseur_fini_universel_preuve())
    reste = list(fdg.hypotheses)
    assert len(reste) == 1, f"hyps résiduelles inattendues : {len(reste)}"
    h_card = reste[0]
    card_cX = card_est_un_cardinal(vX, lieur=h_card.lieur)   # est_cardinal(Card X), liant aligné
    assert card_cX.conclusion == h_card, "est_cardinal(Card X) : forme non alignée"
    fdg = _decharge_par_conclusion(fdg, card_cX)        # (∀x)fini_downward(Card X,x)  CLOS

    fd_at_cE = instancie(fdg, cE)
    assert fd_at_cE.conclusion == fini_downward(cX, cE), "instanciation fini_downward inattendue"

    h = N.assume(et(inclus(vX, vE), est_fini_ensemble(vE)))
    X_sub = conjonction_elim_gauche(h)
    E_fini = conjonction_elim_droite(h)                 # Fini(Card E)
    le_card = N.modus_ponens(N.modus_ponens(X_sub, le_XE), pont)        # Card X ≤ Card E
    fini_cX = N.modus_ponens(conjonction_intro(le_card, E_fini), fd_at_cE)   # Fini(Card X)
    res = N.loi_deduction(et(inclus(vX, vE), est_fini_ensemble(vE)), fini_cX)
    assert res.conclusion == partie_finie_est_finie_enonce(vX, vE), "conclusion ≠ énoncé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (B) CLAUSE « PLUS PETIT » — toute partie non vide d'un FINI totalement
#  ordonné a un plus petit élément  (la 2e composante de est_bien_ordonne).
# ════════════════════════════════════════════════════════════════════════════
def _petit_clause(G, E_set, X="Sbo", a="a", w="w"):
    """La 2e composante de est_bien_ordonne(R_G, E), TEXTUELLEMENT (binders X,a,w) :
        (∀X)( (X⊂E et ¬(X=∅)) ⇒ (∃a)(a∈X et (∀w)(w∈X ⇒ (a,w)∈G)) )."""
    vG, vE = _t(G), _t(E_set)
    R = R_de(vG)
    vX, va, vw = var(X), var(a), var(w)
    petit = existe(a, et(appartient(va, vX),
                         pourtout(w, impl(appartient(vw, vX), R(va, vw)))))
    return pourtout(X, impl(et(inclus(vX, vE), non(egal(vX, E.VIDE))), petit))


def clause_plus_petit_fini_total(G="Gbo", E_set="Ebo", X="Sbo", a="a", w="w"):
    """⊢ ( totalement_ordonne(G,E) et est_fini_ensemble(E) ) ⇒
         (∀X)( (X⊂E et ¬(X=∅)) ⇒ (∃a)(a∈X et (∀w)(w∈X ⇒ (a,w)∈G)) ).

    Pour toute partie X⊂E non vide : E fini ⇒ X fini (partie_finie_est_finie),
    donc prop3_total_min (sous totalement_ordonne) fournit un plus petit élément.
    Le ∃-corps de plus_petit_element COÏNCIDE avec le ∃-corps de est_bien_ordonne
    modulo les noms de liants (a/w internes ; on aligne EXACTEMENT)."""
    vG, vE = _t(G), _t(E_set)
    vX = var(X)
    R = R_de(vG)

    hyp = et(totalement_ordonne(G, E_set), est_fini_ensemble(vE))
    hH = N.assume(hyp)
    htot = conjonction_elim_gauche(hH)                  # totalement_ordonne(G,E)
    hEfini = conjonction_elim_droite(hH)                # est_fini_ensemble(E)

    # prop3_total_min : totalement_ordonne(G,E) ⇒ (∀Xppt)((Fini Xppt et Xppt⊂E et Xppt≠∅)⇒(∃m)ppe)
    # ⚠️ binder SÛR « Xppt » (le défaut) — « X » collisionnerait avec le τ-cardinal interne.
    p3 = prop3_total_min(G, E_set)                      # ⊢ totalement_ordonne ⇒ (∀Xppt)(...)
    forall_X = N.modus_ponens(htot, p3)
    p3_X = instancie(forall_X, vX)                      # (Fini X et X⊂E et X≠∅) ⇒ (∃m)ppe(G,X,m)

    # corps cible : (X⊂E et X≠∅) ⇒ (∃a)(...)
    Hgarde = N.assume(et(inclus(vX, vE), non(egal(vX, E.VIDE))))
    X_sub = conjonction_elim_gauche(Hgarde)            # X⊂E
    X_nv = conjonction_elim_droite(Hgarde)             # X≠∅
    # X fini  (E fini + X⊂E)
    pfe = partie_finie_est_finie(X, E_set)             # (X⊂E et E fini) ⇒ X fini   CLOS
    X_fini = N.modus_ponens(conjonction_intro(X_sub, hEfini), pfe)   # est_fini_ensemble(X)
    # antécédent de p3 : (Fini X et X⊂E) et X≠∅  — ordre EXACT de prop3_total_min_enonce
    ante_p3 = conjonction_intro(conjonction_intro(X_fini, X_sub), X_nv)
    ex_m = N.modus_ponens(ante_p3, p3_X)               # (∃m)plus_petit_element(G,X,m)  [via _ppe]

    # _ppe(G,X,m) = m∈X et (∀zppT)(zppT∈X ⇒ (m,zppT)∈G), liant interne _ZPP.
    # cible petit = (∃a)(a∈X et (∀w)(w∈X ⇒ (a,w)∈G)).  On α-renomme le ∃ vers `a`,
    # et le ∀ interne de _ZPP vers `w`.
    m = "m_ppf"
    vm = var(m)
    # forme actuelle du ∃ (liant m, corps _ppe avec liant interne _ZPP)
    corps_ppe = _ppe(G, vX, vm)                        # m∈X et (∀zppT)(zppT∈X⇒(m,zppT)∈G)
    # corps cible (liant interne w)
    petit_corps_pour_a = et(appartient(var(a), vX),
        pourtout(w, impl(appartient(var(w), vX), R(var(a), var(w)))))
    Hwit = N.assume(corps_ppe)                         # m∈X et (∀zppT)(...)
    m_in = conjonction_elim_gauche(Hwit)              # m∈X
    m_min = conjonction_elim_droite(Hwit)            # (∀zppT)(zppT∈X⇒(m,zppT)∈G)
    # reconstruire (∀w)(w∈X⇒(m,w)∈G)
    vw = var(w)
    body_w = N.loi_deduction(appartient(vw, vX),
                             N.modus_ponens(N.assume(appartient(vw, vX)), instancie(m_min, vw)))
    forall_w = N.generalisation(w, body_w)            # (∀w)(w∈X⇒(m,w)∈G)
    corps_a_m = conjonction_intro(m_in, forall_w)    # m∈X et (∀w)(w∈X⇒(m,w)∈G)
    # ∃a via S5 (témoin m)
    ex_a_from_m = N.modus_ponens(corps_a_m, N.s5(petit_corps_pour_a, vm, a))
    # éliminer ∃m
    wit_imp = N.loi_deduction(corps_ppe, ex_a_from_m)
    ex_imp = existe_elimination(wit_imp, m)
    ex_a = N.modus_ponens(ex_m, ex_imp)              # (∃a)(a∈X et (∀w)(w∈X⇒(a,w)∈G))

    corps = N.loi_deduction(et(inclus(vX, vE), non(egal(vX, E.VIDE))), ex_a)
    forall = N.generalisation(X, corps)
    res = N.loi_deduction(hyp, forall)
    assert res.conclusion == impl(hyp, _petit_clause(G, E_set, X, a, w)), "clause petit ≠ cible"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (B) CIBLE PRINCIPALE — fini_total_est_bien_ordonne
#  (sous l'hyp ORDRE explicite est_relation_ordre_dans(R_G, E), cf. note d'honnêteté)
# ════════════════════════════════════════════════════════════════════════════
def fini_total_est_bien_ordonne_enonce(G, E_set, x="x", y="y", z="z", X="Sbo", a="a", w="w"):
    """⊢-cible :
        ( est_relation_ordre_dans(R_G,E) et totalement_ordonne(G,E) et est_fini_ensemble(E) )
        ⇒ est_bien_ordonne_graphe(G, E).

    NB : le facteur ORDRE est_relation_ordre_dans(R_G,E) est en hypothèse (cf. note
    d'honnêteté du module : non dérivable de totalement_ordonne seul).  La clause
    « plus petit » est, elle, prouvée INCONDITIONNELLEMENT."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import est_relation_ordre_dans
    vG, vE = _t(G), _t(E_set)
    R = R_de(vG)
    hyp = et(et(est_relation_ordre_dans(R, vE, x, y, z), totalement_ordonne(G, E_set)),
             est_fini_ensemble(vE))
    return impl(hyp, est_bien_ordonne_graphe(vG, vE, x, y, z, X, a, w))


# @livre Ch.III §5.3 Prop.6 | E III.38 L.21-26 | PDF p.141
def fini_total_est_bien_ordonne(G="Gbo", E_set="Ebo",
                                x="x", y="y", z="z", X="Sbo", a="a", w="w"):
    """🎯 ⊢ ( est_relation_ordre_dans(R_G,E) et totalement_ordonne(G,E) et est_fini_ensemble(E) )
            ⇒ est_bien_ordonne_graphe(G, E).

    « Tout ensemble fini totalement ordonné est bien ordonné » (Prop. 6 §III.5,
    moitié bien-ordonné).  est_bien_ordonne_graphe = est_relation_ordre_dans(R_G,E)
    [HYP] ∧ clause-plus-petit [prouvée via clause_plus_petit_fini_total]."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import est_relation_ordre_dans
    vG, vE = _t(G), _t(E_set)
    R = R_de(vG)

    cible_bo = est_bien_ordonne_graphe(vG, vE, x, y, z, X, a, w)
    # Les 2 conjoints de est_bien_ordonne, construits TEXTUELLEMENT (l'encodage de
    # `et` via De Morgan rend .sous opaque ; on rebâtit par les abrégés et on
    # VALIDE l'assemblage par égalité finale à cible_bo).
    ord_part_cible = est_relation_ordre_dans(R, vE, x, y, z)
    petit_part_cible = _petit_clause(G, E_set, X, a, w)

    hyp = et(et(est_relation_ordre_dans(R, vE, x, y, z), totalement_ordonne(G, E_set)),
             est_fini_ensemble(vE))
    hH = N.assume(hyp)
    ord_part = conjonction_elim_gauche(conjonction_elim_gauche(hH))    # est_relation_ordre_dans
    htot = conjonction_elim_droite(conjonction_elim_gauche(hH))        # totalement_ordonne
    hEfini = conjonction_elim_droite(hH)                              # est_fini_ensemble

    assert ord_part.conclusion == ord_part_cible, "facteur ordre : forme ≠ cible bien-ordonne"

    # clause plus-petit, alignée sur les binders X,a,w de cible_bo
    petit_thm = clause_plus_petit_fini_total(G, E_set, X, a, w)        # (tot et Efini)⇒clause
    petit = N.modus_ponens(conjonction_intro(htot, hEfini), petit_thm)
    assert petit.conclusion == petit_part_cible, "clause petit : forme ≠ cible bien-ordonne"

    bo = conjonction_intro(ord_part, petit)
    assert bo.conclusion == cible_bo, "assemblage bien-ordonne : conclusion ≠ est_bien_ordonne_graphe"
    res = N.loi_deduction(hyp, bo)
    assert res.conclusion == fini_total_est_bien_ordonne_enonce(G, E_set, x, y, z, X, a, w), \
        "conclusion ≠ énoncé"
    return res


__all__ = [
    "partie_finie_est_finie_enonce", "partie_finie_est_finie",
    "clause_plus_petit_fini_total",
    "fini_total_est_bien_ordonne_enonce", "fini_total_est_bien_ordonne",
]
