# -*- coding: utf-8 -*-
"""TOUT DIVISEUR DIVISE LA FACTORIELLE — la brique G (Euclide-infinitude).

    ⊢ (Fini d ∧ ¬(d=0)) ⇒ (∀n)( Fini n ⇒ ( d ≤ n ⇒ d | n! ) )

Récurrence C61 sous les hypothèses AMBIANTES {Fini d, d≠0} (modèle
produit_binaire_entier : elles traversent base et pas, déchargées en fin).
  base  : d ≤ 0 + 0 ≤ d (zero_inf_egal_cardinal, coupe) + antisymétrie
          (nesting c1, BR6) ⇒ d = 0 — mort par ex_falso contre d≠0.
  pas   : d ≤ succ n se SCINDE par successeur_ordre (l'équivalence est un et
          encodé : élim gauche = le sens direct, BR6) ;
          · d ≤ n   → P(n) → d|n! → PONT-α qdiv↦wg2 (témoin var qdiv sous
            lieur frais, playbook collisions) → G2 → d | n!·(n+1) ;
          · d = n+1 → G3 (Fini(n!) par la brique F) → n+1 | n!·(n+1) →
            Leibniz d ↦ n+1 sur le 1er argument ;
          les deux → Leibniz ultime (pont n∈ℕ, BR5) : d | (n+1)!.
Lieur de divisibilité UNIFORME « qdiv » (le réflexif/producteur du dépôt)."""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[4]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, impl, non, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (  # noqa: E402
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (  # noqa: E402
    equivalence_arriere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (  # noqa: E402
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (  # noqa: E402
    _antisym_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (  # noqa: E402
    factorielle_def2,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_close import (  # noqa: E402
    factorielle_def2_ultime,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini, successeur, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (  # noqa: E402
    fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (  # noqa: E402
    zero_est_un_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (  # noqa: E402
    fini_implique_fini_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (  # noqa: E402
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (  # noqa: E402
    predecesseur_fini_universel_preuve,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (  # noqa: E402
    _fini_et_P_implique_succ,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (  # noqa: E402
    successeur_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (  # noqa: E402
    zero_inf_egal_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import (  # noqa: E402
    _fini_dans_NN,
)
from outils_ia.arithmetique.machine_num import ex_falso, existe_temoin_verifie  # noqa: E402
from outils_ia.decouvertes.autonomie.euclide_c61.divise_produit import (  # noqa: E402
    divise_produit_droite, divise_produit_gauche,
)
from outils_ia.decouvertes.autonomie.euclide_c61.fini_factorielle import (  # noqa: E402
    fini_factorielle,
)

mp = N.modus_ponens


def _cut(thm, hyp, preuve_hyp):
    return mp(preuve_hyp, N.loi_deduction(hyp, thm))


def _fic_t(t):
    """⊢ Fini T ⇒ est_cardinal T  (version terme)."""
    return instancie(N.generalisation("Aficg", fini_implique_cardinal("Aficg")), t)


def _fisucc_t(t):
    """⊢ Fini T ⇒ Fini(succ T)  (version terme)."""
    return instancie(N.generalisation("Afsg",
                                      fini_implique_fini_successeur("Afsg")), t)


def _so_t(tx, tb):
    """⊢ card X ⇒ ( X≤succ B ⟺ (X≤B ∨ X=succ B) )  (version terme)."""
    g = N.generalisation("Xsog", N.generalisation("Bsog",
        successeur_ordre("Xsog", "Bsog")))
    return instancie(instancie(g, tx), tb)


def _g2_t(td, ta, tb):
    """⊢ (card D ∧ D|A [wg2] ∧ Fini B) ⇒ D | A·B  (version terme)."""
    g = N.generalisation("XdG", N.generalisation("YdG", N.generalisation("ZdG",
        divise_produit_droite("XdG", "YdG", "ZdG"))))
    return instancie(instancie(instancie(g, td), ta), tb)


def _g3_t(tb, ta):
    """⊢ Fini A ⇒ B | A·B  (version terme)."""
    g = N.generalisation("Bg3G", N.generalisation("Ag3G",
        divise_produit_gauche("Bg3G", "Ag3G")))
    return instancie(instancie(g, tb), ta)


def divise_factorielle_cible(d="dG", n="nG"):
    """Énoncé visé : (Fini d ∧ ¬(d=0)) ⇒ ∀n( Fini n ⇒ ( d≤n ⇒ d|n! ) )."""
    vd, vn = var(d), var(n)
    return impl(et(est_fini(vd), non(egal(vd, ZERO))),
                pourtout(n, impl(est_fini(vn),
                                 impl(inf_egal_card(vd, vn),
                                      divise_propre(vd, factorielle_def2(vn),
                                                    q="qdiv")))))


def divise_factorielle(d="dG", n="nG", k="kpred"):
    """🎯 ⊢ (Fini d ∧ d≠0) ⇒ ∀n( Fini n ⇒ (d≤n ⇒ d|n!) ).              [G]"""
    vd, vn = var(d), var(n)
    Hamb = et(est_fini(vd), non(egal(vd, ZERO)))
    hamb = N.assume(Hamb)
    hfd = conjonction_elim_gauche(hamb)                      # Fini d
    hn0 = conjonction_elim_droite(hamb)                      # ¬(d=0)
    card_d = mp(hfd, _fic_t(vd))                             # est_cardinal d

    def P(t):
        return impl(inf_egal_card(vd, t),
                    divise_propre(vd, factorielle_def2(t), q="qdiv"))

    # ── BASE : P(0) — d≤0 ⇒ d=0 (antisym) ⇒ ⊥ contre d≠0 ───────────────────
    h0 = N.assume(inf_egal_card(vd, ZERO))                   # d ≤ 0
    z = zero_inf_egal_cardinal(vd)                           # {card d} ⊢ 0 ≤ d
    hz = next(iter(z.hypotheses))
    assert hz == est_cardinal(vd), "zero_inf_egal_cardinal : hyp inattendue"
    le0 = _cut(z, hz, card_d)                                # 0 ≤ d
    cz = zero_est_un_cardinal()                              # card 0
    assert cz.conclusion == est_cardinal(ZERO)
    ante = conjonction_intro(conjonction_intro(
        conjonction_intro(h0, le0), card_d), cz)             # nesting c1 (BR6)
    d_eq_0 = mp(ante, _antisym_t(vd, ZERO))                  # d = 0
    assert d_eq_0.conclusion == egal(vd, ZERO)
    cible0 = divise_propre(vd, factorielle_def2(ZERO), q="qdiv")
    p0 = N.loi_deduction(inf_egal_card(vd, ZERO),
                         ex_falso(d_eq_0, hn0, cible0))
    assert p0.conclusion == P(ZERO), "base : P(0) mal formé"

    # ── PAS : {Fini n ∧ P(n)} ⊢ P(succ n) ───────────────────────────────────
    hstep = N.assume(et(est_fini(vn), P(vn)))
    fini_n = conjonction_elim_gauche(hstep)                  # Fini n
    Pn = conjonction_elim_droite(hstep)                      # d≤n ⇒ d|n!
    hsucc = N.assume(inf_egal_card(vd, successeur(vn)))      # d ≤ succ n
    eqv = mp(card_d, _so_t(vd, vn))                          # équivalence (et encodé)
    split = mp(hsucc, conjonction_elim_gauche(eqv))          # d≤n ∨ d=succ n

    fn = factorielle_def2(vn)
    fsn = factorielle_def2(successeur(vn))
    rhs = produit_cardinal_binaire(fn, successeur(vn))       # n!·(n+1)
    n_NN = mp(fini_n, _fini_dans_NN(vn))                     # n ∈ ℕ (pont BR5)
    ult = factorielle_def2_ultime(n)
    hyp_u = next(iter(ult.hypotheses))
    assert n_NN.conclusion == hyp_u, "pont ≠ hyp ultime"
    eq_s = _cut(ult, hyp_u, n_NN)                            # (n+1)! = n!·(n+1)
    assert eq_s.conclusion == egal(fsn, rhs)
    leibC = N.s6(fsn, rhs, "wG", divise_propre(vd, var("wG"), q="qdiv"))
    arr = equivalence_arriere(mp(eq_s, leibC))               # d|rhs ⇒ d|(n+1)!

    # branche 1 : d ≤ n → d|n! → pont-α qdiv↦wg2 → G2 → d|rhs
    b1h = N.assume(inf_egal_card(vd, vn))
    dfn = mp(b1h, Pn)                                        # d|n!  (lieur qdiv)
    m_q = et(est_fini(var("qdiv")), egal(fn, produit_cardinal_binaire(vd, var("qdiv"))))
    t_q = N.assume(m_q)
    mat_w = et(est_fini(var("wg2")), egal(fn, produit_cardinal_binaire(vd, var("wg2"))))
    ex_w = existe_temoin_verifie(t_q, mat_w, var("qdiv"), "wg2")
    dfn_w = mp(dfn, existe_elimination(N.loi_deduction(m_q, ex_w), "qdiv"))
    assert dfn_w.conclusion == divise_propre(vd, fn, q="wg2")
    fini_sn = mp(fini_n, _fisucc_t(vn))                      # Fini(succ n)
    dprod = mp(conjonction_intro(conjonction_intro(card_d, dfn_w), fini_sn),
               _g2_t(vd, fn, successeur(vn)))                # d | rhs
    assert dprod.conclusion == divise_propre(vd, rhs, q="qdiv")
    br1 = N.loi_deduction(inf_egal_card(vd, vn), mp(dprod, arr))

    # branche 2 : d = succ n → G3 (brique F) → succ n|rhs → Leibniz 1er arg
    b2h = N.assume(egal(vd, successeur(vn)))
    fini_fn = mp(fini_n, instancie(fini_factorielle(), vn))  # Fini(n!)
    sn_div = mp(fini_fn, _g3_t(successeur(vn), fn))          # succ n | rhs
    assert sn_div.conclusion == divise_propre(successeur(vn), rhs, q="qdiv")
    leib2 = N.s6(vd, successeur(vn), "wG2",
                 divise_propre(var("wG2"), rhs, q="qdiv"))
    arr2 = equivalence_arriere(mp(b2h, leib2))               # (succ n|rhs)⇒(d|rhs)
    br2 = N.loi_deduction(egal(vd, successeur(vn)),
                          mp(mp(sn_div, arr2), arr))

    r = cas(split, br1, br2)                                 # d | (n+1)!
    psucc = N.loi_deduction(inf_egal_card(vd, successeur(vn)), r)
    assert psucc.conclusion == P(successeur(vn)), "P(succ n) mal formé"
    step = N.generalisation(n, N.loi_deduction(et(est_fini(vn), P(vn)), psucc))
    assert step.conclusion == _fini_et_P_implique_succ(P, n), "pas mal formé"

    # ── PRINCIPE C61 + décharges ────────────────────────────────────────────
    princ = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ.hypotheses, "résidu prédécesseur absent"
    princ = _cut(princ, pfu, predecesseur_fini_universel_preuve(k=k))
    allP = mp(conjonction_intro(p0, step), princ)            # ∀n(Fini n ⇒ P n)
    th = N.loi_deduction(Hamb, allP)
    assert th.est_clos and not th.hypotheses, "divise_factorielle non clos"
    assert th.conclusion == divise_factorielle_cible(d, n), (
        "divise_factorielle : conclusion != cible")
    return th


__all__ = ["divise_factorielle", "divise_factorielle_cible"]
