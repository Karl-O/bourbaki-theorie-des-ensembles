# -*- coding: utf-8 -*-
"""FINITUDE DE LA FACTORIELLE — ⊢ (∀n)( Fini n ⇒ Fini(n!) )   (Euclide-infinitude, brique F).

Récurrence C61 (principe_recurrence_preuve, résidu prédécesseur déchargé),
calquée sur produit_binaire_entier (prop3, le MODÈLE) :
  base  P(0)   : f(0) = 1 (factorielle_def2_zero, CLOS) + Fini(1) (fini_un)
                 + Leibniz s6 arrière ;
  pas           : sous {Fini n ∧ Fini(f n)} — le PONT Fini n ⇒ n∈ℕ
                 (_fini_dans_NN, mesuré == l'hypothèse de ultime, BR5) décharge
                 factorielle_def2_ultime → f(succ n) = f(n)·(succ n) ; la
                 finitude du produit (produit_binaire_entier, versions-terme)
                 et Fini(succ n) (fini_implique_fini_successeur) concluent par
                 Leibniz arrière.
Mesures BR3-BR5 : f(0) == UN exact (les deux côtés) ; pont == hyp-ultime au
MÊME nom de variable (le mismatch BR4 était le nom, pas la forme)."""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[4]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, impl, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (  # noqa: E402
    equivalence_arriere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (  # noqa: E402
    factorielle_def2, factorielle_def2_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_close import (  # noqa: E402
    factorielle_def2_ultime,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini, successeur, UN, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (  # noqa: E402
    fini_un,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (  # noqa: E402
    produit_binaire_entier,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import (  # noqa: E402
    _fini_dans_NN,
)

mp = N.modus_ponens


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H (clos), Γ∪Δ⊢C  (loi_deduction + modus_ponens)."""
    return mp(preuve_hyp, N.loi_deduction(hyp, thm))


def _P(t):
    """P(t) := Fini( t! )   (le prédicat de la récurrence)."""
    return est_fini(factorielle_def2(t))


def _fisucc_t(t):
    """⊢ Fini T ⇒ Fini(succ T)   (version terme capture-safe)."""
    g = N.generalisation("Afsff", fini_implique_fini_successeur("Afsff"))
    return instancie(g, t)


def _pbe_t(tx, ty):
    """⊢ (Fini X ∧ Fini Y) ⇒ Fini(X·Y)   (version terme capture-safe)."""
    g = N.generalisation("Xpbff", N.generalisation("Ypbff",
        produit_binaire_entier("Xpbff", "Ypbff")))
    return instancie(instancie(g, tx), ty)


def fini_factorielle_cible(n="nff"):
    """Énoncé visé : (∀n)( Fini n ⇒ Fini(n!) )."""
    vn = var(n)
    return pourtout(n, impl(est_fini(vn), est_fini(factorielle_def2(vn))))


def fini_factorielle(n="nff", k="kpred"):
    """🎯 ⊢ (∀n)( Fini n ⇒ Fini(n!) ).                                   [CLOS]"""
    vn = var(n)

    # ── BASE : Fini(f(0)) ────────────────────────────────────────────────────
    eq0 = factorielle_def2_zero()                            # f(0) = 1     CLOS
    assert eq0.conclusion == egal(factorielle_def2(ZERO), UN)
    f1 = fini_un()                                           # Fini(1)
    assert f1.conclusion == est_fini(UN), "fini_un : forme inattendue"
    leib0 = N.s6(factorielle_def2(ZERO), UN, "wff0", est_fini(var("wff0")))
    p0 = mp(f1, equivalence_arriere(mp(eq0, leib0)))         # Fini(f(0))
    assert p0.conclusion == _P(ZERO), "base : P(0) mal formé"

    # ── PAS : {Fini n ∧ Fini(f n)} ⊢ Fini(f(succ n)) ────────────────────────
    hstep = N.assume(et(est_fini(vn), _P(vn)))
    fini_n = conjonction_elim_gauche(hstep)                  # Fini n
    fini_fn = conjonction_elim_droite(hstep)                 # Fini(f n)
    n_NN = mp(fini_n, _fini_dans_NN(vn))                     # n ∈ ℕ  (pont BR5)
    ult = factorielle_def2_ultime(n)                         # {n∈ℕ} ⊢ f(n+1)=f(n)·(n+1)
    hyp_u = next(iter(ult.hypotheses))
    assert n_NN.conclusion == hyp_u, "pont ≠ hypothèse de ultime (BR5 démenti ?)"
    eq_s = _cut(ult, hyp_u, n_NN)                            # f(n+1) = f(n)·(n+1)
    rhs = produit_cardinal_binaire(factorielle_def2(vn), successeur(vn))
    assert eq_s.conclusion == egal(factorielle_def2(successeur(vn)), rhs)
    fini_sn = mp(fini_n, _fisucc_t(vn))                      # Fini(succ n)
    fini_pr = mp(conjonction_intro(fini_fn, fini_sn), _pbe_t(factorielle_def2(vn),
                                                             successeur(vn)))
    assert fini_pr.conclusion == est_fini(rhs)               # Fini(f(n)·(n+1))
    leibS = N.s6(factorielle_def2(successeur(vn)), rhs, "wffs", est_fini(var("wffs")))
    p_sn = mp(fini_pr, equivalence_arriere(mp(eq_s, leibS))) # Fini(f(succ n))
    assert p_sn.conclusion == _P(successeur(vn))
    step = N.generalisation(n, N.loi_deduction(et(est_fini(vn), _P(vn)), p_sn))
    assert step.conclusion == _fini_et_P_implique_succ(_P, n), "pas mal formé"

    # ── PRINCIPE C61 + décharge du résidu prédécesseur ──────────────────────
    princ = principe_recurrence_preuve(_P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ.hypotheses, "résidu prédécesseur absent"
    princ = _cut(princ, pfu, predecesseur_fini_universel_preuve(k=k))
    res = mp(conjonction_intro(p0, step), princ)             # (∀n)(Fini n ⇒ Fini(n!))
    assert res.est_clos and not res.hypotheses, "fini_factorielle non clos"
    assert res.conclusion == fini_factorielle_cible(n), (
        "fini_factorielle : conclusion != cible")
    return res


__all__ = ["fini_factorielle", "fini_factorielle_cible"]
