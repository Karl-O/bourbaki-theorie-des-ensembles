# -*- coding: utf-8 -*-
"""EXTRACTION DU DIVISEUR — le cœur logique du cas composé (Euclide, brique D).

    ⊢ ( ¬(n=1) ∧ ¬est_premier(n) ) ⇒ ∃d( (Fini d ∧ d|n) ∧ (¬(d=1) ∧ ¬(d=n)) )

De la non-primalité, extraire un diviseur PROPRE non trivial : ¬et(A,B) se
déplie en ¬¬(¬A∨¬B) (dne), preuve par cas — la branche ¬¬(n=1) meurt par
ex_falso contre l'hypothèse n≠1 ; la branche ¬∀d(…) devient ∃d¬(…) (déf. du ∀
+ dne), puis un transport PROPOSITIONNEL sous ∃ (monotonie_existe) transforme
¬((F∧D)⇒(U∨E)) en (F∧D)∧(¬U∧¬E) — les gestes : s2/s3 pour les ∨-intro,
neg_intro/ex_falso, dne (c16). Lieurs : d/q de est_premier = dex/qex.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, non, ou, impl, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, cas,
    tiers_exclu,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (  # noqa: E402
    monotonie_existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini,
)
from outils_ia.arithmetique.machine_num import ex_falso, neg_intro    # noqa: E402
from outils_ia.conjectures.goldbach import est_premier, un, _ou       # noqa: E402

mp = N.modus_ponens


def _dne(thm_nn, A):
    """Γ ⊢ ¬¬A  ⟹  Γ ⊢ A   (ABRÉGÉ : tiers exclu + cas — la couche-0
    double_negation_elim prend un Assemblage, pas une Formule ; mesuré)."""
    br_a = N.loi_deduction(A, N.assume(A))
    br_na = N.loi_deduction(non(A), ex_falso(N.assume(non(A)), thm_nn, A))
    return cas(tiers_exclu(A), br_a, br_na)


def _du_niant_de_impl(X, U, Ecas):
    """{¬(X ⇒ (U∨E))} ⊢ X ∧ (¬U ∧ ¬E)   (transport propositionnel, X/U/E formules).

    impl(X,Y) = ou(¬X, Y). Sous h = ¬(¬X ∨ Y) :
      X  : {¬X} ⊢ ¬X∨Y (s2+? : s2(¬X,Y) donne ¬X⇒(¬X∨Y)) → ⊥ → ¬¬X → X (c16)
      ¬Y : {Y}  ⊢ ¬X∨Y (s2(Y,¬X) puis s3 échange) → ⊥ → ¬Y
      puis ¬(U∨E) → ¬U (s2) et ¬E (s2+s3)."""
    Y = _ou(U, Ecas)                    # ⚠️ le _ou ENCODÉ de est_premier
    #   (¬(¬U∧¬E)) — pas le ou primitif : les deux formes ≠, la décharge de
    #   loi_deduction ne matchait pas et 'dex' restait libre (mesuré).
    h = N.assume(non(ou(non(X), Y)))
    # X — neg_intro exige que le faux conclue ¬f (S1 sur f ⇒ ¬f) : cible = ¬f.
    nnX = neg_intro(non(X), ex_falso(mp(N.assume(non(X)), N.s2(non(X), Y)), h,
                                     non(non(X))))
    X_thm = _dne(nnX, X)
    # ¬Y
    nY = neg_intro(Y, ex_falso(mp(mp(N.assume(Y), N.s2(Y, non(X))),
                                  N.s3(Y, non(X))), h, non(Y)))
    # ¬Y = ¬_ou(U,E) = ¬¬(et(¬U,¬E)) → dne → et(¬U,¬E) → élims directes
    et_nUnE = _dne(nY, et(non(U), non(Ecas)))
    nU = conjonction_elim_gauche(et_nUnE)
    nE = conjonction_elim_droite(et_nUnE)
    return conjonction_intro(X_thm, conjonction_intro(nU, nE))


def extraction_diviseur_cible(n="nex", d="dex", q="qex"):
    """Énoncé visé : (¬(n=1) ∧ ¬premier n) ⇒ ∃d((Fini d ∧ d|n) ∧ (¬(d=1) ∧ ¬(d=n)))."""
    vn, vd = var(n), var(d)
    corps = et(et(est_fini(vd), divise_propre(vd, vn, q=q)),
               et(non(egal(vd, un())), non(egal(vd, vn))))
    return impl(et(non(egal(vn, un())), non(est_premier(vn, d=d, q=q))),
                existe(d, corps))


def extraction_diviseur(n="nex", d="dex", q="qex"):
    """🎯 ⊢ (¬(n=1) ∧ ¬premier n) ⇒ ∃d((Fini d ∧ d|n) ∧ (¬(d=1) ∧ ¬(d=n)))."""
    vn, vd = var(n), var(d)
    A = non(egal(vn, un()))                              # ¬(n=1)   (= conjoint 1 de premier)
    X = et(est_fini(vd), divise_propre(vd, vn, q=q))
    U, Ecas = egal(vd, un()), egal(vd, vn)
    B = non(existe(d, non(impl(X, _ou(U, Ecas)))))       # ∀d(...) tel que DANS est_premier
    H = et(A, non(est_premier(vn, d=d, q=q)))
    h = N.assume(H)
    h_ne1 = conjonction_elim_gauche(h)                   # ¬(n=1)
    h_np = conjonction_elim_droite(h)                    # ¬ et(¬(n=1), B) = ¬¬(¬¬(n=1) ∨ ¬B)
    # est_premier = et(A,B) = ¬(¬A ∨ ¬B)  →  ¬premier = ¬¬(¬A∨¬B)  →  (¬A ∨ ¬B)
    disj = _dne(h_np, ou(non(A), non(B)))                # ¬A ∨ ¬B  (¬A = ¬¬(n=1))
    cible = existe(d, et(X, et(non(U), non(Ecas))))
    # branche gauche : ¬¬(n=1) → n=1 → ⊥ (contre h_ne1) → cible
    br_g = N.loi_deduction(non(A), ex_falso(_dne(N.assume(non(A)), egal(vn, un())),
                                            h_ne1, cible))
    # branche droite : ¬B = ¬¬∃d¬(...) → ∃d¬(...) → transport → cible
    interne = _du_niant_de_impl(X, U, Ecas)              # {¬(X⇒(U∨E))} ⊢ X∧(¬U∧¬E)
    transport = monotonie_existe(
        N.loi_deduction(non(impl(X, _ou(U, Ecas))), interne), d)
    #   transport : ∃d ¬(X⇒(U∨E)) ⇒ ∃d (X∧(¬U∧¬E))
    br_d = N.loi_deduction(non(B), mp(_dne(N.assume(non(B)),
                                           existe(d, non(impl(X, _ou(U, Ecas))))),
                                      transport))
    r = cas(disj, br_g, br_d)
    th = N.loi_deduction(H, r)
    assert th.est_clos and not th.hypotheses, "extraction_diviseur non clos"
    assert th.conclusion == extraction_diviseur_cible(n, d, q), (
        "extraction_diviseur : conclusion != cible")
    return th


__all__ = ["extraction_diviseur", "extraction_diviseur_cible"]
