# -*- coding: utf-8 -*-
"""Primalité effective, versant NÉGATIF  —  ⊢ ¬ est_premier( N(c) )  pour c composé.

LE TEST DE SANITÉ SÉMANTIQUE de l'encodage `goldbach.est_premier` (zone d'ombre
n°3, discussion Karl 8 août 2026) : le noyau doit pouvoir RÉFUTER la primalité
des non-premiers, sinon rien ne garantit que le prédicat dit « premier ».
`est_premier_num` (primalite.py) couvre le versant positif (2, 3, 5, 7…) ;
ce module couvre le dual : un témoin i (1 < i < c, i | c) réfute la clause
universelle, donc la conjonction.

LA ROUTE (duale de primalite.py, MÊMES constructeurs — jamais transcrits) :
  est_premier(N c) = et( ¬(N c = 1),  (∀d)( (Fini d ∧ d|N c) ⇒ (d=1 ∨ d=N c) ) )
  · X(N i)   : Fini N(i) (fini_num) ∧ N(i) | N(c) (divise_positif) ;
  · ¬Y(N i)  : ¬(N i = un()) (ne_num_sym + pont_un, motif de primalite) et
               ¬(N i = N c) (ne_num) — le « ou » _ou encodé se réfute par sa
               conjonction de négations ;
  · ¬(X ⇒ Y) : cas sur le ou primitif de l'implication, mort des deux côtés ;
  · ∃d ¬(…)  : témoin N(i) (existe_temoin_verifie, lieur d de l'énoncé) ;
  · ¬(∀d)    : pourtout = ¬∃¬ — une double négation (neg_intro) ;
  · ¬et(A,B) : de ¬B, ou-intro (s2+s3) puis neg_intro sur l'et encodé.
⚠️ Aucune modification de goldbach.py : l'énoncé réfuté est CELUI de la
campagne (défauts d="dgb", q="qgb"), à l'octet près."""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, non, ou, impl, pourtout, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, cas,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini,
)
import outils_ia.arithmetique.machine_num as M  # noqa: E402
from outils_ia.arithmetique.machine_num import NUM, fini_num  # noqa: E402
from outils_ia.arithmetique.non_divisibilite import divise_positif  # noqa: E402
import outils_ia.conjectures.goldbach as GB  # noqa: E402
from outils_ia.conjectures.goldbach import divise_propre, _ou  # noqa: E402
from outils_ia.conjectures.primalite import pont_un  # noqa: E402

mp = N.modus_ponens


def non_est_premier_num_cible(c, d="dgb", q="qgb"):
    """Énoncé visé : ¬ est_premier( N(c) )  (l'énoncé goldbach, tout-défaut)."""
    return non(GB.est_premier(NUM(c), d=d, q=q))


def non_est_premier_num(c, i, d="dgb", q="qgb"):
    """🎯 ⊢ ¬ est_premier( N(c) )   pour c composé, témoin i.   [CLOS, 0 hyp]

    Gardes Python (le noyau re-juge tout ; elles évitent les runs perdus) :
    i > 1, i ≠ c, i | c — le témoin réfutant la clause universelle.
    Couvre AUSSI c = 0 (témoin 2 : 2|0 par 0 = 2·0, produit_num gère n=0)."""
    assert i > 1 and i != c and c % i == 0, (
        "témoin invalide : il faut i > 1, i ≠ c et i|c")
    Nc, Ni, vd = NUM(c), NUM(i), var(d)

    # ── le MIROIR de l'énoncé (mêmes constructeurs que primalite.py) ────────
    A = non(egal(Nc, GB.un()))
    corps = impl(et(est_fini(vd), divise_propre(vd, Nc, q=q)),
                 _ou(egal(vd, GB.un()), egal(vd, Nc)))
    Bq = pourtout(d, corps)
    cible_premier = GB.est_premier(Nc, d=d, q=q)
    assert cible_premier == et(A, Bq), "miroir est_premier : forme inattendue"
    assert Bq == non(existe(d, non(corps))), "pourtout ≠ ¬∃¬ ?"
    but = non(cible_premier)

    # ── X(N i) : Fini N(i) ∧ N(i) | N(c) ────────────────────────────────────
    X_i = conjonction_intro(fini_num(i), divise_positif(i, c, q=q))
    Xf = et(est_fini(Ni), divise_propre(Ni, Nc, q=q))
    assert X_i.conclusion == Xf

    # ── ¬Y(N i) : le « ou » encodé se réfute par et(¬U, ¬E) ─────────────────
    n_i1 = M.reecrit(pont_un(), M.ne_num_sym(1, i),
                     non(egal(Ni, var(M._HOLE))))            # ¬(N i = un())
    assert n_i1.conclusion == non(egal(Ni, GB.un()))
    #   ne_num exige m < n ; pour i > c (cas c = 0), la version symétrisée
    n_ic = M.ne_num(i, c) if i < c else M.ne_num_sym(c, i)   # ¬(N i = N c)
    assert n_ic.conclusion == non(egal(Ni, Nc))
    Y = _ou(egal(Ni, GB.un()), egal(Ni, Nc))
    nY = M.neg_intro(Y, M.ex_falso(conjonction_intro(n_i1, n_ic),
                                   N.assume(Y), non(Y)))     # ¬Y

    # ── ¬( X(N i) ⇒ Y(N i) ) : cas sur le ou primitif, mort des deux côtés ──
    imp_f = impl(Xf, Y)                                      # = ou(¬Xf, Y)
    h_imp = N.assume(imp_f)
    br_nx = N.loi_deduction(non(Xf),
                            M.ex_falso(X_i, N.assume(non(Xf)), non(imp_f)))
    br_y = N.loi_deduction(Y, M.ex_falso(N.assume(Y), nY, non(imp_f)))
    n_imp = M.neg_intro(imp_f, cas(h_imp, br_nx, br_y))      # ¬(X ⇒ Y)

    # ── ∃d ¬(X ⇒ Y)  puis  ¬(∀d)(X ⇒ Y) ────────────────────────────────────
    ex = M.existe_temoin_verifie(n_imp, non(corps), Ni, d)
    assert ex.conclusion == existe(d, non(corps))
    nB = M.neg_intro(Bq, M.ex_falso(ex, N.assume(Bq), non(Bq)))   # ¬Bq

    # ── ¬et(A, Bq) : ou-intro droite (s2 + échange s3) puis neg_intro ───────
    disj = mp(mp(nB, N.s2(non(Bq), non(A))), N.s3(non(Bq), non(A)))
    assert disj.conclusion == ou(non(A), non(Bq))
    res = M.neg_intro(cible_premier,
                      M.ex_falso(disj, N.assume(cible_premier), but))
    assert res.conclusion == non_est_premier_num_cible(c, d=d, q=q)
    assert res.est_clos and not res.hypotheses, (
        "non_est_premier_num(%d) non clos" % c)
    return res


def non_est_premier_un(d="dgb", q="qgb"):
    """🎯 ⊢ ¬ est_premier( N(1) )   — 1 n'est pas premier.       [CLOS, 0 hyp]

    Ici c'est le CONJOINT GAUCHE qui meurt : A = ¬(N(1) = un()) est réfuté par
    le pont N(1) = un() lui-même (pont_un) — double négation, ou-intro gauche
    (s2 direct, pas d'échange), neg_intro sur l'et encodé."""
    N1 = NUM(1)
    A = non(egal(N1, GB.un()))
    corps = impl(et(est_fini(var(d)), divise_propre(var(d), N1, q=q)),
                 _ou(egal(var(d), GB.un()), egal(var(d), N1)))
    Bq = pourtout(d, corps)
    cible_premier = GB.est_premier(N1, d=d, q=q)
    assert cible_premier == et(A, Bq), "miroir est_premier(1) : forme inattendue"
    but = non(cible_premier)

    pont = pont_un()                                         # N(1) = un()
    assert pont.conclusion == egal(N1, GB.un())
    nA = M.neg_intro(A, M.ex_falso(pont, N.assume(A), non(A)))   # ¬A = ¬¬(N1=un())
    disj = mp(nA, N.s2(non(A), non(Bq)))                     # ¬A ∨ ¬Bq (s2 direct)
    assert disj.conclusion == ou(non(A), non(Bq))
    res = M.neg_intro(cible_premier,
                      M.ex_falso(disj, N.assume(cible_premier), but))
    assert res.conclusion == non_est_premier_num_cible(1, d=d, q=q)
    assert res.est_clos and not res.hypotheses, "non_est_premier_un non clos"
    return res


__all__ = ["non_est_premier_num", "non_est_premier_num_cible",
           "non_est_premier_un"]
