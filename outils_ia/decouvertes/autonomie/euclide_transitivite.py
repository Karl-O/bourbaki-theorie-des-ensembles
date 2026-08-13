# -*- coding: utf-8 -*-
"""TRANSITIVITÉ de la divisibilité — 2ᵉ pilier de la récurrence forte (Euclide, brique C).

    ⊢ ( est_cardinal(b) ∧ b|a ∧ a|c ) ⇒ b|c                              [CLOS]

Le couloir : sous témoins w1 (a = b·w1) et w2 (c = a·w2),
    c = Card(Card(b×w1) × w2)         [congruence de = sur eq1 dans eq2]
      = Card((b×w1) × w2)             [bien_defini symétrisé : (refl, Card w2 = w2)]
      = Card(b × (w1×w2))             [associativité du produit cardinal]
      = b · Card(w1×w2)               [bien_defini : (Card b = b, refl)]
et le témoin Q := w1·w2 est FINI (produit_binaire_entier). ∃-intro par la
tactique à témoin vérifié, puis DOUBLE ∃-élimination : les lieurs des deux
hypothèses (w1tr, w2tr) sont choisis pour coïncider LITTÉRALEMENT avec les
noms d'élimination — zéro α-gymnastique (playbook collisions) ; la conclusion
b|c reprend le lieur « qdiv » du dépôt (réflexif, producteur).
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (  # noqa: E402
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (  # noqa: E402
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (  # noqa: E402
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (  # noqa: E402
    est_cardinal, cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre, _card_de_card_t, _pcbd_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire, produit_cardinal_associatif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (  # noqa: E402
    produit_binaire_entier,
)
from outils_ia.arithmetique.machine_num import fic_t, existe_temoin_verifie  # noqa: E402

mp = N.modus_ponens


def _assoc_t(tx, ty, tz):
    """⊢ Card((X×Y)×Z) = Card(X×(Y×Z))  (version TERME capture-safe)."""
    g = produit_cardinal_associatif("Xastr", "Yastr", "Zastr")
    gen = N.generalisation("Xastr", N.generalisation("Yastr",
          N.generalisation("Zastr", g)))
    return instancie(instancie(instancie(gen, tx), ty), tz)


def transitivite_divise_cible(b="btr", a="atr", c="ctr", w1="w1tr", w2="w2tr"):
    """Énoncé visé : (est_cardinal b ∧ b|a ∧ a|c) ⇒ b|c   (b|c sur « qdiv »)."""
    vb, va, vc = var(b), var(a), var(c)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    return impl(et(et(est_cardinal(vb), divise_propre(vb, va, q=w1)),
                   divise_propre(va, vc, q=w2)),
                divise_propre(vb, vc, q="qdiv"))


def transitivite_divise(b="btr", a="atr", c="ctr", w1="w1tr", w2="w2tr"):
    """🎯 ⊢ (est_cardinal b ∧ b|a ∧ a|c) ⇒ b|c.                        [CLOS]"""
    vb, va, vc, vw1, vw2 = var(b), var(a), var(c), var(w1), var(w2)
    H = et(et(est_cardinal(vb), divise_propre(vb, va, q=w1)),
           divise_propre(va, vc, q=w2))
    h = N.assume(H)
    hA = conjonction_elim_gauche(conjonction_elim_gauche(h))     # est_cardinal b
    hB = conjonction_elim_droite(conjonction_elim_gauche(h))     # b|a  (∃w1)
    hC = conjonction_elim_droite(h)                              # a|c  (∃w2)
    card_b_eq = mp(hA, _card_de_card_t(vb))                      # Card b = b

    # ── sous les témoins LIBRES w1, w2 (mêmes noms que les lieurs des hyps) ──
    m1 = et(est_fini(vw1), egal(va, produit_cardinal_binaire(vb, vw1)))
    m2 = et(est_fini(vw2), egal(vc, produit_cardinal_binaire(va, vw2)))
    t1 = N.assume(m1)
    t2 = N.assume(m2)
    fin1, eq1 = conjonction_elim_gauche(t1), conjonction_elim_droite(t1)
    fin2, eq2 = conjonction_elim_gauche(t2), conjonction_elim_droite(t2)

    P = E.produit(vb, vw1)                     # b×w1  (ensemble)
    CardP = cardinal(P)                        # = b·w1
    W = E.produit(vw1, vw2)                    # w1×w2
    Q = cardinal(W)                            # témoin : w1·w2

    # (1) c = Card(CardP × w2)   [réécrit a ↦ CardP dans c = Card(a×w2)]
    trou = var("wtrou_tr")
    motif = cardinal(E.produit(trou, vw2))
    cong1 = mp(eq1, congruence_terme(va, CardP, motif, w="wtrou_tr"))
    c2 = composer_egalites(eq2, cong1)
    assert c2.conclusion == egal(vc, cardinal(E.produit(CardP, vw2)))

    # (2) … = Card((b×w1) × w2)   [bien_defini(P, w2, CardP, w2), symétrisé]
    card_w2_eq = mp(mp(fin2, fic_t(vw2)), _card_de_card_t(vw2))  # Card w2 = w2
    bdP = mp(conjonction_intro(N.reflexivite(CardP), card_w2_eq),
             _pcbd_t(P, vw2, CardP, vw2))
    #   bdP : Card(P×w2) = Card(CardP×w2) ; on la retourne
    g, d_ = bdP.conclusion.termes
    c3 = composer_egalites(c2, mp(bdP, symetrie(g, d_)))
    assert c3.conclusion == egal(vc, cardinal(E.produit(P, vw2)))

    # (3) … = Card(b × (w1×w2))   [associativité]
    c4 = composer_egalites(c3, _assoc_t(vb, vw1, vw2))
    assert c4.conclusion == egal(vc, cardinal(E.produit(vb, W)))

    # (4) … = b · Q               [bien_defini(b, W, b, Q) : (Card b = b, refl Q)]
    bdQ = mp(conjonction_intro(card_b_eq, N.reflexivite(Q)),
             _pcbd_t(vb, W, vb, Q))
    c5 = composer_egalites(c4, bdQ)
    assert c5.conclusion == egal(vc, produit_cardinal_binaire(vb, Q))

    # (5) Fini Q                  [produit de finis]
    finQ = mp(conjonction_intro(fin1, fin2), produit_binaire_entier(w1, w2))
    assert finQ.conclusion == est_fini(produit_cardinal_binaire(vw1, vw2))

    # (6) ∃-intro (témoin Q, lieur « qdiv » du dépôt)
    matrice = et(est_fini(var("qdiv")),
                 egal(vc, produit_cardinal_binaire(vb, var("qdiv"))))
    ex = existe_temoin_verifie(conjonction_intro(finQ, c5), matrice, Q, "qdiv")
    assert ex.conclusion == divise_propre(vb, vc, q="qdiv")

    # (7) double ∃-élimination (lieurs = noms d'élimination, LITTÉRALEMENT)
    r2 = mp(hC, existe_elimination(N.loi_deduction(m2, ex), w2))
    r1 = mp(hB, existe_elimination(N.loi_deduction(m1, r2), w1))
    th = N.loi_deduction(H, r1)
    assert th.est_clos and not th.hypotheses, "transitivite_divise non clos"
    assert th.conclusion == transitivite_divise_cible(b, a, c, w1, w2), (
        "transitivite_divise : conclusion != cible")
    return th


__all__ = ["transitivite_divise", "transitivite_divise_cible"]
