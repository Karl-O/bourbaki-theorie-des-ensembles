# -*- coding: utf-8 -*-
"""DIVISIBILITÉ ET PRODUIT — les deux micro-briques du pas de G (Euclide-infinitude).

    divise_produit_droite : ⊢ (est_cardinal d ∧ d|a ∧ Fini b) ⇒ d | a·b   [G2]
    divise_produit_gauche : ⊢ Fini a ⇒ b | a·b                             [G3]

G2 = le couloir de la transitivité (ev.331) où la cible a·b est FORMÉE (départ
par congruence sur a = d·w, pas d'équation hypothésée) : sous témoin w,
    a·b = Card((d·w)×b) = Card((d×w)×b) = Card(d×(w×b)) = d·(w·b),
témoin Q = w·b fini (produit_binaire_entier), ∃-intro « qdiv », ∃-élim w
(lieur LITTÉRAL). G3 = commutation seule : a·b = Card(a×b) = Card(b×a) = b·a,
témoin a — aucune élimination."""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[4]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, impl,
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
    produit_cardinal_binaire, produit_cardinal_associatif, produit_cardinal_commutatif,
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
    """⊢ Card((X×Y)×Z) = Card(X×(Y×Z))  (version terme capture-safe)."""
    g = produit_cardinal_associatif("Xasdp", "Yasdp", "Zasdp")
    gen = N.generalisation("Xasdp", N.generalisation("Yasdp",
          N.generalisation("Zasdp", g)))
    return instancie(instancie(instancie(gen, tx), ty), tz)


def _comm_t(tx, ty):
    """⊢ Card(X×Y) = Card(Y×X)  (version terme capture-safe)."""
    g = produit_cardinal_commutatif("Xcmdp", "Ycmdp")
    gen = N.generalisation("Xcmdp", N.generalisation("Ycmdp", g))
    return instancie(instancie(gen, tx), ty)


def divise_produit_droite_cible(d="dg2", a="ag2", b="bg2", w="wg2"):
    """Énoncé visé : (est_cardinal d ∧ d|a ∧ Fini b) ⇒ d | a·b."""
    vd, va, vb = var(d), var(a), var(b)
    return impl(et(et(est_cardinal(vd), divise_propre(vd, va, q=w)),
                   est_fini(vb)),
                divise_propre(vd, produit_cardinal_binaire(va, vb), q="qdiv"))


def divise_produit_droite(d="dg2", a="ag2", b="bg2", w="wg2"):
    """🎯 ⊢ (est_cardinal d ∧ d|a ∧ Fini b) ⇒ d | a·b.                  [G2]"""
    vd, va, vb, vw = var(d), var(a), var(b), var(w)
    H = et(et(est_cardinal(vd), divise_propre(vd, va, q=w)), est_fini(vb))
    h = N.assume(H)
    hcd = conjonction_elim_gauche(conjonction_elim_gauche(h))    # est_cardinal d
    hdiv = conjonction_elim_droite(conjonction_elim_gauche(h))   # d|a  (∃w)
    hfb = conjonction_elim_droite(h)                             # Fini b
    card_d_eq = mp(hcd, _card_de_card_t(vd))                     # Card d = d

    # ── sous le témoin LIBRE w (même nom que le lieur de l'hypothèse) ────────
    m = et(est_fini(vw), egal(va, produit_cardinal_binaire(vd, vw)))
    t = N.assume(m)
    finw, eq1 = conjonction_elim_gauche(t), conjonction_elim_droite(t)

    C = produit_cardinal_binaire(va, vb)       # a·b — LA CIBLE (= Card(a×b))
    P = E.produit(vd, vw)                      # d×w
    CardP = cardinal(P)                        # = d·w
    W = E.produit(vw, vb)                      # w×b
    Q = cardinal(W)                            # témoin : w·b

    # (1) a·b = Card(CardP × b)   [congruence a ↦ CardP dans Card(a×b)]
    trou = var("wtrou_dp")
    cong1 = mp(eq1, congruence_terme(va, CardP,
                                     cardinal(E.produit(trou, vb)), w="wtrou_dp"))
    assert cong1.conclusion == egal(C, cardinal(E.produit(CardP, vb)))

    # (2) … = Card((d×w) × b)   [bien_defini(P, b, CardP, b), symétrisé]
    card_b_eq = mp(mp(hfb, fic_t(vb)), _card_de_card_t(vb))      # Card b = b
    bdP = mp(conjonction_intro(N.reflexivite(CardP), card_b_eq),
             _pcbd_t(P, vb, CardP, vb))
    g_, d_ = bdP.conclusion.termes
    c3 = composer_egalites(cong1, mp(bdP, symetrie(g_, d_)))
    assert c3.conclusion == egal(C, cardinal(E.produit(P, vb)))

    # (3) … = Card(d × (w×b))   [associativité]
    c4 = composer_egalites(c3, _assoc_t(vd, vw, vb))
    assert c4.conclusion == egal(C, cardinal(E.produit(vd, W)))

    # (4) … = d · Q             [bien_defini(d, W, d, Q) : (Card d = d, refl Q)]
    bdQ = mp(conjonction_intro(card_d_eq, N.reflexivite(Q)),
             _pcbd_t(vd, W, vd, Q))
    c5 = composer_egalites(c4, bdQ)
    assert c5.conclusion == egal(C, produit_cardinal_binaire(vd, Q))

    # (5) Fini Q                [produit de finis]
    finQ = mp(conjonction_intro(finw, hfb), produit_binaire_entier(w, b))
    assert finQ.conclusion == est_fini(produit_cardinal_binaire(vw, vb))

    # (6) ∃-intro (témoin Q, lieur « qdiv ») puis (7) ∃-élim w
    matrice = et(est_fini(var("qdiv")),
                 egal(C, produit_cardinal_binaire(vd, var("qdiv"))))
    ex = existe_temoin_verifie(conjonction_intro(finQ, c5), matrice, Q, "qdiv")
    assert ex.conclusion == divise_propre(vd, C, q="qdiv")
    r = mp(hdiv, existe_elimination(N.loi_deduction(m, ex), w))
    th = N.loi_deduction(H, r)
    assert th.est_clos and not th.hypotheses, "divise_produit_droite non clos"
    assert th.conclusion == divise_produit_droite_cible(d, a, b, w), (
        "divise_produit_droite : conclusion != cible")
    return th


def divise_produit_gauche_cible(b="bg3", a="ag3"):
    """Énoncé visé : Fini a ⇒ b | a·b."""
    va, vb = var(a), var(b)
    return impl(est_fini(va),
                divise_propre(vb, produit_cardinal_binaire(va, vb), q="qdiv"))


def divise_produit_gauche(b="bg3", a="ag3"):
    """🎯 ⊢ Fini a ⇒ b | a·b   (témoin a, commutation seule).           [G3]"""
    va, vb = var(a), var(b)
    h = N.assume(est_fini(va))
    C = produit_cardinal_binaire(va, vb)
    comm = _comm_t(va, vb)                                       # a·b = b·a
    assert comm.conclusion == egal(C, produit_cardinal_binaire(vb, va))
    matrice = et(est_fini(var("qdiv")),
                 egal(C, produit_cardinal_binaire(vb, var("qdiv"))))
    ex = existe_temoin_verifie(conjonction_intro(h, comm), matrice, va, "qdiv")
    assert ex.conclusion == divise_propre(vb, C, q="qdiv")
    th = N.loi_deduction(est_fini(va), ex)
    assert th.est_clos and not th.hypotheses, "divise_produit_gauche non clos"
    assert th.conclusion == divise_produit_gauche_cible(b, a), (
        "divise_produit_gauche : conclusion != cible")
    return th


__all__ = ["divise_produit_droite", "divise_produit_droite_cible",
           "divise_produit_gauche", "divise_produit_gauche_cible"]
