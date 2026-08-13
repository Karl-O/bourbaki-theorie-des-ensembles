# -*- coding: utf-8 -*-
"""BORNE DU DIVISEUR — d ≤ n (la mesure de la récurrence forte ; Euclide, brique E).

    ⊢ ( est_cardinal(d) ∧ ¬(n = 0) ∧ d | n ) ⇒ d ≤ n                     [CLOS]

Sous témoin w (n = d·w) : si w = ∅, n = Card(d×∅) = 0 (produit-zéro) — mort
par ex_falso contre n≠0 ; sinon {∅} ≤ w (un_inf_egal — son « 1 » EST le
singleton, mesuré BR2), la monotonie à droite donne d×{∅} ≤ d×w, puis le pont
d = Card(d×{∅}) (produit-un + Card d = d), les ponts Eq(X, Card X) ⇒ ≤ dans
les deux sens, deux transitivités de ≤, et deux réécritures de Leibniz.
Mesures BR1-BR2 : NUM(0) == ZERO (aucun pont côté zéro) ; lieur w LITTÉRAL =
nom d'élimination (leçon ev.331).
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, non, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu,
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
    est_cardinal, cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (  # noqa: E402
    _inf_egal_transitive_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_props_diverses import (  # noqa: E402
    equipotents_mutuellement_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre, _card_de_card_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_2_monotonie.ensembles_arith_cardinale_props_produit_monotone import (  # noqa: E402
    inf_egal_produit_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (  # noqa: E402
    produit_cardinal_un, produit_cardinal_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini, ZERO,
)

mp = N.modus_ponens
_SING = E.singleton(E.VIDE)


def _gen1_t(builder, nom, t):
    return instancie(N.generalisation(nom, builder(nom)), t)


def _pz_t(t):
    """⊢ Card(A×∅) = 0  (terme)."""
    return _gen1_t(produit_cardinal_zero, "Apzbr", t)


def _pu_t(t):
    """⊢ Card(A×{∅}) = Card A  (terme)."""
    return _gen1_t(produit_cardinal_un, "Apubr", t)


def _uie_t(t):
    """⊢ ¬(X=∅) ⇒ ({∅} ≤ X)  (terme)."""
    return _gen1_t(un_inf_egal_import, "Xuibr", t)


from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_un_borne import (  # noqa: E402
    un_inf_egal as un_inf_egal_import,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    _prop1_direct_t,  # (non utilisé — garde d'import homogène)  # noqa: F401
)


def _pdroite_t(tb, tb1, tc):
    """⊢ (B ≤ B₁) ⇒ (C×B ≤ C×B₁)  (termes)."""
    g = inf_egal_produit_droite("Bpdbr", "B1pdbr", "Cpdbr")
    gen = N.generalisation("Bpdbr", N.generalisation("B1pdbr",
          N.generalisation("Cpdbr", g)))
    return instancie(instancie(instancie(gen, tb), tb1), tc)


def _mut_t(tx, ty):
    """⊢ Eq(X,Y) ⇒ (X≤Y ∧ Y≤X)  (termes) — forme VÉRIFIÉE à l'usage (assert)."""
    g = equipotents_mutuellement_inf_egal("Xmubr", "Ymubr")
    gen = N.generalisation("Xmubr", N.generalisation("Ymubr", g))
    return instancie(instancie(gen, tx), ty)


def borne_diviseur_cible(d="dbr", n="nbr", w="wbr"):
    """Énoncé visé : (est_cardinal d ∧ ¬(n=0) ∧ d|n) ⇒ d ≤ n."""
    vd, vn = var(d), var(n)
    return impl(et(et(est_cardinal(vd), non(egal(vn, ZERO))),
                   divise_propre(vd, vn, q=w)),
                inf_egal_card(vd, vn))


def borne_diviseur(d="dbr", n="nbr", w="wbr"):
    """🎯 ⊢ (est_cardinal d ∧ ¬(n=0) ∧ d|n) ⇒ d ≤ n.                    [CLOS]"""
    vd, vn, vw = var(d), var(n), var(w)
    H = et(et(est_cardinal(vd), non(egal(vn, ZERO))),
           divise_propre(vd, vn, q=w))
    h = N.assume(H)
    hcd = conjonction_elim_gauche(conjonction_elim_gauche(h))    # est_cardinal d
    hn0 = conjonction_elim_droite(conjonction_elim_gauche(h))    # ¬(n=0)
    hdiv = conjonction_elim_droite(h)                            # d|n (∃w)
    card_d_eq = mp(hcd, _card_de_card_t(vd))                     # Card d = d

    m = et(est_fini(vw), egal(vn, produit_cardinal_binaire(vd, vw)))
    t = N.assume(m)
    eqn = conjonction_elim_droite(t)                             # n = Card(d×w)
    cible = inf_egal_card(vd, vn)
    dw = E.produit(vd, vw)
    dsing = E.produit(vd, _SING)

    # ── CAS A : w = ∅ → n = 0 → mort ────────────────────────────────────────
    ha = N.assume(egal(vw, E.VIDE))
    trou = var("wtroubr")
    cong = mp(ha, congruence_terme(vw, E.VIDE,
                                   cardinal(E.produit(vd, trou)), w="wtroubr"))
    n_eq_zero = composer_egalites(composer_egalites(eqn, cong), _pz_t(vd))
    assert n_eq_zero.conclusion == egal(vn, ZERO)
    brA = N.loi_deduction(egal(vw, E.VIDE), ex_falso_local(n_eq_zero, hn0, cible))

    # ── CAS B : w ≠ ∅ → {∅} ≤ w → d×{∅} ≤ d×w → d ≤ n ──────────────────────
    hb = N.assume(non(egal(vw, E.VIDE)))
    le1 = mp(hb, _uie_t(vw))                                     # {∅} ≤ w
    le2 = mp(le1, _pdroite_t(_SING, vw, vd))                     # d×{∅} ≤ d×w
    assert le2.conclusion == inf_egal_card(dsing, dw)
    # d = Card(d×{∅})
    d_eq = mp(composer_egalites(_pu_t(vd), card_d_eq),
              symetrie(cardinal(dsing), vd))                     # d = Card(d×{∅})
    assert d_eq.conclusion == egal(vd, cardinal(dsing))
    # ponts Eq : X ≤ Card X et Card X ≤ X (les deux ensembles-produits)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal,
    )
    eq_dsing = _gen1_t(equipotent_son_cardinal, "Xescbr", dsing)  # Eq(dsing, Card dsing)?
    both1 = mp(eq_dsing, _mut_t(dsing, cardinal(dsing)))
    card_le_set = conjonction_elim_droite(both1)                 # Card(dsing) ≤ dsing
    eq_dw = _gen1_t(equipotent_son_cardinal, "Xescbr", dw)
    both2 = mp(eq_dw, _mut_t(dw, cardinal(dw)))
    set_le_card = conjonction_elim_gauche(both2)                 # dw ≤ Card(dw)
    # transitivités : Card(dsing) ≤ dw, puis ≤ Card(dw)
    t1 = mp(conjonction_intro(card_le_set, le2),
            _inf_egal_transitive_t(cardinal(dsing), dsing, dw))
    t2 = mp(conjonction_intro(t1, set_le_card),
            _inf_egal_transitive_t(cardinal(dsing), dw, cardinal(dw)))
    assert t2.conclusion == inf_egal_card(cardinal(dsing), cardinal(dw))
    # Leibniz : Card(dsing) → d  puis  Card(dw) → n
    from outils_ia.arithmetique.machine_num import reecrit, _HOLE
    r1 = reecrit(mp(d_eq, symetrie(vd, cardinal(dsing))), t2,
                 inf_egal_card(var(_HOLE), cardinal(dw)))
    r2 = reecrit(mp(eqn, symetrie(vn, cardinal(dw))), r1,
                 inf_egal_card(vd, var(_HOLE)))
    assert r2.conclusion == cible
    brB = N.loi_deduction(non(egal(vw, E.VIDE)), r2)

    r = cas(tiers_exclu(egal(vw, E.VIDE)), brA, brB)
    rr = mp(hdiv, existe_elimination(N.loi_deduction(m, r), w))
    th = N.loi_deduction(H, rr)
    assert th.est_clos and not th.hypotheses, "borne_diviseur non clos"
    assert th.conclusion == borne_diviseur_cible(d, n, w), (
        "borne_diviseur : conclusion != cible")
    return th


def ex_falso_local(thm_p, thm_np, cible):
    from outils_ia.arithmetique.machine_num import ex_falso
    return ex_falso(thm_p, thm_np, cible)


__all__ = ["borne_diviseur", "borne_diviseur_cible"]
