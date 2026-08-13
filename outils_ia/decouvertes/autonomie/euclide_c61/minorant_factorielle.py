# -*- coding: utf-8 -*-
"""MINORANT DE LA FACTORIELLE — ⊢ (∀n)( Fini n ⇒ 1 ≤ n! )   (Euclide-infinitude).

La pièce qui rend succ(n!) ≠ 1 dans l'assemblage (via l'injectivité du
successeur : succ(n!) = 1 = succ(0) ⇒ n! = 0, or 1 ≤ n! l'interdit).
Récurrence C61 : base = réflexivité + f(0)=1 ; pas = monotonie droite du
produit par {∅} ≤ succ n (un_inf_egal — succ n ≠ ∅ se DÉRIVE sans lemme
neuf : succ n = ∅ ⇒ Card(succ n) = 0 ⇒ succ n = 0, et succ n = 0 avec
0 ≤ n donnerait succ n ≤ n, mort par succ_pas_inf_egal), pont Card
(motif borne), produit_cardinal_un, Leibniz ultime, transitivité."""
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
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (  # noqa: E402
    symetrie, composer_egalites, congruence_terme, equivalence_avant,
    equivalence_arriere,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (  # noqa: E402
    equipotent_son_cardinal, inf_egal_reflexif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_props_diverses import (  # noqa: E402
    equipotents_mutuellement_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_un_borne import (  # noqa: E402
    un_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    _card_de_card_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_2_monotonie.ensembles_arith_cardinale_props_produit_monotone import (  # noqa: E402
    inf_egal_produit_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (  # noqa: E402
    produit_cardinal_un,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (  # noqa: E402
    fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (  # noqa: E402
    successeur_est_un_cardinal,
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
    succ_pas_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (  # noqa: E402
    zero_inf_egal_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import (  # noqa: E402
    _fini_dans_NN,
)
from outils_ia.arithmetique.machine_num import ex_falso, neg_intro  # noqa: E402
from outils_ia.decouvertes.autonomie.euclide_c61.fini_factorielle import (  # noqa: E402
    fini_factorielle,
)

mp = N.modus_ponens
_SING = E.singleton(E.VIDE)


def _cut(thm, hyp, preuve_hyp):
    return mp(preuve_hyp, N.loi_deduction(hyp, thm))


def _gen1_t(builder, nom, t):
    return instancie(N.generalisation(nom, builder(nom)), t)


def _fic_t(t):
    return _gen1_t(fini_implique_cardinal, "AficM", t)


def _mut_t(tx, ty):
    g = equipotents_mutuellement_inf_egal("XmuM", "YmuM")
    gen = N.generalisation("XmuM", N.generalisation("YmuM", g))
    return instancie(instancie(gen, tx), ty)


def _pdroite_t(tb, tb1, tc):
    g = inf_egal_produit_droite("BpdM", "B1pdM", "CpdM")
    gen = N.generalisation("BpdM", N.generalisation("B1pdM",
          N.generalisation("CpdM", g)))
    return instancie(instancie(instancie(gen, tb), tb1), tc)


def _card_le_card(le_set, tx, ty):
    """De ⊢ X ≤ Y (ensembles), ⊢ Card X ≤ Card Y  (pont borne)."""
    both_x = mp(_gen1_t(equipotent_son_cardinal, "XescM", tx),
                _mut_t(tx, cardinal(tx)))
    both_y = mp(_gen1_t(equipotent_son_cardinal, "XescM", ty),
                _mut_t(ty, cardinal(ty)))
    t1 = mp(conjonction_intro(conjonction_elim_droite(both_x), le_set),
            _inf_egal_transitive_t(cardinal(tx), tx, ty))
    return mp(conjonction_intro(t1, conjonction_elim_gauche(both_y)),
              _inf_egal_transitive_t(cardinal(tx), ty, cardinal(ty)))


def _rw_avant(eq_thm, motif_w, w, thm):
    x, y = eq_thm.conclusion.termes
    return mp(thm, equivalence_avant(mp(eq_thm, N.s6(x, y, w, motif_w))))


def _rw_arriere(eq_thm, motif_w, w, thm):
    x, y = eq_thm.conclusion.termes
    return mp(thm, equivalence_arriere(mp(eq_thm, N.s6(x, y, w, motif_w))))


def minorant_factorielle_cible(n="nMF"):
    """Énoncé visé : (∀n)( Fini n ⇒ 1 ≤ n! )."""
    vn = var(n)
    return pourtout(n, impl(est_fini(vn), inf_egal_card(UN, factorielle_def2(vn))))


def minorant_factorielle(n="nMF", k="kpred"):
    """🎯 ⊢ (∀n)( Fini n ⇒ 1 ≤ n! ).                                     [CLOS]"""
    vn = var(n)
    trou = var("wtrouM")

    def P(t):
        return inf_egal_card(UN, factorielle_def2(t))

    # ── BASE : 1 ≤ f(0)  (réflexivité + f(0)=1, Leibniz arrière) ────────────
    eq0 = factorielle_def2_zero()                            # f(0) = 1
    refl = _gen1_t(inf_egal_reflexif, "XrlM", UN)            # 1 ≤ 1
    p0 = _rw_arriere(eq0, inf_egal_card(UN, var("wM0")), "wM0", refl)
    assert p0.conclusion == P(ZERO), "base : P(0) mal formé"

    # ── PAS : {Fini n ∧ 1 ≤ f(n)} ⊢ 1 ≤ f(succ n) ──────────────────────────
    hstep = N.assume(et(est_fini(vn), P(vn)))
    fini_n = conjonction_elim_gauche(hstep)
    un_le_fn = conjonction_elim_droite(hstep)
    card_n = mp(fini_n, _fic_t(vn))
    fn = factorielle_def2(vn)
    sn = successeur(vn)
    fsn = factorielle_def2(sn)
    fini_fn = mp(fini_n, instancie(fini_factorielle(), vn))  # Fini(n!) [brique F]
    card_fn_eq = mp(mp(fini_fn, _fic_t(fn)), _card_de_card_t(fn))  # Card fn = fn

    # succ n ≠ 0 : sinon succ n ≤ n (0 ≤ n + Leibniz), mort succ_pas_inf_egal
    hsz = N.assume(egal(sn, ZERO))
    z_le = _cut(zero_inf_egal_cardinal(vn),
                est_cardinal(vn), card_n)                    # 0 ≤ n
    sle = _rw_arriere(hsz, inf_egal_card(var("wM1"), vn), "wM1", z_le)
    spie = mp(fini_n, _gen1_t(succ_pas_inf_egal, "BspM", vn))
    n_sz = neg_intro(egal(sn, ZERO),
                     ex_falso(sle, spie, non(egal(sn, ZERO))))   # ¬(succ n = 0)

    # succ n ≠ ∅ : sinon Card(succ n) = 0 puis succ n = 0 — mort
    hsv = N.assume(egal(sn, E.VIDE))
    cgv = mp(hsv, congruence_terme(sn, E.VIDE, cardinal(trou), w="wtrouM"))
    assert cgv.conclusion == egal(cardinal(sn), ZERO)
    card_sn_eq = mp(_gen1_t(successeur_est_un_cardinal, "AscM", vn),
                    _card_de_card_t(sn))                     # Card(succ n) = succ n
    sn_eq_0 = composer_egalites(mp(card_sn_eq, symetrie(cardinal(sn), sn)), cgv)
    assert sn_eq_0.conclusion == egal(sn, ZERO)
    n_sv = neg_intro(egal(sn, E.VIDE),
                     ex_falso(sn_eq_0, n_sz, non(egal(sn, E.VIDE))))

    # {∅} ≤ succ n → monotonie droite → pont Card → produit_cardinal_un
    sing_le = mp(n_sv, _gen1_t(un_inf_egal, "XuiM", sn))     # {∅} ≤ succ n
    le_set = mp(sing_le, _pdroite_t(_SING, sn, fn))          # fn×{∅} ≤ fn×succ n
    le_card = _card_le_card(le_set, E.produit(fn, _SING), E.produit(fn, sn))
    pu = _gen1_t(produit_cardinal_un, "ApuM", fn)            # Card(fn×{∅}) = Card fn
    eq_pu = composer_egalites(pu, card_fn_eq)                # Card(fn×{∅}) = fn
    fn_le_pcb = _rw_avant(eq_pu, inf_egal_card(
        var("wM2"), produit_cardinal_binaire(fn, sn)), "wM2", le_card)
    assert fn_le_pcb.conclusion == inf_egal_card(fn, produit_cardinal_binaire(fn, sn))

    # pont n∈ℕ + ultime : f(succ n) = fn·succ n, Leibniz arrière sur le membre droit
    n_NN = mp(fini_n, _fini_dans_NN(vn))
    ult = factorielle_def2_ultime(n)
    hyp_u = next(iter(ult.hypotheses))
    assert n_NN.conclusion == hyp_u, "pont ≠ hyp ultime"
    eq_s = _cut(ult, hyp_u, n_NN)                            # f(succ n) = fn·succ n
    fn_le_fsn = _rw_arriere(eq_s, inf_egal_card(fn, var("wM3")), "wM3", fn_le_pcb)
    p_sn = mp(conjonction_intro(un_le_fn, fn_le_fsn),
              _inf_egal_transitive_t(UN, fn, fsn))           # 1 ≤ f(succ n)
    assert p_sn.conclusion == P(sn)
    step = N.generalisation(n, N.loi_deduction(et(est_fini(vn), P(vn)), p_sn))
    assert step.conclusion == _fini_et_P_implique_succ(P, n), "pas mal formé"

    # ── PRINCIPE C61 + décharge ─────────────────────────────────────────────
    princ = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ.hypotheses
    princ = _cut(princ, pfu, predecesseur_fini_universel_preuve(k=k))
    res = mp(conjonction_intro(p0, step), princ)
    assert res.est_clos and not res.hypotheses, "minorant_factorielle non clos"
    assert res.conclusion == minorant_factorielle_cible(n), (
        "minorant_factorielle : conclusion != cible")
    return res


__all__ = ["minorant_factorielle", "minorant_factorielle_cible"]
