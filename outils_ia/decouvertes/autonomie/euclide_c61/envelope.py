# -*- coding: utf-8 -*-
"""L'ENVELOPPE C61 — LE DIVISEUR PREMIER UNIVERSEL (Euclide, l'assembleur final).

    ⊢ (∀n)( Fini n ⇒ [ (Fini n ∧ n≠0 ∧ n≠1) ⇒ ∃p( premier p ∧ Fini p ∧ p|n ) ] )

Récurrence FORTE (principe prouvé du dépôt, `recurrence_forte`) assemblant les
QUATRE briques du jour : au pas, tiers exclu sur la primalité de n —
  · n premier  : témoin p := n (réflexivité de |, inline du producteur) ;
  · n composé  : extraction → d (d|n, d≠1, d≠n) → micro-F2 (d≠0 : sinon
    n = Card(0×w) = 0, via ZERO == Card(∅), bien_defini, commutatif,
    produit-zéro — contra n≠0) → borne → d ≤ n → d < n (définitionnel) →
    hypothèse forte S{n} en d → R(d) → p (premier, fini, p|d) →
    transitivité → p|n.
GRAPHIE UNIQUE : est_premier(·, d="dep", q="qep") partout ; divisibilité du
corps en « qdiv » (le lieur du dépôt) ; celle de l'extraction en « qep ».
Lieurs d'∃-élimination LITTÉRAUX (dep, pex, qep2) — leçon ev.331.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[4]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, non, impl, existe, pourtout,
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
    est_cardinal, cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre, divise_propre_reflexif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire, produit_cardinal_commutatif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (  # noqa: E402
    produit_cardinal_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    _card_de_card_t, _pcbd_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_forte_preuve import (  # noqa: E402
    recurrence_forte,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (  # noqa: E402
    s_recurrence_forte, hypothese_recurrence_forte,
)
from outils_ia.arithmetique.machine_num import (                      # noqa: E402
    fic_t, existe_temoin_verifie, ex_falso, neg_intro, reecrit, _HOLE,
)
from outils_ia.conjectures.goldbach import est_premier, un            # noqa: E402
from outils_ia.decouvertes.autonomie.euclide_extraction import extraction_diviseur  # noqa: E402
from outils_ia.decouvertes.autonomie.euclide_borne import borne_diviseur  # noqa: E402
from outils_ia.decouvertes.autonomie.euclide_transitivite import transitivite_divise  # noqa: E402

mp = N.modus_ponens


def _corps(t, p="pex"):
    """∃-matrice de R : premier p ∧ Fini p ∧ p | t   (au binder p)."""
    vp = var(p)
    return et(est_premier(vp, d="dep", q="qep"),
              et(est_fini(vp), divise_propre(vp, t, q="qdiv")))


def _R(t):
    """R{t} := (Fini t ∧ t≠0 ∧ t≠1) ⇒ ∃p( premier p ∧ Fini p ∧ p|t )."""
    return impl(et(et(est_fini(t), non(egal(t, ZERO))), non(egal(t, un()))),
                existe("pex", _corps(t)))


def _comm_t(tx, ty):
    """⊢ Card(X×Y) = Card(Y×X)  (termes)."""
    g = produit_cardinal_commutatif("Xcmc61", "Ycmc61")
    gen = N.generalisation("Xcmc61", N.generalisation("Ycmc61", g))
    return instancie(instancie(gen, tx), ty)


def _pz_t(t):
    g = N.generalisation("Apzc61", produit_cardinal_zero("Apzc61"))
    return instancie(g, t)


def _pas(n="nfor"):
    """{S{n}} ⊢ R{n}   — le pas de la récurrence forte (les 4 briques)."""
    vn = var(n)
    Sn = s_recurrence_forte(_R, vn, p="pfor")
    hS = N.assume(Sn)
    ante = et(et(est_fini(vn), non(egal(vn, ZERO))), non(egal(vn, un())))
    hA = N.assume(ante)
    h_fini = conjonction_elim_gauche(conjonction_elim_gauche(hA))
    h_n0 = conjonction_elim_droite(conjonction_elim_gauche(hA))
    h_n1 = conjonction_elim_droite(hA)
    but_ex = existe("pex", _corps(vn))
    P = est_premier(vn, d="dep", q="qep")

    # ── branche PREMIÈRE : témoin n ─────────────────────────────────────────
    hp = N.assume(P)
    card_n = mp(h_fini, fic_t(vn))
    div_nn = mp(card_n, divise_propre_reflexif(n))
    tw = conjonction_intro(hp, conjonction_intro(h_fini, div_nn))
    exP = existe_temoin_verifie(tw, _corps(vn), vn, "pex")
    brP = N.loi_deduction(P, exP)

    # ── branche COMPOSÉE ────────────────────────────────────────────────────
    hnp = N.assume(non(P))
    extr = mp(conjonction_intro(h_n1, hnp), extraction_diviseur(n, "dep", "qep"))
    #   ∃dep( (Fini dep ∧ dep|n[qep]) ∧ (dep≠1 ∧ dep≠n) )
    vd = var("dep")
    m_d = et(et(est_fini(vd), divise_propre(vd, vn, q="qep")),
             et(non(egal(vd, un())), non(egal(vd, vn))))
    td = N.assume(m_d)
    fin_d = conjonction_elim_gauche(conjonction_elim_gauche(td))
    div_dn = conjonction_elim_droite(conjonction_elim_gauche(td))
    d_ne1 = conjonction_elim_gauche(conjonction_elim_droite(td))
    d_nen = conjonction_elim_droite(conjonction_elim_droite(td))

    # micro-F2 : ¬(dep = 0) — sinon n = Card(0×w) = 0, contra n≠0
    vq2 = var("qep")   # LIEUR LITTÉRAL de la divisibilité d extraction
    m3 = et(est_fini(vq2), egal(vn, produit_cardinal_binaire(vd, vq2)))
    t3 = N.assume(m3)
    fin_q2 = conjonction_elim_gauche(t3)
    eq_n = conjonction_elim_droite(t3)                   # n = Card(dep×qep2)
    hz = N.assume(egal(vd, ZERO))
    cong = mp(hz, congruence_terme(vd, ZERO,
                                   cardinal(E.produit(var("wtc61"), vq2)),
                                   w="wtc61"))
    n_eq_zq = composer_egalites(eq_n, cong)              # n = Card(ZERO×qep2)
    #   Card(ZERO×q2) = Card(∅×q2)  :  bien_defini(∅, q2, ZERO, q2) symétrisé
    card_q2 = mp(mp(fin_q2, fic_t(vq2)), _card_de_card_t(vq2))   # Card q2 = q2
    bd0 = mp(conjonction_intro(N.reflexivite(ZERO), card_q2),
             _pcbd_t(E.VIDE, vq2, ZERO, vq2))
    #   bd0 : Card(∅×q2) = Card(ZERO×q2)   (ZERO == Card(∅) comme TERMES)
    g0, d0 = bd0.conclusion.termes
    n_eq_vq = composer_egalites(n_eq_zq, mp(bd0, symetrie(g0, d0)))
    #   n = Card(∅×q2) → commutatif → Card(q2×∅) → produit-zéro → Card(∅) = ZERO
    n_eq_final = composer_egalites(composer_egalites(n_eq_vq,
                                   _comm_t(E.VIDE, vq2)), _pz_t(vq2))
    falso = ex_falso(n_eq_final, h_n0, non(egal(vd, ZERO)))
    nz_sous_m3 = neg_intro(egal(vd, ZERO), falso)        # ¬(dep=0)  [sous m3]
    d_ne0 = mp(div_dn, existe_elimination(
        N.loi_deduction(m3, nz_sous_m3), "qep"))        # ¬(dep=0)

    # borne : d ≤ n  puis  d < n (définitionnel)
    card_d = mp(fin_d, fic_t(vd))
    le_dn = mp(conjonction_intro(conjonction_intro(card_d, h_n0), div_dn),
               borne_diviseur("dep", n, "qep"))
    lt_dn = conjonction_intro(le_dn, d_nen)              # d < n
    assert lt_dn.conclusion == inf_strict_card(vd, vn)

    # hypothèse forte en d → R(d) → son existentiel
    Rd = mp(conjonction_intro(conjonction_intro(h_fini, fin_d), lt_dn),
            instancie(hS, vd))
    exd = mp(conjonction_intro(conjonction_intro(fin_d, d_ne0), d_ne1), Rd)
    #   ∃pex( premier ∧ Fini ∧ pex|dep[qdiv] )
    vp = var("pex")
    m_p = _corps(vd, p="pex")
    tp = N.assume(m_p)
    prem_p = conjonction_elim_gauche(tp)
    fin_p = conjonction_elim_gauche(conjonction_elim_droite(tp))
    div_pd = conjonction_elim_droite(conjonction_elim_droite(tp))

    # transitivité : p|d ∧ d|n ⇒ p|n
    ecard_p = mp(fin_p, fic_t(vp))       # fic conclut DIRECTEMENT est_cardinal(p)
    div_pn = mp(conjonction_intro(conjonction_intro(ecard_p, div_pd), div_dn),
                transitivite_divise("pex", "dep", n, w1="qdiv", w2="qep"))
    tw2 = conjonction_intro(prem_p, conjonction_intro(fin_p, div_pn))
    exN = existe_temoin_verifie(tw2, _corps(vn), vp, "pex")
    #   décharges : m_p (∃-élim pex), m_d (∃-élim dep)
    r_p = mp(exd, existe_elimination(N.loi_deduction(m_p, exN), "pex"))
    r_d = mp(extr, existe_elimination(N.loi_deduction(m_d, r_p), "dep"))
    brC = N.loi_deduction(non(P), r_d)

    r = cas(tiers_exclu(P), brP, brC)
    r_ante = N.loi_deduction(ante, r)                    # R{n}   [sous S{n}]
    assert r_ante.conclusion == _R(vn)
    return N.loi_deduction(Sn, r_ante)                   # S{n} ⇒ R{n}


def _est_cardinal_depuis_card(t):
    """⊢ (Card t = t) ⇒ est_cardinal(t)  — ∃-intro témoin t sur ∃X(t = Card X)…

    NON : est_cardinal(t) = ∃X(t = Card X) ; de Card t = t on tire t = Card t
    (symétrie) puis ∃-intro témoin t. Rendu comme IMPLICATION pour mp."""
    h = N.assume(egal(cardinal(t), t))
    t_eq = mp(h, symetrie(cardinal(t), t))               # t = Card t
    matrice = egal(t, cardinal(var("Xc61")))
    exi = existe_temoin_verifie(t_eq, matrice, t, "Xc61")
    return N.loi_deduction(egal(cardinal(t), t), exi)


def diviseur_premier_universel():
    """🎯🎯🎯 ⊢ (∀n)( Fini n ⇒ R{n} )   avec R{n} = (Fini n ∧ n≠0 ∧ n≠1) ⇒
    ∃p( premier p ∧ Fini p ∧ p|n ).   Hypothèses restantes = les résidus
    HONNÊTES de la récurrence forte (déchargés si prouvés au dépôt)."""
    pas = _pas("nfor")
    H = hypothese_recurrence_forte(_R, n="nfor", p="pfor")
    H_thm = N.generalisation("nfor", pas)
    assert H_thm.est_clos and H_thm.conclusion == H, "le pas ne donne pas H"
    princ = recurrence_forte(_R, p="pfor")               # {H, résidu} ⊢ ∀n(...)
    lib = mp(H_thm, N.loi_deduction(H, princ))
    # décharge du résidu C61 : predecesseur_fini_universel est PROUVÉ au dépôt
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    pred = predecesseur_fini_universel_preuve()
    for hyp in list(lib.hypotheses):
        if hyp == pred.conclusion:
            lib = mp(pred, N.loi_deduction(hyp, lib))
    assert lib.est_clos and not lib.hypotheses, "résidu C61 non déchargé"
    return lib


__all__ = ["diviseur_premier_universel", "_R", "_pas"]
