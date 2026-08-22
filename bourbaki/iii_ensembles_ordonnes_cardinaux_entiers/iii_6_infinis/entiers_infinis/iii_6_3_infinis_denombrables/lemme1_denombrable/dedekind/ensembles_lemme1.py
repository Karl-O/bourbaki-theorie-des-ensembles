# -*- coding: utf-8 -*-
"""§III.6.3 — D1d : 🏆 LE LEMME 1 — TOUT ENSEMBLE INFINI CONTIENT UN DÉNOMBRABLE.

🎯 CIBLE (l'énoncé de Bourbaki, E III.47 : « Tout ensemble infini E contient
un ensemble équipotent à N ») :

    lemme_1 :  { est_infini(Card E) }  ⊢  (∃D)( D ⊂ E  ∧  Eq(D, ℕ) )

Assemblage final : la chaîne K6 (paramétrique en (u, x0)) est instanciée aux
données Dedekind u := x↦h((x,0)), x0 := h((∅,1)) ; ses six hypothèses sont
déchargées (l'itération forte fournit le corps sous x0∈E ; D1b/D1c fournissent
le reste sous h_bij) ; le témoin gcap puis le témoin h s'éliminent ; Eq(W,E)
(D1a, par la chaîne des cardinaux et Dedekind) referme — il ne reste que
« Card E est infini ».

⚠️ Fidélité : l'ÉNONCÉ colle au livre ; la DÉMONSTRATION du livre passe par le
bon ordre (Th.1, segments de ℕ), la nôtre par l'itération de Dedekind —
écart consigné dans docs/journal/ANOMALIES.md (précédent Th2).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, existe, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, equipotent, est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_c63_vrai import (
    corps_c63_fort,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_regle_clampee import (
    regle_clampee, iteration_dedekind_forte,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_iteree import (
    x0_hors_image,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_lemme1_partiel import (
    lemme1_sous_hypotheses,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_carte_egale import (
    ensemble_marque, eq_w_e,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_donnees_dedekind import (
    x0_dedekind, u_dedekind, x0_dans_E, _cut,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_hyps_u import (
    dom_u_egal_E, u_inclus_EE, hors_x0, u_injective,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.III §6.3 Lem.1 | E III.47 L.34-35 | PDF p.150
# @livre Ch.III §6.3 Demo.Lem1 | E III.47 L.36-41 | PDF p.150  (⚠️ démonstration du
#   livre par le bon ordre ; ICI par l'itération de Dedekind — cf. ANOMALIES.md)
def lemme_1(e="Eld", h="hdk"):
    """🏆 LEMME 1 : { est_infini(Card E) } ⊢ (∃D)( D ⊂ E ∧ Eq(D, ℕ) )   [1 hyp].

    Instancie la chaîne K6 aux données Dedekind (u, x0) construites depuis la
    bijection h : E⊔{∅} → E (D1a) ; décharge les six hypothèses ; élimine les
    témoins gcap puis h."""
    vh, ve = _t(h), _t(e)
    W = ensemble_marque(ve)
    udk, x0dk = u_dedekind(vh, ve), x0_dedekind(vh)
    _, S_c = regle_clampee(udk, x0dk, ve)

    base = lemme1_sous_hypotheses(udk, x0dk, ve)            # {6 hyps}
    # ── le corps fort : itération de Dedekind + élimination du témoin gcap ──
    imp = N.loi_deduction(corps_c63_fort(S_c, x0dk), base)
    exg = existe_elimination(imp, "gcap")
    b = N.modus_ponens(iteration_dedekind_forte(udk, x0dk, ve), exg)
    # ── les cinq données, prouvées sous h_bij (D1b/D1c) ─────────────────────
    b = _cut(x0_dans_E(h, e), appartient(x0dk, ve), b)
    b = _cut(u_inclus_EE(h, e), inclus(udk, E.produit(ve, ve)), b)
    dom_thm = dom_u_egal_E(h, e)
    b = _cut(dom_thm, dom_thm.conclusion, b)
    b = _cut(hors_x0(h, e), x0_hors_image(udk, x0dk, ve), b)
    b = _cut(u_injective(h, e), E.injective_dans(udk, ve), b)
    assert list(b.hypotheses) == [est_bijection_de(vh, W, ve)], \
        "lemme_1 : il devrait rester la seule hypothèse h_bij"
    # ── éliminer le témoin h et refermer par Eq(W, E) (D1a) ─────────────────
    imp_h = N.loi_deduction(est_bijection_de(vh, W, ve), b)
    ex_h = existe_elimination(imp_h, h if isinstance(h, str) else h.nom)
    eq = eq_w_e(e)                                          # {est_infini(Card E)}
    if eq.conclusion != existe(h, est_bijection_de(vh, W, ve)):
        eq = N.modus_ponens(eq, equivalence_avant(
            alpha_existe("F", h, est_bijection_de(var("F"), W, ve))))
    res = N.modus_ponens(eq, ex_h)

    vD, NN = var("Dld"), ensemble_NN()
    assert res.conclusion == existe("Dld", et(inclus(vD, ve),
                                              equipotent(vD, NN))), \
        "lemme_1 : forme"
    assert list(res.hypotheses) == [est_infini(cardinal(ve))], \
        "lemme_1 : hyps ≠ {est_infini(Card E)}"
    return res


__all__ = ["lemme_1"]
