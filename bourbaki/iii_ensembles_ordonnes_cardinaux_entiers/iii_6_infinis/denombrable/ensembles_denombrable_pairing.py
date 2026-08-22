# -*- coding: utf-8 -*-
"""§III.6 (Lemme 2) — W5 : l'INJECTIVITÉ du couplage (m,n) ↦ 2^m·3^n.

🎯 CIBLE (pairing_injectif) :
    ⊢ (Fini m ∧ Fini mp ∧ Fini n ∧ Fini np ∧ 2^m·3^n = 2^mp·3^np)
      ⇒ (m = mp ∧ n = np).

ASSEMBLAGE PUR des briques closes :
  • 3^n, 3^np impairs (trois_puiss_impair, W1) et finis (trois_puissance_dans_NN) ;
  • la 2-VALUATION UNIQUE (deux_valuation_unique, W3) à (m, mp, 3^n, 3^np)
    ⇒ m = mp  et  3^n = 3^np ;
  • la 3-INJECTIVITÉ (trois_puiss_injectif, W4) ⇒ n = np.

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche as elg,
    conjonction_elim_droite as eld,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, DEUX, TROIS,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_deux_trois_NN import (
    trois_puissance_dans_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_injection_iii6 import (
    trois_puiss_impair,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_valuation_recurrence import (
    deux_valuation_unique,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_trois_injectif import (
    trois_puiss_injectif,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _e2(s):
    return exposant_cardinal_binaire(DEUX, _t(s))


def _e3(s):
    return exposant_cardinal_binaire(TROIS, _t(s))


def _prod(a, b):
    return produit_cardinal_binaire(_t(a), _t(b))


def pairing_terme(m, n):
    """2^m · 3^n   (le terme de couplage)."""
    return _prod(_e2(m), _e3(n))


def pairing_injectif_cible(m="mpg", mp="mppg", n="npg", np="nppg"):
    vm, vmp, vn, vnp = _t(m), _t(mp), _t(n), _t(np)
    ante = et(et(et(est_fini(vm), est_fini(vmp)), et(est_fini(vn), est_fini(vnp))),
              egal(pairing_terme(vm, vn), pairing_terme(vmp, vnp)))
    return impl(ante, et(egal(vm, vmp), egal(vn, vnp)))


def pairing_injectif(m="mpg", mp="mppg", n="npg", np="nppg"):
    """🎯 ⊢ (Fini m,mp,n,np ∧ 2^m·3^n = 2^mp·3^np) ⇒ (m=mp ∧ n=np).   (W5.)"""
    vm, vmp, vn, vnp = _t(m), _t(mp), _t(n), _t(np)
    ante = et(et(et(est_fini(vm), est_fini(vmp)), et(est_fini(vn), est_fini(vnp))),
              egal(pairing_terme(vm, vn), pairing_terme(vmp, vnp)))
    h = N.assume(ante)
    fs, eq = elg(h), eld(h)
    fm, fmp = elg(elg(fs)), eld(elg(fs))
    fn, fnp = elg(eld(fs)), eld(eld(fs))

    # 3^n, 3^np : impairs et finis
    g_imp = N.generalisation("ntpi", trois_puiss_impair("ntpi"))
    imp_n = N.modus_ponens(fn, instancie(g_imp, vn))
    imp_np = N.modus_ponens(fnp, instancie(g_imp, vnp))
    g_fin = N.generalisation("npdt", trois_puissance_dans_NN("npdt"))
    fe_n = N.modus_ponens(fn, instancie(g_fin, vn))
    fe_np = N.modus_ponens(fnp, instancie(g_fin, vnp))

    # W3 : 2-valuation unique à (m, mp, 3^n, 3^np)
    g_w3 = N.generalisation("mdv", deux_valuation_unique())
    P_m = N.modus_ponens(fm, instancie(g_w3, vm))            # ∀mp∀u∀up(...)
    w3 = instancie(instancie(instancie(P_m, vmp), _e3(vn)), _e3(vnp))
    ante_w3 = conjonction_intro(
        conjonction_intro(fmp, conjonction_intro(fe_n, fe_np)),
        conjonction_intro(conjonction_intro(imp_n, imp_np), eq))
    r3 = N.modus_ponens(ante_w3, w3)                         # m = mp  et  3^n = 3^np
    m_eq, e3_eq = elg(r3), eld(r3)

    # W4 : 3-injectivité à (n, np)
    g_w4 = N.generalisation("ntj", trois_puiss_injectif())
    P_n = N.modus_ponens(fn, instancie(g_w4, vn))            # ∀np(...)
    w4 = instancie(P_n, vnp)
    n_eq = N.modus_ponens(conjonction_intro(fnp, e3_eq), w4)  # n = np

    res = N.loi_deduction(ante, conjonction_intro(m_eq, n_eq))
    assert res.conclusion == pairing_injectif_cible(m, mp, n, np), \
        f"pairing_injectif : conclusion inattendue\n{res.conclusion}"
    assert not res.hypotheses, "pairing_injectif : hypothèses résiduelles"
    return res


__all__ = ["pairing_terme", "pairing_injectif", "pairing_injectif_cible"]
