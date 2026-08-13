# -*- coding: utf-8 -*-
"""CAS PREMIER du diviseur-premier — LE PREMIER PRODUCTEUR DE PREMIERS (Euclide, brique B).

    ⊢ ∀n( (Fini n ∧ est_premier n) ⇒ ∃p( est_premier p ∧ p | n ) )      [CLOS]

C'est exactement la forme que la machine déclarait INTROUVABLE (PB7, ev.328 :
« aucune implication du corpus ne conclut en ∃p(premier ∧ …) ») — le manque
total qu'elle avait nommé. Témoin p := n : un premier se divise lui-même
(réflexivité du dépôt, témoin q=1), sa primalité est l'hypothèse.

Chaîne : élimination des conjoints → Fini n ⇒ card n (fic) → réflexivité
instanciée → ∃-intro par la TACTIQUE À TÉMOIN VÉRIFIÉ (ev.283) → décharge →
généralisation. Liants : d/q de est_premier = dep/qep ; le q de la
divisibilité du corps = « qdiv » (celui du réflexif) — disjoints (playbook
collisions).
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, et, impl, pourtout, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre, divise_propre_reflexif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini,
)
from outils_ia.arithmetique.machine_num import fic_t, existe_temoin_verifie  # noqa: E402
from outils_ia.conjectures.goldbach import est_premier                # noqa: E402

mp = N.modus_ponens


def cas_premier_diviseur_cible(n="nep", p="pep", d="dep", q="qep"):
    """Énoncé visé : ∀n( (Fini n ∧ premier n) ⇒ ∃p( premier p ∧ p | n ) )."""
    vn, vp = var(n), var(p)
    ante = et(est_fini(vn), est_premier(vn, d=d, q=q))
    corps = et(est_premier(vp, d=d, q=q), divise_propre(vp, vn, q="qdiv"))
    return pourtout(n, impl(ante, existe(p, corps)))


def cas_premier_diviseur(n="nep", p="pep", d="dep", q="qep"):
    """🎯 ⊢ ∀n( (Fini n ∧ premier n) ⇒ ∃p( premier p ∧ p | n ) ).   [CLOS]"""
    vn, vp = var(n), var(p)
    ante = et(est_fini(vn), est_premier(vn, d=d, q=q))
    h = N.assume(ante)
    h_fini = conjonction_elim_gauche(h)                 # Fini n
    h_prem = conjonction_elim_droite(h)                 # premier n
    card_n = mp(h_fini, fic_t(vn))                      # est_cardinal n
    div_nn = mp(card_n, divise_propre_reflexif(n))      # n | n  (témoin q=1)

    corps = et(est_premier(vp, d=d, q=q), divise_propre(vp, vn, q="qdiv"))
    temoin_thm = conjonction_intro(h_prem, div_nn)      # premier n ∧ n | n
    ex = existe_temoin_verifie(temoin_thm, corps, vn, p)

    r = N.loi_deduction(ante, ex)
    th = N.generalisation(n, r)
    assert th.est_clos and not th.hypotheses, "cas_premier_diviseur non clos"
    assert th.conclusion == cas_premier_diviseur_cible(n, p, d, q), (
        "cas_premier_diviseur : conclusion != cible")
    return th


__all__ = ["cas_premier_diviseur", "cas_premier_diviseur_cible"]
