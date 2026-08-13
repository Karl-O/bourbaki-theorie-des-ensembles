# -*- coding: utf-8 -*-
"""ÉNONCÉS de la campagne EUCLIDE — la route non-bornée demandée par la machine (ev.325).

PREMIÈRE THÉORIE HORS-LIVRE : le livre ne définit pas « nombre premier »
(vérifié V7, 8 août 2026) — ces énoncés vivent donc côté outils_ia, jamais
dans bourbaki/. Le prédicat `est_premier` est RÉEMPLOYÉ depuis l'énoncé
Goldbach (prélèvement : mêmes combinateurs, garde est_fini(d) comprise —
jamais transcrit). Deux cibles, celles que la machine a rendues nécessaires
en nommant son manque au niveau général (« une route qui produit des premiers
pour k libre ») :

    enonce_diviseur_premier()  ∀n( (Fini n ∧ n≠0 ∧ n≠1) ⇒ ∃p(premier p ∧ p|n) )
    enonce_infinitude()        ∀n( Fini n ⇒ ∃p(premier p ∧ Fini p ∧ n ≤ p) )

Module d'ÉNONCÉS seulement : aucun théorème ici — les preuves seront la
campagne (récurrence forte pour le premier, n!+1 pour le second).
⚠️ Liants : d/q de est_premier restent FRAIS par appel (playbook collisions).
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, impl, non, pourtout, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (  # noqa: E402
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini,
)
from outils_ia.conjectures.goldbach import (                          # noqa: E402
    est_premier, divise_propre, un,
)


def enonce_diviseur_premier(n="nfor", p="pex", d="dep", q="qep", q2="qdiv"):
    """∀n( (Fini n ∧ ¬(n=0·) ∧ ¬(n=1)) ⇒ ∃p( premier p ∧ p | n ) ).

    Le « n≠0 » est rendu par ¬(n=un()) doublé de n≠… — NON : ici la garde
    utile est n≠1 seule (0 a pour diviseur premier 2 ? Non — 0 n'en a pas au
    sens divise_propre ; on garde n≠0 ET n≠1 comme l'antécédent Goldbach).
    Liants : d/q frais dans est_premier ; q2 DOIT être « qdiv » (le lieur du
    réflexif et du producteur du dépôt — α-variants ≠ dans ce noyau, piège mesuré
    PB8 : avec qep2 le matcher ne trouvait AUCUNE route)."""
    # HARMONISÉ sur le THÉORÈME (ev.335-337) : antécédent et(et(Fini,≠0),≠1),
    # binder « pex », Fini p DANS le corps — l'énoncé EST la conclusion du
    # théorème (modulo la garde externe Fini n de C61), fermable par l'organe.
    vn, vp = var(n), var(p)
    from outils_ia.arithmetique.machine_num import NUM
    ante = et(et(est_fini(vn), non(egal(vn, NUM(0)))), non(egal(vn, un())))
    corps = existe(p, et(est_premier(vp, d=d, q=q),
                         et(est_fini(vp), divise_propre(vp, vn, q=q2))))
    return pourtout(n, impl(est_fini(vn), impl(ante, corps)))


def enonce_infinitude(n="nep", p="pep", d="dep", q="qep"):
    """∀n( Fini n ⇒ ∃p( premier p ∧ Fini p ∧ n ≤ p ) ) — Euclide.

    La forme « pour tout entier, un premier au-delà » : c'est exactement la
    route NON-bornée que la machine a exigée (ev.325) — un producteur de
    premiers pour n LIBRE, sans plafond."""
    vn, vp = var(n), var(p)
    corps = existe(p, et(est_premier(vp, d=d, q=q),
                         et(est_fini(vp), inf_egal_card(vn, vp))))
    return pourtout(n, impl(est_fini(vn), corps))


__all__ = ["enonce_diviseur_premier", "enonce_infinitude"]
