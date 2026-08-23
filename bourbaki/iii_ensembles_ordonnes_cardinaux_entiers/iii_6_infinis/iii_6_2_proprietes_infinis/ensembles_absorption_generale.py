# -*- coding: utf-8 -*-
"""§III.6.3 — L'ABSORPTION a + a = a, GLOBALE (et non plus « au maximal »).

🎯 CIBLE :

    absorption_sous_hessenberg(A) :
        { enonce_hessenberg(A), est_infini(Card A) }
            ⊢  Card A + Card A = Card A

CE QUI CHANGE.  Le dépôt possédait déjà cette absorption, mais LOCALE :
`absorption_au_maximal` la tirait de la bijection φ₀ fournie par l'élément
maximal de Zorn — ce qui suffisait à la démonstration de Hessenberg, mais ne
donnait rien pour un cardinal infini quelconque.  Le Théorème 2 étant démontré
(2026-08-23), le carré 𝔞·𝔞 = 𝔞 est disponible partout, et l'absorption cesse
d'être locale.

⚠️ AUCUNE PREUVE N'EST RÉÉCRITE.  Toute la chaîne — distributivité 𝔞·2 = 𝔞+𝔞,
2 ≤ 𝔞 par infinité, monotonie du produit, 𝔞 ≤ 𝔞+𝔞, antisymétrie — vit dans
`absorption_depuis_carre`, extrait de `absorption_au_maximal` sans qu'une ligne
de raisonnement ne change.  La bijection φ₀ n'y servait qu'à UNE étape ; c'est
elle, et elle seule, que Hessenberg remplace.

⚠️ Et le carré demandé est EXACTEMENT le conséquent de `enonce_hessenberg(A)` —
`produit_cardinal_binaire(Card A, Card A) = Card A`.  Aucun pont, aucune
réécriture : un modus ponens suffit.

⚠️ RÈGLE PERF.  `enonce_hessenberg(A)` reste une HYPOTHÈSE HONNÊTE (sa preuve
coûte 5172,8 s, mesuré) ; on ne la décharge qu'au dernier étage.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_absorption import (
    absorption_depuis_carre,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def enonce_absorption_generale(a="A"):
    """FORMULE : Card A + Card A = Card A."""
    cA = cardinal(_t(a))
    return egal(somme_cardinale_binaire(cA, cA), cA)


# @livre Ch.III §6.3 Cor.4 | E III.49 L.28-30 | PDF p.152
#   (cas diagonal a = b du Corollaire 4 : a + a = a pour a infini)
def carre_depuis_hessenberg(a="A"):
    """{ enonce_hessenberg(A), est_infini(Card A) } ⊢ Card A · Card A = Card A.

    Le conséquent du Théorème 2, détaché de son antécédent.  C'est la seule
    étape que la version « au maximal » tirait de la bijection φ₀."""
    cA = cardinal(_t(a))
    res = N.modus_ponens(N.assume(est_infini(cA)), N.assume(enonce_hessenberg(a)))
    assert res.conclusion == egal(produit_cardinal_binaire(cA, cA), cA), \
        "carre_depuis_hessenberg : l'énoncé du Th. 2 a changé de forme"
    return res


# @livre Ch.III §6.3 Cor.4 | E III.49 L.28-30 | PDF p.152
def absorption_sous_hessenberg(a="A"):
    """🎯 { enonce_hessenberg(A), est_infini(Card A) } ⊢ Card A + Card A = Card A.

    L'absorption pour un cardinal infini QUELCONQUE, là où le dépôt ne l'avait
    qu'au maximal.  Le raisonnement est celui d'`absorption_depuis_carre`, mot
    pour mot ; seule la provenance du carré change."""
    res = absorption_depuis_carre(a, carre_depuis_hessenberg(a))
    assert res.conclusion == enonce_absorption_generale(a), \
        "absorption_sous_hessenberg : forme"
    assert set(res.hypotheses) == {enonce_hessenberg(a), est_infini(cardinal(_t(a)))}, \
        "absorption_sous_hessenberg : hypothèses résiduelles inattendues (%d)" % len(res.hypotheses)
    return res


__all__ = ["enonce_absorption_generale", "carre_depuis_hessenberg",
           "absorption_sous_hessenberg"]
