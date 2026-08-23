# -*- coding: utf-8 -*-
"""§III.6.3 — DU CLAIM À HESSENBERG, DANS LA PORTÉE DU MAXIMAL.

🎯 CIBLE (le dernier maillon de l'endgame, celui qui sort de la portée) :

    claim_vers_endgame(vS0, vphi0, bij0, claim) :
        { Card S₀ = Card E }  ∪  hyps(bij0)   ⊢   enonce_hessenberg(E)

Étant donné le CLAIM (le maximal atteint le cardinal de E) et la bijection
φ₀ du maximal, l'énoncé de Hessenberg suit : `maximal_carre_egal` transforme
la bijection en « Card(S₀×S₀) = Card S₀ », et `hessenberg_aa_egal_de_maximal`
conclut — sa conclusion ne mentionne QUE E, ce qui permettra de sortir de la
portée du témoin une fois le CLAIM lui-même dérivé.

C'est le morceau mécanique de STEP B ; ce qui reste en amont est l'argument
d'extension de Bourbaki qui établit le CLAIM par contradiction.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_maximal_card import (
    hessenberg_aa_egal_de_maximal,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def claim_vers_endgame(E_set, S, phi, bij0, claim):
    """🎯 { Card S₀=Card E } ∪ hyps(bij0) ⊢ enonce_hessenberg(E).

    `bij0` : ⊢ est_bijection_de(φ₀, S₀×S₀, S₀)  (donnée du maximal) ;
    `claim` : ⊢ Card S₀ = Card E                (le CLAIM de Bourbaki).
    La conclusion ne mentionne que E."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_maximal_card import (
        maximal_carre_egal,
    )
    vE, vS0 = _t(E_set), _t(S)
    Sname = S if isinstance(S, str) else S.nom
    phiname = phi if isinstance(phi, str) else phi.nom
    cS, cE = cardinal(vS0), cardinal(vE)
    SxS = E.produit(vS0, vS0)
    h_carre = egal(cardinal(SxS), cS)

    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_bijection_de,
    )
    h_bij = est_bijection_de(_t(phi), SxS, vS0)
    endg = hessenberg_aa_egal_de_maximal(E_set, Sname)      # {claim, h_carre}
    carre = maximal_carre_egal(Sname, phiname)              # {bij φ₀} ⊢ h_carre
    assert carre.conclusion == h_carre, "claim_vers_endgame : carré inattendu"
    res = _cut(carre, h_carre, endg)                        # h_carre déchargée
    if h_bij in res.hypotheses:                             # la bijection du maximal
        res = _cut(bij0, h_bij, res)
    res = _cut(claim, egal(cS, cE), res)                    # CLAIM déchargé
    assert res.conclusion == enonce_hessenberg(E_set), "claim_vers_endgame : forme"
    return res


__all__ = ["claim_vers_endgame"]
