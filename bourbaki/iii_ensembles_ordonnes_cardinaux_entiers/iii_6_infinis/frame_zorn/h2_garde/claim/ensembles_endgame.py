# -*- coding: utf-8 -*-
"""§III.6.3 — LE CLAIM : Card S₀ = Card E, dans la portée du maximal.

🎯 CIBLES :

    donnees_extension : l'unique énoncé porté, quantifié sur U —
        (∀U)( (U⊂E∖S₀ et Card U=Card S₀) ⇒ (∃ψ) PAQUET(U,ψ) )
    non_strict_clos   : ⊢ ¬( Card S₀ < Card E )      [témoins tous éliminés]
    claim_clos        : ⊢ Card S₀ = Card E           [LE CLAIM de Bourbaki]

La forme quantifiée du garde est ce qui rend la sortie de portée possible :
le paquet mentionne le témoin U, donc il ne peut pas rester en hypothèse
résiduelle ; porté sous « pour tout U admissible, il existe un ψ », il devient
un énoncé CLOS en U, instanciable à l'intérieur de la portée et déchargeable
à l'extérieur.  C'est le même patron que `donnees_recollement` pour les
chaînes (cf. DECISIONS 2026-08-23).

Trois éliminations en cascade, dans l'ordre imposé par les dépendances :
ψ (rien d'autre ne le mentionne une fois le paquet déchargé), puis U (le garde
déchargé, `existe_u_cadre` fournit son existence), puis l'hypothèse de
l'absurde elle-même — qui, ayant produit sa propre négation, tombe par S1.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, existe, pourtout, impl, inclus, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_extension import (
    existe_u_cadre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_paquet import (
    paquet_extension,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_sortie import (
    non_strict_sous_garde,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge `formule` de `thm` par `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _garde(E_set, S, U):
    """L'antécédent : U ⊂ E∖S₀  et  Card U = Card S₀   (ce que fournit `existe_u_cadre`)."""
    vE, vS, vU = _t(E_set), _t(S), _t(U)
    return et(inclus(vU, E.difference(vE, vS)),
              egal(cardinal(vU), cardinal(vS)))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.30-33 | PDF p.151
def donnees_extension(E_set="E", S="S0", phi0="phi0", psi="psi",
                      U="Ucadre", u="z"):
    """L'unique énoncé porté par l'argument d'extension :

        (∀U)( (U⊂E∖S₀ et Card U=Card S₀) ⇒ (∃ψ) PAQUET(U,ψ) ).

    Chez Bourbaki : « on peut définir une bijection de (F∪Y)×(F∪Y) sur F∪Y »
    — l'existence de ψ pour CHAQUE U admissible, obtenue par le calcul
    cardinal 𝔟·𝔟=𝔟 et 𝔟+𝔟=𝔟.  Le ψ est existentiel à l'intérieur : un ψ par
    U, et non un ψ unique pour tous."""
    nU = U if isinstance(U, str) else U.nom
    npsi = psi if isinstance(psi, str) else psi.nom
    return pourtout(nU, impl(_garde(E_set, S, U),
                             existe(npsi, paquet_extension(E_set, S, phi0,
                                                           psi, U, u))))


# @livre Ch.III §6.3 Demo.2 | E III.49 L.5-6 | PDF p.152  (« l'hypothèse 𝔟<𝔞 est donc absurde »)
def non_strict_clos(E_set="E", S="S0", phi0="phi0", psi="psi",
                    U="Ucadre", u="z"):
    """⊢ ¬( Card S₀ < Card E ), TOUS TÉMOINS ÉLIMINÉS.

    Hypothèses restantes : `donnees_extension`, l'absorption 𝔟+𝔟=𝔟, le
    transport, S₀⊂E et les données du maximal — aucune ne mentionne U ni ψ."""
    vE, vS, vU = _t(E_set), _t(S), _t(U)
    nU = U if isinstance(U, str) else U.nom
    npsi = psi if isinstance(psi, str) else psi.nom
    absurde = inf_strict_card(cardinal(vS), cardinal(vE))
    garde, paquet = _garde(E_set, S, U), paquet_extension(E_set, S, phi0, psi, U, u)

    res = non_strict_sous_garde(E_set, S, phi0, psi, U, u)   # ⊢ ¬absurde
    h_garde = N.assume(garde)
    res = _cut(conjonction_elim_gauche(h_garde),
               inclus(vU, E.difference(vE, vS)), res)
    res = _cut(conjonction_elim_droite(h_garde),
               egal(cardinal(vU), cardinal(vS)), res)

    #  (1) élimination de ψ : plus rien d'autre ne le mentionne
    imp_psi = existe_elimination(N.loi_deduction(paquet, res), npsi)
    ex_psi = N.modus_ponens(h_garde,
                            instancie(N.assume(donnees_extension(
                                E_set, S, phi0, psi, U, u)), vU))
    res = N.modus_ponens(ex_psi, imp_psi)                    # ¬absurde, sous garde

    #  (2) élimination de U : le garde déchargé, `existe_u_cadre` le fournit
    imp_U = existe_elimination(N.loi_deduction(garde, res), nU)
    res = N.modus_ponens(existe_u_cadre(E_set, S), imp_U)

    #  (3) l'absurde a produit sa propre négation : elle tombe (S1)
    res = N.modus_ponens(N.loi_deduction(absurde, res), N.s1(non(absurde)))

    assert res.conclusion == non(absurde), "non_strict_clos : forme"
    assert absurde not in res.hypotheses, "non_strict_clos : absurde non déchargé"
    for h in res.hypotheses:
        libres = libres_f(h)
        assert nU not in libres and npsi not in libres, \
            "non_strict_clos : témoin résiduel dans une hypothèse"
    return res


def non_strict_sans_paquet(E_set="E", S="S0", phi0="phi0"):
    """⊢ ¬( Card S₀ < Card E ) SANS le paquet ψ en résidu.   [~385 s]

    Le CHEMIN COMPLET : `negation_strict_sous_maximal_reunion` (step_b_prop5)
    construit lui-même la bijection ψ — par `cadre_card_trois_b_reunion` et le
    recâblage RÉUNION qui dissout le mur de la somme disjointe — au lieu de la
    porter en hypothèse ∀U.  Vérifié en code le 2026-08-23 : conclusion exacte,
    7 hypothèses, aucune ne mentionnant Ucadre, ψ ni uwit (RECHERCHE R-11).

    À réserver à la CERTIFICATION : il coûte ~385 s là où `non_strict_clos` en
    demande ~20, au prix d'un résidu nommé.  Les deux chemins prouvent le même
    énoncé ; seul diffère ce qui reste ouvert."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_stepb3 import (
        negation_strict_sous_maximal_reunion,
    )
    vE, vS = _t(E_set), _t(S)
    res = negation_strict_sous_maximal_reunion(E_set, S, phi0)
    assert res.conclusion == non(inf_strict_card(cardinal(vS), cardinal(vE))),         "non_strict_sans_paquet : conclusion inattendue"
    for h in res.hypotheses:
        libres = libres_f(h)
        assert not ({"Ucadre", "psi", "uwit"} & libres),             "non_strict_sans_paquet : témoin résiduel"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.49 L.6-7 | PDF p.152  (« on a donc Card F = Card E »)
def claim_clos(E_set="E", S="S0", phi0="phi0", psi="psi", U="Ucadre", u="z",
               paquet_derive=False):
    """🎯🎯 ⊢ Card S₀ = Card E — LE CLAIM, dans la portée du maximal.

    `paquet_derive=True` emprunte `non_strict_sans_paquet` : plus aucun résidu
    honnête, mais ~385 s au lieu de ~20."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_claim import (
        claim_depuis_non_strict,
    )
    vE, vS = _t(E_set), _t(S)
    non_strict = (non_strict_sans_paquet(E_set, S, phi0) if paquet_derive
                  else non_strict_clos(E_set, S, phi0, psi, U, u))
    res = claim_depuis_non_strict(E_set, S, N.assume(inclus(vS, vE)), non_strict)
    assert res.conclusion == egal(cardinal(vS), cardinal(vE)), "claim_clos : forme"
    return res


__all__ = ["donnees_extension", "non_strict_clos",
           "non_strict_sans_paquet", "claim_clos"]
