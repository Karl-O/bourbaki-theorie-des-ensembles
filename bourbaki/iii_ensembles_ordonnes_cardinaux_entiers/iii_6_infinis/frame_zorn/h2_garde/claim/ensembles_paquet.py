# -*- coding: utf-8 -*-
"""§III.6.3 — LE PAQUET D'EXTENSION : ce qui, dans STEP 5, mentionne U ou ψ.

🎯 CIBLES :

    paquet_extension(…)            : l'ÉNONCÉ (une conjonction) du groupe (c)
    contradiction_sous_paquet(…)   : { paquet, u∈U, U⊂E∖S₀, S₀⊂E, données du
                                       maximal } ⊢ ¬(u∈U)

`extension_absurde_chainee` (STEP 5) conclut ¬(u∈U) sous douze hypothèses.
Deux d'entre elles sont DÉRIVÉES de « U ⊂ E∖S₀ » (`ensembles_u_data`) et sont
déchargées ici ; quatre sont fournies par la portée du maximal ; le témoin u∈U
viendra de « U ≠ ∅ ».  Le RESTE — tout ce qui mentionne le témoin U ou la
bijection ψ — est collationné en UNE conjonction, le PAQUET.

⚠️ Pourquoi une conjonction et non des hypothèses séparées : le paquet mentionne
le témoin Ucadre, donc il ne peut pas survivre à l'∃-élimination de U ; il doit
être porté par un énoncé ∀U ⇒ (∃ψ)(…), et ψ ne peut être existentiel que si
tout ce qui le concerne est réuni sous le même ∃ (cf. DECISIONS 2026-08-23).

⚠️ `Theoreme.hypotheses` est un `frozenset` : son ordre d'itération dépend du
hachage (randomisé par processus).  Le paquet est donc replié dans l'ordre
CANONIQUE de `afficher_f` — sans ce tri, l'énoncé changerait d'un run à l'autre.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from functools import reduce

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, afficher_f, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.assemblage_vrai.ensembles_hessenberg_chaine_vraie import (
    extension_absurde_chainee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_u_data import (
    u_disjoint_S, reunion_inclus_E,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _nom(x):
    """Nom d'une variable donnée par chaîne ou par Terme."""
    return x if isinstance(x, str) else x.nom


def _conjoints_du_paquet(E_set, S, phi0, psi, U, u):
    """La LISTE canonique des conjoints du paquet (triée par `afficher_f`).

    = hypothèses de STEP 5 mentionnant U ou ψ, MOINS les deux dérivables de
    « U ⊂ E∖S₀ » et MOINS le témoin u∈U (qui viendra de « U non vide »)."""
    step5 = extension_absurde_chainee(E_set, phi0, psi, S, U, u)
    nU, npsi, nu = _nom(U), _nom(psi), _nom(u)
    deja = {u_disjoint_S(E_set, S, U, u).conclusion,
            reunion_inclus_E(E_set, S, U).conclusion,
            appartient(var(nu), _t(U))}
    reste = [h for h in step5.hypotheses
             if h not in deja and (nU in libres_f(h) or npsi in libres_f(h))]
    return sorted(reste, key=afficher_f)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.30-33 | PDF p.151
#   (« on peut donc définir une bijection de (F∪Y)×(F∪Y) sur F∪Y »)
def paquet_extension(E_set="E", S="S0", phi0="phi0", psi="psi",
                     U="Ucadre", u="uwit"):
    """L'ÉNONCÉ du paquet : la conjonction (repliée à droite) du groupe (c).

    Contenu : la géométrie du carré (S₀∪U)² et les propriétés de ψ (bijection
    de la zone complémentaire sur U, domaines disjoints, image en réunion et
    en intersection).  C'est exactement ce que Bourbaki obtient en E III.48
    par le calcul cardinal 𝔟·𝔟 = 𝔟 et 𝔟+𝔟 = 𝔟."""
    conj = _conjoints_du_paquet(E_set, S, phi0, psi, U, u)
    assert conj, "paquet_extension : paquet vide (STEP 5 a changé ?)"
    return reduce(lambda acc, x: et(x, acc), reversed(conj[:-1]), conj[-1])


def _decoupe(thm, n):
    """Découpe le théorème d'une conjonction repliée à droite en ses n conjoints."""
    out, cur = [], thm
    for _ in range(n - 1):
        out.append(conjonction_elim_gauche(cur))
        cur = conjonction_elim_droite(cur)
    out.append(cur)
    return out


def contradiction_sous_paquet(E_set="E", S="S0", phi0="phi0", psi="psi",
                              U="Ucadre", u="uwit"):
    """{ paquet, u∈U, U⊂E∖S₀, S₀⊂E, données du maximal } ⊢ ¬(u∈U).

    STEP 5 avec ses hypothèses RANGÉES : les deux dérivables déchargées par
    `ensembles_u_data`, le groupe (c) regroupé sous le seul `paquet`.  Les
    hypothèses restantes ne mentionnent U que par « U ⊂ E∖S₀ » (l'antécédent
    du garde) et par le témoin u∈U — les deux seront consommées à la sortie
    de portée."""
    res = extension_absurde_chainee(E_set, phi0, psi, S, U, u)

    for lemme in (u_disjoint_S(E_set, S, U, u), reunion_inclus_E(E_set, S, U)):
        if lemme.conclusion in res.hypotheses:
            res = N.modus_ponens(lemme, N.loi_deduction(lemme.conclusion, res))

    conj = _conjoints_du_paquet(E_set, S, phi0, psi, U, u)
    paquet = paquet_extension(E_set, S, phi0, psi, U, u)
    for morceau in _decoupe(N.assume(paquet), len(conj)):
        assert morceau.conclusion in res.hypotheses, \
            "contradiction_sous_paquet : conjoint absent des hypothèses"
        res = N.modus_ponens(morceau, N.loi_deduction(morceau.conclusion, res))

    assert paquet in res.hypotheses, "contradiction_sous_paquet : paquet absent"
    npsi = _nom(psi)
    for h in res.hypotheses:
        assert h == paquet or npsi not in libres_f(h), \
            "contradiction_sous_paquet : ψ subsiste hors du paquet"
    return res


__all__ = ["paquet_extension", "contradiction_sous_paquet"]
