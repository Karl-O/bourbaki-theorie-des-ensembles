# -*- coding: utf-8 -*-
"""§III.6.3 — L'ABSORPTION 𝔟+𝔟 = 𝔟 AU MAXIMAL (résidu 1/3 de Hessenberg).

🎯 CIBLE :

    absorption_au_maximal(S₀, φ₀) :
        { S₀ infini,  φ₀ bijection S₀×S₀ → S₀ }  ⊢  Card S₀ + Card S₀ = Card S₀

L'absorption n'est PAS un théorème global qu'il faudrait importer : au maximal
elle se tire de la bijection φ₀ elle-même.  C'est ce qui la rend LOCALE, donc
dérivable dans la portée du maximal — et c'est ainsi que Bourbaki l'emploie
en E III.48 (« 𝔟 + 𝔟 = 𝔟 » y va de soi une fois 𝔟·𝔟 = 𝔟 acquis).

Chaîne (𝔟 := Card S₀) :

    𝔟 + 𝔟  =  𝔟·2      car 2 = 1+1 et 𝔟·1 = 𝔟          [distributivité]
    2 ≤ 𝔟                                              [S₀ infini]
    𝔟·2 ≤ 𝔟·𝔟                                          [monotonie du produit]
    𝔟·𝔟 = 𝔟                                            [la bijection φ₀]
    𝔟 ≤ 𝔟+𝔟                                            [somme à gauche]
    ⇒ 𝔟+𝔟 = 𝔟                                          [antisymétrie]

⚠️ LE PIÈGE DES TROIS « UN ».  Le dépôt manipule trois objets distincts qui
valent tous 1 : l'ENSEMBLE {∅}, son CARDINAL Card({∅}), et l'ENTIER
UN = successeur(0).  Ils ne sont PAS syntaxiquement égaux, et `produit_cardinal_un`
ne parle que du premier.  Le pont est `produit_cardinal_bien_defini` — « Card(X×Y)
ne dépend que de Card X et Card Y » — qui traverse les trois niveaux d'un coup,
sans jamais reconstruire un τ-terme (LEÇON 15).

Choix des arguments de la distributivité : b := UN et c := {∅} EXACTEMENT, car
somme_cardinale_binaire(UN, {∅}) est successeur(UN) = DEUX *syntaxiquement* —
le « 2 » de `deux_inf_egal_infini` et de la monotonie tombe alors juste.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire, somme_disjointe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (
    produit_cardinal_un,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_distributivite_operations import (
    distributivite_operations,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinal_ordre_props import (
    produit_cardinale_monotone_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_antisymetrique_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import (
    _inf_egal_somme_gauche_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_prop13_complement import (
    _cardinal_est_son_cardinal_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    UN, DEUX,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (
    un_egale_card_singleton,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import (
    est_cardinal_de_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini, est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.infinis_descentes.ensembles_fini_inf_egal_infini import (
    deux_inf_egal_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_maximal_card import (
    maximal_carre_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_structural_discharge import (
    _set_le_eq_card, _le_trans_t,
)

_UNITE = E.singleton(E.VIDE)                 # l'ENSEMBLE {∅}


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _reecrire(eq, gabarit, trou="wab"):
    """⊢ gabarit{gauche} = gabarit{droite}, à partir de ⊢ gauche = droite."""
    g, d = eq.conclusion.termes
    return N.modus_ponens(eq, congruence_terme(g, d, gabarit, trou))


def enonce_absorption(S="S0"):
    """L'ÉNONCÉ seul : Card S₀ + Card S₀ = Card S₀   (sans le dériver).

    `absorption_au_maximal` coûte ~200 s ; l'assemblage n'a besoin que de la
    FORME pour savoir qu'elle ne compte plus parmi les résidus à porter."""
    b = cardinal(_t(S))
    return egal(somme_cardinale_binaire(b, b), b)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.27-28 | PDF p.151  (« 𝔟 + 𝔟 = 𝔟 »)
def absorption_depuis_carre(S, carre):
    """{ S infini } ∪ hyps(carre) ⊢ Card S + Card S = Card S.

    Le CŒUR de l'absorption, paramétré par la seule étape qui varie : `carre`,
    une preuve de « 𝔟·𝔟 = 𝔟 ».  Tout le reste — distributivité, 2 ≤ 𝔟,
    monotonie, antisymétrie — est indépendant de la PROVENANCE du carré.

    ⚠️ 2026-08-23 : extrait de `absorption_au_maximal` sans en changer une
    ligne de raisonnement.  Au maximal, le carré vient de la bijection φ₀ ;
    depuis que le Théorème 2 est démontré, il peut aussi venir de Hessenberg —
    et l'absorption cesse alors d'être locale (cf. `ensembles_absorption_generale`)."""
    vS = _t(S)
    b = cardinal(vS)                                        # 𝔟 = Card S₀
    somme_bb = somme_cardinale_binaire(b, b)                # 𝔟 + 𝔟
    carre_b = produit_cardinal_binaire(b, b)                # 𝔟 · 𝔟

    #  ── (0) 𝔟 est un cardinal, donc Card 𝔟 = 𝔟 ─────────────────────────────
    h_card = est_cardinal_de_cardinal(vS)                   # est_cardinal(𝔟)
    card_b = N.modus_ponens(h_card, _cardinal_est_son_cardinal_t(b))   # Card 𝔟 = 𝔟

    #  ── (1) 𝔟·{∅} = 𝔟   puis   𝔟·1 = 𝔟 (l'ENTIER un) ──────────────────────
    b_unite = composer_egalites(produit_cardinal_un(b), card_b)        # 𝔟·{∅} = 𝔟
    card_unite = N.modus_ponens(un_egale_card_singleton(),
                                symetrie(UN, cardinal(_UNITE)))        # Card{∅} = 1
    bien_def = N.modus_ponens(conjonction_intro(card_b, card_unite),
                              produit_cardinal_bien_defini(b, _UNITE, b, UN))
    b_un = composer_egalites(N.modus_ponens(bien_def, symetrie(
        cardinal(E.produit(b, _UNITE)), produit_cardinal_binaire(b, UN))),
        b_unite)                                            # 𝔟·1 = 𝔟

    #  ── (2) 𝔟·2 = 𝔟+𝔟   (distributivité ; 1+{∅} EST 2, syntaxiquement) ────
    dist = distributivite_operations(b, UN, _UNITE)
    gauche, droite = dist.conclusion.termes
    assert gauche == produit_cardinal_binaire(b, DEUX), \
        "absorption : 1+{∅} n'est pas DEUX — l'encodage a changé"
    etape = _reecrire(b_un, somme_cardinale_binaire(var("wab"),
                                                    produit_cardinal_binaire(b, _UNITE)))
    etape = composer_egalites(etape, _reecrire(
        b_unite, somme_cardinale_binaire(b, var("wab"))))
    deux_b = composer_egalites(dist, etape)                 # 𝔟·2 = 𝔟+𝔟

    #  ── (3) 𝔟·2 ≤ 𝔟·𝔟   (2 ≤ 𝔟 puisque S₀ est infini) ────────────────────
    h_inf = N.assume(est_infini_ensemble(vS))
    assert h_inf.conclusion == est_infini(b), "absorption : infini ensemble/cardinal"
    deux_le = N.modus_ponens(conjonction_intro(h_card, h_inf),
                             deux_inf_egal_infini(b))        # 2 ≤ 𝔟
    mono = N.modus_ponens(deux_le, produit_cardinale_monotone_droite(DEUX, b, b))

    #  ── (4) 𝔟·𝔟 = 𝔟   (fourni par l'appelant : bijection φ₀, ou Hessenberg) ──
    assert carre.conclusion == egal(carre_b, b),         "absorption_depuis_carre : `carre` ne conclut pas 𝔟·𝔟 = 𝔟"

    #  ── (5) 𝔟+𝔟 ≤ 𝔟 ≤ 𝔟+𝔟, puis antisymétrie ───────────────────────────
    #  réécritures de Leibniz SUR LA FORMULE (S6), aux deux membres de `mono`
    prod_deux = produit_cardinal_binaire(b, DEUX)
    haut = N.modus_ponens(mono, equivalence_avant(N.modus_ponens(
        deux_b, N.s6(prod_deux, somme_bb, "wab",
                     inf_egal_card(var("wab"), carre_b)))))   # 𝔟+𝔟 ≤ 𝔟·𝔟
    haut = N.modus_ponens(haut, equivalence_avant(N.modus_ponens(
        carre, N.s6(carre_b, b, "wab",
                    inf_egal_card(somme_bb, var("wab"))))))   # 𝔟+𝔟 ≤ 𝔟
    #  ⚠️ `_inf_egal_somme_gauche_t` conclut au niveau ENSEMBLE (𝔟 ≤ 𝔟⊔𝔟) ;
    #  le pont X ≤ Card X puis la transitivité amènent au niveau CARDINAL.
    disj = somme_disjointe(b, b)
    bas = N.modus_ponens(conjonction_intro(_inf_egal_somme_gauche_t(b, b),
                                           _set_le_eq_card(disj)),
                         _le_trans_t(b, disj, somme_bb))      # 𝔟 ≤ 𝔟+𝔟
    assert bas.conclusion == inf_egal_card(b, somme_bb), \
        "absorption : la somme à gauche n'a pas la forme attendue"
    #  l'antisymétrie est ∀-clôturée sur des NOMS : on l'instancie aux termes
    anti = instancie(instancie(inf_egal_antisymetrique_card(), somme_bb), b)
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(haut, bas),
        est_cardinal_de_cardinal(somme_disjointe(b, b))), h_card), anti)

    assert res.conclusion == egal(somme_bb, b), "absorption : forme"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.27-28 | PDF p.151  (« 𝔟 + 𝔟 = 𝔟 »)
def absorption_au_maximal(S="S0", phi="phi0"):
    """🎯 { S₀ infini, φ₀ bijection } ⊢ Card S₀ + Card S₀ = Card S₀.

    Les deux hypothèses sont exactement des DONNÉES DU MAXIMAL, fournies dans
    la portée par `unpack_sous_maximal` : l'absorption cesse donc d'être un
    résidu à porter.

    Le carré 𝔟·𝔟 = 𝔟 vient ici de la bijection φ₀ ; le reste du raisonnement
    est dans `absorption_depuis_carre`."""
    vS = _t(S)
    b = cardinal(vS)
    carre_b = produit_cardinal_binaire(b, b)
    refl = N.reflexivite(b)                                  # Card S₀ = 𝔟
    sq = N.modus_ponens(conjonction_intro(refl, refl),
                        produit_cardinal_bien_defini(vS, vS, b, b))
    carre = composer_egalites(N.modus_ponens(sq, symetrie(
        cardinal(E.produit(vS, vS)), carre_b)),
        maximal_carre_egal(S, phi))                          # 𝔟·𝔟 = 𝔟
    return absorption_depuis_carre(S, carre)


__all__ = ["enonce_absorption", "absorption_depuis_carre",
           "absorption_au_maximal"]
