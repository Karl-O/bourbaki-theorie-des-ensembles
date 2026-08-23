# -*- coding: utf-8 -*-
"""§III.6.3 — 🏆 HESSENBERG a·a = a, PAR L'ARGUMENT D'EXTENSION COMPLET.

🎯 CIBLE (Th. 2, E III.47) :

    hessenberg_par_extension(E) :
        { existence_maximal(E),  residus_maximal(E) }  ⊢  enonce_hessenberg(E)

Le dernier assemblage.  `claim_clos` établit « Card S₀ = Card E » dans la
portée du maximal ; `claim_vers_endgame` en tire l'énoncé de Hessenberg ; il
ne reste qu'à sortir de la portée par `unpack_sous_maximal`.

⚠️ LA CONTRAINTE QUI FAÇONNE CE MODULE.  Sortir de la portée exige qu'AUCUNE
hypothèse résiduelle ne mentionne les témoins S₀, φ₀, m.  Or le résidu honnête
du CLAIM — le paquet ψ — les mentionne.  Il est donc porté SOUS
(∀S)(∀φ) — exactement le traitement déjà appliqué à U dans `donnees_extension`
et aux chaînes dans `donnees_recollement`.

Astuce de robustesse : les liants portent le NOM MÊME des témoins (Smx, phimx),
si bien que l'instanciation à l'intérieur de la portée est l'identité — la
correspondance avec les hypothèses du CLAIM est alors garantie, et non
seulement espérée (les τ-termes rendent toute reconstruction fragile, LEÇON 15).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from functools import lru_cache, reduce

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, inclus, pourtout, afficher_f, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant, instancie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_unpack_garde import (
    unpack_sous_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_claim import (
    claim_vers_endgame,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_endgame import (
    claim_clos,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_absorption import (
    enonce_absorption, absorption_au_maximal,
)

_S, _PHI, _M = "Smx", "phimx", "mmx"


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge `formule` de `thm` par `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _donnees_du_maximal(E_set, S=_S, phi=_PHI):
    """Les cinq énoncés que `unpack_sous_maximal` fournit dans la portée."""
    vE, vS, vphi = _t(E_set), _t(S), _t(phi)
    couple = E.couple(vS, vphi)
    return {est_bijection_de(vphi, E.produit(vS, vS), vS),
            inclus(vS, vE),
            est_infini_ensemble(vS),
            element_maximal(frame_ordre(vE), frame_pair(vE), couple, "x"),
            appartient(couple, frame_pair(vE))}


@lru_cache(maxsize=None)
def _claim_memo(E_set, S, phi, paquet_derive):
    """`claim_clos` MÉMOÏSÉ (arguments hashables, Theoreme immuable).

    Mesure : le chemin complet coûte ~385 s et l'assemblage l'appelle trois
    fois (collationnement des résidus, énoncé du paquet, dérivation).  Le
    cache ramène le total au coût d'UNE dérivation.  Aucun effet sur la
    soundness : la fonction est pure et le noyau ne connaît pas l'identité
    des objets."""
    return claim_clos(E_set, S, phi, paquet_derive=paquet_derive)


def _residus(E_set, S=_S, phi=_PHI, paquet_derive=False):
    """Les résidus honnêtes du CLAIM (transport, garde d'extension) — tout ce
    qui n'est ni donnée du maximal, ni DÉRIVÉ sur place.

    L'absorption 𝔟+𝔟=𝔟 n'en fait plus partie : `absorption_au_maximal` la tire
    de la bijection φ₀.  On la reconnaît par son ÉNONCÉ seul, pour ne pas payer
    les ~200 s de sa dérivation à chaque collationnement."""
    claim = _claim_memo(E_set, S, phi, paquet_derive)
    connus = _donnees_du_maximal(E_set, S, phi) | {enonce_absorption(S)}
    return sorted((h for h in claim.hypotheses if h not in connus),
                  key=afficher_f)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.26-33 | PDF p.151
def residus_maximal(E_set="E", S=_S, phi=_PHI, paquet_derive=False):
    """L'UNIQUE hypothèse honnête restante, quantifiée sur le maximal :

        (∀S)(∀φ)(∀U)( garde ⇒ (∃ψ) PAQUET(U,ψ) ).

    C'est le calcul cardinal de Bourbaki : la zone (S₀∪U)² ∖ (S₀×S₀) a le
    cardinal 𝔟, donc se met en bijection avec U.  NOMMÉE, jamais postulée
    vraie, déchargée explicitement.

    Les deux autres résidus ont été ÉLIMINÉS le 2026-08-23 : l'ABSORPTION est
    dérivée (`ensembles_absorption`), et le TRANSPORT était déjà clos en amont
    (GAP B, `existe_sous_ensemble_cardinal_transporte`).

    ⚠️ RETOURNE `None` quand il n'y a PLUS AUCUN résidu — c'est l'état VISÉ, pas
    une anomalie : avec `paquet_derive=True` le paquet ψ est construit et le
    claim ne porte plus que les données du maximal.  Une conjonction vide n'a
    pas de formule ; l'appelant saute alors l'étape de décharge."""
    res = _residus(E_set, S, phi, paquet_derive)
    if not res:
        return None
    corps = reduce(lambda acc, x: et(x, acc), reversed(res[:-1]), res[-1])
    #  le ∀S∀φ ne sert QUE si le corps mentionne le maximal ; avec
    #  `paquet_derive` les résidus sont déjà CLOS, l'enrobage serait décoratif.
    libres = libres_f(corps)
    if S in libres or phi in libres:
        return pourtout(S, pourtout(phi, corps))
    return corps


def _decoupe(thm, n):
    """Découpe le théorème d'une conjonction repliée à droite en ses n conjoints."""
    out, cur = [], thm
    for _ in range(n - 1):
        out.append(conjonction_elim_gauche(cur))
        cur = conjonction_elim_droite(cur)
    out.append(cur)
    return out


# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150
def hessenberg_par_extension(E_set="E", paquet_derive=False):
    """🏆🏆 { existence_maximal(E) [, residus_maximal(E)] } ⊢ enonce_hessenberg(E).

    Le théorème de Hessenberg par la démonstration de Bourbaki au complet :
    Zorn fournit le maximal (F,f), l'argument d'extension force Card F = Card E,
    et la bijection f : F×F → F transporte l'égalité à E.

    Sous `paquet_derive=True` il n'y a PLUS de résidu du tout (`residus_maximal`
    rend `None`) : l'existence du maximal reste seule, et `hessenberg_final` la
    décharge à son tour."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    residus = _residus(E_set, paquet_derive=paquet_derive)
    paquet_residus = residus_maximal(E_set, paquet_derive=paquet_derive)
    #  `residus_maximal` n'enrobe de (∀S)(∀φ) que si le corps mentionne le
    #  maximal : on le détecte en comparant au corps replié, pas en comptant.
    #  Sans aucun résidu (paquet_derive=True), il n'y a ni corps ni enrobage.
    enrobe = False
    if residus:
        corps_nu = reduce(lambda acc, x: et(x, acc),
                          reversed(residus[:-1]), residus[-1])
        enrobe = paquet_residus != corps_nu

    def derive(bij0, S_inc, S_inf, h_max, vS0, vphi0, p_eq):
        claim = _claim_memo(E_set, vS0.nom, vphi0.nom, paquet_derive)
        couple = E.couple(vS0, vphi0)

        #  l'absorption est DÉRIVÉE de la bijection φ₀, non portée en résidu
        abso = absorption_au_maximal(vS0.nom, vphi0.nom)
        if abso.conclusion in claim.hypotheses:
            claim = _cut(abso, abso.conclusion, claim)
        vm = _t(_M)

        #  transport Leibniz : ce qui vaut de m vaut de (S₀,φ₀)
        def vers_couple(thm, motif):
            return N.modus_ponens(thm, equivalence_avant(
                N.modus_ponens(p_eq, N.s6(vm, couple, "wmx", motif))))

        max_c = vers_couple(h_max, element_maximal(Gam, Fr, var("wmx"), "x"))
        in_c = vers_couple(conjonction_elim_gauche(h_max),
                           appartient(var("wmx"), Fr))

        for preuve in (bij0, S_inc, S_inf, max_c, in_c):
            if preuve.conclusion in claim.hypotheses:
                claim = _cut(preuve, preuve.conclusion, claim)

        #  les résidus honnêtes : instanciation (identité) du ∀S∀φ.
        #  Liste vide ⇒ rien à décharger : le claim est déjà sans résidu.
        if residus:
            corps = N.assume(paquet_residus)
            if enrobe:
                corps = instancie(instancie(corps, vS0), vphi0)
            for morceau in _decoupe(corps, len(residus)):
                if morceau.conclusion in claim.hypotheses:
                    claim = _cut(morceau, morceau.conclusion, claim)

        return claim_vers_endgame(E_set, vS0.nom, vphi0.nom, bij0, claim)

    res = unpack_sous_maximal(E_set, derive)
    assert res.conclusion == enonce_hessenberg(E_set), \
        "hessenberg_par_extension : conclusion"
    return res


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151
def hess_maximal_clos(E_set="E"):
    """🎯🎯🎯 { est_infini(Card E) } ⊢ (∃m) element_maximal( Γ𝔉(E), 𝔉(E), m ).

    `hess_maximal` portait DEUX hypothèses ; la seconde, `donnees_recollement`,
    est devenue un théorème (`donnees_recollement_prouve`, 0 hypothèse, via les
    onze données du recollement).  Il ne reste que la donnée du théorème."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_hess_garde import (
        hess_maximal, donnees_recollement,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_recollement import (
        donnees_recollement_prouve,
    )
    base = hess_maximal(E_set)
    dr = donnees_recollement_prouve(E_set)
    assert dr.conclusion == donnees_recollement(E_set),         "hess_maximal_clos : le théorème ne coïncide pas avec l'hypothèse portée"
    res = _cut(dr, dr.conclusion, base)
    assert len(res.hypotheses) == 1,         "hess_maximal_clos : hyps ≠ 1 (%d)" % len(res.hypotheses)
    return res


# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150
def hessenberg_final(E_set="E", paquet_derive=True):
    """🏆🏆🏆 { est_infini(Card E) } ⊢ enonce_hessenberg(E).

    L'existence du maximal, jusqu'ici portée en hypothèse, est DÉCHARGÉE par
    `hess_maximal_clos` — elle ne coûte plus que « E est infini », qui est
    l'hypothèse même du théorème de Bourbaki.

    ⚠️ 2026-08-23 : `predecesseur_fini_universel` ne figure plus ici.  Le dépôt
    la PROUVE (Prop. 2 §III.5) et elle est déchargée à la source, dans
    `fini_downward_cardinal` ; l'ancienne docstring la portait encore.  Il ne
    reste donc QUE l'hypothèse de Bourbaki."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_unpack_garde import (
        existence_maximal,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        alpha_existe,
    )
    base = hessenberg_par_extension(E_set, paquet_derive=paquet_derive)
    porte = existence_maximal(E_set)
    maxi = hess_maximal_clos(E_set)
    if maxi.conclusion != porte:
        #  les liants diffèrent (« m » chez hess_maximal, « mmx » ici) : α-pont
        maxi = N.modus_ponens(maxi, equivalence_avant(alpha_existe(
            maxi.conclusion.lieur, porte.lieur, maxi.conclusion.sous[0])))
    assert maxi.conclusion == porte, "hessenberg_final : α-pont insuffisant"
    res = _cut(maxi, porte, base)
    assert res.conclusion == enonce_hessenberg(E_set), "hessenberg_final : forme"
    return res


__all__ = ["residus_maximal", "hessenberg_par_extension",
           "hess_maximal_clos", "hessenberg_final"]
