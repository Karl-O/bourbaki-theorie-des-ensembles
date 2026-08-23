# -*- coding: utf-8 -*-
"""§III.6.3 — 🏆 HESSENBERG a·a = a, PAR L'ARGUMENT D'EXTENSION COMPLET.

🎯 CIBLE (Th. 2, E III.47) :

    hessenberg_par_extension(E) :
        { existence_maximal(E),  residus_maximal(E) }  ⊢  enonce_hessenberg(E)

Le dernier assemblage.  `claim_clos` établit « Card S₀ = Card E » dans la
portée du maximal ; `claim_vers_endgame` en tire l'énoncé de Hessenberg ; il
ne reste qu'à sortir de la portée par `unpack_sous_maximal`.

⚠️ LA CONTRAINTE QUI FAÇONNE CE MODULE.  Sortir de la portée exige qu'AUCUNE
hypothèse résiduelle ne mentionne les témoins S₀, φ₀, m.  Or les trois résidus
honnêtes du CLAIM les mentionnent tous (l'absorption porte sur Card S₀, le
transport sur E∖S₀, le paquet sur (S₀,φ₀)).  Ils sont donc portés SOUS
(∀S)(∀φ) — exactement le traitement déjà appliqué à U dans `donnees_extension`
et aux chaînes dans `donnees_recollement`.

Astuce de robustesse : les liants portent le NOM MÊME des témoins (Smx, phimx),
si bien que l'instanciation à l'intérieur de la portée est l'identité — la
correspondance avec les hypothèses du CLAIM est alors garantie, et non
seulement espérée (les τ-termes rendent toute reconstruction fragile, LEÇON 15).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from functools import reduce

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, appartient, inclus, pourtout, afficher_f,
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


def _residus(E_set, S=_S, phi=_PHI):
    """Les résidus honnêtes du CLAIM, en ordre canonique (absorption,
    transport, garde d'extension) — tout ce qui n'est pas donnée du maximal."""
    claim = claim_clos(E_set, S, phi)
    connus = _donnees_du_maximal(E_set, S, phi)
    return sorted((h for h in claim.hypotheses if h not in connus),
                  key=afficher_f)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.26-33 | PDF p.151
def residus_maximal(E_set="E", S=_S, phi=_PHI):
    """L'unique hypothèse honnête restante, quantifiée sur le maximal :

        (∀S)(∀φ)( absorption(Card S)  et  transport(Card S, E∖S)
                  et  (∀U)(garde ⇒ (∃ψ)PAQUET) ).

    Ce sont les trois pièces que Bourbaki obtient par le calcul cardinal et
    par le choix d'une partie de E∖F ; elles sont ici NOMMÉES, jamais
    postulées vraies, et déchargées explicitement."""
    res = _residus(E_set, S, phi)
    corps = reduce(lambda acc, x: et(x, acc), reversed(res[:-1]), res[-1])
    return pourtout(S, pourtout(phi, corps))


def _decoupe(thm, n):
    """Découpe le théorème d'une conjonction repliée à droite en ses n conjoints."""
    out, cur = [], thm
    for _ in range(n - 1):
        out.append(conjonction_elim_gauche(cur))
        cur = conjonction_elim_droite(cur)
    out.append(cur)
    return out


# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150
def hessenberg_par_extension(E_set="E"):
    """🏆🏆 { existence_maximal(E), residus_maximal(E) } ⊢ enonce_hessenberg(E).

    Le théorème de Hessenberg par la démonstration de Bourbaki au complet :
    Zorn fournit le maximal (F,f), l'argument d'extension force Card F = Card E,
    et la bijection f : F×F → F transporte l'égalité à E."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    residus = _residus(E_set)
    paquet_residus = residus_maximal(E_set)

    def derive(bij0, S_inc, S_inf, h_max, vS0, vphi0, p_eq):
        claim = claim_clos(E_set, vS0.nom, vphi0.nom)
        couple = E.couple(vS0, vphi0)
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

        #  les résidus honnêtes : instanciation (identité) du ∀S∀φ
        corps = instancie(instancie(N.assume(paquet_residus), vS0), vphi0)
        for morceau in _decoupe(corps, len(residus)):
            if morceau.conclusion in claim.hypotheses:
                claim = _cut(morceau, morceau.conclusion, claim)

        return claim_vers_endgame(E_set, vS0.nom, vphi0.nom, bij0, claim)

    res = unpack_sous_maximal(E_set, derive)
    assert res.conclusion == enonce_hessenberg(E_set), \
        "hessenberg_par_extension : conclusion"
    return res


__all__ = ["residus_maximal", "hessenberg_par_extension"]
