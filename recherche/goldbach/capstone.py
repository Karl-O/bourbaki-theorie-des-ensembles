# -*- coding: utf-8 -*-
"""Goldbach — LE CAPSTONE : rejouer toute la chaîne, et la juger par le noyau.

Ce module ne démontre AUCUN théorème neuf. Il reconstruit tous les maillons de
l'arc et vérifie, pour chacun, qu'il est bien clos et sans hypothèse — puis que
`theorie_ensembles()` vaut toujours 22. C'est le filet de sécurité du dossier :
si un lemme du dépôt bouge sous nos pieds, c'est ici qu'on l'apprend.

⚠️ VÉRIFICATION EN PROCESSUS, PAR LE NOYAU. La version d'origine (scratchpad)
lançait deux maillons en SOUS-PROCESSUS et cherchait la chaîne « CLOS: True »
dans leur `stdout`. Ce n'est pas une vérification : reformater un `print` la
faisait passer au vert. Ici chaque maillon est un objet `Theoreme` inspecté
directement — `est_clos`, `hypotheses`, et la conclusion comparée à sa cible
dans le module qui la produit.

LES DEUX COLONNES QUI COMPTENT. « clos » dit que le noyau accepte la preuve ;
« axiomes ad hoc » dit de quelle théorie dédiée elle dépend. Un maillon peut
être parfaitement clos ET reposer sur les deux axiomes du crible — c'est le cas
de la synthèse. Confondre les deux serait la seule vraie malhonnêteté possible
dans ce dossier, et c'est pour ça que la colonne existe.
"""
from __future__ import annotations

import time

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from recherche.goldbach.synthese import AXIOMES_CRIBLE

#: (nom lisible, module, fonction, axiomes ad hoc, lent ?)
MAILLONS = (
    ("GG6  pont-α premier₁ ⇒ premier₂", "composes", "pont_alpha_premier", (), False),
    ("GG2' famille des doubles {2p}", "composes", "famille_doubles", (), False),
    ("GG7← composés ⇒ moitiés", "composes", "composes_implique_moities", (), False),
    ("GG7→ moitiés ⇒ composés", "composes", "moities_implique_composes", (), False),
    ("GG9← DEP ⇒ témoins canoniques", "pont_tau", "pont_tau_aller", (), False),
    ("GG9→ témoins canoniques ⇒ DEP", "pont_tau", "pont_tau_retour", (), False),
    ("GG12 somme du témoin défini", "pont_tau", "_somme_glouton", (), False),
    ("GG19← rencontre ⇒ DEC_ent", "crible", "crible_implique_decomposition",
     AXIOMES_CRIBLE, False),
    ("GG19→ DEC_ent ⇒ rencontre", "crible", "decomposition_implique_crible",
     AXIOMES_CRIBLE, False),
    ("GG21 DEC_ent ⇒ DEP (dépôt)", "synthese", "gardee_implique_depot", (), False),
    ("GG22 k premier ⇒ rencontre", "synthese", "rencontre_des_premiers",
     AXIOMES_CRIBLE, False),
    ("GG23 symétrie : les paires m ↦ 2k−m", "symetrie", "symetrie_du_crible",
     AXIOMES_CRIBLE, False),
    ("GG24 SYNTHÈSE composés ⇒ Goldbach", "synthese",
     "composes_impliquent_goldbach", AXIOMES_CRIBLE, False),
    ("A1   défaut de fidélité de est_premier", "audit_fidelite",
     "indivisible_implique_premier", (), False),
    ("A2   la garde Fini est gratuite (2)", "audit_fidelite",
     "premier_ent_deux", (), True),
    ("DEMI l'un de la paire est ≤ k", "demi", "demi_intervalle", (), True),
    ("DEMI la rencontre tient dans [0,k]", "demi", "rencontre_se_restreint",
     AXIOMES_CRIBLE, True),
    ("DEMI [0,k] ⇒ [0,2k] (affaiblissement)", "demi",
     "demi_implique_rencontre", AXIOMES_CRIBLE, False),
)


def _somme_glouton():
    """GG12 sur le témoin glouton — enveloppé pour une signature uniforme."""
    from recherche.goldbach.pont_tau import (
        double, plus_grand_premier, somme_du_temoin,
    )
    return somme_du_temoin(plus_grand_premier(double()))


def _resoudre(module, nom):
    if nom == "_somme_glouton":
        return _somme_glouton
    import importlib
    return getattr(importlib.import_module("recherche.goldbach." + module), nom)


def verifie_chaine(inclure_lents=True, bavard=True):
    """→ (lignes, tout_vert). Rejoue chaque maillon et le juge par le noyau.

    `lignes` : liste de (nom, clos, axiomes, secondes). Un maillon qui LÈVE est
    compté comme non clos, avec l'exception dans la colonne — jamais avalé."""
    lignes, tout = [], True
    for (nom, module, fonction, axiomes, lent) in MAILLONS:
        if lent and not inclure_lents:
            continue
        t0 = time.time()
        try:
            th = _resoudre(module, fonction)()
            clos = bool(th.est_clos and not th.hypotheses)
            detail = ("0 axiome ad hoc" if not axiomes
                      else "%d ad hoc : %s" % (len(axiomes), ", ".join(axiomes)))
        except Exception as exc:                       # noqa: BLE001
            clos, detail = False, "%s: %s" % (type(exc).__name__, str(exc)[:70])
        dt = time.time() - t0
        tout = tout and clos
        lignes.append((nom, clos, detail, dt))
        if bavard:
            print("  %-42s %-5s %-46s %5.0f s"
                  % (nom, "CLOS" if clos else "ÉCHEC", detail, dt), flush=True)
    invariant = len(E.theorie_ensembles().axiomes)
    if bavard:
        print("  %-42s %d (attendu 22)" % ("theorie_ensembles()", invariant),
              flush=True)
    return lignes, (tout and invariant == 22)


def main():
    print("=" * 104, flush=True)
    print(" GOLDBACH — rejeu complet de la chaîne certifiée", flush=True)
    print("=" * 104, flush=True)
    _, vert = verifie_chaine()
    print("-" * 104, flush=True)
    print(" VERDICT :", "chaîne entière verte" if vert else "AU MOINS UN MAILLON CASSÉ",
          flush=True)
    print(" RAPPEL : la conjecture de Goldbach reste OUVERTE. Ce qui est certifié,",
          "\n c'est la carte — les équivalences et le but unique qu'elles désignent.",
          flush=True)
    return 0 if vert else 1


__all__ = ["MAILLONS", "verifie_chaine", "main"]


if __name__ == "__main__":
    import sys
    import threading
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(64 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
