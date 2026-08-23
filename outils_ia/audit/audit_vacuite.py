# -*- coding: utf-8 -*-
"""AUDIT DE VACUITÉ — un théorème porte-t-il une hypothèse NON SATISFAITE ?

MOTIF (2026-08-23, §III.6.3).  Le noyau garantit la *soundness* : aucune
dérivation fausse.  Il ne garantit RIEN sur la vérité d'une hypothèse honnête.
Si une hypothèse est insatisfaisable, tout théorème qui la porte est VRAI ET
VIDE — la dérivation est correcte et l'énoncé ne dit rien.

Le cas fondateur : `fini_downward_thm` conclut l'universel NU
`(∀a)(∀x)( (a ≤ x et Fini x) ⇒ Fini a )` depuis deux hypothèses closes dont
l'une — la ∀∀-clôture nue de `cardinal_pas_entre` — n'est pas satisfaite : le
dépôt ne prouve que la forme GARDÉE par `est_cardinal`, et la nue est fausse dès
que `a` n'est pas un cardinal.  Voir `docs/journal/ANOMALIES.md`, 2026-08-23.

AUCUN test ne l'attrape : les tests vérifient qu'un théorème se construit, pas
que ses hypothèses soient vraies.  D'où cet outil.

USAGE :

    python -m outils_ia.audit.audit_vacuite recherche.goldbach

    ou, en bibliothèque :
        rapport = audite_paquet("recherche.goldbach", MODULES)

PORTÉE ET LIMITE, à dire clairement.  L'outil éprouve les exports `__all__`
appelables SANS argument et compare leurs hypothèses au REGISTRE des formules
connues insatisfaisables.  Il ne découvre pas de nouvelles formules fausses :
il vérifie la non-contamination par celles qu'on a déjà datées.  Un théorème
SANS hypothèse est immunisé par construction — c'est le résultat le plus fort
qu'il puisse rendre.
"""
from __future__ import annotations

import importlib
import inspect

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau.noyau_abrege import (
    Theoreme,
)


def registre_insatisfaisables():
    """Les formules DATÉES comme non satisfaites, avec leur étiquette.

    Import PARESSEUX : ces modules sont lourds (cardinaux), et l'outil doit
    rester appelable sur un paquet qui ne les touche pas."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
        cardinal_pas_entre,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
        fini_downward,
    )
    return {
        "cardinal_pas_entre NU (ANOMALIES 2026-08-23)":
            pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c")))),
        "fini_downward NU (ANOMALIES 2026-08-23)":
            pourtout("a", pourtout("x", fini_downward(var("a"), var("x")))),
    }


def _sans_argument(fn):
    """→ True si `fn` s'appelle sans argument (tous paramètres à défaut)."""
    try:
        params = inspect.signature(fn).parameters.values()
    except (TypeError, ValueError):
        return False
    return all(p.default is not inspect.Parameter.empty for p in params)


def audite_module(chemin, suspectes):
    """→ (eprouves, touches, echecs, immunises) pour UN module importable.

    `immunises` compte les théorèmes à ZÉRO hypothèse : le mode de défaillance
    exige une hypothèse pour s'y loger, donc ceux-là sont hors d'atteinte."""
    eprouves, touches, echecs, immunises = 0, [], [], 0
    try:
        mod = importlib.import_module(chemin)
    except Exception as exc:                       # import lourd, remontée douce
        return 0, [], [(chemin, "import : %s" % str(exc)[:70])], 0

    for nom in getattr(mod, "__all__", []):
        fn = getattr(mod, nom, None)
        if not callable(fn) or not _sans_argument(fn):
            continue
        try:
            th = fn()
        except Exception as exc:
            echecs.append(("%s.%s" % (chemin, nom),
                           "%s : %s" % (type(exc).__name__, str(exc)[:60])))
            continue
        if not isinstance(th, Theoreme):
            continue
        eprouves += 1
        if not th.hypotheses:
            immunises += 1
            continue
        for etiquette, formule in suspectes.items():
            if formule in th.hypotheses:
                touches.append(("%s.%s" % (chemin, nom), etiquette))
    return eprouves, touches, echecs, immunises


def audite_paquet(paquet, modules, suspectes=None):
    """→ le rapport agrégé sur une liste de modules d'un même paquet."""
    suspectes = registre_insatisfaisables() if suspectes is None else suspectes
    eprouves, touches, echecs, immunises = 0, [], [], 0
    for m in modules:
        e, t, x, i = audite_module("%s.%s" % (paquet, m), suspectes)
        eprouves, immunises = eprouves + e, immunises + i
        touches.extend(t)
        echecs.extend(x)
    return {"eprouves": eprouves, "touches": touches,
            "echecs": echecs, "immunises": immunises}


def imprime(rapport):
    """Une sortie honnête : ce qui est éprouvé, ce qui est immunisé, ce qui rate."""
    print("THÉORÈMES ÉPROUVÉS                     : %d" % rapport["eprouves"])
    print("  dont SANS hypothèse (immunisés)      : %d" % rapport["immunises"])
    print("PORTENT UNE HYPOTHÈSE NON SATISFAITE   : %d" % len(rapport["touches"]))
    for f, e in rapport["touches"]:
        print("   ✗ %-48s %s" % (f, e))
    print("non évaluables (erreur à l'appel)      : %d" % len(rapport["echecs"]))
    for f, e in rapport["echecs"][:8]:
        print("   · %-48s %s" % (f, e))
    return 1 if rapport["touches"] else 0


#  Les modules de la chaîne Goldbach — le paquet pour lequel l'outil est né.
MODULES_GOLDBACH = ["capstone", "composes", "crible", "demi", "pont_tau",
                    "symetrie", "synthese", "audit_fidelite"]


def _main(argv):
    import io as _io
    import sys as _sys
    _sys.stdout = _io.TextIOWrapper(_sys.stdout.buffer, encoding="utf-8",
                                    errors="replace")
    paquet = argv[1] if len(argv) > 1 else "recherche.goldbach"
    modules = argv[2:] or (MODULES_GOLDBACH if paquet == "recherche.goldbach"
                           else [])
    if not modules:
        print("usage : python -m outils_ia.audit.audit_vacuite <paquet> <mod...>")
        return 2
    return imprime(audite_paquet(paquet, modules))


if __name__ == "__main__":
    import sys
    sys.exit(_main(sys.argv))


__all__ = ["registre_insatisfaisables", "audite_module", "audite_paquet",
           "imprime", "MODULES_GOLDBACH"]
