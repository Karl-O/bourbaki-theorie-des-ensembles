# -*- coding: utf-8 -*-
"""M1 — Ax(D) : quels axiomes une dérivation a-t-elle RÉELLEMENT consommés ?

LE PROBLÈME (mesuré le 2026-07-26).
    `noyau_abrege.axiome(theorie, f)` renvoie un `Theoreme` à **zéro hypothèse**,
    quelle que soit la théorie. Et `Theoreme.__slots__` vaut
    `("hypotheses", "conclusion", "justification")` : aucun lien vers les
    prémisses, donc le DAG de dérivation est détruit à la construction.
    Conséquence : un théorème bâti sur une théorie DÉDIÉE (« Inter-selection »,
    « P-Zorn », « Famille-assoc-reunion », …) est *indiscernable* d'un théorème
    bâti sur les seuls 22 axiomes de `theorie_ensembles()` — ni le compte
    d'hypothèses, ni l'invariant « 22 » ne le voient. Ce n'est pas de la triche
    (le procédé est établi et documenté fichier par fichier), mais l'invariant
    « 22 » ne mesure PAS ce qu'il prétend mesurer.

CE QUE CE MODULE MESURE (définitions arrêtées avec Karl le 2026-07-26).
    Ax(D)      := { (nom_théorie, formule) : la règle `axiome(T, α)` a été
                    appliquée AVEC SUCCÈS pendant la dérivation D }
    Dette(th)  := hypotheses(th) ∪ { α : (nom, α) ∈ Ax(D), (nom, α) hors de T0 }
    « rien postulé »   ⟺  Dette(th) = ∅
    invariant CORRECT  ⟺  Ax(D) ⊆ {T0.nom} × A_T0      (et NON |A_T0| = 22)

COMMENT — OBSERVATION PURE, ZÉRO MONKEYPATCH.
    On installe un `sys.setprofile` le temps du thunk et on relève les frames
    dont l'objet code EST celui de la règle `axiome`. Rien n'est remplacé :
    `N.axiome` reste `N.axiome`, le noyau et `subst` sont INTOUCHÉS, aucun
    `Theoreme` n'est fabriqué ici. Le profileur est restauré dans un `finally`.

    ⚠️ Il existe DEUX implémentations de la règle : `noyau/noyau.py` (τ) et
    `noyau/noyau_abrege.py` (abrégé). Surveiller une seule produit un FAUX
    NÉGATIF SILENCIEUX. `regles_surveillees()` publie ce qui est réellement
    observé — appelez-la en cas de doute.

COÛT — MESURÉ le 2026-07-26 (python 3.13 global, meilleur de 5 rounds) :
        axiome + 3 `instancie`         0,292 ms → 1,013 ms   ×3,47
        `inter_donne_membres()`        0,689 ms → 2,132 ms   ×3,09
        `inter_par_membres_si_temoin()` 1,142 ms → 4,024 ms   ×3,52
    Soit **≈ ×3,4, franchement au-dessus de ×2** : `sys.setprofile` intercepte
    CHAQUE appel/retour Python du thunk, pas seulement `axiome`. Conclusion
    assumée : **outil d'AUDIT, à ne PAS installer dans la suite de tests**
    (une suite déjà à ~2 h passerait à ~7 h).

LIMITES (à lire avant de conclure « rien postulé »).
    1. MÉMOÏSATION = FAUX NÉGATIF. Une fonction de preuve décorée `lru_cache`
       (il y en a dans le corpus : `ensembles_aleph0.py`, `ensembles_ensemble_NN.py`,
       `ensembles_gate_onto_top.py`, `ensembles_prop8_fini2.py`, `transposition/_existence.py`)
       ne rejoue PAS son corps au 2ᵉ appel du process : `axiome` n'est pas
       rappelée, Ax(D) revient VIDE alors que la dérivation consomme bel et bien
       des axiomes. Mesurez toujours en process FRAIS, ou premier appel.
       (Le test miroir DÉMONTRE ce faux négatif au lieu de le taire.)
    2. Un `Theoreme` construit au niveau MODULE (à l'import) échappe au thunk :
       il est déjà bâti quand la sonde s'installe. Même trou pour un `Theoreme`
       stocké dans une globale/un cache maison entre deux appels. Règle
       générale : **la sonde ne voit que ce qui RENTRE dans le corps Python de
       `axiome` pendant le thunk** — jamais un résultat réutilisé.
       (`axiome` est une fonction Python pure : appelée depuis du code C —
       `map`, callback — elle crée quand même sa frame et EST vue. La cécité au
       C n'est donc pas ici ; elle est en 1 et 2, où l'appel n'a pas lieu.)
    3. `sys.setprofile` est PAR THREAD : une dérivation menée dans un thread
       fils (ou un sous-process) est totalement invisible.
    4. On mesure les axiomes CONSOMMÉS, pas les axiomes NÉCESSAIRES : un appel
       `axiome` dont le résultat est jeté compte quand même (sur-estimation).
       Symétriquement, Ax(D) ne dit rien de la fidélité de l'énoncé.
       Et Ax(D) est un ENSEMBLE : il ne dit pas combien de fois un axiome sert.
    5. Cet outil est incompatible avec un autre profileur/couverture actif : il
       restaure celui qu'il a trouvé, mais ne peut pas en faire tourner deux.

PREMIÈRE MESURE UTILE (2026-07-26). `theorie_inter_selection()` (« Inter-selection »,
    §II.4.1) sert une formule qui EST devenue, mot pour mot, `E.AXIOME_INTER_FAM`,
    l'un des 22 — la réparation de l'incohérence de l'intersection l'a absorbée.
    M1 la compte donc en dette (le nom diffère, cf. la définition arrêtée), mais
    cette dette est DÉCHARGEABLE au sens de M2 `classer_residu` : A_T0 ⊢ h en un
    pas. Lire un verdict M1 sans passer par M2 sur-estime la dette réelle.
"""
from __future__ import annotations

import os
import sys
from typing import Any, Callable

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau as _noyau_tau,
    noyau_abrege as _noyau_abrege,
)

# ── Les DEUX règles `axiome` du dépôt ────────────────────────────────────────
_REGLES = (_noyau_tau.axiome, _noyau_abrege.axiome)
_NOM_REGLE = "axiome"
_CODES = frozenset(r.__code__ for r in _REGLES)
_SOURCES = frozenset(os.path.realpath(r.__code__.co_filename) for r in _REGLES)

# Cache co_filename → est-ce un fichier-noyau ? (le profileur est un chemin chaud)
_EST_SOURCE_NOYAU: dict[str, bool] = {}


def regles_surveillees() -> tuple[str, ...]:
    """Chemins des fichiers dont la règle `axiome` est observée (auto-diagnostic).

    Doit contenir DEUX entrées : `noyau.py` et `noyau_abrege.py`. S'il n'y en a
    qu'une, toute mesure de ce module est un faux négatif en puissance."""
    return tuple(sorted(_SOURCES))


def _est_regle_axiome(code) -> bool:
    """True ssi `code` est l'objet code d'une des deux règles `axiome` du noyau.

    Le test d'identité suffit dans le cas normal ; le repli par chemin réel
    rattrape le cas où le paquet `noyau` a été importé DEUX fois (préfixes
    `sys.path` différents ⇒ objets code distincts pour le MÊME fichier), qui
    ferait sinon manquer des axiomes sans le dire."""
    if code in _CODES:
        return True
    if code.co_name != _NOM_REGLE:
        return False
    fichier = code.co_filename
    reponse = _EST_SOURCE_NOYAU.get(fichier)
    if reponse is None:
        try:
            reponse = os.path.realpath(fichier) in _SOURCES
        except OSError:                     # chemin exotique (<string>, zipimport)
            reponse = False
        _EST_SOURCE_NOYAU[fichier] = reponse
    return reponse


def _sonde(collecte: list, anomalies: list) -> Callable:
    """Fabrique la fonction de profilage. Elle n'écrit QUE dans `collecte`."""

    def profil(frame, event, arg):
        # On relève au RETOUR, et seulement si la règle a rendu un objet :
        # `axiome` lève quand la formule n'est pas un axiome explicite, et un
        # appel qui lève ne met AUCUN Theoreme dans la dérivation (arg is None).
        if event != "return" or arg is None:
            return
        code = frame.f_code
        if code.co_name != _NOM_REGLE or not _est_regle_axiome(code):
            return
        try:
            noms = code.co_varnames[: code.co_argcount]
            locales = frame.f_locals
            theorie = locales.get(noms[0])
            formule = locales.get(noms[1])
            collecte.append((getattr(theorie, "nom", "<théorie-sans-nom>"), formule))
        except Exception as exc:            # jamais silencieux : cf. axiomes_consommes
            anomalies.append(exc)

    return profil


# ── API ──────────────────────────────────────────────────────────────────────
def axiomes_consommes(thunk: Callable[[], Any]) -> tuple[Any, frozenset]:
    """Exécute `thunk()` sous observation et renvoie `(résultat, Ax(D))`.

    `Ax(D)` est un `frozenset` de couples `(nom_de_la_théorie, formule)` : un
    couple par axiome DISTINCT effectivement consommé (les répétitions
    fusionnent — Ax(D) est un ensemble, pas un multiensemble).

    Le résultat du thunk est rendu tel quel (aucune vérification de type ici :
    `dette` s'en charge). Le profileur précédent est TOUJOURS restauré, y
    compris si `thunk` lève — l'exception se propage inchangée.

    Lève `RuntimeError` si la sonde elle-même a échoué : sous-compter en
    silence serait pire que planter."""
    collecte: list = []
    anomalies: list = []
    precedent = sys.getprofile()
    sys.setprofile(_sonde(collecte, anomalies))
    try:
        resultat = thunk()
    finally:
        sys.setprofile(precedent)
    if anomalies:
        raise RuntimeError(
            "sonde axiomes_consommes défaillante (%d incident(s)) — mesure NON "
            "fiable : %r" % (len(anomalies), anomalies[0])
        )
    return resultat, frozenset(collecte)


def _etrangers(ax: frozenset, T0) -> frozenset:
    """Sous-ensemble de Ax(D) qui n'est PAS un axiome explicite de T0.

    Critère : `nom != T0.nom` (la définition arrêtée) **ou** la formule n'est
    pas dans `T0.axiomes`. Le second disjoint est une extension CONSERVATRICE :
    il ne peut qu'AJOUTER de la dette (cas d'une théorie tierce qui usurperait
    le nom de T0), jamais en cacher. Sur le dépôt au 2026-07-26, un seul site
    construit `Theorie("Ensembles", …)` — les deux critères coïncident donc."""
    connus = frozenset(T0.axiomes)
    nom0 = T0.nom
    return frozenset((n, f) for (n, f) in ax if n != nom0 or f not in connus)


def dette(thunk: Callable[[], Any], T0) -> tuple[frozenset, frozenset]:
    """`(Dette(th), axiomes étrangers NOMMÉS)` de la dérivation faite par `thunk`.

    * 1ᵉʳ membre — `frozenset[Formule]` : hypothèses non déchargées du théorème
      **∪** formules des axiomes consommés hors de T0. C'est la mesure de
      « rien postulé » : `Dette = ∅` ⟺ le théorème ne doit rien à personne.
    * 2ᵉ membre — `frozenset[tuple[str, Formule]]` : les MÊMES axiomes étrangers,
      mais nommés par leur théorie, pour qu'un rapport puisse écrire
      « doit l'axiome de la théorie *Inter-selection* » et pas juste « doit 1 ».

    `thunk` doit rendre un `Theoreme` (on lit ses `hypotheses`) ; sinon
    `TypeError`, plutôt qu'une dette faussement vide."""
    theoreme, ax = axiomes_consommes(thunk)
    hypotheses = getattr(theoreme, "hypotheses", None)
    if hypotheses is None:
        raise TypeError(
            "dette() attend un thunk rendant un Theoreme ; reçu %r" % (type(theoreme),)
        )
    etrangers = _etrangers(ax, T0)
    return frozenset(hypotheses) | frozenset(f for (_, f) in etrangers), etrangers


def invariant_reel(thunk: Callable[[], Any], T0) -> bool:
    """L'invariant que « `len(theorie_ensembles().axiomes) == 22` » ne teste pas.

    True ⟺ `Ax(D) ⊆ {T0.nom} × A_T0` : la dérivation n'a consommé QUE des
    axiomes explicites de T0. Compter les axiomes de T0 ne dit rien de ce qu'une
    preuve consomme AILLEURS ; ceci le dit.

    N.B. — c'est bien un énoncé sur les AXIOMES : un théorème peut satisfaire
    `invariant_reel` et garder des hypothèses non déchargées. Pour « rien
    postulé » au sens fort, exigez `dette(...)[0] == frozenset()`."""
    _, ax = axiomes_consommes(thunk)
    return not _etrangers(ax, T0)


__all__ = ["axiomes_consommes", "dette", "invariant_reel", "regles_surveillees"]
