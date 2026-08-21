# -*- coding: utf-8 -*-
"""LE MINEUR DE MOTIFS — retrouver l'opération dans le but (21 août 2026, A4).

La moitié « proposition » du marcheur : anti-unification structurelle à SLOTS
PARTAGÉS sur les sous-termes du but, classement par gain MDL
(occurrences−1)×taille — le critère de compression de v20 (notions), transposé
des formules aux termes. Le motif ⊕ SORT DU BUT : personne ne le nomme.

DEUX LOIS DE CONCEPTION, toutes deux MESURÉES le 21 août (MESURES.md de A4) :
  · l'appariement se fait par SIGNATURE DE RACINE, pas par taille — le
    « top-24 des plus gros sous-termes » ne voyait que des fragments des
    développements τ (un ⊕ à trois étages ≈ 13 700 nœuds) et RATAIT ⊕ ;
  · tout motif est VALIDÉ PAR RECONSTRUCTION : appliqué aux morceaux de son
    générateur il doit le rebâtir à l'identique (égalité d'assemblages O(1),
    jamais de navigation crue — loi du projet).

Scindé de `marcheur.py` le 21 août (limite des 300 lignes) : ici le minage,
là-bas les schémas et la marche.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from outils_ia.decouvertes.autonomie.congruence import (  # noqa: E402
    _enfants, _est_terme, _reconstruire,
)

#: préfixe des variables de slot — improbable dans les énoncés du dépôt
PREFIXE_SLOT = "wmarche"

#: taille minimale d'un motif (même seuil que v20 : un atome n'est pas une notion)
TAILLE_MINI = 4


class _Divergence(Exception):
    """Anti-unification impossible : divergence à une position non-terme."""


def _taille(x):
    """Nombre de nœuds de l'assemblage — descente générique."""
    return 1 + sum(_taille(e) for e in _enfants(x))


def _est_slot(x):
    return (_est_terme(x) and x.tag == "var"
            and (x.nom or "").startswith(PREFIXE_SLOT))


def _generaliser(u, v, slots):
    """Anti-unification structurelle à SLOTS PARTAGÉS : même paire divergente
    (a, b) → même slot, où qu'elle apparaisse. Indispensable ici : les
    τ-termes du dépôt RÉPÈTENT leurs arguments dans leur développement
    (cf. `congruence.contexte_commun`), si bien qu'un motif comme ⊕ porte
    chaque opérande à plusieurs positions. → template, ou lève _Divergence."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    if u == v:
        return u
    memes = (type(u) is type(v)
             and all(getattr(u, a, None) == getattr(v, a, None)
                     for a in ("tag", "nom", "lieur")))
    if memes:
        eu, ev = _enfants(u), _enfants(v)
        if len(eu) == len(ev) and eu:
            return _reconstruire(
                u, [_generaliser(a, b, slots) for a, b in zip(eu, ev)])
    if not (_est_terme(u) and _est_terme(v)):
        raise _Divergence          # une formule ne se remplace pas par une var
    cle = (u, v)
    if cle not in slots:
        slots[cle] = var("%s%d" % (PREFIXE_SLOT, len(slots) + 1))
    return slots[cle]


def _noms_slots(motif, acc=None):
    """Les noms de slots du motif, dans l'ordre de PREMIÈRE rencontre."""
    if acc is None:
        acc = []
    if _est_slot(motif):
        if motif.nom not in acc:
            acc.append(motif.nom)
        return acc
    for e in _enfants(motif):
        _noms_slots(e, acc)
    return acc


def _correspond(motif, t, liaison):
    """`t` est-il une instance du motif ? Liaison CONSISTANTE des slots."""
    if _est_slot(motif):
        if motif.nom in liaison:
            return liaison[motif.nom] == t
        liaison[motif.nom] = t
        return True
    if motif == t:
        return True
    memes = (type(motif) is type(t)
             and all(getattr(motif, a, None) == getattr(t, a, None)
                     for a in ("tag", "nom", "lieur")))
    if not memes:
        return False
    em, et = _enfants(motif), _enfants(t)
    if len(em) != len(et) or not em:
        return False
    return all(_correspond(a, b, liaison) for a, b in zip(em, et))


def _appliquer(motif, noms, args):
    """L'instance du motif aux arguments — substitution PAR LE NOYAU."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        subst_t,
    )
    t = motif
    for nom, a in zip(noms, args):
        t = subst_t(a, nom, t)
    return t


def _sous_termes(x, acc):
    """Tous les nœuds-TERMES de l'assemblage, dédupliqués (descente générique)."""
    if _est_terme(x) and x not in acc:
        acc.add(x)
    for e in _enfants(x):
        _sous_termes(e, acc)
    return acc


def miner_motifs(but, extras=(), arite=2, top=4, maxi_paire=40000):
    """Les motifs de termes répétés du but (et des formules `extras`), à
    `arite` slots, classés par gain MDL décroissant. → [{motif, noms, occ,
    gain}]. Voir la docstring de module pour les deux lois de conception."""
    sources = set()
    _sous_termes(but, sources)
    for f in extras:
        _sous_termes(f, sources)
    tailles = {s: _taille(s) for s in sources}
    sources = [s for s in sources if tailles[s] >= TAILLE_MINI]

    groupes = {}
    for s in sources:
        cle = (s.tag, s.nom, s.lieur, len(s.args))
        groupes.setdefault(cle, []).append(s)

    vus = {}
    for membres in groupes.values():
        membres.sort(key=lambda s: tailles[s])
        for i in range(1, len(membres)):
            u = membres[i]
            #   DESCENTE JUSQU'À LA RENCONTRE (2e correction mesurée, 21 août) :
            #   la signature de racine confond TOUS les τ-termes (tau/Z/1 arg),
            #   et l'appariement (i-1, 0) ratait la paire (SC(b,c), SC(PCB,PCB))
            #   aux positions 2 et 4 d'un groupe de 5. On descend donc vers le
            #   bas jusqu'à la première anti-unification COMPATIBLE — une
            #   divergence est bon marché et discrimine les opérations entre
            #   elles — avec un cap d'essais DIT ici (12, et 2 rencontres max).
            essais, rencontres = 0, 0
            for j in range(i - 1, -1, -1):
                v = membres[j]
                if u == v or tailles[u] + tailles[v] > maxi_paire:
                    continue
                if essais >= 12 or rencontres >= 2:
                    break
                essais += 1
                slots = {}
                try:
                    motif = _generaliser(u, v, slots)
                except (_Divergence, RecursionError):
                    continue
                rencontres += 1
                if len(slots) != arite or _est_slot(motif):
                    continue
                noms = _noms_slots(motif)
                #   validation par reconstruction sur le premier générateur
                pieces = {w.nom: cle[0] for cle, w in slots.items()}
                if _appliquer(motif, noms, [pieces[n] for n in noms]) != u:
                    continue
                vus.setdefault(motif, noms)
    resultat = []
    for motif, noms in vus.items():
        occ = sum(1 for s in sources if _correspond(motif, s, {}))
        gain = (occ - 1) * _taille(motif)
        if occ >= 2 and gain > 0:
            resultat.append({"motif": motif, "noms": noms,
                             "occ": occ, "gain": gain})
    resultat.sort(key=lambda d: d["gain"], reverse=True)
    return resultat[:top]


__all__ = ["PREFIXE_SLOT", "TAILLE_MINI", "miner_motifs",
           "_appliquer", "_correspond", "_generaliser", "_noms_slots",
           "_sous_termes", "_taille", "_est_slot"]
