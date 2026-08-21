# -*- coding: utf-8 -*-
"""LE MARCHEUR — une marche sur les états de dérivation, le noyau en garde-fou
(21 août 2026, chantier A4).

LA PORTE QU'IL FRANCHIT (plan éditorial, 10 août) : fermer au moins un but que
le chaînage seul ne ferme pas. Mesuré le 21 août sur le banc ⊕ de v16-v18
(`a ⊕ b := (a+b)+1`, pool = les deux lois brutes sur `+`) :

  · but B4 = ((a⊕b)⊕c)⊕d = a⊕(b⊕(c⊕d)) en chaînage direct : ÉCHEC en 692 s
    (budget épuisé — la chaîne brute dépasse `max_pas=5`, borne mesurée v18) ;
  · le lemme ⊕-assoc certifié à part : 4-7 s ; B4 avec ce lemme SEUL au
    pool : FERMÉ en 73 s (contre 962 s si l'on AJOUTE le lemme aux lois
    brutes — la compression est un REMPLACEMENT, pas un ajout, facteur 13).

UN PAS DE MARCHE (état = but + pool de faits certifiés) :
  1. MINER le but lui-même : les motifs de termes répétés, par
     anti-unification à slots partagés, classés par gain MDL
     (occurrences−1)×taille — le critère de v20, transposé des formules
     aux termes. Le motif ⊕ SORT DU BUT : personne ne le nomme.
  2. CONJECTURER : instancier sur chaque motif binaire les schémas de lois
     (commutativité, associativité, idempotence — liste OUVERTE).
  3. RÉFUTER à bas prix : `oracle_num.contre_exemple` sur petits entiers.
     Une conjecture fausse meurt en millisecondes, jamais en minutes de noyau.
  4. CERTIFIER : `besoins(conjecture, pool)` — le noyau juge. Une conjecture
     certifiée devient un fait : c'est le pas de COMPRESSION.
  5. RE-ESSAYER le but sur le pool COMPRIMÉ (les lemmes dérivés seuls).
     Rien de nouveau → s'arrêter et rendre les manques terminaux : le
     marcheur, comme l'organe de besoin, échoue en nommant.

PRINCIPE DE SÛRETÉ INCHANGÉ (ev.374) : le marcheur SUGGÈRE, le noyau JUGE.
Un mauvais pas coûte une route morte, jamais un faux théorème. Aucun
`Theoreme` n'est construit ici : tout sort de `besoins`, donc du noyau.

⚠️ DETTE DE RANGEMENT, signalée et non masquée : `autonomie/` compte déjà 11
entrées pour une convention à 10. Ce fichier y va parce que c'est sa place
sémantique (il orchestre `besoin`, `reecriture`, `congruence`) ; l'éclatement
du dossier (un sous-paquet `euclide/`) est une dette antérieure à lui.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_CORPUS = _V9 / "outils_ia" / "corpus"
if str(_CORPUS) not in sys.path:
    sys.path.insert(0, str(_CORPUS))

from outils_ia.decouvertes.autonomie.congruence import (  # noqa: E402
    _enfants, _est_formule, _est_terme, _reconstruire,
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
    gain}].

    APPARIEMENT PAR SIGNATURE DE RACINE, pas par taille. Première version
    mesurée (21 août) : le « top-24 des plus gros sous-termes » ne retenait
    que des fragments de développements τ (un ⊕ à trois étages fait ~13 700
    nœuds) et les petites instances ⊕(a, b) — celles qui portent le motif —
    n'y entraient jamais. On groupe donc par (tag, nom, lieur, arité) et l'on
    anti-unifie chaque terme avec ses VOISINS DE TAILLE dans son groupe :
    O(n) paires au lieu de O(n²), et les instances d'une même opération se
    rencontrent forcément. Les occurrences, elles, se comptent sur TOUTES
    les sources.

    Le motif est VALIDÉ par reconstruction : appliqué aux morceaux de son
    générateur, il doit le REBÂTIR à l'identique (jamais de navigation crue —
    loi du projet). Un motif qui ne reconstruit pas est jeté."""
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
            for j in (i - 1, 0):
                u, v = membres[i], membres[j]
                if u == v or tailles[u] + tailles[v] > maxi_paire:
                    continue
                slots = {}
                try:
                    motif = _generaliser(u, v, slots)
                except (_Divergence, RecursionError):
                    continue
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


#: schémas de lois essayés sur un motif BINAIRE — liste OUVERTE (règle
#: STYLE_ARTICLES §8) : rien ne prouve qu'il n'en faudra pas d'autres.
def conjectures_pour(motif, noms):
    """→ [(nom_schema, conjecture, noms_des_variables_libres)]."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, var,
    )
    if len(noms) != 2:
        return []
    x, y, z = var("xmarche"), var("ymarche"), var("zmarche")

    def F(u, v):
        return _appliquer(motif, noms, [u, v])

    return [
        ("commutativite", egal(F(x, y), F(y, x)), ["xmarche", "ymarche"]),
        ("associativite", egal(F(F(x, y), z), F(x, F(y, z))),
         ["xmarche", "ymarche", "zmarche"]),
        ("idempotence", egal(F(x, x), x), ["xmarche"]),
    ]


def marcher(but, faits_bruts, impls=(), rondes=3, profondeur=4,
            borne_oracle=8, trace=None):
    """La marche complète. → (Theoreme_ou_None, journal).

    Le journal est la DONNÉE du marcheur : chaque motif miné, chaque
    conjecture réfutée (et par quelle affectation), chaque lemme certifié,
    chaque re-essai — l'échec final rend les manques terminaux.

    ⚠️ Le re-essai se fait sur le pool COMPRIMÉ (les lemmes dérivés SEULS) :
    mesuré le 21 août, B4 ferme en 73 s ainsi contre 962 s sur pool cumulé.
    L'essai sur pool cumulé n'est PAS fait ici — dit dans le journal, jamais
    en silence."""
    from outils_ia.arithmetique.oracle_num import contre_exemple
    from outils_ia.decouvertes.besoin import besoins

    journal = []
    note = journal.append
    derives = {}
    tentees = set()
    extras = []
    for ronde in range(1, rondes + 1):
        motifs = miner_motifs(but, extras=extras)
        note({"type": "motifs", "ronde": ronde,
              "gains": [(m["occ"], m["gain"]) for m in motifs]})
        nouveaux = 0
        for m in motifs:
            for schema, conj, libres in conjectures_pour(m["motif"], m["noms"]):
                if conj in faits_bruts or conj in derives or conj in tentees:
                    continue
                tentees.add(conj)
                aff = contre_exemple(conj, libres, borne_oracle)
                if aff is not None:
                    note({"type": "réfuté", "schema": schema, "par": aff})
                    continue
                pool = dict(faits_bruts)
                pool.update(derives)
                th, _ = besoins(conj, list(impls), pool, profondeur=profondeur)
                if th is not None and th.est_clos and th.conclusion == conj:
                    derives[conj] = ("marche:" + schema, th)
                    nouveaux += 1
                    note({"type": "certifié", "schema": schema})
                else:
                    note({"type": "non-certifié", "schema": schema})
        if derives:
            th, manques = besoins(but, list(impls), dict(derives),
                                  profondeur=profondeur)
            if th is not None and th.est_clos and th.conclusion == but:
                note({"type": "FERMÉ", "ronde": ronde,
                      "pool": "comprimé (%d lemmes)" % len(derives)})
                if trace:
                    trace(journal)
                return th, journal
            note({"type": "ouvert", "ronde": ronde, "manques": len(manques)})
            extras = [d["manque"] for d in manques
                      if d.get("manque") is not None]
        if nouveaux == 0:
            break
    note({"type": "terminal",
          "non-essayé": "pool cumulé (brut+dérivés) — coût mesuré 962 s sur B4"})
    if trace:
        trace(journal)
    return None, journal


__all__ = ["miner_motifs", "conjectures_pour", "marcher"]
