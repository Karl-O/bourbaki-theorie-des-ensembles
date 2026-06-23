"""Couche 5 (bis) — recherche guidée par l'IA de pertinence, branchée sur le noyau.

On ferme la boucle : l'IA sur valeurs pures guide la recherche, le noyau certifie.

1. TRACES : on prouve des buts par saturation modus ponens (en gardant la
   provenance). Pour chaque preuve trouvée, les intermédiaires RÉELLEMENT
   utilisés sont des exemples positifs « (intermédiaire, but) pertinent » ; un
   échantillon d'intermédiaires inutilisés donne les négatifs.
2. MODÈLE : une régression logistique sur `traits_paire_seq` apprend la
   pertinence.
3. RECHERCHE : meilleur-d'abord où l'on active en priorité les faits jugés
   pertinents par l'IA. On MESURE les nœuds (modus ponens vérifiés) vs une
   heuristique de distance.

Tout résultat reste un `Theoreme` du noyau.
"""
from __future__ import annotations
import heapq
from itertools import count

from bourbaki.assemblage.assemblage import Assemblage
from bourbaki.logique.i_1_termes_relations.propositions import SIG_PROP, A, B, C, D
from bourbaki.logique.i_1_termes_relations.lecture import est_relation
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques import antecedent_consequent
from outils_ia.chercheur import vocabulaire, instances_schemas, _est_implication
from outils_ia.encodeur import traits_paire_seq, encoder_sequence, _sequence_canonique
from outils_ia.modele import RegressionLogistique


def _dist(a: tuple, b: tuple) -> int:
    n, m = len(a), len(b)
    prec = list(range(m + 1))
    for i in range(1, n + 1):
        cur = [i] + [0] * m
        for j in range(1, m + 1):
            cur[j] = min(cur[j - 1] + 1, prec[j] + 1,
                         prec[j - 1] + (0 if a[i - 1] == b[j - 1] else 1))
        prec = cur
    return prec[m]


def _saturer_trace(but, sig, noeuds_max):
    """Saturation MP avec provenance. Renvoie (faits, prov, trouve)."""
    seeds = instances_schemas(vocabulaire((but,), sig), sig)
    faits, prov = {}, {}
    for t in seeds:
        faits.setdefault(t.conclusion, t)
        prov.setdefault(t.conclusion, ())
    noeuds, change = 0, True
    while change and noeuds < noeuds_max:
        change = False
        for timp in [t for t in list(faits.values()) if _est_implication(t.conclusion, sig)]:
            a, _ = antecedent_consequent(timp.conclusion, sig)
            if a in faits:
                try:
                    nv = noyau.modus_ponens(faits[a], timp, sig)
                except ValueError:
                    continue
                if nv.conclusion not in faits:
                    faits[nv.conclusion] = nv
                    prov[nv.conclusion] = (timp.conclusion, a)
                    noeuds += 1
                    change = True
    return faits, prov, (but in faits)


def _utilises(but, prov):
    util, pile, vus = set(), [but], set()
    while pile:
        c = pile.pop()
        if c in vus or c not in prov:
            continue
        vus.add(c)
        util.add(c)
        pile.extend(prov[c])
    return util


def jeu_relevance(buts, sig=SIG_PROP, noeuds_max=2000):
    """Construit (X, y) de pertinence depuis les traces de preuves vérifiées."""
    X, y = [], []
    for but in buts:
        faits, prov, trouve = _saturer_trace(but, sig, noeuds_max)
        if not trouve:
            continue
        util = _utilises(but, prov)
        inutil = [c for c in faits if c not in util]
        for c in util:
            X.append(traits_paire_seq(c, but)); y.append(1)
        for c in inutil[:len(util) * 2]:          # négatifs ~2× les positifs
            X.append(traits_paire_seq(c, but)); y.append(0)
    return X, y


def prouver_guide(but, sig=SIG_PROP, modele=None, noeuds_max=2000):
    """Meilleur-d'abord. Si `modele` fourni : priorité = pertinence IA ; sinon distance.

    Renvoie (theoreme | None, noeuds explorés).
    """
    seeds = instances_schemas(vocabulaire((but,), sig), sig)
    faits, pq, cpt, noeuds = {}, [], count(), 0
    cible = but.signes

    def score(concl):
        if modele is not None:
            return -modele.proba(traits_paire_seq(concl, but))   # + pertinent → tôt
        return float(_dist(concl.signes, cible))

    def pousser(thm):
        heapq.heappush(pq, (score(thm.conclusion), next(cpt), thm))

    for t in seeds:
        pousser(t)
    while pq and noeuds < noeuds_max:
        _, _, thm = heapq.heappop(pq)
        c = thm.conclusion
        if c in faits:
            continue
        faits[c] = thm
        if c == but:
            return thm, noeuds
        for autre in list(faits.values()):
            for imp, ante in ((thm, autre), (autre, thm)):
                if not _est_implication(imp.conclusion, sig):
                    continue
                a, _ = antecedent_consequent(imp.conclusion, sig)
                if a == ante.conclusion:
                    try:
                        nv = noyau.modus_ponens(ante, imp, sig)
                    except ValueError:
                        continue
                    if nv.conclusion not in faits:
                        noeuds += 1
                        pousser(nv)
    return None, noeuds


__all__ = ["jeu_relevance", "prouver_guide", "_saturer_trace"]
