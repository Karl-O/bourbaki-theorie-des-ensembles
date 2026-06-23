"""Ré-évaluation du guidage IA sur le prouveur GOAL-DIRECTED (terrain équitable).

Maintenant que le prouveur atteint les feuilles, on mesure si l'IA de pertinence
réduit les nœuds là où la recherche de feuille a un vrai coût : le tiers exclu
X∨¬X (~28 nœuds). Entraînement sur certains atomes, test sur d'autres (jamais
vus). Chiffres réels ; chaque preuve reste certifiée par le noyau.

  python V9/benchmark_goal_ia.py
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import disjonction, negation
from bourbaki.logique.i_1_termes_relations.propositions import A, B, C, D, E, SIG_PROP
from bourbaki.logique.i_1_termes_relations.lecture import est_relation  # noqa: F401  (cohérence d'API)
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques import antecedent_consequent
from outils_ia.chercheur import _est_implication
from outils_ia.prouveur_goal import _rels, _instances, _macros, prouver
from outils_ia.encodeur import traits_paire_seq, traits_alignement
from outils_ia.modele import RegressionLogistique


def _seeds(but, hyps, sig):
    rels = _rels(but, hyps, sig)
    return ([noyau.assume(h, sig) for h in hyps]
            + _instances(rels, sig) + _macros(hyps, rels, sig))


def _trace(but, sig, noeuds_max):
    """Saturation MP (FIFO) avec provenance, pour récolter les intermédiaires utilisés."""
    faits, prov = {}, {}
    for t in _seeds(but, (), sig):
        faits.setdefault(t.conclusion, t); prov.setdefault(t.conclusion, ())
    n, change = 0, True
    while change and n < noeuds_max:
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
                    n += 1; change = True
    return faits, prov, (but in faits)


def _used(but, prov):
    util, pile, vus = set(), [but], set()
    while pile:
        c = pile.pop()
        if c in vus or c not in prov:
            continue
        vus.add(c); util.add(c); pile.extend(prov[c])
    return util


def jeu(goals, traits, sig=SIG_PROP, noeuds_max=2000):
    X, y = [], []
    for but in goals:
        faits, prov, ok = _trace(but, sig, noeuds_max)
        if not ok:
            continue
        util = _used(but, prov)
        # ordre DÉTERMINISTE (sinon l'ordre du set fait varier le SGD → bruit)
        util_t = sorted(util, key=lambda a: (len(a.signes), a.signes))
        inutil = [c for c in faits if c not in util]    # dict : ordre d'insertion stable
        for c in util_t:
            X.append(traits(c, but)); y.append(1)
        for c in inutil[:2 * len(util_t)]:
            X.append(traits(c, but)); y.append(0)
    return X, y


def _nodes(test, score, noeuds_max):
    return sum(prouver(b, sig=SIG_PROP, noeuds_max=noeuds_max, score=score)[1] for b in test)


def lancer(traits, noeuds_max=2000):
    train = [disjonction(X, negation(X)) for X in (A, B, C)]
    test = [disjonction(X, negation(X)) for X in (D, E)]
    X, y = jeu(train, traits, noeuds_max=noeuds_max)
    m = RegressionLogistique(len(traits(A, A)))
    m.entrainer(X, y, epochs=200, lr=0.2)
    nd = _nodes(test, None, noeuds_max)                         # distance
    ni = _nodes(test, lambda c, b: -m.proba(traits(c, b)), noeuds_max)
    return nd, ni


if __name__ == "__main__":
    print("Tiers exclu X∨¬X — buts de test (D, E) jamais vus :")
    nd, ni_bg = lancer(traits_paire_seq)
    _, ni_al = lancer(traits_alignement)
    print(f"  heuristique de distance      : {nd} nœuds")
    print(f"  IA bi-grammes                : {ni_bg} nœuds  ({100*(nd-ni_bg)/nd:+.0f} %)")
    print(f"  IA alignement (riche)        : {ni_al} nœuds  ({100*(nd-ni_al)/nd:+.0f} %)")
    print("\nChaque preuve certifiée par le noyau ; chiffres réels (pas postulés).")
