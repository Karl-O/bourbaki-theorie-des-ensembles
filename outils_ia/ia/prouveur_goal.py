"""Couche 4 (refonte) — prouveur GOAL-DIRECTED (chaînage arrière).

Refonte motivée par le résultat négatif de `benchmark_ia` : le prouveur en
saturation aveugle ne couvrait pas `¬B⇒¬B`, `(A∨D)⇒(A∨D)`, … Ici on raisonne
à l'envers :

  * but de la forme R⇒S  →  **déduction** (C6) : supposer R, prouver S, décharger.
    Cela rend toute implication (et `R⇒R`) immédiate, sans générer d'instances.
  * but « feuille » (non-implication, ex. ¬X, X∨Y)  →  recherche avant guidée :
    saturation modus ponens sur le contexte + instances de schémas pertinentes,
    en meilleur-d'abord (score = distance, ou modèle IA si fourni).

Tout résultat reste un `Theoreme` du noyau. `prouver` renvoie (theoreme|None,
nombre de nœuds = modus ponens vérifiés).
"""
from __future__ import annotations
import heapq
from itertools import count

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_app_lecture import DEFAUT, est_relation
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques import antecedent_consequent
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_prop import contraposition, double_negation_intro, double_negation_elim
from outils_ia.ia.chercheur import vocabulaire, _est_implication

_CAP = 8  # nb max de relations servant à engendrer les instances de feuille


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


def _rels(but, hyps, sig):
    vocab = vocabulaire((but,) + tuple(hyps), sig)
    return sorted((r for r in vocab if est_relation(r, sig)), key=lambda a: a.n)[:_CAP]


def _instances(rels, sig):
    """Instances S1–S4 sur les relations pertinentes."""
    out = []
    for r in rels:
        out.append(noyau.s1(r, sig))
        for s in rels:
            out.append(noyau.s2(r, s, sig)); out.append(noyau.s3(r, s, sig))
            for t in rels:
                out.append(noyau.s4(r, s, t, sig))
    return out


def _macros(hyps, rels, sig):
    """Théorèmes issus des TACTIQUES prouvées, utiles aux feuilles :
    contraposée des hypothèses-implications, double négation des sous-formules."""
    out = []
    for h in hyps:
        if _est_implication(h, sig):
            try:
                out.append(contraposition(noyau.assume(h, sig), sig))  # {h} ⊢ ¬S⇒¬R
            except (ValueError, IndexError):
                pass
    for r in rels:
        try:
            out.append(double_negation_intro(r, sig))   # ⊢ R ⇒ ¬¬R
            out.append(double_negation_elim(r, sig))     # ⊢ ¬¬R ⇒ R
        except (ValueError, IndexError):
            pass
    return out


def _forward(but, hyps, sig, noeuds_max, compteur, score):
    """Saturation MP meilleur-d'abord vers `but`. Renvoie un Theoreme ou None."""
    rels = _rels(but, hyps, sig)
    seeds = ([noyau.assume(h, sig) for h in hyps]
             + _instances(rels, sig) + _macros(hyps, rels, sig))
    faits, pq, cpt = {}, [], count()

    def pousser(thm):
        s = score(thm.conclusion, but) if score else float(_dist(thm.conclusion.signes, but.signes))
        heapq.heappush(pq, (s, next(cpt), thm))

    for t in seeds:
        pousser(t)
    while pq and compteur[0] < noeuds_max:
        _, _, thm = heapq.heappop(pq)
        c = thm.conclusion
        if c in faits:
            continue
        faits[c] = thm
        if c == but:
            return thm
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
                        compteur[0] += 1
                        pousser(nv)
    return None


def prouver(but, hyps=(), profondeur_max: int = 6, noeuds_max: int = 4000,
            sig=DEFAUT, score=None):
    """Prouveur goal-directed. Renvoie (Theoreme|None, nœuds explorés)."""
    compteur = [0]

    def rec(but, hyps, prof):
        # déduction d'abord pour les implications (rend R⇒R immédiat)
        if prof > 0 and _est_implication(but, sig):
            a, b = antecedent_consequent(but, sig)
            sous = rec(b, hyps + (a,), prof - 1)
            if sous is not None:
                return noyau.loi_deduction(a, sous, sig)
        # feuille (ou repli) : recherche avant guidée
        return _forward(but, hyps, sig, noeuds_max, compteur, score)

    return rec(but, tuple(hyps), profondeur_max), compteur[0]


__all__ = ["prouver"]
