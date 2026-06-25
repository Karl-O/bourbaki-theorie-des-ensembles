"""Couche 4 (suite) — recherche guidée par des priors APPRIS, sur espace vérifié.

Analogue honnête du `cherche_appris` de V8, mais :
  * la recherche est en meilleur-d'abord sur de vrais `Theoreme` du noyau ;
  * « preuve trouvée » == « preuve vérifiée » (rien ne peut être renvoyé sans
    passer par le noyau) ;
  * la métrique « nœuds explorés » est RÉELLE (un nœud = un modus ponens
    effectivement appliqué et vérifié), pas une statistique sur des étiquettes.

Apprentissage : après chaque preuve trouvée, on remonte la provenance pour voir
quelles familles de schémas (S1–S4) ont réellement servi, et on met à jour
P(famille). Ces priors biaisent l'ordre d'exploration (meilleur-d'abord) des
preuves suivantes — donc le nombre de nœuds peut baisser. Le gain réel est
mesuré, pas postulé.
"""
from __future__ import annotations
from dataclasses import dataclass, field
import heapq
import math
from itertools import count

from bourbaki.assemblage.assemblage import Assemblage
from bourbaki.logique.i_1_termes_relations.lecture import Signature, DEFAUT
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.noyau.noyau import Theoreme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques import antecedent_consequent
from outils_ia.ia.chercheur import vocabulaire, instances_schemas, _est_implication

_FAMILLES = ("S1", "S2", "S3", "S4")
_LAMBDA = 2.0  # poids du prior dans le score (meilleur-d'abord)


@dataclass
class TableProbas:
    """P(famille de schéma utile), mise à jour bayésienne simple (Laplace)."""
    succes: dict = field(default_factory=dict)
    total: dict = field(default_factory=dict)

    def prob(self, tag: str) -> float:
        if tag not in _FAMILLES:
            return 1.0
        return (self.succes.get(tag, 0) + 1) / (self.total.get(tag, 0) + 2)

    def maj(self, tag: str, utilisee: bool) -> None:
        self.total[tag] = self.total.get(tag, 0) + 1
        if utilisee:
            self.succes[tag] = self.succes.get(tag, 0) + 1


def _distance(a: tuple, b: tuple) -> int:
    """Distance d'édition entre deux suites de signes (heuristique vers le but)."""
    n, m = len(a), len(b)
    prec = list(range(m + 1))
    for i in range(1, n + 1):
        cur = [i] + [0] * m
        for j in range(1, m + 1):
            cur[j] = min(cur[j - 1] + 1, prec[j] + 1,
                         prec[j - 1] + (0 if a[i - 1] == b[j - 1] else 1))
        prec = cur
    return prec[m]


def instances_tagge(vocab, sig: Signature = DEFAUT) -> list:
    """Comme instances_schemas, mais chaque théorème porte sa famille (tag)."""
    out = []
    for thm in instances_schemas(vocab, sig):
        out.append((thm.justification, thm))   # justification ∈ {"S1",..,"S4"}
    return out


@dataclass
class Resultat:
    theoreme: Theoreme
    provenance: dict
    noeuds: int


def prouver_appris(but: Assemblage, priors: TableProbas, hypotheses: tuple = (),
                   profondeur_max: int = 3, noeuds_max: int = 4000,
                   sig: Signature = DEFAUT) -> Resultat | None:
    """Recherche meilleur-d'abord guidée par les priors. Renvoie un Resultat ou None."""
    seeds = [("HYP", noyau.assume(h, sig)) for h in hypotheses]
    seeds += instances_tagge(vocabulaire((but,) + tuple(hypotheses), sig), sig)

    faits: dict = {}
    prov: dict = {}
    pq: list = []
    cpt = count()
    noeuds = 0
    cible = but.signes

    def score(concl: Assemblage, tag: str) -> float:
        return _distance(concl.signes, cible) - _LAMBDA * math.log(priors.prob(tag))

    def pousser(tag, thm, parents):
        heapq.heappush(pq, (score(thm.conclusion, tag), next(cpt), tag, thm, parents))

    for tag, thm in seeds:
        pousser(tag, thm, ())

    while pq and noeuds < noeuds_max:
        _, _, tag, thm, parents = heapq.heappop(pq)
        c = thm.conclusion
        if c in faits:
            continue
        faits[c] = thm
        prov[c] = (tag, parents)
        if c == but:
            return Resultat(thm, prov, noeuds)
        for autre in list(faits.values()):
            for imp, ante in ((thm, autre), (autre, thm)):
                if not _est_implication(imp.conclusion, sig):
                    continue
                a, _ = antecedent_consequent(imp.conclusion, sig)
                if a != ante.conclusion:
                    continue
                try:
                    nouveau = noyau.modus_ponens(ante, imp, sig)
                except ValueError:
                    continue
                if nouveau.conclusion not in faits:
                    noeuds += 1
                    pousser("MP", nouveau, (imp.conclusion, ante.conclusion))

    # repli : chaînage arrière sur un but en implication (via déduction)
    if profondeur_max > 0 and _est_implication(but, sig):
        a, b = antecedent_consequent(but, sig)
        sous = prouver_appris(b, priors, hypotheses + (a,),
                              profondeur_max - 1, noeuds_max, sig)
        if sous is not None:
            ded = noyau.loi_deduction(a, sous.theoreme, sig)
            return Resultat(ded, sous.provenance, sous.noeuds)
    return None


def _familles_utilisees(but: Assemblage, prov: dict) -> set:
    """Remonte la provenance depuis le but : familles de schémas réellement utilisées."""
    utilisees, pile, vus = set(), [but], set()
    while pile:
        c = pile.pop()
        if c in vus or c not in prov:
            continue
        vus.add(c)
        tag, parents = prov[c]
        if tag in _FAMILLES:
            utilisees.add(tag)
        pile.extend(parents)
    return utilisees


@dataclass
class ChercheurAppris:
    """Prouveur apprenant : mémorise des priors et les met à jour à chaque succès."""
    priors: TableProbas = field(default_factory=TableProbas)
    sig: Signature = field(default_factory=lambda: dict(DEFAUT))

    def prouver(self, but: Assemblage, hypotheses: tuple = (),
                noeuds_max: int = 4000, apprendre: bool = True) -> Resultat | None:
        res = prouver_appris(but, self.priors, hypotheses, 3, noeuds_max, self.sig)
        if res is not None and apprendre:
            utilisees = _familles_utilisees(but, res.provenance)
            for fam in _FAMILLES:                       # mise à jour de tous les priors
                self.priors.maj(fam, utilisee=(fam in utilisees))
        return res


__all__ = ["TableProbas", "ChercheurAppris", "prouver_appris", "Resultat",
           "instances_tagge"]
