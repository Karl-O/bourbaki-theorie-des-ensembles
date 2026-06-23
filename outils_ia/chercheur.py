"""Couche 4 — Recherche de démonstrations branchée sur le noyau.

C'est le chaînon manquant de V8 : ici, « preuve trouvée » == « preuve vérifiée ».
Le prouveur ne manipule QUE des `Theoreme` du noyau ; il lui est donc
*impossible* de retourner un théorème non démontré (cf. la frontière de
confiance de `noyau.py`). Contraste avec V8, où la recherche opérait sur des
étiquettes de forme et ne produisait aucune preuve vérifiable.

Moteur (fragment propositionnel + implication) :
  1. saturation par modus ponens sur un ensemble de théorèmes connus ;
  2. chaînage arrière sur les buts en implication via la loi de déduction
     (pour prouver A⇒B : supposer A, prouver B, décharger) ;
  3. matière première : instances de schémas S1–S4 engendrées depuis le
     « vocabulaire » du but (ses sous-relations, clôturées par ¬ et ∨).

Les théorèmes prouvés sont mémorisés (`base`) et réutilisés — analogue honnête,
et vérifié, de la base de chemins de V8.
"""
from __future__ import annotations
from dataclasses import dataclass, field

from bourbaki.assemblage.assemblage import Assemblage, negation, disjonction
from bourbaki.logique.i_1_termes_relations.lecture import Signature, DEFAUT, depuis_assemblage, vers_assemblage, est_relation
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.noyau.noyau import Theoreme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques import antecedent_consequent

_MAX_VOCAB = 5  # borne le nombre de relations servant à engendrer les schémas
                # (S4 est cubique : 5³ instances ; suffit pour le fragment visé)


def _est_implication(asm: Assemblage, sig: Signature) -> bool:
    try:
        a = depuis_assemblage(asm, sig)
        return a.tete == "OU" and bool(a.enfants) and a.enfants[0].tete == "NON"
    except Exception:
        return False


def _collecter_relations(arbre, acc: set) -> None:
    if arbre.sorte == "relation":
        acc.add(vers_assemblage(arbre))
    for c in arbre.enfants:
        _collecter_relations(c, acc)


def vocabulaire(assemblages, sig: Signature = DEFAUT) -> set:
    """Sous-relations de chaque assemblage, clôturées par ¬ et ∨ (profondeur 1)."""
    base: set = set()
    for a in assemblages:
        try:
            _collecter_relations(depuis_assemblage(a, sig), base)
        except Exception:
            pass
    clos = set(base)
    for r in base:
        clos.add(negation(r))
        for s in base:
            clos.add(disjonction(r, s))
    return clos


def instances_schemas(vocab, sig: Signature = DEFAUT) -> list[Theoreme]:
    """Instances closes de S1–S4 sur le vocabulaire (borné à _MAX_VOCAB relations)."""
    rels = sorted((r for r in vocab if est_relation(r, sig)), key=lambda a: a.n)[:_MAX_VOCAB]
    out: list[Theoreme] = []
    for r in rels:
        out.append(noyau.s1(r, sig))
        for s in rels:
            out.append(noyau.s2(r, s, sig))
            out.append(noyau.s3(r, s, sig))
            for t in rels:
                out.append(noyau.s4(r, s, t, sig))
    return out


def saturer_mp(theoremes, sig: Signature = DEFAUT, noeuds_max: int = 4000):
    """Clôture d'un ensemble de théorèmes sous modus ponens.

    Renvoie (faits : conclusion → Theoreme, noeuds explorés).
    """
    faits: dict = {}
    for t in theoremes:
        faits.setdefault(t.conclusion, t)
    noeuds = 0
    change = True
    while change and noeuds < noeuds_max:
        change = False
        implications = [t for t in list(faits.values())
                        if _est_implication(t.conclusion, sig)]
        for timp in implications:
            a, _ = antecedent_consequent(timp.conclusion, sig)
            if a in faits:
                try:
                    nouveau = noyau.modus_ponens(faits[a], timp, sig)
                except ValueError:
                    continue
                noeuds += 1
                if nouveau.conclusion not in faits:
                    faits[nouveau.conclusion] = nouveau
                    change = True
                if noeuds >= noeuds_max:
                    break
    return faits, noeuds


@dataclass
class Prouveur:
    """Prouveur branché sur le noyau. Tout résultat est un Theoreme vérifié."""
    sig: Signature = field(default_factory=lambda: dict(DEFAUT))
    base: dict = field(default_factory=dict)   # conclusion → Theoreme (lemmes appris)
    noeuds: int = 0

    def prouver(self, but: Assemblage, hypotheses: tuple = (),
                lemmes: tuple = (), profondeur_max: int = 4,
                noeuds_max: int = 4000, schemas: bool = True) -> Theoreme | None:
        """Cherche une démonstration de `but` (sous `hypotheses`). None si échec.

        Le théorème renvoyé a ses hypothèses incluses dans `hypotheses` ; au
        niveau supérieur (hypotheses == ()), c'est donc un théorème clos.
        """
        materiel: list[Theoreme] = [noyau.assume(h, self.sig) for h in hypotheses]
        materiel += list(lemmes) + list(self.base.values())
        if schemas:
            vocab = vocabulaire((but,) + tuple(hypotheses), self.sig)
            materiel += instances_schemas(vocab, self.sig)

        faits, n = saturer_mp(materiel, self.sig, noeuds_max)
        self.noeuds += n
        if but in faits:
            return self._memoriser(faits[but])

        if profondeur_max > 0 and _est_implication(but, self.sig):
            a, b = antecedent_consequent(but, self.sig)
            sous = self.prouver(b, hypotheses + (a,), lemmes,
                                profondeur_max - 1, noeuds_max, schemas)
            if sous is not None:
                return self._memoriser(noyau.loi_deduction(a, sous, self.sig))
        return None

    def _memoriser(self, thm: Theoreme) -> Theoreme:
        if thm.est_clos:
            self.base.setdefault(thm.conclusion, thm)
        return thm


__all__ = ["Prouveur", "saturer_mp", "vocabulaire", "instances_schemas"]
