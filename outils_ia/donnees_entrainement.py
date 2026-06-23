"""Couche 5 (bis) — jeu de données pour « ta propre IA », sur ATOMES propositionnels.

Représentation propre (cf. propositions.py) : A⇒A est ∨¬AA, A⇒B est ∨¬AB.
Étiquettes garanties par le noyau, pas devinées :
  * positifs (théorème) : instances S1–S4 + clôture par modus ponens, sur les
    atomes — chacun est un `Theoreme` vérifié ;
  * négatifs (non-théorème) : la NÉGATION de chaque théorème (non-théorème par
    cohérence), plus les atomes seuls et des implications entre atomes distincts.
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import negation, implication, disjonction
from bourbaki.logique.i_1_termes_relations.propositions import SIG_PROP, A, B, C, D
from outils_ia.chercheur import vocabulaire, instances_schemas, saturer_mp
from outils_ia.encodeur import encoder
from bourbaki.logique.i_2_criteres_C.tactiques import tactiques as _T
from bourbaki.logique.i_2_criteres_C.tactiques import tactiques_prop as _P
from bourbaki.logique.i_4_egalitaires.tactiques_egalite import reflexivite, symetrie, transitivite

_ATOMES = [A, B, C]          # atomes propositionnels (∨¬AA, …)


def theoremes_du_livre(sig=SIG_PROP) -> list:
    """Théorèmes réellement DÉMONTRÉS (du livre), tous clos et vérifiés par le noyau.

    Ajoute de la diversité : tautologies propositionnelles + propriétés de
    l'égalité (Th1–3), au-delà des seules instances de schémas engendrées.
    """
    ths = []
    for X in (A, B, C, D):
        ths += [_T.a_implique_a(X, sig),
                _P.double_negation_intro(X, sig),
                _P.double_negation_elim(X, sig),
                _P.equivalence_reflexive(X, sig)]
    for X in (A, B, C):
        for Y in (A, B, C):
            ths += [_P.projection_gauche(X, Y, sig), _P.projection_droite(X, Y, sig)]
    ths += [reflexivite("x", sig), symetrie("x", "y", sig),
            transitivite("x", "y", "z", sig)]            # égalité : =, lettres
    return [t.conclusion for t in ths if t.est_clos]


def theoremes_verifies(sig=SIG_PROP, noeuds_max: int = 3000, livre: bool = True) -> list:
    """Théorèmes : instances S1–S4 + clôture MP, plus (si `livre`) ceux démontrés."""
    vocab = vocabulaire(_ATOMES, sig)
    seeds = instances_schemas(vocab, sig)
    faits, _ = saturer_mp(seeds, sig, noeuds_max)
    engendres = list(faits.keys())
    if livre:
        vus = set(engendres)
        engendres += [t for t in theoremes_du_livre(sig) if t not in vus]
    return engendres


def non_theoremes(theoremes: list, sig=SIG_PROP) -> list:
    """Non-théorèmes : négations de théorèmes + atomes + implications fausses."""
    negs = [negation(t) for t in theoremes]          # ¬(théorème) : jamais théorème
    negs += list(_ATOMES)                              # un atome seul n'est pas un théorème
    negs += [implication(A, B), implication(B, C), disjonction(A, B)]
    return negs


def jeu_de_donnees(sig=SIG_PROP, noeuds_max: int = 3000, enc=None):
    """Renvoie (X, y, positifs, negatifs). `enc` : assemblage→vecteur (défaut: comptes)."""
    enc = enc or (lambda a: encoder(a, sig))
    pos = theoremes_verifies(sig, noeuds_max)
    neg = non_theoremes(pos, sig)
    pos_set = set(pos)
    neg = [n for n in neg if n not in pos_set]
    X = [enc(a) for a in pos] + [enc(a) for a in neg]
    y = [1] * len(pos) + [0] * len(neg)
    return X, y, pos, neg


__all__ = ["theoremes_verifies", "non_theoremes", "jeu_de_donnees"]
