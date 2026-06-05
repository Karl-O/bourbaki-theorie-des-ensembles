"""Couche 5 (bis) — encodage des VALEURS PURES (assemblages) pour une IA numérique.

Deuxième tête, complémentaire du LLM : ici l'IA ne voit PAS de notation lisible,
elle opère directement sur la valeur pure — la matrice (signes, liens) de
l'assemblage. Ce module en extrait un vecteur de traits numériques, entrée d'une
politique/valeur apprenable (régression, réseau, GNN sur les liens…).

L'apprentissage se fera sur des *traces vérifiées* : la recherche (chercheur)
produit des couples (état, action, succès) où chaque état est un Theoreme réel ;
le modèle apprend à scorer ces valeurs pures. Le noyau reste le garde-fou : le
modèle ne fait que classer des coups, il ne peut jamais fabriquer un faux.

`encoder` est déterministe et testable sans aucun entraînement (brique d'entrée).
"""
from __future__ import annotations

from collections import Counter

from bourbaki.assemblage.assemblage import Assemblage, est_lettre
from bourbaki.logique.lecture import Signature, DEFAUT, depuis_assemblage, vers_assemblage

# Ordre figé des traits (un changement d'ordre changerait l'entrée du modèle).
TRAITS = (
    "longueur", "nb_liens", "nb_OU", "nb_NON", "nb_TAU", "nb_CARRE",
    "nb_egal", "nb_lettres", "nb_lettres_distinctes", "profondeur", "est_relation",
    "impl_reflexive", "repetition_max",
)


def _profondeur(arbre) -> int:
    if not arbre.enfants:
        return 1
    return 1 + max(_profondeur(c) for c in arbre.enfants)


def _sous_relations(arbre, acc: list) -> None:
    if arbre.sorte == "relation":
        acc.append(vers_assemblage(arbre))
    for c in arbre.enfants:
        _sous_relations(c, acc)


def encoder(asm: Assemblage, sig: Signature = DEFAUT) -> list[float]:
    """Vecteur de traits numériques tiré de la valeur pure (signes, liens).

    Aucune notation lisible n'intervient : on lit directement la matrice.
    """
    signes = asm.signes
    lettres = [s for s in signes if est_lettre(s)]
    prof, est_rel, impl_refl, rep_max = 0, 0, 0, 1
    try:
        arbre = depuis_assemblage(asm, sig)
        prof = _profondeur(arbre)
        est_rel = 1 if arbre.sorte == "relation" else 0
        # implication A⇒B (= OU ¬A B) dont l'antécédent égale le conséquent
        if arbre.tete == "OU" and arbre.enfants[0].tete == "NON":
            if vers_assemblage(arbre.enfants[0].enfants[0]) == vers_assemblage(arbre.enfants[1]):
                impl_refl = 1
        # sous-relation la plus répétée (capte A∨A, A⇒A, …)
        sous: list = []
        _sous_relations(arbre, sous)
        if sous:
            rep_max = max(Counter(sous).values())
    except Exception:
        pass
    return [
        float(len(signes)),
        float(len(asm.liens)),
        float(signes.count("OU")),
        float(signes.count("NON")),
        float(signes.count("TAU")),
        float(signes.count("CARRE")),
        float(signes.count("=")),
        float(len(lettres)),
        float(len(set(lettres))),
        float(prof),
        float(est_rel),
        float(impl_refl),
        float(rep_max),
    ]


def _distance_signes(a: tuple, b: tuple) -> int:
    n, m = len(a), len(b)
    prec = list(range(m + 1))
    for i in range(1, n + 1):
        cur = [i] + [0] * m
        for j in range(1, m + 1):
            cur[j] = min(cur[j - 1] + 1, prec[j] + 1,
                         prec[j - 1] + (0 if a[i - 1] == b[j - 1] else 1))
        prec = cur
    return prec[m]


# ── Encodage SÉQUENTIEL de la valeur pure (fidèle, invariant par renommage) ───
#
# Au lieu d'agréger en comptes (qui perdent position/identité), on lit la suite
# de signes elle-même. Les lettres LIBRES sont canonicalisées par ordre de
# première apparition (a,b,c → L0,L1,L2…), de sorte que (a=b)⇒(a=b) et
# (c=d)⇒(c=d) aient le MÊME encodage (invariance par renommage), tandis que
# (a=b)⇒(a=b) et (a=b)⇒(b=c) diffèrent — sans aucun trait fabriqué à la main.

_STRUCT = ("OU", "NON", "TAU", "CARRE", "=")
_VOCAB = _STRUCT + tuple(f"L{k}" for k in range(5)) + ("L+",) \
    + tuple(f"S{k}" for k in range(5)) + ("S+",)
_IDX = {v: i for i, v in enumerate(_VOCAB)}


def _sequence_canonique(asm: Assemblage) -> list[str]:
    """Suite de signes canonique : lettres libres → L0,L1,… ; signes spécifiques
    (atomes propositionnels, ∈, …) → S0,S1,… (chacun par 1ʳᵉ apparition).

    Invariant par renommage des lettres ET des atomes : (PA⇒PA) et (PB⇒PB) ont
    la même séquence, mais (PA⇒PA) et (PA⇒PB) diffèrent.
    """
    canon, lettres, signes = [], {}, {}
    for s in asm.signes:
        if est_lettre(s):
            k = lettres.setdefault(s, len(lettres))
            canon.append(f"L{k}" if k < 5 else "L+")
        elif s in _STRUCT:
            canon.append(s)
        else:
            k = signes.setdefault(s, len(signes))
            canon.append(f"S{k}" if k < 5 else "S+")
    return canon


def encoder_sequence(asm: Assemblage) -> list[float]:
    """Sac d'unigrammes + bigrammes sur la séquence canonique des signes.

    Lit la valeur pure sans la réduire à des comptes globaux : capte l'ordre et
    les répétitions (donc distingue A⇒A de A⇒B nativement), invariant par
    renommage des lettres libres.
    """
    canon = _sequence_canonique(asm)
    n = len(_VOCAB)
    uni = [0] * n
    bi = [0] * (n * n)
    for s in canon:
        uni[_IDX[s]] += 1
    for a, b in zip(canon, canon[1:]):
        bi[_IDX[a] * n + _IDX[b]] += 1
    return [float(x) for x in uni + bi]


def traits_paire(etat: Assemblage, but: Assemblage,
                 sig: Signature = DEFAUT) -> list[float]:
    """Traits d'un couple (état courant, but) : entrée typique d'une politique.

    = encoder(état) ++ encoder(but) ++ [distance d'édition des signes].
    """
    return (encoder(etat, sig) + encoder(but, sig)
            + [float(_distance_signes(etat.signes, but.signes))])


def traits_paire_seq(etat: Assemblage, but: Assemblage) -> list[float]:
    """Traits d'un couple (intermédiaire, but) pour un modèle de PERTINENCE :
    concat des encodages séquentiels. Entrée d'une politique de recherche."""
    return encoder_sequence(etat) + encoder_sequence(but)


def _sous_formules_canon(asm: Assemblage, sig: Signature = DEFAUT) -> set:
    """Ensemble des sous-relations, chacune en forme canonique (invariante par
    renommage) : permet de comparer l'alignement structurel entre deux assemblages."""
    acc: set = set()
    try:
        arbre = depuis_assemblage(asm, sig)
    except Exception:
        return acc

    def walk(n):
        if n.sorte == "relation":
            acc.add(tuple(_sequence_canonique(vers_assemblage(n))))
        for c in n.enfants:
            walk(c)

    walk(arbre)
    return acc


def traits_alignement(etat: Assemblage, but: Assemblage,
                      sig: Signature = DEFAUT) -> list[float]:
    """Traits d'ALIGNEMENT (intermédiaire, but) — ce qui manquait aux bi-grammes.

    Inclut la distance d'édition (le baseline) + des mesures de structure
    partagée : sous-formules communes, containment, recouvrement de bi-grammes.
    Le modèle peut donc au minimum égaler la distance, et l'améliorer.
    """
    d = float(_distance_signes(etat.signes, but.signes))
    Se, Sb = _sous_formules_canon(etat, sig), _sous_formules_canon(but, sig)
    inter = len(Se & Sb)
    union = len(Se | Sb) or 1
    ce, cb = _sequence_canonique(etat), _sequence_canonique(but)
    bge = set(zip(ce, ce[1:]))
    bgb = set(zip(cb, cb[1:]))
    bg_union = len(bge | bgb) or 1
    return [
        d,
        float(len(etat.signes)), float(len(but.signes)),
        float(abs(len(etat.signes) - len(but.signes))),
        float(len(Se)), float(len(Sb)), float(inter), inter / union,
        1.0 if tuple(ce) in Sb else 0.0,      # l'état est une sous-formule du but
        1.0 if tuple(cb) in Se else 0.0,      # le but est une sous-formule de l'état
        len(bge & bgb) / bg_union,            # recouvrement de bi-grammes (Jaccard)
    ]


__all__ = ["TRAITS", "encoder", "encoder_sequence",
           "traits_paire", "traits_paire_seq", "traits_alignement"]
