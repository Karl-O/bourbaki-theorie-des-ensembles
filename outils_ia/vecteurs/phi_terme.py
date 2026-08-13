"""N1 — le vecteur structurel φ(t) ∈ ℝ^d par Weisfeiler-Leman.

────────────────────────────────────────────────────────────────────────────────
L'ÉQUATION (spec : `outils_ia/ameliorations/VECTORISATION.md` §1)

    ℓ⁰(v)   = (type(v), tag(v), nom(v), lieur(v))        identité locale du nœud
    ℓᵏ⁺¹(v) = ( ℓᵏ(v), multiensemble{ ℓᵏ(c) : c enfant de v } )
    φ(t)    = normalisé( Σ_{k≤K} Σ_v  e_hash(k, ℓᵏ(v)) mod d )
    sim(t,u)= ⟨φ(t), φ(u)⟩                                        (cosinus)

Chaque nœud résume son voisinage de rayon k ; l'histogramme haché de ces résumés
EST le vecteur.  Déterministe, sans entraînement, sans apprentissage.

────────────────────────────────────────────────────────────────────────────────
TROIS INTERDITS, chacun payé une fois pendant le prototype du 31 juillet 2026 —
les enfreindre ne fait pas échouer le calcul, il le rend FAUX SILENCIEUSEMENT.

1. **L'étiquette porte `tag` ET `nom`.**  Avec l'un ou l'autre seulement, tous les
   termes `app` se confondent et des formules distinctes mesurent cos = 1,0000.
2. **Les enfants d'un `Terme` vivent dans `.args`**, pas dans `.termes` (qui est
   vide pour un terme).  Un marcheur qui l'ignore s'arrête au premier niveau et
   rend toutes les formules indistinguables.
3. **On MARCHE l'arbre, on ne l'IMPRIME pas.**  Aucun `repr()` sur un nœud : le
   dépliage τ d'un seul cardinal vaut 4,5·10¹² signes.  Seules des chaînes déjà
   extraites (tag, nom, lieur) entrent dans le hachage.

La leçon générale, elle, vaut pour toute feature map : **valider sur des paires
dont la similarité est CONNUE d'avance** (cf. `tests/outils_ia/vecteurs/`).

────────────────────────────────────────────────────────────────────────────────
GARDE ANTI-τ.  Le corpus contient des termes cardinaux dont l'arbre DÉPLIÉ est
astronomique alors que l'arbre abrégé est petit (les sous-arbres sont partagés).
On compte donc les occurrences avec un BUDGET : dépassé, on lève plutôt que de
rendre un vecteur calculé sur un arbre tronqué en silence.

DÉTERMINISME.  Le hachage est `blake2b`, pas `hash()` : celui-ci est randomisé
par processus (PYTHONHASHSEED) et rendrait les cosinus non reproductibles d'un
run à l'autre — inacceptable pour un chiffre publié.
"""
from __future__ import annotations

import hashlib
import math

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Formule, Terme,
)

#: profondeur WL et dimension du hachage — les valeurs publiées.
K_DEFAUT = 3
D_DEFAUT = 512
#: garde anti-τ : nombre maximal d'occurrences de nœuds explorées.
BUDGET_NOEUDS = 400_000


class BudgetDepasse(ValueError):
    """L'arbre déplié dépasse le budget — typiquement un τ cardinal."""


def enfants(n):
    """Les enfants d'un nœud. ⚠️ `.args` pour un Terme, `.sous`+`.termes` pour
    une Formule — c'est l'interdit n°2 de l'en-tête."""
    if isinstance(n, Formule):
        return tuple(n.sous) + tuple(n.termes)
    if isinstance(n, Terme):
        return tuple(n.args)
    raise TypeError(f"nœud inattendu : {type(n).__name__}")


def etiquette0(n):
    """ℓ⁰(v) — l'identité locale. Porte tag ET nom (interdit n°1)."""
    if isinstance(n, Formule):
        return ("F", n.tag, "", n.lieur or "")
    return ("T", n.tag, n.nom or "", n.lieur or "")


def _hache(*morceaux) -> int:
    """blake2b sur des CHAÎNES déjà extraites — jamais sur un nœud (interdit n°3)."""
    m = hashlib.blake2b(digest_size=8)
    for p in morceaux:
        m.update(str(p).encode("utf-8"))
        m.update(b"\x1f")
    return int.from_bytes(m.digest(), "big")


def _topologie(racine, budget):
    """(ordre enfants-avant-parents sur les nœuds UNIQUES, occurrences dépliées).

    Les sous-arbres sont partagés : on mémorise les étiquettes par nœud unique
    (elles ne dépendent que du sous-arbre) mais on compte les OCCURRENCES dans
    l'arbre déplié, car c'est un histogramme."""
    occ = {}
    pile = [racine]
    vus = 0
    while pile:
        n = pile.pop()
        vus += 1
        if vus > budget:
            raise BudgetDepasse(
                f"arbre déplié > {budget} nœuds — garde anti-τ (cardinal ?)")
        occ[n] = occ.get(n, 0) + 1
        pile.extend(enfants(n))

    ordre, vu, pile = [], set(), [(racine, False)]
    while pile:
        n, traite = pile.pop()
        if traite:
            ordre.append(n)
            continue
        if n in vu:
            continue
        vu.add(n)
        pile.append((n, True))
        for c in enfants(n):
            pile.append((c, False))
    return ordre, occ


def phi(objet, K=K_DEFAUT, d=D_DEFAUT, budget=BUDGET_NOEUDS):
    """φ(objet) ∈ ℝ^d, normalisé — le vecteur structurel de l'en-tête."""
    ordre, occ = _topologie(objet, budget)
    lab = {n: _hache(*etiquette0(n)) for n in ordre}
    v = [0.0] * d
    for n in ordre:
        v[lab[n] % d] += occ[n]
    for k in range(1, K + 1):
        suivant = {}
        for n in ordre:                       # enfants avant parents : lab est prêt
            voisins = sorted(lab[c] for c in enfants(n))
            suivant[n] = _hache(k, lab[n], *voisins)
        lab = suivant
        for n in ordre:
            v[_hache(k, lab[n]) % d] += occ[n]
    norme = math.sqrt(sum(x * x for x in v))
    return [x / norme for x in v] if norme else v


def sim(a, b, **kw):
    """Cosinus de deux objets (formules ou termes). Dans [0,1] en pratique : les
    composantes sont des comptes, donc positives."""
    u, w = (a if isinstance(a, list) else phi(a, **kw),
            b if isinstance(b, list) else phi(b, **kw))
    return sum(x * y for x, y in zip(u, w))


def taille(objet, budget=BUDGET_NOEUDS):
    """Nombre de nœuds de l'arbre déplié — utile pour lire un cosinus (deux
    formules de tailles très différentes ne peuvent pas être proches)."""
    _, occ = _topologie(objet, budget)
    return sum(occ.values())


__all__ = ["phi", "sim", "taille", "enfants", "etiquette0", "BudgetDepasse",
           "K_DEFAUT", "D_DEFAUT", "BUDGET_NOEUDS"]
