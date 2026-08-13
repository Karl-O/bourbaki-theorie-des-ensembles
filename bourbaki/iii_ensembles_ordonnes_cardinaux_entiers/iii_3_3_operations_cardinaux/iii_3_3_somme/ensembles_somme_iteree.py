# -*- coding: utf-8 -*-
"""Associativité ITÉRÉE de l'addition cardinale — `(a+b)+c = a+(b+c)`.

CE QUE CE MODULE AJOUTE, ET POURQUOI IL MANQUAIT. `ensembles_somme_associe`
démontre l'associativité au niveau des sommes **disjointes** :

    Card((A ⊔ B) ⊔ C) = Card(A ⊔ (B ⊔ C))                    (Cor. de Prop. 5)

Ce n'est pas la forme itérée de l'opération. En notant `a + b := Card(a ⊔ b)`
(`somme_cardinale_binaire`), le membre gauche de l'associativité itérée est

    (a + b) + c  =  Card( Card(a ⊔ b) ⊔ c )

— avec un `Card` **de plus à l'intérieur**. Passer de l'une à l'autre exige de
remplacer un argument de la somme par un ensemble équipotent, ce que le
corollaire ne dit pas. Tant que ce chaînon manquait, l'addition cardinale
n'était pas utilisable comme une **opération** : on pouvait l'écrire, pas la
réassocier. (Anomalie relevée le 11 août 2026 ; cf. `docs/journal/ANOMALIES.md`.)

LE CHAÎNON — l'invariance de la somme par équipotence d'un argument :

    Card( Card(X) ⊔ Z ) = Card( X ⊔ Z )        `invariance_somme_gauche`
    Card( Z ⊔ Card(X) ) = Card( Z ⊔ X )        `invariance_somme_droite`

Démonstration : `Eq(Card X, X)` (symétrique de `equipotent_son_cardinal`) et
`Eq(Z, Z)` (réflexivité) donnent `Eq(Card X ⊔ Z, X ⊔ Z)` par
`eq_somme_invariant` ; la Proposition 1 (sens direct) conclut sur les cardinaux.

ASSEMBLAGE de `somme_cardinale_associative_iteree` :

    (a+b)+c = Card( Card(a⊔b) ⊔ c )
            = Card( (a⊔b) ⊔ c )        [invariance_somme_gauche]
            = Card( a ⊔ (b⊔c) )        [Cor. de Prop. 5, au dépôt]
            = Card( a ⊔ Card(b⊔c) )    [invariance_somme_droite, sens inverse]
            = a+(b+c)

⚠️ PIÈGE MESURÉ, coûteux (11 août). `equipotence_symetrique` et
`eq_somme_invariant` portent des liants de graphe **canoniques** (`F`, `G`).
Les généraliser puis instancier les α-renomme, et un modus ponens **interne**
à ces fonctions est alors refusé. Ces deux fonctions acceptent des TERMES en
argument : on les appelle **directement**, jamais via `generalisation`/
`instancie`. Les lemmes ci-dessous acceptent donc eux aussi des termes.

PORTÉE. Avec la commutativité (`ensembles_somme_commute`), le neutre
(`ensembles_somme_zero`) et cette associativité, l'addition cardinale est un
**monoïde commutatif** au sens strict du dépôt — c'est la première structure
algébrique complète disponible aux outils de recherche de preuve, qui peuvent
dès lors réassocier et commuter librement (cf. `outils_ia/decouvertes/`).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)


def _t(x):
    """Un TERME depuis un nom de variable ou un terme déjà construit."""
    return var(x) if isinstance(x, str) else x


def _gen_inst(builder, noms, termes):
    """Généralise `builder(*noms)` sur `noms`, puis instancie aux `termes`.

    Réservé aux lemmes SANS liant canonique (cf. le piège en tête de module)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        instancie,
    )
    th = builder(*noms)
    for n in noms:
        th = N.generalisation(n, th)
    for t in termes:
        th = instancie(th, t)
    return th


def _eq_son_cardinal_t(t):
    """⊢ Eq(t, Card t) pour un TERME `t`."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal,
    )
    return _gen_inst(equipotent_son_cardinal, ("Xesc",), (t,))


def _eq_reflexive_t(t):
    """⊢ Eq(t, t) pour un TERME `t`."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotence_reflexive,
    )
    return _gen_inst(equipotence_reflexive, ("Xrfl",), (t,))


def _eq_symetrique_t(u, v, th_uv):
    """De ⊢ Eq(u, v) déduit ⊢ Eq(v, u), pour des TERMES `u`, `v`.

    Appel DIRECT (liant de graphe canonique `F` préservé) — cf. le piège."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (
        equipotence_symetrique,
    )
    return N.modus_ponens(th_uv, equipotence_symetrique(f="F", x=u, y=v))


def _prop1_t(u, v, th_eq):
    """De ⊢ Eq(u, v) déduit ⊢ Card u = Card v (Prop. 1 §III.3.3, sens direct)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
        _prop1_direct_t,
    )
    return N.modus_ponens(th_eq, _prop1_direct_t(u, v))


def _invariance(X, Z, gauche=True):
    """⊢ Card( Card X ⊔ Z ) = Card( X ⊔ Z )  —  ou le symétrique si `gauche` est faux."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_disjointe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
        eq_somme_invariant,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro,
    )
    X, Z = _t(X), _t(Z)
    eqX = _eq_symetrique_t(X, cardinal(X), _eq_son_cardinal_t(X))
    eqZ = _eq_reflexive_t(Z)
    if gauche:
        A, B, A1, B1 = cardinal(X), Z, X, Z
        paire = conjonction_intro(eqX, eqZ)
    else:
        A, B, A1, B1 = Z, cardinal(X), Z, X
        paire = conjonction_intro(eqZ, eqX)
    #   liants de graphe CANONIQUES `F`/`G` : appel direct, jamais généralisé.
    g = eq_somme_invariant(f="F", g="G", a=A, b=B, a1=A1, b1=B1)
    return _prop1_t(somme_disjointe(A, B), somme_disjointe(A1, B1),
                    N.modus_ponens(paire, g))


# @livre Ch.III §3.3 Cor.- | E III.27 L.12-12 | PDF p.130
def invariance_somme_gauche(x="X", z="Z"):
    """⊢ Card( Card(X) ⊔ Z ) = Card( X ⊔ Z ).   Accepte des TERMES."""
    return _invariance(x, z, gauche=True)


# @livre Ch.III §3.3 Cor.- | E III.27 L.12-12 | PDF p.130
def invariance_somme_droite(x="X", z="Z"):
    """⊢ Card( Z ⊔ Card(X) ) = Card( Z ⊔ X ).   Accepte des TERMES."""
    return _invariance(x, z, gauche=False)


# @livre Ch.III §3.3 Cor.- | E III.27 L.12-12 | PDF p.130
def somme_cardinale_associative_iteree(a="A", b="B", c="C"):
    """⊢ (a + b) + c = a + (b + c), pour l'opération `somme_cardinale_binaire`.

    C'est-à-dire ⊢ Card( Card(a⊔b) ⊔ c ) = Card( a ⊔ Card(b⊔c) ). Accepte des
    TERMES en `a`, `b`, `c` : le lemme est ainsi réutilisable sur n'importe
    quelle instance, ce dont les outils de recherche de preuve ont besoin."""
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        composer_egalites, symetrie,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_disjointe,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_associe import (
        somme_cardinale_associative,
    )
    va, vb, vc = _t(a), _t(b), _t(c)
    gauche = invariance_somme_gauche(somme_disjointe(va, vb), vc)
    droite = invariance_somme_droite(somme_disjointe(vb, vc), va)
    assoc = somme_cardinale_associative(a=va, b=vb, c=vc)
    #   le maillon : les deux doivent parler du MÊME Card((a⊔b)⊔c)
    assert assoc.conclusion.termes[0] == gauche.conclusion.termes[1], \
        "maillon rompu : Card((a⊔b)⊔c) attendu des deux côtés"
    u, v = droite.conclusion.termes
    droite_inv = N.modus_ponens(droite, symetrie(u, v))
    return composer_egalites(composer_egalites(gauche, assoc), droite_inv)


__all__ = ["invariance_somme_gauche", "invariance_somme_droite",
           "somme_cardinale_associative_iteree"]
