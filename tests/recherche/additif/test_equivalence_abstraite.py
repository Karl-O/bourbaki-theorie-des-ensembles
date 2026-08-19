# -*- coding: utf-8 -*-
"""Tests — la forme crible et la branche facile, sans arithmétique.

Ces tests ferment l'écart signalé par l'article A3 (`article/goldbach/`, §5.3).
`crible_abstrait` et `demi_abstrait` établissaient DEUX des quatre grandes
réductions de la carte Goldbach comme dépourvues de contenu arithmétique ; la
prose en annonçait QUATRE. Ce fichier mesure les deux manquantes.

Le protocole est celui des tests voisins, et c'est lui qui porte la thèse :
rejouer la MÊME démonstration sur des prédicats sans aucun rapport entre eux.
Si elle ferme à chaque fois, elle ne parlait pas des nombres premiers."""
from __future__ import annotations

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    et,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    est_pair_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from outils_ia.conjectures.goldbach import est_premier
from recherche.additif.demi_abstrait import rencontre_sur as rencontre_sur_demi
from recherche.additif.equivalence_abstraite import (
    decomposition_abstraite, decomposition_implique_rencontre, garde,
    rencontre_des_elements, rencontre_implique_decomposition, rencontre_sur,
)

#: les trois instanciations du protocole — aucune n'a de rapport avec les autres
PRIMALITE = lambda x: est_premier(x, d="d1", q="q1")          # noqa: E731
PARITE = lambda x: est_pair_propre(x, q="qpa")                # noqa: E731


def _clos(th):
    return th.est_clos and not th.hypotheses


def _invariant():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equivalence_sur_un_predicat_totalement_opaque():
    """⊢ les DEUX sens de la forme crible, avec `S(x) := x ∈ 𝕊` opaque.

    Rien n'est supposé de `S`. Que les deux sens ferment ici signifie que la
    version concrète (`recherche/goldbach/crible.py`) n'a jamais eu besoin
    d'ouvrir la primalité — elle la transportait comme un conjoint."""
    for th in (rencontre_implique_decomposition(),
               decomposition_implique_rencontre()):
        assert _clos(th)
    _invariant()


def test_goldbach_est_une_instance_de_l_equivalence():
    """🎯 LA MÊME preuve, avec `S := est_premier`. Aucune ligne ne change.

    C'est GG19 — l'équivalence crible du dépôt — obtenue comme simple
    instanciation. « Goldbach est une instance » est une exécution."""
    for th in (rencontre_implique_decomposition(S=PRIMALITE),
               decomposition_implique_rencontre(S=PRIMALITE)):
        assert _clos(th)
    _invariant()


def test_un_predicat_sans_rapport_ferme_aussi():
    """La même preuve avec `S := être pair` — question additive triviale.

    C'est le test qui porte la thèse : une démonstration qui ne distingue pas
    les nombres premiers d'un ensemble sans structure ne peut pas servir à
    démontrer Goldbach."""
    for th in (rencontre_implique_decomposition(S=PARITE),
               decomposition_implique_rencontre(S=PARITE)):
        assert _clos(th)
    _invariant()


def test_gg22_la_branche_facile_ignore_la_primalite():
    """🎯 GG22 sur les trois prédicats — la mesure la plus nette du lot.

    Concrètement : « si `k` est premier alors `2k` se décompose ». Ici : « si
    `k` est dans `S` alors `k+k` est somme de deux éléments de `S` ». La
    primalité n'y jouait aucun rôle, seulement l'appartenance — et le
    pont d'habit α que payait la version concrète disparaît entièrement."""
    for S in (None, PRIMALITE, PARITE):
        th = rencontre_des_elements() if S is None else rencontre_des_elements(S=S)
        assert _clos(th)
    _invariant()


def test_la_rencontre_est_bien_la_meme_formule_que_dans_demi_abstrait():
    """VERROU DE COHÉRENCE. `equivalence_abstraite` redéfinit `rencontre_sur`
    pour ne pas dépendre du demi-intervalle, qui la suppose. Deux définitions
    d'une même formule est exactement la façon dont deux modules divergent
    sans que rien ne le signale — ce test l'interdit."""
    b = E.VIDE
    assert rencontre_sur(b) == rencontre_sur_demi(b)


def test_les_enonces_sont_bien_formes():
    """Garde-fou de forme, et la garde `Fini` est bien AU PREMIER RANG.

    Sans elle, `prop2_sous_fini` ne s'applique pas et le sens ⇒ n'est pas
    démontrable : c'est le défaut de fidélité de `est_premier`, évité ici par
    construction. C'est l'ORDRE des conjoints qu'on verrouille, parce que les
    `_cg`/`_cd` des preuves en dépendent.

    ⚠️ On ne teste PAS `tag == "and"` : chez Bourbaki la conjonction n'est pas
    primitive, `et(A,B)` est `¬(¬A ∨ ¬B)` et son tag vaut donc `non`. Écrire
    l'assertion naïve fait échouer un test qui a pourtant raison sur le fond —
    mesuré ici même."""
    assert decomposition_abstraite(PRIMALITE, E.VIDE).tag == "exists"
    assert rencontre_sur(E.VIDE).tag == "exists"
    assert garde(PRIMALITE, E.VIDE) == et(est_fini(E.VIDE), PRIMALITE(E.VIDE))
