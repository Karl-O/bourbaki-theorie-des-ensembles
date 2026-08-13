# -*- coding: utf-8 -*-
"""L'ORACLE NUMÉRIQUE — calculer AVANT de démontrer.

POURQUOI CET ORGANE. Le système ne calcule jamais pour se guider : il démontre,
ou il échoue. Or le résultat le plus rentable de toute la campagne Goldbach,
rapporté à son coût, fut une MESURE et non une preuve — le critère des tiroirs
`2·π(2k) > 2k+1` tué en quelques secondes par un crible d'Ératosthène en Python
pur, là où aucune tentative de démonstration n'aurait donné l'information.

Cet oracle systématise ce geste : **tester une formule sur des petits entiers
avant de dépenser une heure de noyau dessus.**

⚠️ IL NE DÉMONTRE RIEN, ET NE DOIT JAMAIS ÊTRE CRU SUR LE POSITIF. Aucun
`Theoreme` ne sort d'ici. « Aucun contre-exemple jusqu'à 200 » ne vaut pas
« vrai » — c'est exactement l'erreur que la conjecture de Goldbach elle-même
illustre. Sa valeur est ASYMÉTRIQUE : un contre-exemple trouvé est une
information CERTAINE (la formule est fausse, inutile de chercher à la prouver),
une absence de contre-exemple n'est qu'une autorisation de dépenser du temps.

TROIS VALEURS, PAS DEUX. L'évaluation est de Kleene : `VRAI`, `FAUX`, ou
`None` quand une sous-formule est hors du fragment interprété (un ensemble
opaque, un τ-terme, une notion qu'on ne sait pas calculer). `None` se propage
correctement — `FAUX ∧ inconnu` vaut `FAUX`, pas `inconnu` — ce qui permet de
trancher des formules partiellement interprétables.

CE QU'IL SAIT LIRE. Les primitives du langage (`¬`, `∨`, `∃`, `=`) — et donc
GRATUITEMENT `et`, `⇒`, `∀`, qui en sont des abréviations — plus une table de
prédicats arithmétiques reconnus par RECONSTRUCTION VÉRIFIÉE : on rebâtit le
motif attendu et l'on exige l'égalité, jamais un test de forme approximatif.
"""
from __future__ import annotations

from outils_ia.arithmetique.numeraux import num

#: borne par défaut du balayage — au-delà, le coût de construction des
#: numéraux domine (le partage de sous-termes vaut un facteur ~466, mais il
#: ne rend pas la chose gratuite pour autant).
BORNE_DEFAUT = 60


# ══════════════════════════════════════════════════════════════════════════════
#  ÉVALUATION DES TERMES — par TABLE, jamais par descente
# ══════════════════════════════════════════════════════════════════════════════
# ⚠️ LOI DE CONCEPTION, mesurée le 12 août et valable pour tout le projet.
# Dans ce noyau, les termes arithmétiques sont des τ-TERMES OPAQUES : `N(7)` et
# `N(3)+N(4)` ont tous deux `tag == 'tau'` et UN seul argument (une formule).
# On ne peut donc PAS descendre dans un terme pour l'évaluer — il n'y a rien à
# décomposer. La seule voie est la RECONSTRUCTION : bâtir le terme attendu et
# comparer. C'est praticable parce que les assemblages sont hashables et que
# l'égalité est en O(1) ; c'est impraticable si l'on reconstruit à chaque appel,
# d'où la table bâtie UNE fois.
#
# Les FORMULES, elles, se décomposent normalement (`¬`, `∨`, `∃`, `=`). La
# frontière « formule décomposable / terme opaque » est la structure de tout
# évaluateur possible ici.

#: table {terme → entier}, bâtie paresseusement, partagée
_TABLE = {}
_TABLE_BORNE = 0


def table(borne=24):
    """La table des termes évaluables jusqu'à `borne` — bâtie UNE fois.

    Contient les numéraux, leurs sommes et leurs produits. Sa construction
    coûte O(borne²) constructions de termes ; son usage est en O(1)."""
    global _TABLE_BORNE
    if borne <= _TABLE_BORNE:
        return _TABLE
    for k in range(borne + 1):
        _TABLE[num(k)] = k
    for a in range(borne + 1):
        for b in range(borne + 1 - a):
            _TABLE.setdefault(_somme(num(a), num(b)), a + b)
            if a * b <= borne:
                _TABLE.setdefault(_produit(num(a), num(b)), a * b)
    _TABLE_BORNE = borne
    return _TABLE


def valeur(t, env=None, borne=24):
    """→ l'entier que dénote le terme `t`, ou `None` si hors table.

    `env` affecte des entiers aux variables libres : la substitution se fait
    par le NOYAU (`subst_t`), jamais à la main."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        subst_t,
    )
    for nom, k in (env or {}).items():
        t = subst_t(num(k), nom, t)
    return table(borne).get(t)


def _zero():
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
        ensembles_abrege as E,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        cardinal,
    )
    return cardinal(E.VIDE)


def _somme(a, b):
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    return somme_cardinale_binaire(a, b)


def _produit(a, b):
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire,
    )
    return produit_cardinal_binaire(a, b)


# ══════════════════════════════════════════════════════════════════════════════
#  PRÉDICATS ARITHMÉTIQUES — reconnus par RECONSTRUCTION, jamais par navigation
# ══════════════════════════════════════════════════════════════════════════════
# Même loi que pour les termes : on ne descend PAS dans la formule à coups de
# `.sous[...]` pour deviner ses morceaux (c'est illisible, ça casse au premier
# changement, et le projet l'a déjà payé — cf. PIEGES_MESURES §9). On rebâtit
# le motif attendu sur des candidats connus, et l'on exige l'égalité littérale.
# Les candidats sont les termes de la table : c'est fini, et le hachage rend
# chaque test O(1).

#: les graphies de liants employées dans le dépôt pour `est_premier`
HABITS = (("d1", "q1"), ("d2", "q2"), ("dgb", "qgb"), ("d3", "q3"))

#: index {formule → verdict}, bâti une fois — MÊME LOI QUE POUR LES TERMES.
#: Première version : on reconstruisait le motif à CHAQUE consultation, soit
#: |table|² ≈ 26 000 constructions de formule par appel. Inutilisable. L'index
#: est bâti une fois et consulté en O(1).
_INDEX = {}
_INDEX_BORNE = 0


def index(borne=12):
    """L'index des formules atomiques reconnues, bâti UNE fois.

    ⚠️ LIMITE ASSUMÉE : `a ≤ b` n'est indexé qu'entre NUMÉRAUX, pas entre
    termes composés — la table complète donnerait |T|² entrées. Une inégalité
    entre sommes rendra donc `None` (« je ne sais pas »), ce qui est le
    comportement sûr : l'oracle se tait plutôt que d'affirmer."""
    global _INDEX_BORNE
    if borne <= _INDEX_BORNE:
        return _INDEX
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        inf_egal_card,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        est_fini,
    )
    from outils_ia.conjectures.goldbach import est_premier
    T = table(borne)
    for t, k in T.items():
        _INDEX.setdefault(est_fini(t), ("fini", k))
        for (d, q) in HABITS:
            _INDEX.setdefault(est_premier(t, d=d, q=q), ("premier", k))
    for a in range(borne + 1):                         # ≤ : numéraux seulement
        for b in range(borne + 1):
            _INDEX.setdefault(inf_egal_card(num(a), num(b)), ("le", a, b))
    _INDEX_BORNE = borne
    return _INDEX


def _atome(f, borne):
    """→ le verdict d'une formule atomique reconnue, ou `None`."""
    v = index(borne).get(f)
    if v is None:
        return None
    if v[0] == "premier":
        return _premier(v[1])
    if v[0] == "fini":
        return True
    return v[1] <= v[2]


def _premier(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


# ══════════════════════════════════════════════════════════════════════════════
#  ÉVALUATION DES FORMULES — logique de Kleene à trois valeurs
# ══════════════════════════════════════════════════════════════════════════════

def verite(f, env=None, borne=24):
    """→ `True`, `False`, ou `None` (hors fragment interprété).

    ⚠️ `None` n'est PAS « faux ». Il signifie « je ne sais pas calculer ceci »,
    et se propage selon Kleene : `False ∧ inconnu` vaut `False`."""
    env = env or {}
    tag = getattr(f, "tag", None)

    #   substitution PAR LE NOYAU des variables affectées, une fois pour toutes
    if env:
        from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
            subst_f,
        )
        for nom, k in env.items():
            f = subst_f(num(k), nom, f)
        env, tag = {}, getattr(f, "tag", None)

    #   les prédicats arithmétiques, reconnus AVANT la descente structurelle
    a = _atome(f, borne)
    if a is not None:
        return a

    #   les primitives — et donc et/⇒/∀ gratuitement, ce sont des abréviations
    if tag == "=":
        a = valeur(f.termes[0], env, borne)
        b = valeur(f.termes[1], env, borne)
        return None if a is None or b is None else a == b
    if tag == "non":
        v = verite(f.sous[0], env, borne)
        return None if v is None else not v
    if tag == "ou":
        g, d = verite(f.sous[0], env, borne), verite(f.sous[1], env, borne)
        if g is True or d is True:
            return True                                # Kleene : vrai absorbe
        if g is False and d is False:
            return False
        return None
    if tag == "exists":
        inconnu = False
        for k in range(borne + 1):
            e = dict(env)
            e[f.lieur] = k
            v = verite(f.sous[0], e, borne)
            if v is True:
                return True                            # témoin trouvé : CERTAIN
            if v is None:
                inconnu = True
        #   aucun témoin sous la borne : on ne conclut PAS `False`, le domaine
        #   est infini. Sauf si tout était interprété — et même alors, prudence.
        return None if inconnu else None
    return None


def contre_exemple(f, variables, borne=24):
    """Cherche une affectation des `variables` qui rend `f` FAUSSE.

    → le dictionnaire fautif, ou `None` si aucun n'a été trouvé sous `borne`.

    C'EST LE SEUL USAGE FIABLE DE CET ORACLE. Un contre-exemple trouvé est une
    information CERTAINE : inutile de chercher à démontrer `f`. Une absence de
    contre-exemple n'est qu'une autorisation de dépenser du temps de noyau —
    jamais une preuve."""
    noms = list(variables)
    for aff in _affectations(noms, borne):
        if verite(f, aff, borne) is False:
            return aff
    return None


def _affectations(noms, borne):
    if not noms:
        yield {}
        return
    tete, reste = noms[0], noms[1:]
    for k in range(borne + 1):
        for suite in _affectations(reste, borne):
            d = dict(suite)
            d[tete] = k
            yield d


__all__ = ["BORNE_DEFAUT", "HABITS", "table", "index", "valeur",
           "verite", "contre_exemple"]
