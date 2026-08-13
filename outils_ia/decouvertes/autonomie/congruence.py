# -*- coding: utf-8 -*-
"""ORGANE V16 — LA CONGRUENCE AUTOMATIQUE (11 août 2026, ev.410).

DIAGNOSTIC QUI L'A FAIT NAÎTRE (script `ALG1_operation_nouvelle.py`). On
définit une opération absente du dépôt, `a ⊕ b := (a+b)+1`, et on demande
`a ⊕ b = b ⊕ a` avec, au pool, la seule commutativité de `+` :

  · sans aide           : NON fermé — le manque nommé est le but lui-même ;
  · avec `congruence_terme` versée en route : FERMÉ, clos.

Autrement dit la machine sait **chaîner** le pas de congruence, mais pas le
**fabriquer**. Or toute propriété d'une opération DÉRIVÉE se ramène à des
congruences sur les opérations de base : c'est exactement ce qui lui fermait
l'accès à l'étude de structures nouvelles.

CE QUE FAIT L'ORGANE. Devant un but `u = v` avec `u ≠ v`, il cherche le
**contexte commun** : si `u` et `v` ne divergent qu'en UNE position, il
existe un terme `C(w)` et des sous-termes `a`, `b` tels que
`u = C(a)` et `v = C(b)`. Il vise alors `a = b` (récursion), et referme par
`congruence_terme` — jugé par le noyau.

POURQUOI UNE ANTI-UNIFICATION. Les opérations du dépôt sont des **τ-termes**
(`SC(a,b)` et `successeur(a)` ont tous deux `tag='tau'`, `lieur='Z'`, un seul
argument qui est une FORMULE) : la divergence entre `(a+b)+1` et `(b+a)+1`
est enfouie à plusieurs niveaux. Une comparaison d'arguments de surface ne la
voit pas ; il faut descendre récursivement dans termes ET formules.

GARDES. (1) Zéro divergence ⇒ rien à faire (c'est la réflexivité, organe v9).
(2) Deux divergences ou plus ⇒ on renonce (une seule congruence ne suffit
pas). (3) Si la variable de contexte est capturée par un lieur rencontré en
chemin, on renonce — jamais de capture silencieuse.
"""
from __future__ import annotations

#: variable de contexte — improbable dans les énoncés du dépôt
LIANT_CONTEXTE = "wcong16"


def _est_terme(x):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        Terme,
    )
    return isinstance(x, Terme)


def _est_formule(x):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        Formule,
    )
    return isinstance(x, Formule)


def _enfants(x):
    """Les sous-objets d'un terme ou d'une formule, dans un ordre stable."""
    if _est_terme(x):
        return list(x.args)
    if _est_formule(x):
        return list(x.termes) + list(x.sous)
    return []


def _reconstruire(x, enfants):
    """Rebâtit `x` avec la liste d'enfants donnée (même ordre que `_enfants`)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        Formule, Terme,
    )
    if _est_terme(x):
        return Terme(x.tag, nom=x.nom, lieur=x.lieur, args=tuple(enfants))
    n = len(x.termes)
    return Formule(x.tag, lieur=x.lieur,
                   termes=tuple(enfants[:n]), sous=tuple(enfants[n:]))


def contexte_commun(u, v, w=LIANT_CONTEXTE):
    """→ (contexte, a, b) tel que `u = contexte[w:=a]` et `v = contexte[w:=b]`,
    ou `None` si aucun tel contexte n'existe.

    ⚠️ PLUSIEURS OCCURRENCES SONT ADMISES — et c'est indispensable. Les
    opérations du dépôt sont des τ-termes dont le développement RÉPÈTE leurs
    arguments (`SC(a,b)` fait apparaître `a` et `b` en plusieurs points), si
    bien qu'une garde « exactement une divergence » ne se déclenche jamais.
    Comme `congruence_terme` substitue TOUTES les occurrences de `w`, on
    accepte N divergences **à condition qu'elles portent toutes sur la même
    paire (a, b)** — sinon une seule égalité ne peut pas les justifier."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    if u == v:
        return None                                    # zéro divergence
    if type(u) is not type(v):
        return var(w), u, v                            # divergence ICI
    for att in ("tag", "nom", "lieur"):
        if getattr(u, att, None) != getattr(v, att, None):
            return var(w), u, v
    if getattr(u, "lieur", None) == w:
        return None                                    # capture : on renonce
    eu, ev = _enfants(u), _enfants(v)
    if len(eu) != len(ev) or not eu:
        return var(w), u, v

    cands = candidats(u, v, w)
    return cands[-1] if cands else None


def candidats(u, v, w=LIANT_CONTEXTE, max_niveaux=40):
    """→ liste de (contexte, a, b), **du plus GROS au plus fin**.

    Le contexte le plus gros prend la divergence au nœud courant (sous-but
    `u = v`) ; les suivants descendent d'un cran à chaque fois, produisant des
    sous-buts de plus en plus profonds. L'appelant essaie dans l'ordre, car
    c'est le sous-but **le plus haut disponible au pool** qui ferme : sur
    `succ(a+b) = succ(b+a)`, le bon niveau est `a+b = b+a` (un théorème du
    dépôt) — descendre plus bas mène dans les entrailles du τ, où plus rien
    n'est nommé.

    Cas de l'échange : `SC(a,b)` / `SC(b,a)` divergent sur DEUX paires
    distinctes (`a` vs `b`, puis `b` vs `a`) ; aucune variable unique ne les
    couvre, donc la descente s'arrête là — et c'est exactement le bon niveau.

    ⚠️ DESCENTE LINÉAIRE, sans retour arrière. Une version exhaustive
    (récursion dans une boucle sur les candidats) est EXPONENTIELLE : mesurée
    sur `succ(a+b) = succ(b+a)`, elle ne terminait pas en deux minutes. On ne
    suit donc qu'UNE chaîne : tant qu'il n'y a qu'un seul enfant divergent, on
    descend ; dès qu'il y en a deux, on s'arrête — et c'est précisément le
    niveau utile."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    out, trou = [], var(w)

    def _descendre(x, y, rebuild, prof):
        if x == y or prof > max_niveaux:
            return
        out.append((rebuild(trou), x, y))
        if type(x) is not type(y):
            return
        for att in ("tag", "nom", "lieur"):
            if getattr(x, att, None) != getattr(y, att, None):
                return
        if getattr(x, "lieur", None) == w:
            return                                     # capture : on s'arrête
        ex, ey = _enfants(x), _enfants(y)
        if len(ex) != len(ey) or not ex:
            return
        div = [i for i in range(len(ex)) if ex[i] != ey[i]]
        if len(div) != 1:
            return                     # ≥2 divergences : c'est le bon niveau
        i = div[0]

        def _rb(t, _x=x, _i=i, _reb=rebuild):
            e = _enfants(_x)
            return _reb(_reconstruire(_x, e[:_i] + [t] + e[_i + 1:]))

        _descendre(ex[i], ey[i], _rb, prof + 1)

    _descendre(u, v, lambda t: t, 0)
    return out


def _sous_termes(x, acc=None, prof=0):
    """Tous les TERMES apparaissant dans `x` (y compris `x`), sans doublon."""
    if acc is None:
        acc = []
    if prof > 60:
        return acc
    if _est_terme(x) and x not in acc:
        acc.append(x)
    for e in _enfants(x):
        _sous_termes(e, acc, prof + 1)
    return acc


def _abstraire(x, a, w):
    """`x` où toute occurrence du terme `a` est remplacée par la variable `w`."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    if x == a:
        return var(w)
    enfants = _enfants(x)
    if not enfants:
        return x
    return _reconstruire(x, [_abstraire(e, a, w) for e in enfants])


def _lire_trou(ctx, cible, w):
    """Le terme que `cible` place là où `ctx` porte la variable `w`.

    → ce terme si toutes les occurrences s'accordent, sinon `None`."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    trou = var(w)
    trouve = []

    def _parcourir(c, t):
        if c == trou:
            trouve.append(t)
            return True
        if c == t:
            return True
        if type(c) is not type(t):
            return False
        for att in ("tag", "nom", "lieur"):
            if getattr(c, att, None) != getattr(t, att, None):
                return False
        ec, et_ = _enfants(c), _enfants(t)
        if len(ec) != len(et_):
            return False
        return all(_parcourir(x, y) for x, y in zip(ec, et_))

    if not _parcourir(ctx, cible) or not trouve:
        return None
    return trouve[0] if all(t == trouve[0] for t in trouve) else None


def paires_par_abstraction(u, v, w=LIANT_CONTEXTE, maxi=24):
    """→ liste de (contexte, a, b), **du plus GROS sous-terme au plus petit**.

    Approche RETENUE (la descente structurelle échoue sur les τ-termes, dont
    le développement DUPLIQUE les arguments : il y a alors plusieurs
    divergences dès le premier niveau et l'on n'isole jamais `a+b`).

    Ici on abstrait : pour chaque sous-terme `a` de `u`, on remplace toutes
    ses occurrences par `w`, puis on LIT dans `v` ce qui occupe le trou. Si la
    lecture est cohérente, `(contexte, a, b)` est un candidat. Les gros
    sous-termes d'abord : c'est le sous-but le plus haut — donc le plus
    susceptible d'être au pool — qui doit être essayé en premier."""
    out = []
    for a in sorted(_sous_termes(u), key=lambda t: -len(_sous_termes(t))):
        ctx = _abstraire(u, a, w)
        if ctx == u:
            continue                                   # aucune occurrence
        b = _lire_trou(ctx, v, w)
        if b is None or b == a:
            continue
        out.append((ctx, a, b))
        if len(out) >= maxi:
            break
    return out


def fermer_par_congruence(but, viser):
    """Tente `u = v` par congruence. `viser(sous_but)` doit rendre un
    `Theoreme` ou `None`. → `Theoreme` (jugé noyau) ou `None`.

    `viser` est fourni par l'appelant (c'est la récursion de l'organe de
    besoin) : ce module ne connaît pas la stratégie de recherche."""
    if getattr(but, "tag", None) != "=" or len(getattr(but, "termes", ())) != 2:
        return None
    u, v = but.termes
    if u == v:
        return None                                    # v9 s'en charge
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, var,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        congruence_terme,
    )
    trivial = var(LIANT_CONTEXTE)
    for (contexte, a, b) in paires_par_abstraction(u, v):
        if contexte == trivial:
            continue                                   # sous-but == but : boucle
        if not (_est_terme(contexte) and _est_terme(a) and _est_terme(b)):
            continue                                   # congruence de TERMES
        th_ab = viser(egal(a, b))
        if th_ab is None:
            continue
        try:
            th = N.modus_ponens(th_ab, congruence_terme(a, b, contexte,
                                                        w=LIANT_CONTEXTE))
        except Exception:
            continue
        if th.conclusion == but:
            return th
    return None


__all__ = ["paires_par_abstraction", "fermer_par_congruence",
           "LIANT_CONTEXTE"]
