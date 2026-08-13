# -*- coding: utf-8 -*-
"""ORGANE V17 — LA RÉÉCRITURE PAR LES ÉGALITÉS DU POOL (11 août 2026, ev.411).

DIAGNOSTIC QUI L'A FAIT NAÎTRE (`ALG2_associativite.py`). Avec l'organe v16,
la machine ferme la COMMUTATIVITÉ de `a ⊕ b := (a+b)+1` — un seul pas de
congruence suffit. Mais sur l'ASSOCIATIVITÉ :

    (a ⊕ b) ⊕ c  =  ((a+b)+1 + c) + 1
    a ⊕ (b ⊕ c)  =  (a + ((b+c)+1)) + 1

elle échoue, chaîne « (aucune route) » : les deux membres ne se ramènent pas
l'un à l'autre par UNE congruence — il faut associer, commuter, ré-associer.
`composer_egalites` (transitivité) existe au dépôt, mais rien ne la mobilisait.

CE QUE FAIT L'ORGANE. Une recherche en largeur depuis `u` vers `v`, où chaque
pas applique une égalité `l = r` du pool à un sous-terme :

    t  =  C[l]   ──(congruence sur l = r)──►   C[r]  =  t'

et les pas se composent par transitivité. Les égalités sont utilisées dans les
DEUX SENS (`l → r` et `r → l`) : une chaîne peut avoir à défaire avant de
refaire.

BORNES — ce moteur est le seul endroit du projet qui explore vraiment, donc il
est borné explicitement : `max_pas` (longueur de chaîne) et `max_noeuds`
(termes visités). Dépassement ⇒ on renonce proprement, jamais d'explosion
silencieuse. Les bornes sont basses par défaut : mieux vaut échouer vite et
NOMMER le manque que faire attendre.

⚠️ Ne JAMAIS `str()` un terme ici pour tracer : les τ-termes ont un `__repr__`
récursif qui explose en MemoryError (piège mesuré). On compte, on compare.
"""
from __future__ import annotations

from outils_ia.decouvertes.autonomie.congruence import (
    LIANT_CONTEXTE, _abstraire, _est_terme, _sous_termes,
)


def _egalites_du_pool(faits):
    """Les théorèmes du pool dont la conclusion est une égalité `l = r`.

    → liste de (theoreme, l, r). Les deux sens sont produits par l'appelant."""
    out = []
    for ccl, (_nom, th) in faits.items():
        if getattr(ccl, "tag", None) == "=" and len(ccl.termes) == 2:
            l, r = ccl.termes
            if l != r:
                out.append((th, l, r))
    return out


def _var(nom):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var,
    )
    return var(nom)


def _instances(t, th_eq, l, r, libres, maxi=8):
    """La loi telle quelle, PUIS ses instances qui matchent un sous-terme de `t`.

    ORGANE V18 (12 août 2026, ev.412) — DIAGNOSTIC. Le moteur ne trouvait
    jamais où s'appliquer : il cherchait le membre gauche d'une égalité du pool
    **littéralement** parmi les sous-termes. Or les lois parlent de `a+b` tandis
    que le but contient `(a+b)+1` — la loi est bonne, c'est son INSTANCE qui
    manque. On ne corrige pas le cas, on comble la classe : une égalité du pool
    est une LOI dont les variables libres sont des paramètres, matchée au
    moment d'être appliquée (`_match`, 1er ordre) et instanciée par le NOYAU.

    La soundness n'est pas en jeu : un mauvais match ne peut que RATER une
    réécriture, jamais en fabriquer une fausse — c'est le noyau qui construit."""
    out = [(l, r, th_eq)]
    if not libres:
        return out
    import sys
    from pathlib import Path
    _corpus = Path(__file__).resolve().parents[2] / "corpus"
    if str(_corpus) not in sys.path:
        sys.path.insert(0, str(_corpus))
    from conj_base import _match, _instancier
    for cible in _sous_termes(t):
        if len(out) > maxi:
            break
        sigma = {}
        if not _match(l, cible, sigma, libres):
            continue
        sigma = {k: v for k, v in sigma.items() if v != _var(k)}
        if not sigma:
            continue                                   # déjà couvert par la loi
        try:
            th2 = _instancier(th_eq, sigma)
        except Exception:
            continue
        c2 = th2.conclusion
        if getattr(c2, "tag", None) == "=" and c2.termes[0] != c2.termes[1]:
            out.append((c2.termes[0], c2.termes[1], th2))
    return out


def _un_pas(t, th_eq, l, r):
    """Applique `l = r` à `t` : → (t', theoreme de `t = t'`) ou `None`.

    Toutes les occurrences de `l` dans `t` sont remplacées d'un coup —
    c'est ce que fait `congruence_terme`, qui substitue la variable de
    contexte partout."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        subst_t,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        congruence_terme,
    )
    ctx = _abstraire(t, l, LIANT_CONTEXTE)
    if ctx == t:
        return None                                    # `l` n'apparaît pas
    try:
        th = N.modus_ponens(th_eq, congruence_terme(l, r, ctx,
                                                    w=LIANT_CONTEXTE))
    except Exception:
        return None
    tp = subst_t(r, LIANT_CONTEXTE, ctx)
    if th.conclusion.termes != (t, tp):
        return None
    return tp, th


def reecrire_vers(u, v, faits, max_pas=5, max_noeuds=1200):
    """Cherche une chaîne `u = … = v` par réécriture. → Theoreme ou None.

    Largeur d'abord : les chaînes courtes sont trouvées en premier, ce qui
    donne les preuves les plus simples.

    BORNES CALIBRÉES SUR MESURE (12 août, `ASSOC4_moteur_fusionne.py`), pas
    choisies à vue. L'associativité de l'opération dérivée `a ⊕ b := (a+b)+1`
    demande une chaîne de **5** pas :

        ((a+b)+1)+c = (a+b)+(1+c) = (a+b)+(c+1) = a+(b+(c+1)) = a+((b+c)+1)

    Avec `max_pas=3` (l'ancienne valeur) elle échouait, non par manque de
    puissance mais d'un cran de budget. Coûts relevés : 1 s / 2 s / 3 s / 4 s
    pour max_pas = 2 / 3 / 4 / 5 — la croissance est douce parce que la
    largeur d'abord coupe par `vus`, contrairement à la profondeur d'abord
    (95 s à profondeur 7, et toujours en échec)."""
    if u == v:
        return None                                    # la réflexivité (v9)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        composer_egalites, symetrie,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
        noyau_abrege as N,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f,
    )
    regles = []
    for (th, l, r) in _egalites_du_pool(faits):
        regles.append((th, l, r, libres_f(th.conclusion)))
        try:                                           # le sens inverse
            ths = N.modus_ponens(th, symetrie(l, r))
            regles.append((ths, r, l, libres_f(ths.conclusion)))
        except Exception:
            pass
    if not regles:
        return None

    vus = {u}
    front = [(u, None)]                                # (terme, preuve u = t)
    for _pas in range(max_pas):
        suivant = []
        for (t, preuve) in front:
            for (th_eq, l, r, libres) in regles:
                if not (_est_terme(l) and _est_terme(r)):
                    continue
                for (li, ri, th_i) in _instances(t, th_eq, l, r, libres):
                    res = _un_pas(t, th_i, li, ri)
                    if res is None:
                        continue
                    tp, th_pas = res
                    if tp in vus:
                        continue
                    chaine = th_pas if preuve is None else composer_egalites(
                        preuve, th_pas)
                    if tp == v:
                        return chaine
                    vus.add(tp)
                    suivant.append((tp, chaine))
                    if len(vus) > max_noeuds:
                        return None                    # borne : on renonce
        if not suivant:
            return None
        front = suivant
    return None


def fermer_par_reecriture(but, faits, max_pas=5):
    """Tente `u = v` par réécriture depuis le pool. → Theoreme ou None."""
    if getattr(but, "tag", None) != "=" or len(getattr(but, "termes", ())) != 2:
        return None
    u, v = but.termes
    if u == v:
        return None
    th = reecrire_vers(u, v, faits, max_pas=max_pas)
    return th if th is not None and th.conclusion == but else None


__all__ = ["reecrire_vers", "fermer_par_reecriture"]
