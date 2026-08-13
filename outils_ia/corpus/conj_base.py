#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Socle du conjectureur — matching σ, détecteurs de forme, canonicalisation, intérêt, subsomption.

Extrait de `conjecturer.py` (découpage ≤300 lignes, une responsabilité par fichier). Ce module ne
contient AUCUN chaîneur : uniquement les briques pures réutilisées par les 4 régimes
(`conj_regimes.py`), le moteur d'implications (`conjecturer.py`) et les catalogues émis.
Soundness NON concernée ici : le noyau juge toujours le théorème final chez les appelants.
"""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N   # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie  # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_t, var  # noqa: E402

PACKAGES = ["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"]


def _match(pat, cible, subst, vlibres):
    """Matching 1er ordre : lie les variables LIBRES de `pat` (∈ vlibres) pour rendre pat == cible.

    Renvoie True et remplit `subst` {nom_var: terme}, ou False. Soundness NON concernée : un
    mauvais match ne peut que rater une découverte (le noyau construit le théorème final et on
    vérifie sa conclusion) — jamais en fabriquer un faux."""
    if not (hasattr(pat, "tag") and hasattr(cible, "tag")):    # Assemblage (couche primitive)
        return pat == cible
    pat_terme = hasattr(pat, "args") and not hasattr(pat, "sous")
    cib_terme = hasattr(cible, "args") and not hasattr(cible, "sous")
    if pat_terme != cib_terme:
        return False
    if pat_terme:
        if pat.tag == "var" and pat.nom in vlibres:
            if pat.nom in subst:
                return subst[pat.nom] == cible
            subst[pat.nom] = cible
            return True
        if pat.tag != cible.tag or pat.nom != cible.nom or pat.lieur != cible.lieur:
            return False
        if len(pat.args) != len(cible.args):
            return False
        return all(_match(a, b, subst, vlibres) for a, b in zip(pat.args, cible.args))
    if pat.tag != cible.tag or pat.lieur != cible.lieur:
        return False
    if len(pat.termes) != len(cible.termes) or len(pat.sous) != len(cible.sous):
        return False
    return (all(_match(a, b, subst, vlibres) for a, b in zip(pat.termes, cible.termes))
            and all(_match(a, b, subst, vlibres) for a, b in zip(pat.sous, cible.sous)))


def _instancier(thm, subst):
    """Applique σ à un théorème CLOS via le noyau : generalisation(v) puis instancie(t), par var."""
    for v, t in subst.items():
        thm = instancie(N.generalisation(v, thm), t)
    return thm


# ── Détecteurs de forme (couche abrégée ; robustes au corpus mixte Formule/Assemblage) ────────
def _comme_impl(f):
    """(A, B) si f est l'implication A⇒B (= ¬A ∨ B), sinon None."""
    if getattr(f, "tag", None) == "ou" and len(f.sous) == 2 and f.sous[0].tag == "non":
        return f.sous[0].sous[0], f.sous[1]
    return None


def _comme_egal(f):
    """(a, b) si f est l'égalité a=b, sinon None."""
    if getattr(f, "tag", None) == "=" and len(f.termes) == 2:
        return f.termes[0], f.termes[1]
    return None


def _comme_equiv(f):
    """(A, B) si f est l'équivalence A⇔B, sinon None.

    equiv(A,B) = et(A⇒B, B⇒A) = ¬(¬(A⇒B) ∨ ¬(B⇒A)) — on décompose la conjonction et on
    vérifie que les deux implications sont bien MUTUELLEMENT inverses."""
    if getattr(f, "tag", None) != "non" or len(getattr(f, "sous", ())) != 1:
        return None
    s = f.sous[0]
    if getattr(s, "tag", None) != "ou" or len(s.sous) != 2:
        return None
    g, h = s.sous
    if getattr(g, "tag", None) != "non" or getattr(h, "tag", None) != "non":
        return None
    ab, ba = _comme_impl(g.sous[0]), _comme_impl(h.sous[0])
    if ab and ba and ab[0] == ba[1] and ab[1] == ba[0]:
        return ab                                     # (A, B)
    return None


def _comme_inclus(f):
    """(t, u, z) si f est l'inclusion t⊂u (= ∀z(z∈t ⇒ z∈u)), sinon None.

    pourtout(z,g) = ¬∃z¬g ; on vérifie que le corps est bien (z∈t ⇒ z∈u) avec z le liant
    (non libre dans t, u)."""
    if getattr(f, "tag", None) != "non" or len(getattr(f, "sous", ())) != 1:
        return None
    e = f.sous[0]
    if getattr(e, "tag", None) != "exists":
        return None
    z, n = e.lieur, e.sous[0]
    if n.tag != "non":
        return None
    ab = _comme_impl(n.sous[0])
    if not ab:
        return None
    A, B = ab
    if (getattr(A, "tag", None) == "in" and getattr(B, "tag", None) == "in"
            and A.termes[0] == var(z) == B.termes[0]):
        t, u = A.termes[1], B.termes[1]
        if z not in libres_t(t) | libres_t(u):
            return t, u, z
    return None


# ── Affichage lisible ─────────────────────────────────────────────────────────────────────────
def _tf(t):
    if t.tag == "var":
        return t.nom
    if t.tag == "app":
        return f"{t.nom}({','.join(_tf(a) for a in t.args)})"
    if t.tag == "tau":
        return f"τ{t.lieur}(…)"
    return "?"


def _fmt(f):
    ab = _comme_impl(f)
    if ab:
        return f"({_fmt(ab[0])} ⇒ {_fmt(ab[1])})"
    if f.tag == "ou":
        return f"({_fmt(f.sous[0])} ∨ {_fmt(f.sous[1])})"
    if f.tag == "non":
        return f"¬{_fmt(f.sous[0])}"
    if f.tag == "=":
        return f"{_tf(f.termes[0])}={_tf(f.termes[1])}"
    if f.tag == "in":
        return f"{_tf(f.termes[0])}∈{_tf(f.termes[1])}"
    if f.tag == "exists":
        return f"∃{f.lieur} {_fmt(f.sous[0])}"
    return "?"


# ── Canonicalisation, mesure, intérêt ─────────────────────────────────────────────────────────
def _est_terme(x):
    return hasattr(x, "args") and not hasattr(x, "sous")


def _vars_de(f, memo):
    """Tous les NOMS (variables ET lieurs) du sous-arbre — id-mémoïsé sur le DAG."""
    r = memo.get(id(f))
    if r is not None:
        return r
    if not hasattr(f, "tag"):
        s = frozenset()
    elif _est_terme(f):
        if f.tag == "var":
            s = frozenset((f.nom,))
        else:
            s = frozenset((f.lieur,)) if f.lieur else frozenset()
            for a in f.args:
                s |= _vars_de(a, memo)
    else:
        s = frozenset((f.lieur,)) if f.lieur else frozenset()
        for t in f.termes:
            s |= _vars_de(t, memo)
        for x in f.sous:
            s |= _vars_de(x, memo)
    memo[id(f)] = s
    return s


def _cle_canon(f, ordre=None, out=None):
    """Clé α-canonique (dédup) : digest Merkle de la sérialisation où TOUTES les
    variables (libres + liées) sont renommées par ordre de 1ʳᵉ apparition DÉPLIÉE.

    Même sémantique que l'ancienne version-chaîne, mais calculée EN PARTAGE :
    un sous-arbre revu plus tard a TOUTES ses variables déjà numérotées (elles
    l'ont été à sa première sérialisation), son digest est donc mémoïsable par
    (id, indices-de-ses-variables) — l'ordre d'apparition déplié est préservé
    exactement, car on ne court-circuite que des sous-arbres sans nom neuf.
    Avant : sérialisation dépliée en chaîne — MemoryError mesuré sur le régime
    CY1 avec premier(13) (8 août 2026).  `ordre`/`out` conservés pour
    compatibilité de signature, ignorés."""
    vmemo, cmemo, ctx = {}, {}, {}

    def rec(g):
        vs = _vars_de(g, vmemo)
        complet = all(n in ctx for n in vs)
        if complet:
            rel = tuple(sorted((n, ctx[n]) for n in vs))
            hit = cmemo.get((id(g), rel))
            if hit is not None:
                return hit
        h = hashlib.blake2b(digest_size=16)
        if not hasattr(g, "tag"):                 # Assemblage (couche primitive)
            h.update(b"raw:" + repr(g).encode("utf-8", "replace"))
        elif _est_terme(g):
            if g.tag == "var":
                h.update(b"#%d" % ctx.setdefault(g.nom, len(ctx)))
            else:
                li = b"#%d" % ctx.setdefault(g.lieur, len(ctx)) if g.lieur else b""
                h.update(("%s:%s:" % (g.tag, g.nom)).encode("utf-8") + li + b"(")
                for a in g.args:
                    h.update(rec(a))
                h.update(b")")
        else:
            li = b"#%d" % ctx.setdefault(g.lieur, len(ctx)) if g.lieur else b""
            h.update(("[%s:" % g.tag).encode("utf-8") + li)
            for t in g.termes:
                h.update(rec(t))
            for s in g.sous:
                h.update(rec(s))
            h.update(b"]")
        d = h.digest()
        if complet:
            cmemo[(id(g), rel)] = d
        return d

    return rec(f).hex()


def _taille(f, _memo=None):
    """Taille DÉPLIÉE exacte, calculée EN PARTAGE (mémo local par id — les comptes
    s'additionnent). L'ancienne récursion nue gelait le tri des briques sur les
    conclusions-monstres τZ du compounding (mesuré au flux CY2, 8 août 2026)."""
    if _memo is None:
        _memo = {}
    n = _memo.get(id(f))
    if n is not None:
        return n
    n = 1
    if _est_terme(f):
        for a in f.args:
            n += _taille(a, _memo)
    else:
        for t in f.termes:
            n += _taille(t, _memo)
        for s in f.sous:
            n += _taille(s, _memo)
    _memo[id(f)] = n
    return n


def _apps(f, acc=None):
    """Ensemble des symboles applicatifs (app.nom) — mesure du « pont ».
    EN PARTAGE (mémo local par id) : même piège de dépliage que `_taille`."""
    memo = {}

    def rec(g):
        r = memo.get(id(g))
        if r is not None:
            return r
        s = set()
        if _est_terme(g):
            if g.tag == "app":
                s.add(g.nom)
            for a in g.args:
                s |= rec(a)
        else:
            for t in g.termes:
                s |= rec(t)
            for x in g.sous:
                s |= rec(x)
        memo[id(g)] = s
        return s

    r = rec(f)
    if acc is not None:
        acc |= r
        return acc
    return r


def _interet(mode, s1, s2, thm):
    """Score d'intérêt d'une découverte (heuristique statique). Plus haut = plus intéressant.

    · PONT INTER-MODULES : chaîner deux théorèmes de modules différents relie deux domaines ;
    · PONT DE SYMBOLES : antécédent et conséquent partageant PEU de symboles = plus surprenant ;
    · PARCIMONIE : conclusion plus petite = plus utilisable (les monstres ¬/∨ profonds = bruit)."""
    mod1, mod2 = s1.split(".")[0], s2.split(".")[0]
    cross = 1 if mod1 != mod2 else 0
    ab = _comme_impl(thm.conclusion)
    if ab:
        sa, sc = _apps(ab[0]), _apps(ab[1])
        union = sa | sc
        pont = 1 - (len(sa & sc) / len(union)) if union else 0.0     # distance de Jaccard
    else:
        pont = 0.0
    taille = _taille(thm.conclusion)
    return (cross, round(pont, 3), -taille)


# ── Filtre de SUBSOMPTION (anti-trivialité, façon POET) ───────────────────────────────────────
def universels_de(preuve_de):
    """Pré-calcule les conclusions-patrons du corpus pour le filtre de SUBSOMPTION :
    [(conclusion, vars_libres)] — seules les Formule (couche abrégée) sont des patrons."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
    out = []
    for c in preuve_de:
        if hasattr(c, "tag"):
            out.append((c, libres_f(c)))
    return out


def _est_instance_connue(concl, universels):
    """ANTI-TRIVIALITÉ : vrai si `concl` est une σ-INSTANCE d'un théorème connu (donc pas une
    vraie découverte — ex. ∅⊂X∪b est l'instance X:=X∪b de vide_inclus_partout). Un faux
    négatif ici ne coûte qu'une découverte redondante ; la soundness n'est pas concernée."""
    for (pat, vlib) in universels:
        if not vlib:
            continue                                  # les clos sont gérés par la dédup α
        s = {}
        if _match(pat, concl, s, vlib):
            return True
    return False
