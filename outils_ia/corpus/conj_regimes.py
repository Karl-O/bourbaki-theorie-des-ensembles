#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Régimes algébriques du conjectureur — chaînage de =, ⇔, ⊂ et pont inter-régimes S6.

Extrait de `conjecturer.py` (découpage ≤300 lignes). Chaque régime syntaxique du langage a SA
transitivité dérivée au noyau et son compounding ; le moteur générique est partout le même :
(détecteur de forme, matching σ, composeur noyau, dédup α, subsomption, tri intérêt).
Sound par construction : le noyau bâtit chaque théorème final et la conclusion est vérifiée.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from conj_base import (_match, _instancier, _cle_canon, _interet,      # noqa: E402
                       _comme_egal, _comme_equiv, _comme_inclus,
                       universels_de, _est_instance_connue)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N   # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    instancie, conjonction_intro, equivalence_avant, equivalence_arriere)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites  # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    egal, equiv, inclus, appartient, libres_f, var)


# ── Régime « = » ──────────────────────────────────────────────────────────────────────────────
def egalites_de(preuve_de):
    """Extrait les théorèmes-ÉGALITÉ (a=b) du corpus : [(nom, thm, a, b)]."""
    out = []
    for c, (nom, thm) in preuve_de.items():
        ab = _comme_egal(c)
        if ab and ab[0] != ab[1]:
            out.append((nom, thm, ab[0], ab[1]))
    return out


def chainer_egalites(egalites, preuve_de):
    """Transitivité de l'ÉGALITÉ : T1⊢a=b, T2⊢b'=c avec σ(b')=b → ⊢a=σ(c), prouvé par
    `composer_egalites` (primitive noyau). Débloque l'algèbre ensembliste (associativité,
    commutativité, De Morgan…) invisible au régime ⇒. Dédup α-canonique + subsomption."""
    connus = {_cle_canon(c) for c in preuve_de}
    universels = universels_de(preuve_de)
    trouves, vus = [], set()
    for (n1, T1, a, b) in egalites:
        for (n2, T2, bp, c) in egalites:
            if n2 == n1:
                continue
            s = {}
            if not _match(bp, b, s, libres_f(T2.conclusion)):
                continue
            sig = {v: t for v, t in s.items() if t != var(v)}
            try:
                T2p = _instancier(T2, sig) if sig else T2
                ab = _comme_egal(T2p.conclusion)
                if ab is None or ab[0] != b:
                    continue
                cp = ab[1]
                if a == cp:
                    continue
                cible = egal(a, cp)
                cle = _cle_canon(cible)
                if cle in connus or cle in vus or _est_instance_connue(cible, universels):
                    continue
                tAC = composer_egalites(T1, T2p)
            except Exception:
                continue
            if tAC.est_clos and tAC.conclusion == cible:
                vus.add(cle)
                trouves.append(("egal.σ" if sig else "egal.", n1, n2, tAC))
    return trouves


def iterer_egalites(preuve_de, rounds=3, garder=30):
    """Compounding des ÉGALITÉS : les égalités découvertes au tour t deviennent des briques
    (« E<t>#k ») du tour t+1 → identités de profondeur croissante. Dédup inter-tours en
    agrandissant `connus`. Renvoie (tous, par_tour)."""
    egs = egalites_de(preuve_de)
    connus = dict(preuve_de)
    tous, par_tour = [], []
    for t in range(rounds):
        d = chainer_egalites(egs, connus)
        par_tour.append(d)
        tous.extend(d)
        if not d or t == rounds - 1:
            break
        for k, (_, _, _, thm) in enumerate(d):
            connus.setdefault(thm.conclusion, (f"E{t + 1}#{k}", thm))
        best = sorted(d, key=lambda x: _interet(*x), reverse=True)[:garder]
        for k, (_, _, _, thm) in enumerate(best):
            a, b = _comme_egal(thm.conclusion)
            egs.append((f"E{t + 1}#{k}", thm, a, b))
    return tous, par_tour


# ── Régime « ⊂ » + pont inter-régimes S6 ──────────────────────────────────────────────────────
def _composer_inclusions(T1, T2, t, u, v):
    """T1⊢t⊂u, T2⊢u⊂v (clos) → ⊢t⊂v en 6 pas noyau, robuste aux liants des sources :
    instancier les deux ∀ sur le liant de la CIBLE (choisi frais par formule.inclus),
    chaîner par MP, décharger, re-généraliser."""
    cible = inclus(t, v)
    z = _comme_inclus(cible)[2]                       # liant canonique de la cible
    zt = var(z)
    i1, i2 = instancie(T1, zt), instancie(T2, zt)     # z∈t⇒z∈u , z∈u⇒z∈v
    h = N.assume(appartient(zt, t))
    imp = N.loi_deduction(appartient(zt, t),
                          N.modus_ponens(N.modus_ponens(h, i1), i2))
    return N.generalisation(z, imp), cible            # ⊢ ∀z(z∈t⇒z∈v)


def inclusions_de(preuve_de):
    """Extrait les théorèmes-INCLUSION clos (t⊂u) du corpus : [(nom, thm, t, u)]."""
    out = []
    for c, (nom, thm) in preuve_de.items():
        r = _comme_inclus(c)
        if r and r[0] != r[1]:
            out.append((nom, thm, r[0], r[1]))
    return out


def egal_vers_inclusions(thm_eq):
    """PONT inter-régimes : ⊢B=C (clos) → (⊢B⊂C, ⊢C⊂B) via S6 + generalisation.

    S6 : (B=C) ⇒ ((z∈B) ⇔ (z∈C)) avec R{w}=(z∈w) ; MP puis projeter chaque sens et
    re-généraliser sur z. Chaque égalité (corpus OU découverte) nourrit le régime ⊂."""
    b, c = _comme_egal(thm_eq.conclusion)
    z = _comme_inclus(inclus(b, c))[2]                # liant frais cohérent avec la cible
    R = appartient(var(z), var("w"))                  # trou conventionnel w
    eqv = N.modus_ponens(thm_eq, N.s6(b, c, "w", R))  # ⊢ (z∈B) ⇔ (z∈C)
    d1 = N.generalisation(z, equivalence_avant(eqv))
    d2 = N.generalisation(z, equivalence_arriere(eqv))
    return d1, d2


def pool_inclusions(preuve_de, egal_decouvertes=()):
    """Pool ⊂ complet : inclusions closes du corpus + inclusions DÉRIVÉES par le pont S6 depuis
    les égalités (corpus + découvertes passées en argument). → (incls, n_corpus, n_pont)."""
    incls = inclusions_de(preuve_de)
    n_corpus = len(incls)
    sources = list(egalites_de(preuve_de))
    for (_, n1, _, thm) in egal_decouvertes:
        ab = _comme_egal(thm.conclusion)
        if ab:
            sources.append((n1, thm, ab[0], ab[1]))
    n_pont = 0
    for (ne, TE, _, _) in sources:
        try:
            d1, d2 = egal_vers_inclusions(TE)
        except Exception:
            continue
        for d in (d1, d2):
            r = _comme_inclus(d.conclusion)
            if r and d.est_clos:
                incls.append((f"pont:{ne}", d, r[0], r[1]))
                n_pont += 1
    return incls, n_corpus, n_pont


def chainer_inclusions(incls, preuve_de):
    """Régime ⊂ : transitivité de l'inclusion, matching σ sur le maillon central.
    Filtre de SUBSOMPTION : les σ-instances de théorèmes connus sont écartées (anti-trivialité)."""
    connus = {_cle_canon(c) for c in preuve_de}
    universels = universels_de(preuve_de)
    trouves, vus = [], set()
    for (n1, T1, t, u) in incls:
        for (n2, T2, up, v) in incls:
            if n2 == n1:
                continue
            s = {}
            if not _match(up, u, s, libres_f(T2.conclusion)):
                continue
            sig = {k: w for k, w in s.items() if w != var(k)}
            try:
                T2p = _instancier(T2, sig) if sig else T2
                r = _comme_inclus(T2p.conclusion)
                if r is None or r[0] != u:
                    continue
                vp = r[1]
                if t == vp:
                    continue
                cible_avant = inclus(t, vp)
                cle = _cle_canon(cible_avant)
                if cle in connus or cle in vus or _est_instance_connue(cible_avant, universels):
                    continue
                tac, cible = _composer_inclusions(T1, T2p, t, u, vp)
            except Exception:
                continue
            if tac.est_clos and tac.conclusion == cible:
                vus.add(cle)
                trouves.append(("incl.σ" if sig else "incl.", n1, n2, tac))
    return trouves


# ── Régime « ⇔ » ──────────────────────────────────────────────────────────────────────────────
def equivalences_de(preuve_de):
    """Extrait les théorèmes-ÉQUIVALENCE (A⇔B) du corpus : [(nom, thm, A, B)]."""
    out = []
    for c, (nom, thm) in preuve_de.items():
        ab = _comme_equiv(c)
        if ab and ab[0] != ab[1]:
            out.append((nom, thm, ab[0], ab[1]))
    return out


def chainer_equivalences(equivs, preuve_de):
    """Transitivité de l'ÉQUIVALENCE — débloque les CARACTÉRISATIONS. T1⊢A⇔B, T2⊢B'⇔C avec
    σ(B')=B → ⊢A⇔σ(C), dérivé en 8 pas noyau : projeter les deux sens (equivalence_avant/
    arriere), chaîner A⇒B⇒C et C⇒B⇒A (assume+MP+loi_deduction), recombiner (conjonction_intro)."""
    connus = {_cle_canon(c) for c in preuve_de}
    universels = universels_de(preuve_de)
    trouves, vus = [], set()
    for (n1, T1, A, B) in equivs:
        for (n2, T2, Bp, C) in equivs:
            if n2 == n1:
                continue
            s = {}
            if not _match(Bp, B, s, libres_f(T2.conclusion)):
                continue
            sig = {v: t for v, t in s.items() if t != var(v)}
            try:
                T2p = _instancier(T2, sig) if sig else T2
                ab = _comme_equiv(T2p.conclusion)
                if ab is None or ab[0] != B:
                    continue
                Cp = ab[1]
                if A == Cp:
                    continue
                cible = equiv(A, Cp)
                cle = _cle_canon(cible)
                if cle in connus or cle in vus or _est_instance_connue(cible, universels):
                    continue
                f1, f2 = equivalence_avant(T1), equivalence_avant(T2p)      # A⇒B, B⇒C
                fwd = N.loi_deduction(A, N.modus_ponens(N.modus_ponens(N.assume(A), f1), f2))
                b1, b2 = equivalence_arriere(T2p), equivalence_arriere(T1)  # C⇒B, B⇒A
                bwd = N.loi_deduction(Cp, N.modus_ponens(N.modus_ponens(N.assume(Cp), b1), b2))
                tac = conjonction_intro(fwd, bwd)                            # (A⇒C) et (C⇒A)
            except Exception:
                continue
            if tac.est_clos and tac.conclusion == cible:
                vus.add(cle)
                trouves.append(("equiv.σ" if sig else "equiv.", n1, n2, tac))
    return trouves
