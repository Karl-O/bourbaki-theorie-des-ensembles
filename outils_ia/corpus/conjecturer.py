#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Conjectureur — trouve des problèmes (nouveaux théorèmes) & les résout, noyau seul juge (JALON 3+).

Réalise la vision « trouver des problèmes à des solutions » dans le seul régime qui FIRE (pas 39-41 :
le forward non guidé erre ; il faut un CONTEXTE À TERMES PARTAGÉS). Le terme partagé est explicite :
deux théorèmes CLOS `T1 ⊢ A⇒B` et `T2 ⊢ B⇒C` qui PARTAGENT B donnent la conjecture `A⇒C`, résolue
par le noyau seul (assume + 2×modus_ponens + loi_deduction). Sound par construction ; la DÉCOUVERTE
= l'énoncé est NOUVEAU (dédup α-canonique + subsomption) et non trivial. Frontière 22 intacte.

Ce module porte le moteur ⇒ (transitivité + détachement), l'itération en profondeur, la fécondité
et le CLI. Les briques pures sont dans `conj_base.py`, les régimes algébriques (=, ⇔, ⊂ + pont S6)
dans `conj_regimes.py` — TOUT est ré-exporté ici (API stable pour tests, tour, eval, catalogues).

USAGE : python outils_ia/corpus/conjecturer.py [package…] [--montre K] [--rounds N]
        [--fecondite | --egalites | --equivalences | --inclusions]
"""
from __future__ import annotations

import importlib
import sys
from collections import defaultdict
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from export_corpus import _decouvrir                            # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N   # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl, libres_f, var  # noqa: E402

# ── Ré-exports (API stable ; ne pas retirer : importés par tests/tour/eval/catalogues) ────────
from conj_base import (  # noqa: E402,F401
    PACKAGES, _match, _instancier, _comme_impl, _comme_egal, _comme_equiv, _comme_inclus,
    _tf, _fmt, _est_terme, _cle_canon, _taille, _apps, _interet,
    universels_de, _est_instance_connue)
from conj_regimes import (  # noqa: E402,F401
    egalites_de, chainer_egalites, iterer_egalites,
    inclusions_de, egal_vers_inclusions, pool_inclusions, chainer_inclusions,
    _composer_inclusions, equivalences_de, chainer_equivalences)
from conj_existe import chainer_existentiels  # noqa: E402,F401


def _corpus(packages):
    """Appelle chaque théorème tout-défaut ; renvoie (implications clos, {conclusion: théorème})."""
    impls, preuve_de = [], {}
    for modname in _decouvrir(packages):
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        for name in getattr(mod, "__all__", []):
            if name.endswith("_cible"):
                continue
            fn = getattr(mod, name, None)
            if not callable(fn):
                continue
            try:
                thm = fn()
            except Exception:
                continue
            if type(thm).__name__ != "Theoreme" or not getattr(thm, "est_clos", False):
                continue
            preuve_de.setdefault(thm.conclusion, (f"{modname.split('.')[-1]}.{name}", thm))
            ab = _comme_impl(thm.conclusion)
            if ab and ab[0] != ab[1]:
                impls.append((f"{modname.split('.')[-1]}.{name}", thm, ab[0], ab[1]))
    return impls, preuve_de


def conjecturer(impls, preuve_de, trace=None):
    """Deux moteurs guidés par TERME PARTAGÉ, matching RELÂCHÉ (unification σ), tranchés par le noyau,
    avec dédup α-CANONIQUE (les variantes à renommage près comptent pour UNE découverte) :
       · TRANSITIVITÉ : T1:A⇒B, T2:Bp⇒C avec σ(Bp)=B → A⇒σ(C) ;
       · DÉTACHEMENT  : T:A⇒B et K⊢φ avec σ(A)=φ → σ(B).
    `trace` (optionnel) : callable(dict) appelé AU FIL DE L'EAU — un événement par
    implication-source traitée et par découverte certifiée. Un long run n'est plus
    une boîte noire (demande Karl, 8 août 2026)."""
    connus_canon = {_cle_canon(c) for c in preuve_de}
    connaissables = list(preuve_de.items())          # (conclusion φ, (nomK, K))
    trouves, vus = [], set()
    if trace:
        trace({"type": "conjecturer", "impls": len(impls), "faits": len(preuve_de)})
    for ki, (nom1, T1, A, B) in enumerate(impls):
        # DÉTACHEMENT relâché : une conclusion connue φ s'unifie-t-elle à l'antécédent A ?
        vlib1 = libres_f(T1.conclusion)
        for (phi, (nomK, K)) in connaissables:
            s = {}
            if not _match(A, phi, s, vlib1):
                continue
            sig = {k: t for k, t in s.items() if t != var(k)}
            try:
                T1p = _instancier(T1, sig) if sig else T1
                ab = _comme_impl(T1p.conclusion)
                if ab is None or ab[0] != phi:
                    continue
                tB = N.modus_ponens(K, T1p)
                cle = _cle_canon(tB.conclusion)
                if tB.conclusion == phi or cle in connus_canon or cle in vus:
                    continue
            except Exception:
                continue
            if tB.est_clos:
                vus.add(cle)
                m = "détach.σ" if sig else "détach."
                trouves.append((m, nomK, nom1, tB))
                if trace:
                    trace({"type": "découverte", "mode": m, "via": f"{nomK} + {nom1}",
                           "concl": _fmt(tB.conclusion)[:150]})

        # TRANSITIVITÉ relâchée : tout T2:Bp⇒C dont l'antécédent Bp s'unifie à B.
        for (nom2, T2, Bp, C) in impls:
            if nom2 == nom1:
                continue
            s = {}
            if not _match(Bp, B, s, libres_f(T2.conclusion)):
                continue
            sig = {k: t for k, t in s.items() if t != var(k)}
            try:
                T2p = _instancier(T2, sig) if sig else T2
                ab = _comme_impl(T2p.conclusion)
                if ab is None or ab[0] != B:
                    continue
                Cp = ab[1]
                if A == Cp:
                    continue
                cible = impl(A, Cp)
                cle = _cle_canon(cible)
                if cle in connus_canon or cle in vus:
                    continue
                tC = N.modus_ponens(N.modus_ponens(N.assume(A), T1), T2p)
                tAC = N.loi_deduction(A, tC)
            except Exception:
                continue
            if tAC.est_clos and tAC.conclusion == cible:
                vus.add(cle)
                m = "transit.σ" if sig else "transit."
                trouves.append((m, nom1, nom2, tAC))
                if trace:
                    trace({"type": "découverte", "mode": m, "via": f"{nom1} + {nom2}",
                           "concl": _fmt(tAC.conclusion)[:150]})
        if trace:
            trace({"type": "avancement", "impl": ki + 1, "n": len(impls),
                   "src": nom1, "cumul": len(trouves)})
    return trouves


def _profond(s1, s2):
    """Vrai si la découverte CHAÎNE sur une découverte d'un tour précédent (brique « D/E<t>#… »)."""
    return any(s[0] in "DE" and "#" in s for s in (s1, s2))


def iterer(impls, preuve_de, rounds=2, garder=15, trace=None, cap_brique=None):
    """Conjecture ITÉRÉE (compounding de découverte) : les théorèmes trouvés au tour t deviennent des
    BRIQUES du tour t+1 → on atteint des théorèmes de profondeur croissante, inaccessibles en un tour.

    Renvoie (tous, par_tour) ; par_tour[t] = découvertes du tour t (nouvelles vs tous les tours ≤ t,
    dédup α-canonique assurée en agrandissant `connus`). Les briques issues d'un tour t sont nommées
    « D<t>#k » → `_profond` détecte les découvertes de profondeur ≥ 2."""
    pool, connus = list(impls), dict(preuve_de)
    par_tour, tous = [], []
    for t in range(rounds):
        if trace:
            trace({"type": "tour", "t": t + 1, "rounds": rounds, "pool": len(pool)})
        d = conjecturer(pool, connus, trace)
        par_tour.append(d)
        tous.extend(d)
        if trace:
            trace({"type": "fin_tour", "t": t + 1, "neufs": len(d), "cumul": len(tous)})
        if not d or t == rounds - 1:
            break
        for k, (_, _, _, thm) in enumerate(d):                 # dédup au tour suivant
            connus.setdefault(thm.conclusion, (f"D{t + 1}#{k}", thm))
        briques = [(m, s1, s2, thm) for (m, s1, s2, thm) in d
                   if _comme_impl(thm.conclusion) is not None]
        # cap_brique : une brique GÉANTE réinjectée empoisonne le matching des
        # tours suivants (le coût croît avec la TAILLE des formules du pool —
        # 3h20 mesurées dans la nuit du 8 août). On saute, et on le DIT.
        if cap_brique:
            avant = len(briques)
            briques = [x for x in briques if _taille(x[3].conclusion) <= cap_brique]
            if trace and len(briques) < avant:
                trace({"type": "briques_sautées", "t": t + 1, "cap": cap_brique,
                       "sautées": avant - len(briques)})
        briques.sort(key=lambda x: _interet(*x), reverse=True)  # ne réinjecter que les meilleures
        for k, (_, _, _, thm) in enumerate(briques[:garder]):
            ab = _comme_impl(thm.conclusion)
            pool.append((f"D{t + 1}#{k}", thm, ab[0], ab[1]))
    return tous, par_tour


# fécondité : extraite dans conj_fecondite.py (discipline ≤300, 8 août 2026) ;
# ré-export ici pour les consommateurs historiques (tests, eval).
from conj_fecondite import fecondite, _rapport_fecondite              # noqa: E402,F401


def main(argv):
    rest = argv[1:]
    montre = 12
    rounds = 1
    for flag, dv in (("--montre", None), ("--rounds", None)):
        if flag in rest:
            i = rest.index(flag)
            val = int(rest[i + 1])
            rest = rest[:i] + rest[i + 2:]
            if flag == "--montre":
                montre = val
            else:
                rounds = val
    packages = [a for a in rest if not a.startswith("--")] or PACKAGES

    print("# CONJECTUREUR (transitivité + détachement, matching σ) — trouver & résoudre des problèmes",
          file=sys.stderr)
    impls, preuve_de = _corpus(packages)
    print(f"# corpus : {len(preuve_de)} théorèmes clos connus, dont {len(impls)} implications A⇒B")

    if "--fecondite" in rest:
        return _rapport_fecondite(impls, preuve_de, montre)

    if "--egalites" in rest:
        tous, par_tour = iterer_egalites(preuve_de, rounds=max(rounds, 1))
        print(f"# AMÉLIORATION : chaînage des ÉGALITÉS (itéré) — "
              f"{len(egalites_de(preuve_de))} égalités-corpus")
        for t, d in enumerate(par_tour):
            prof = sum(1 for (_, s1, s2, _) in d if _profond(s1, s2))
            print(f"# tour {t + 1} : {len(d)} identités nouvelles"
                  + (f" (dont {prof} de profondeur ≥2)" if t > 0 else ""))
        n_cross = sum(1 for (m, s1, s2, _) in tous if s1.split(".")[0] != s2.split(".")[0])
        print(f"# → {len(tous)} NOUVELLES égalités certifiées (noyau), {n_cross} ponts :\n")
        for (mode, s1, s2, thm) in sorted(tous, key=lambda t: _interet(*t), reverse=True)[:montre]:
            st = _fmt(thm.conclusion)
            print(f"■ [{mode}] {st[:150] + '…' if len(st) > 150 else st}   [{s1} ∘ {s2}]")
        return 0

    if "--inclusions" in rest:
        egal_disc, _ = iterer_egalites(preuve_de, rounds=2)
        incls, n_corpus, n_pont = pool_inclusions(preuve_de, egal_disc)
        trouves = chainer_inclusions(incls, preuve_de)
        n_via_pont = sum(1 for (_, s1, s2, _) in trouves
                         if s1.startswith("pont:") or s2.startswith("pont:"))
        print(f"# RÉGIME 4 : chaînage des INCLUSIONS — {n_corpus} ⊂-corpus + {n_pont} dérivées"
              f" des égalités (pont S6)")
        print(f"# → {len(trouves)} NOUVELLES inclusions certifiées (noyau), "
              f"dont {n_via_pont} via le pont =→⊂ :\n")
        for (mode, s1, s2, thm) in sorted(trouves, key=lambda t: _interet(*t), reverse=True)[:montre]:
            st = _fmt(thm.conclusion)
            print(f"■ [{mode}] {st[:150] + '…' if len(st) > 150 else st}   [{s1} ∘ {s2}]")
        if not trouves:
            print("# (aucune — le pool ⊂ clos est mince ; le pont dépend des égalités disponibles)")
        return 0

    if "--existentiels" in rest:
        trouves = chainer_existentiels(preuve_de)
        print(f"# RÉGIME 5 : ∃-INTRO par témoin (S5) — abstraction des sous-termes récurrents")
        print(f"# → {len(trouves)} NOUVEAUX théorèmes existentiels certifiés (noyau) :\n")
        for (mode, src, temoin, thm) in trouves[:montre]:
            st = _fmt(thm.conclusion)
            print(f"■ [{mode}] {st[:140] + '…' if len(st) > 140 else st}")
            print(f"    depuis {src} ; {temoin}   (⊢ clos, {len(thm.hypotheses)} hyp)")
        if not trouves:
            print("# (aucun — pas de sous-terme composite récurrent non subsumé)")
        return 0

    if "--equivalences" in rest:
        eqs = equivalences_de(preuve_de)
        trouves = chainer_equivalences(eqs, preuve_de)
        print(f"# AMÉLIORATION 2 : chaînage des ÉQUIVALENCES — {len(eqs)} théorèmes-⇔ dans le corpus")
        print(f"# → {len(trouves)} NOUVELLES équivalences certifiées (noyau) :\n")
        for (mode, s1, s2, thm) in sorted(trouves, key=lambda t: _interet(*t), reverse=True)[:montre]:
            st = _fmt(thm.conclusion)
            print(f"■ [{mode}] {st[:150] + '…' if len(st) > 150 else st}   [{s1} ∘ {s2}]")
        if not trouves:
            print("# (aucune — soit peu de ⇔ clos exposés tout-défaut, soit pas de maillon partagé)")
        return 0

    if rounds > 1:
        trouves, par_tour = iterer(impls, preuve_de, rounds=rounds)
        for t, d in enumerate(par_tour):
            prof = sum(1 for (_, s1, s2, _) in d if _profond(s1, s2))
            print(f"# tour {t + 1} : {len(d)} découvertes"
                  + (f" (dont {prof} de PROFONDEUR ≥2 — chaînent une découverte du tour précédent)"
                     if t > 0 else ""))
    else:
        trouves = conjecturer(impls, preuve_de)
    n_det = sum(1 for t in trouves if t[0].startswith("détach"))
    n_tr = sum(1 for t in trouves if t[0].startswith("transit"))
    n_cross = sum(1 for (m, s1, s2, _) in trouves if s1.split(".")[0] != s2.split(".")[0])
    # TRI par intérêt : pont inter-modules, puis distinctness antécédent/conséquent, puis parcimonie
    classe = sorted(trouves, key=lambda t: _interet(*t), reverse=True)
    print(f"# {len(trouves)} NOUVEAUX théorèmes certifiés (dédup α-canonique) — {n_det} détachement, "
          f"{n_tr} transitivité ; {n_cross} PONTS inter-modules.")
    print(f"# top {min(montre, len(classe))} par INTÉRÊT (pont inter-modules · symboles disjoints · parcimonie) :\n")
    for (mode, s1, s2, thm) in classe[:montre]:
        cross, pont, negt = _interet(mode, s1, s2, thm)
        concl = _fmt(thm.conclusion)
        if len(concl) > 150:
            concl = concl[:147] + "…"
        lien = f"{s1} ⊢A · {s2}:A⇒B" if mode.startswith("détach") else f"{s1} ∘ {s2}"
        etoile = "★" if cross else " "
        print(f"■{etoile}[{mode}] pont={pont} taille={-negt}  {concl}")
        print(f"    {lien}   (⊢ clos, {len(thm.hypotheses)} hyp)")
    if trouves:
        print(f"\n# = problème TROUVÉ par terme partagé (à σ près) + SOLU par le noyau.")
        print(f"# Chacun CLOS, certifié, absent du corpus — frontière 22 axiomes intacte.")
    else:
        print("# (aucun ce tour)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
