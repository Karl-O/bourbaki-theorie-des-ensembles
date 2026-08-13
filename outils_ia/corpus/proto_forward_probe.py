"""pas 40 — PROBE forward avec TACTIQUES PRODUCTRICES DE CONTENU (probe-first, borné).

Complète le scoping forward de pas 39 (qui n'avait testé QUE `conjonction_intro`, trivialement
recombinante A∧B). Ici : les tactiques de CONTENU avec type-matching strict —
  * composer_egalites(T=U, U=V) -> T=V          [maillon central U doit coïncider]
  * equivalence_transitivite(A⇔B, B⇔C) -> A⇔C   [maillon central B doit coïncider]
  * modus_ponens(R, R⇒S) -> S                    [antécédent doit coïncider]

Seeds = théorèmes CLOS prouvés des modules (getattr(mod,name)() -> Theoreme valide par construction).
On mesure, pour 1 pas forward :
  - attempts = paires ordonnées de seeds du bon type,
  - feasible = paires dont le type-matching (maillon/antécédent) coïncide -> tactique applicable,
  - success  = Theoreme renvoyé sans exception (== feasible attendu),
  - NON-TRIVIAL = conclusion nouvelle (≠ une conclusion déjà connue) et non dégénérée (T≠V).
Le branchement = feasible / attempts (sélectivité du type-matching), et le RENDEMENT non-trivial.

Question clé : forward-contenu trouve-t-il des faits non-triviaux à branchement TRACTABLE
(maillon-coïncidence prune fort -> peu mais utiles) OU erre-t-il (bcp de valides sans intérêt) ?

BORNÉ : PACKAGES rapides (pas cardinaux/entiers) ; pas de gros run ; O(n²) sur seeds typés (petit).
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

os.environ.setdefault("PYTHONIOENCODING", "utf-8")
ROOT = Path(__file__).resolve().parents[2]           # .../V9
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import importlib                                      # noqa: E402

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N          # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites  # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_transitivite  # noqa: E402
from export_corpus import _decouvrir               # noqa: E402

# logique + ensembles : domaine riche en égalités/équivalences/implications et RAPIDE.
# (ordre III.4/III.6/III.7 + structures : proofs lourdes à construire -> écartées du probe.)
PACKAGES_PROBE = ["bourbaki.i_description_mathematique_formelle", "bourbaki.ii_theorie_des_ensembles"]


# ── détecteurs de type de conclusion ─────────────────────────────────────────
def is_eq(f):
    return getattr(f, "tag", None) == "="

def impl_parts(f):
    """impl(A,B) = ou(non A, B) -> (A, B) sinon None."""
    if getattr(f, "tag", None) == "ou" and f.sous[0].tag == "non":
        return f.sous[0].sous[0], f.sous[1]
    return None

def _et_parts(f):
    """et(P,Q) = non(ou(non P, non Q)) -> (P, Q) sinon None."""
    if getattr(f, "tag", None) == "non" and f.sous[0].tag == "ou" \
            and f.sous[0].sous[0].tag == "non" and f.sous[0].sous[1].tag == "non":
        return f.sous[0].sous[0].sous[0], f.sous[0].sous[1].sous[0]
    return None

def equiv_parts(f):
    """equiv(A,B) = et(impl(A,B), impl(B,A)) -> (A, B) sinon None."""
    pq = _et_parts(f)
    if not pq:
        return None
    ip, iq = impl_parts(pq[0]), impl_parts(pq[1])
    if ip and iq and ip[0] == iq[1] and ip[1] == iq[0]:
        return ip[0], ip[1]
    return None


# ── collecte des seeds (théorèmes CLOS prouvés) ──────────────────────────────
def collect_seeds(modnames):
    seeds = []                                        # (modname, name, thm)
    for k, modname in enumerate(modnames):
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        before = len(seeds)
        for name in getattr(mod, "__all__", []):
            if name.endswith("_cible"):
                continue
            obj = getattr(mod, name, None)
            if not callable(obj):
                continue
            try:
                thm = obj()                            # appel sans args
            except Exception:
                continue
            if not hasattr(thm, "conclusion"):
                continue
            if getattr(thm, "hypotheses", None) and len(thm.hypotheses) > 0:
                continue                               # CLOS uniquement
            seeds.append((modname, name, thm))
        print(f"#   [{k+1}/{len(modnames)}] {modname.split('.')[-1]:<44} "
              f"+{len(seeds)-before} (tot {len(seeds)})", file=sys.stderr, flush=True)
    return seeds


def _key(f):
    return repr(f)                                     # Formule a __eq__ ; repr stable pour set


def probe(seeds):
    concls = {_key(t.conclusion) for _, _, t in seeds}
    eqs    = [(m, n, t) for (m, n, t) in seeds if is_eq(t.conclusion)]
    equivs = [(m, n, t) for (m, n, t) in seeds if equiv_parts(t.conclusion)]
    impls  = [(m, n, t) for (m, n, t) in seeds if impl_parts(t.conclusion)]
    facts  = seeds

    res = {}

    # 1) composer_egalites : (T=U, U=V) maillon U coïncide -> T=V
    att = feas = succ = nontriv = 0
    examples = []
    for i, (_, _, a) in enumerate(eqs):
        ta, ua = a.conclusion.termes
        for j, (_, _, b) in enumerate(eqs):
            if i == j:
                continue
            att += 1
            tb, vb = b.conclusion.termes
            if ua != tb:
                continue
            feas += 1
            try:
                out = composer_egalites(a, b)
            except Exception:
                continue
            succ += 1
            ck = _key(out.conclusion)
            t2, v2 = out.conclusion.termes
            if ck not in concls and t2 != v2:
                nontriv += 1
                if len(examples) < 6:
                    examples.append(repr(out.conclusion))
    res["composer_egalites"] = dict(pool=len(eqs), att=att, feas=feas, succ=succ,
                                    nontriv=nontriv, ex=examples)

    # 2) equivalence_transitivite : (A⇔B, B⇔C) maillon B coïncide -> A⇔C
    att = feas = succ = nontriv = 0
    examples = []
    for i, (_, _, a) in enumerate(equivs):
        Aa, Ba = equiv_parts(a.conclusion)
        for j, (_, _, b) in enumerate(equivs):
            if i == j:
                continue
            att += 1
            Bb, Cb = equiv_parts(b.conclusion)
            if Ba != Bb:
                continue
            feas += 1
            try:
                out = equivalence_transitivite(a, b)
            except Exception:
                continue
            succ += 1
            ck = _key(out.conclusion)
            ep = equiv_parts(out.conclusion)
            if ck not in concls and ep and ep[0] != ep[1]:
                nontriv += 1
                if len(examples) < 6:
                    examples.append(repr(out.conclusion))
    res["equivalence_transitivite"] = dict(pool=len(equivs), att=att, feas=feas, succ=succ,
                                           nontriv=nontriv, ex=examples)

    # 3) modus_ponens : (R, R⇒S) antécédent coïncide -> S
    att = feas = succ = nontriv = 0
    examples = []
    for (_, _, imp) in impls:
        ap = impl_parts(imp.conclusion)
        ante, cons = ap
        for (_, _, r) in facts:
            att += 1
            if r.conclusion != ante:
                continue
            feas += 1
            try:
                out = N.modus_ponens(r, imp)
            except Exception:
                continue
            succ += 1
            ck = _key(out.conclusion)
            if ck not in concls:
                nontriv += 1
                if len(examples) < 6:
                    examples.append(repr(out.conclusion))
    res["modus_ponens"] = dict(pool=len(impls), facts=len(facts), att=att, feas=feas,
                               succ=succ, nontriv=nontriv, ex=examples)
    return res, len(seeds), len(eqs), len(equivs), len(impls), len(concls)


def main():
    pkgs = PACKAGES_PROBE
    mods = _decouvrir(pkgs)
    print(f"# --discover : {len(mods)} modules sous {pkgs}", file=sys.stderr)
    seeds = collect_seeds(mods)
    res, ns, neq, neqv, nimp, ncon = probe(seeds)
    print(f"\n=== SEEDS (théorèmes CLOS prouvés) ===")
    print(f"seeds={ns}  conclusions distinctes={ncon}  "
          f"| égalités={neq}  équivalences={neqv}  implications={nimp}")
    print(f"\n=== 1 PAS FORWARD — tactiques de CONTENU (type-matching strict) ===")
    hdr = f"{'tactique':<26} {'pool':>5} {'attempts':>9} {'feasible':>9} {'success':>8} {'NON-TRIV':>9} {'branch f/a':>11}"
    print(hdr)
    print("-" * len(hdr))
    for name, d in res.items():
        att, feas = d["att"], d["feas"]
        br = (feas / att) if att else 0.0
        print(f"{name:<26} {d['pool']:>5} {att:>9} {feas:>9} {d['succ']:>8} "
              f"{d['nontriv']:>9} {br:>10.4%}")
    for name, d in res.items():
        if d["ex"]:
            print(f"\n# exemples NON-TRIVIAUX — {name} :")
            for e in d["ex"]:
                print(f"    {e[:160]}")

    if "--diag" in sys.argv:
        eqs    = [t for _, _, t in seeds if is_eq(t.conclusion)]
        impls  = [t for _, _, t in seeds if impl_parts(t.conclusion)]
        # combien de maillons (membre droit d'une égalité) réapparaissent comme membre gauche d'une autre ?
        gauche = {}
        droite = {}
        for t in eqs:
            l, r = t.conclusion.termes
            gauche.setdefault(repr(l), 0); gauche[repr(l)] += 1
            droite.setdefault(repr(r), 0); droite[repr(r)] += 1
        chevauchement = set(droite) & set(gauche)
        print(f"\n# DIAG composer_egalites : {len(eqs)} égalités | "
              f"membres-droits distincts={len(droite)} membres-gauches distincts={len(gauche)} "
              f"| chevauchement droite∩gauche={len(chevauchement)}")
        print("# échantillon d'égalités (membre_gauche  =  membre_droit) :")
        for t in eqs[:10]:
            l, r = t.conclusion.termes
            print(f"    {repr(l)[:70]:<72} = {repr(r)[:70]}")
        # antécédents d'implications vs conclusions disponibles
        antes = {repr(impl_parts(t.conclusion)[0]) for t in impls}
        conc  = {repr(t.conclusion) for _, _, t in seeds}
        print(f"\n# DIAG modus_ponens : {len(impls)} implications | "
              f"antécédents distincts={len(antes)} | "
              f"antécédents présents comme conclusion d'un seed={len(antes & conc)}")
        print("# échantillon d'antécédents d'implications :")
        for t in impls[:8]:
            a, _ = impl_parts(t.conclusion)
            print(f"    {repr(a)[:120]}")
    print()


if __name__ == "__main__":
    main()
