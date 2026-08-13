#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""INVENTER DES DÉFINITIONS — miner les ÉNONCÉS, pas le code.

LE MANQUE QUE CET ORGANE COMBLE. Tous les organes du projet MANIPULENT des
notions existantes : ils chaînent, réécrivent, instancient, proposent des
témoins. Aucun n'en CRÉE. Or l'histoire des mathématiques est en grande partie
une histoire de définitions — groupe, idéal, faisceau. Chaque fois, le théorème
devient facile *après* que la bonne notion a été posée.

⚠️ CE N'EST PAS `antiunif_notions.py`. Celui-là anti-unifie l'**AST Python**
des scripts de preuve : il abstrait le CODE. Ici on mine les **énoncés** — les
formules elles-mêmes. Deux organes, deux signaux distincts, à ne pas confondre.

LE CRITÈRE, ET IL EST MESURABLE. Une notion est bonne si elle **comprime** le
corpus. On compte les sous-formules récurrentes, à renommage de variables près,
et l'on score chacune par son gain MDL :

    gain = (occurrences − 1) × taille

c'est-à-dire ce qu'on économise en écrivant le nom plutôt que la formule. Une
sous-formule vue une seule fois a un gain nul : nommer un cas particulier
n'apprend rien.

LA CIBLE DE VALIDATION. `premier_ent(x) := Fini(x) ∧ est_premier(x)` a été
posée À LA MAIN le 10 août, après l'audit de fidélité. Si cet organe la remonte
en tête sans qu'on lui dise rien, il fait bien ce qu'on attend de lui. C'est un
test qu'on peut perdre — ce qui en fait un test.

⚠️ IL NE PROMEUT RIEN TOUT SEUL. Cet organe PROPOSE ; la promotion en notion du
dépôt reste une décision humaine, et le noyau reste seul juge des théorèmes qui
l'utiliseront. Aucun `Theoreme` ne sort d'ici.

⚠️ DETTE DE RANGEMENT, signalée et non masquée : `outils_ia/corpus/` compte
déjà 57 entrées pour une convention de projet à 10. Ce fichier y va parce que
c'est sa place sémantique (minage de corpus), pas parce que la règle est
respectée. L'éclatement de ce dossier est une dette antérieure.
"""
from __future__ import annotations

import sys

#: taille minimale d'une sous-formule pour être candidate — en deçà, nommer
#: coûte plus cher que d'écrire (un atome n'est pas une notion)
TAILLE_MINI = 4


def taille(f):
    """Le nombre de nœuds de la formule — sa longueur d'écriture."""
    n = 1
    for c in _enfants(f):
        n += taille(c)
    return n


def _enfants(f):
    return (list(getattr(f, "sous", ()) or ())
            + list(getattr(f, "termes", ()) or ()))


def abreviation(f):
    """Reconnaît une ABRÉVIATION et rend (nom, enfants sémantiques), ou `None`.

    ⚠️ POURQUOI C'EST INDISPENSABLE — défaut mesuré à la première version.
    Dans ce langage, `et(a,b)` vaut `¬(¬a ∨ ¬b)`, `impl(a,b)` vaut `¬a ∨ b`,
    `pourtout(x,F)` vaut `¬∃x¬F`. Miner les sous-formules BRUTES revient donc
    à compter massivement des nœuds intermédiaires — `¬a`, `¬a ∨ ¬b` — qui ne
    sont des formules pour personne. La première version remontait exactement
    ça : des blobs `¬¬(¬… ∨ ¬…)` de 60 nœuds vus 24 fois. Des échafaudages,
    pas des notions.

    On ne descend donc QUE dans les enfants sémantiques."""
    tag = getattr(f, "tag", None)
    sous = list(getattr(f, "sous", ()) or ())
    if tag == "non" and sous:
        c = sous[0]
        ct = getattr(c, "tag", None)
        cs = list(getattr(c, "sous", ()) or ())
        if ct == "ou" and len(cs) == 2                 and getattr(cs[0], "tag", None) == "non"                 and getattr(cs[1], "tag", None) == "non":
            return "et", [cs[0].sous[0], cs[1].sous[0]]        # ¬(¬a ∨ ¬b)
        if ct == "exists" and cs and getattr(cs[0], "tag", None) == "non":
            return "pourtout", [cs[0].sous[0]]                 # ¬∃x¬F
    if tag == "ou" and len(sous) == 2 and getattr(sous[0], "tag", None) == "non":
        return "impl", [sous[0].sous[0], sous[1]]              # ¬a ∨ b
    return None


def sous_formules(f, vues=None):
    """Les sous-formules SIGNIFIANTES de `f` — jamais les entrailles d'une
    abréviation, jamais les termes."""
    vues = vues if vues is not None else []
    tag = getattr(f, "tag", None)
    abrev = abreviation(f)
    if abrev is not None or tag in ("exists", "=", "in", "non"):
        if f not in vues:
            vues.append(f)
    enfants = abrev[1] if abrev is not None else _enfants(f)
    for c in enfants:
        if getattr(c, "tag", None) is not None:
            sous_formules(c, vues)
    return vues


def normalise(f):
    """La formule à RENOMMAGE PRÈS de ses variables libres.

    Sans ça, `Fini(p) ∧ premier(p)` et `Fini(q) ∧ premier(q)` compteraient pour
    deux notions différentes. Les noms sont canonisés par ordre alphabétique —
    arbitraire, mais déterministe, ce qui suffit pour compter."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f, subst_f, var,
    )
    for i, nom in enumerate(sorted(libres_f(f))):
        f = subst_f(var("_v%d" % i), nom, f)
    return f


def candidates(enonces, mini=TAILLE_MINI, top=12):
    """→ [(gain, occurrences, taille, formule_normalisée)] du meilleur au pire.

    `enonces` : les conclusions des théorèmes du corpus. Le gain est le nombre
    de nœuds économisés en nommant la sous-formule plutôt qu'en la réécrivant."""
    compte, repres = {}, {}
    for e in enonces:
        for sf in sous_formules(e):
            if taille(sf) < mini:
                continue
            try:
                cle = normalise(sf)
            except Exception:                          # noqa: BLE001
                continue                               # hors fragment : on passe
            compte[cle] = compte.get(cle, 0) + 1
            repres.setdefault(cle, sf)
    out = []
    for cle, n in compte.items():
        if n < 2:
            continue                                   # vu une fois : gain nul
        t = taille(cle)
        out.append(((n - 1) * t, n, t, cle))
    out.sort(key=lambda x: -x[0])
    return out[:top]


def corpus_recherche():
    """Les conclusions des théorèmes de `recherche/` — le corpus à miner.

    On n'appelle QUE les constructeurs sans argument obligatoire : les autres
    exigent des termes qu'on ne saurait pas fournir. Un constructeur qui lève
    est ignoré, pas masqué — il n'apporte simplement pas d'énoncé."""
    import importlib
    import inspect
    enonces, sources = [], []
    modules = ["recherche.goldbach.composes", "recherche.goldbach.synthese",
               "recherche.goldbach.symetrie", "recherche.goldbach.crible",
               "recherche.goldbach.audit_fidelite", "recherche.additif.crible_abstrait"]
    for nom_mod in modules:
        try:
            mod = importlib.import_module(nom_mod)
        except Exception:                              # noqa: BLE001
            continue
        for nom in getattr(mod, "__all__", ()):
            obj = getattr(mod, nom, None)
            if not inspect.isfunction(obj):
                continue
            params = inspect.signature(obj).parameters
            if any(p.default is inspect.Parameter.empty for p in params.values()):
                continue
            try:
                r = obj()
            except Exception:                          # noqa: BLE001
                continue
            for th in (r if isinstance(r, tuple) else (r,)):
                ccl = getattr(th, "conclusion", th)
                if getattr(ccl, "tag", None) is not None:
                    enonces.append(ccl)
                    sources.append("%s.%s" % (nom_mod.split(".")[-1], nom))
    return enonces, sources


def _texte(f, prof=0):
    """Une lecture COMPACTE de la formule — jamais `str()` sur un τ-terme.

    ⚠️ Le `__repr__` récursif des τ-termes explose en MemoryError (piège
    mesuré du projet). On imprime la STRUCTURE, et l'on nomme les termes par
    leur taille plutôt que par leur contenu."""
    tag = getattr(f, "tag", None)
    if tag is None:
        return "?"
    if prof > 4:
        return "…"
    abrev = abreviation(f)
    if abrev is not None:
        e = [_texte(c, prof + 1) for c in abrev[1]]
        if abrev[0] == "et":
            return "(%s ∧ %s)" % (e[0], e[1])
        if abrev[0] == "impl":
            return "(%s ⇒ %s)" % (e[0], e[1])
        return "∀%s %s" % (getattr(f.sous[0], "lieur", "?"), e[0])
    if tag == "tau":
        return "τ[%d]" % taille(f)
    if tag == "var":
        return getattr(f, "nom", "?")
    enfants = [_texte(c, prof + 1) for c in _enfants(f)]
    if tag == "non":
        return "¬" + enfants[0]
    if tag == "ou":
        return "(%s ∨ %s)" % (enfants[0], enfants[1])
    if tag == "exists":
        return "∃%s %s" % (getattr(f, "lieur", "?"), enfants[0])
    if tag == "=":
        return "(%s = %s)" % (enfants[0], enfants[1])
    if tag == "in":
        return "(%s ∈ %s)" % (enfants[0], enfants[1])
    return "%s(%s)" % (tag, ", ".join(enfants))


def main():
    enonces, sources = corpus_recherche()
    print("=" * 78, flush=True)
    print(" NOTIONS CANDIDATES — sous-formules récurrentes du corpus recherche/",
          flush=True)
    print("=" * 78, flush=True)
    print(" corpus : %d énoncés" % len(enonces), flush=True)
    for s in sorted(set(sources)):
        print("   ·", s, flush=True)
    print("-" * 78, flush=True)
    print(" %5s %4s %5s  %s" % ("gain", "occ", "noeud", "notion"), flush=True)
    for (gain, n, t, cle) in candidates(enonces):
        texte = _texte(cle)
        print(" %5d %4d %5d  %s" % (gain, n, t, texte), flush=True)
    print("-" * 78, flush=True)
    print(" RAPPEL : cet organe PROPOSE. Il ne promeut rien, ne démontre rien,",
          "\n et ne produit aucun Theoreme.", flush=True)
    return 0


__all__ = ["TAILLE_MINI", "taille", "sous_formules", "normalise", "candidates",
           "corpus_recherche"]


if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(64 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
