"""Scan « axiomes jumeaux » — le détecteur d'incohérence par coïncidence.

────────────────────────────────────────────────────────────────────────────────
LA SIGNATURE CHERCHÉE.  Deux axiomes de théories dédiées **quasi identiques**
(cos ≥ θ) qui **caractérisent le MÊME terme** : c'est exactement la forme du
défaut `seg_ext` — deux ordres, un terme, donc deux axiomes contradictoires que
rien dans le noyau ne pouvait opposer, puisqu'ils vivaient dans deux théories.

⚠️ LA CONJONCTION EST ESSENTIELLE.  Le cosinus SEUL produit des faux positifs :
la plus haute similarité d'un balayage peut très bien lier deux axiomes qui
caractérisent des termes DIFFÉRENTS — structurellement jumeaux, sémantiquement
étrangers, aucune alarme à donner.  C'est le second membre (même terme) qui fait
du score un verdict.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST ÉCARTÉ, ET POURQUOI ON LE DIT.  Une théorie dédiée PARAMÉTRIQUE est
une fabrique : elle minte une théorie par jeu d'arguments, et il n'existe pas
d'axiome unique à vectoriser.  On ne peut donc pas la scanner — et elle est
précisément la classe à risque, une fabrique paramétrique étant le mécanisme même
qui a rendu `seg_ext` incohérent.  Les écarter EN SILENCE donnerait un balayage
qui a l'air complet ; on les compte et on les nomme.

Usage :  python outils_ia/vecteurs/scan_jumeaux.py [--theta 0.90] [--tout]
"""
from __future__ import annotations

import argparse
import ast
import importlib
import io
import os
import sys
import time

RACINE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if RACINE not in sys.path:
    sys.path.insert(0, RACINE)

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    Formule, Terme,
)
from outils_ia.vecteurs.phi_terme import (  # noqa: E402
    phi, sim, taille, enfants, BudgetDepasse, K_DEFAUT, D_DEFAUT,
)

THETA_DEFAUT = 0.90
#: au-delà de ce cosinus ET à terme caractérisé commun, on parle de JUMEAUX.
THETA_JUMEAU = 0.95


# ── 1. découverte des fabriques de théories, par AST (aucun import inutile) ──
def fabriques(racine_pkg="bourbaki"):
    """[(module, nom, parametrique)] pour chaque `def theorie_*` du corpus."""
    base = os.path.join(RACINE, racine_pkg)
    trouvees = []
    for dossier, _, fichiers in os.walk(base):
        if "__pycache__" in dossier:
            continue
        for f in fichiers:
            if not f.endswith(".py"):
                continue
            chemin = os.path.join(dossier, f)
            try:
                arbre = ast.parse(io.open(chemin, encoding="utf-8").read())
            except (SyntaxError, UnicodeDecodeError):
                continue
            for n in arbre.body:
                if not isinstance(n, ast.FunctionDef):
                    continue
                if not n.name.startswith("theorie_"):
                    continue
                a = n.args
                obligatoires = len(a.args) - len(a.defaults)
                mod = os.path.relpath(chemin, RACINE)[:-3].replace(os.sep, ".")
                trouvees.append((mod, n.name, obligatoires > 0))
    return sorted(set(trouvees))


# ── 2. le terme CARACTÉRISÉ par un axiome ────────────────────────────────────
def symboles_app(f, vus=None):
    """Noms des termes construits (`app`) apparaissant dans une formule."""
    vus = set() if vus is None else vus
    pile = [f]
    while pile:
        n = pile.pop()
        if isinstance(n, Terme) and n.tag == "app" and n.nom:
            vus.add(n.nom)
        pile.extend(enfants(n))
    return vus


def vocabulaire_de_base():
    """Les symboles déjà présents dans les 22 axiomes de référence : ils ne
    caractérisent rien de DÉDIÉ, donc ils ne peuvent pas servir d'appariement."""
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    commun = set()
    for ax in E.theorie_ensembles().axiomes:
        commun |= symboles_app(ax)
    return commun


def _sans_pourtout(f):
    """Dépile le préfixe (∀x) — encodé ¬(∃x)(¬…)."""
    while (isinstance(f, Formule) and f.tag == "non" and f.sous
           and f.sous[0].tag == "exists"):
        f = f.sous[0].sous[0].sous[0]
    return f


def _membre_gauche_equiv(f):
    """A, pour f = (A ⇔ B). L'équivalence est et(A⇒B, B⇒A), soit
    ¬( ¬(¬A ∨ B) ∨ ¬(¬B ∨ A) ) : cinq niveaux à dépiler."""
    try:
        if f.tag != "non":
            return None
        return f.sous[0].sous[0].sous[0].sous[0].sous[0]
    except (AttributeError, IndexError):
        return None


def terme_caracterise(ax, commun):
    """LE terme que l'axiome définit — pas ceux qu'il mentionne.

    🔴 DISTINCTION MESURÉE (5 août 2026).  Le premier critère écrit ici était
    « les symboles propres à l'axiome », et il produisait un FAUX POSITIF net :
    `axiome_majorants_F` (m ∈ U ⇔ (m ∈ [0,a] et …)) partage `interv_ent` avec
    `axiome_intervalle_entiers` (x ∈ [a,b] ⇔ …) — mais le premier ne fait que
    MENTIONNER l'intervalle dans son membre droit, tandis que le second le
    DÉFINIT.  Deux axiomes qui mentionnent un même terme ne sont pas en conflit ;
    deux axiomes qui le DÉFINISSENT le sont.

    Le définiendum est le membre GAUCHE de l'équivalence, sous la forme
    « x ∈ T(…) » : on rend le symbole de tête de T."""
    corps = _membre_gauche_equiv(_sans_pourtout(ax))
    if corps is None or getattr(corps, "tag", None) != "in":
        return set()
    cible = corps.termes[1]
    if isinstance(cible, Terme) and cible.tag == "app" and cible.nom \
            and cible.nom not in commun:
        return {cible.nom}
    return set()


# ── 3. le balayage ───────────────────────────────────────────────────────────
def collecte(verbeux=False):
    """(axiomes scannés, fabriques écartées, théories importables en échec)."""
    commun = vocabulaire_de_base()
    scannes, ecartees, echecs = [], [], []
    for mod, nom, parametrique in fabriques():
        if parametrique:
            ecartees.append(f"{mod}.{nom}")
            continue
        try:
            m = importlib.import_module(mod)
            th = getattr(m, nom)()
        except Exception as exc:                      # noqa: BLE001
            echecs.append(f"{mod}.{nom} ({type(exc).__name__})")
            continue
        for i, ax in enumerate(getattr(th, "axiomes", [])):
            if not isinstance(ax, Formule):
                continue
            try:
                v = phi(ax)
                n = taille(ax)
            except BudgetDepasse:
                echecs.append(f"{mod}.{nom}#{i} (garde anti-τ)")
                continue
            scannes.append({
                "theorie": getattr(th, "nom", nom), "fabrique": f"{mod}.{nom}",
                "index": i, "vecteur": v, "noeuds": n,
                "termes": terme_caracterise(ax, commun),
            })
            if verbeux:
                print(f"  · {nom}#{i} — {n} nœuds, "
                      f"termes {sorted(ax_t for ax_t in scannes[-1]['termes'])}")
    return scannes, ecartees, echecs


def paires(scannes, theta=THETA_DEFAUT):
    """Les paires au-dessus du seuil, triées par cosinus décroissant."""
    out = []
    for i in range(len(scannes)):
        for j in range(i + 1, len(scannes)):
            a, b = scannes[i], scannes[j]
            if a["fabrique"] == b["fabrique"] and a["index"] == b["index"]:
                continue
            c = sim(a["vecteur"], b["vecteur"])
            if c < theta:
                continue
            partages = a["termes"] & b["termes"]
            out.append({"a": a, "b": b, "cos": c, "partages": partages,
                        "jumeaux": c >= THETA_JUMEAU and bool(partages)})
    return sorted(out, key=lambda p: -p["cos"])


def rapport(theta=THETA_DEFAUT, verbeux=False):
    t0 = time.perf_counter()
    scannes, ecartees, echecs = collecte(verbeux)
    ps = paires(scannes, theta)
    dt = time.perf_counter() - t0
    theories = {s["fabrique"] for s in scannes}
    print(f"\nBALAYAGE — K={K_DEFAUT}, d={D_DEFAUT}, θ={theta}")
    print(f"  {len(scannes)} axiomes de {len(theories)} théories dédiées "
          f"vectorisés en {dt:.1f} s")
    print(f"  {len(ecartees)} fabriques paramétriques ÉCARTÉES "
          f"(non scannables — la classe à risque elle-même)")
    if echecs:
        print(f"  {len(echecs)} théories non mesurables : {echecs[:4]}")
    print(f"  {len(ps)} paires au-dessus du seuil")
    jum = [p for p in ps if p["jumeaux"]]
    print(f"  {len(jum)} JUMEAUX (cos ≥ {THETA_JUMEAU} ET terme partagé)\n")
    for p in ps[:12]:
        marque = "🔴 JUMEAUX" if p["jumeaux"] else "  (termes ≠)"
        print(f"  {p['cos']:.4f} {marque}  {p['a']['theorie']}#{p['a']['index']}"
              f"  ~  {p['b']['theorie']}#{p['b']['index']}"
              + (f"   partagent {sorted(p['partages'])}" if p["partages"] else ""))
    if ecartees and verbeux:
        print("\n  fabriques écartées :")
        for e in ecartees:
            print("   ·", e)
    return {"axiomes": len(scannes), "theories": len(theories),
            "ecartees": len(ecartees), "paires": len(ps), "jumeaux": len(jum),
            "secondes": dt, "echecs": len(echecs)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--theta", type=float, default=THETA_DEFAUT)
    ap.add_argument("--tout", action="store_true", help="détail par axiome")
    a = ap.parse_args()
    rapport(a.theta, a.tout)
