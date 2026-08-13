#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Régime 5 du conjectureur — ∃-INTRO par témoin (S5) : le dernier régime accessible du langage.

Le stress-test avait classé les existentiels « hors de portée (exige un témoin) ». Le cas SOLUBLE
est le sens inverse : le témoin est DÉJÀ là. De `⊢ φ(t)` clos (le corpus), on ABSTRAIT un
sous-terme composite t (via un x frais) et on dérive `⊢ (∃x) φ(x)` en UN pas noyau :

    R = φ[t→x]  ;  N.modus_ponens(⊢φ, N.s5(R, t, x))     # S5 : ⊢ (t|x)R ⇒ (∃x)R

Sound par construction : le noyau recalcule (t|x)R et vérifie qu'il coïncide avec φ (un mauvais
choix d'abstraction — capture, occurrence liée — fait échouer le MP, jamais un faux théorème).
ANTI-BRUIT : on n'abstrait que les sous-termes composites apparaissant ≥ min_occ fois (« le même
objet joue plusieurs rôles » = contenu), dédup α-canonique + filtre de subsomption + cap par
théorème. Frontière 22 axiomes intacte.
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

from conj_base import (_est_terme, _cle_canon, _taille,               # noqa: E402
                       universels_de, _est_instance_connue)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N   # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (           # noqa: E402
    Formule, Terme, existe, libres_f, var)


# ══════════════════════════════════════════════════════════════════════════════
#  STRUCTURE PARTAGÉE (leçon ev.277, 6 août 2026).  Les numéraux du corpus ne
#  sont praticables QUE par le partage des sous-termes : somme_num(2,2) DÉPLIÉ
#  dépasse 400 000 nœuds alors que son DAG en compte quelques centaines.  La
#  première version de cet organe dépliait partout (_cle_canon en chaînes,
#  recensement récursif, _abstraire sans mémo) et mourait en MemoryError sur le
#  premier fait arithmétique.  Tout ici est donc id-mémoïsé sur le DAG.
# ══════════════════════════════════════════════════════════════════════════════
import hashlib


def _enfants(f):
    if _est_terme(f):
        return f.args if f.tag != "var" else ()
    return tuple(f.termes) + tuple(f.sous)


def _taille_dag(f, _memo=None):
    """Nœuds DISTINCTS du DAG (le partage compte UNE fois) — id-mémoïsé, linéaire."""
    if _memo is None:
        _memo = set()
    if id(f) in _memo:
        return 0
    _memo.add(id(f))
    return 1 + sum(_taille_dag(c, _memo) for c in _enfants(f))


def _hash_dag(f, _memo=None):
    """Clé de dédup : blake2b structurel sur le DAG, id-mémoïsé.

    ⚠️ NON α-canonique (les lieurs entrent par leur NOM) : deux α-variantes
    peuvent coûter une découverte redondante — la soundness n'est pas concernée
    (même philosophie que `_est_instance_connue`).  En échange : coût linéaire en
    DAG là où `_cle_canon` explosait en dépliage.  blake2b et non `hash()`, dont
    la randomisation par process rendrait la dédup irreproductible."""
    if _memo is None:
        _memo = {}
    r = _memo.get(id(f))
    if r is not None:
        return r
    h = hashlib.blake2b(digest_size=16)
    if _est_terme(f):
        h.update(("T:%s:%s:%s(" % (f.tag, f.nom, f.lieur)).encode())
    else:
        h.update(("F:%s:%s(" % (f.tag, f.lieur)).encode())
    for c in _enfants(f):
        h.update(_hash_dag(c, _memo))
    r = h.digest()
    _memo[id(f)] = r
    return r


def _occurrences_depliees(racine):
    """occ[t] = nombre d'occurrences DÉPLIÉES de chaque sous-terme composite,
    calculé en temps DAG : chemins(enfant) += chemins(parent) × multiplicité.

    Kahn sur le DAG (parents traités avant enfants), agrégation par clé
    `_hash_dag` (deux objets structurellement égaux comptent ensemble, que
    l'interning les partage ou non).  Rend {clé: (représentant, compte)}."""
    hmemo = {}
    enfants_de, indeg, objets = {}, {}, {id(racine): racine}
    pile, vus = [racine], set()
    while pile:
        f = pile.pop()
        if id(f) in vus:
            continue
        vus.add(id(f))
        cs = _enfants(f)
        enfants_de[id(f)] = cs
        for c in cs:
            objets[id(c)] = c
            indeg[id(c)] = indeg.get(id(c), 0) + 1
            if id(c) not in vus:
                pile.append(c)
    chemins = {id(racine): 1}
    file_ = [racine]
    occ = {}
    while file_:
        f = file_.pop()
        n = chemins.get(id(f), 0)
        # ⚠️ les τ-termes sont CANDIDATS (les numéraux en sont — sans eux, la
        # 1re passe du sélectif n'a jamais pu viser N3 : app seulement, mesuré).
        if _est_terme(f) and f.tag in ("app", "tau"):
            cle = _hash_dag(f, hmemo)
            rep, tot = occ.get(cle, (f, 0))
            occ[cle] = (rep, tot + n)
        for c in enfants_de.get(id(f), ()):
            chemins[id(c)] = chemins.get(id(c), 0) + n
            indeg[id(c)] -= 1
            if indeg[id(c)] == 0:
                file_.append(objets[id(c)])
    return occ


def _sous_termes(f, acc):
    """Compte les sous-termes COMPOSITES (app) d'une formule/terme — candidats à l'abstraction."""
    if _est_terme(f):
        if f.tag == "app":
            acc[f] = acc.get(f, 0) + 1
        if f.tag != "var":
            for a in f.args:
                _sous_termes(a, acc)
    else:
        for tm in f.termes:
            _sous_termes(tm, acc)
        for s in f.sous:
            _sous_termes(s, acc)
    return acc


def _abstraire(f, t, x, _memo=None):
    """Reconstruit f en remplaçant chaque occurrence du terme t par var(x). Pur/structurel :
    la validité du choix (capture, occurrences sous liant) est tranchée par le noyau (S5+MP).

    ⚠️ id-mémoïsé : sans le mémo, la reconstruction DÉPLIE le partage et devient
    exponentielle sur les numéraux (leçon ev.277) — et détruit au passage le
    partage du résultat, que le noyau paie ensuite."""
    if _memo is None:
        _memo = {}
    r = _memo.get(id(f))
    if r is not None:
        return r
    if _est_terme(f):
        if f == t:
            r = var(x)
        elif f.tag == "var":
            r = f
        else:
            r = Terme(f.tag, nom=f.nom, lieur=f.lieur,
                      args=tuple(_abstraire(a, t, x, _memo) for a in f.args))
    else:
        r = Formule(f.tag, lieur=f.lieur,
                    termes=tuple(_abstraire(a, t, x, _memo) for a in f.termes),
                    sous=tuple(_abstraire(s, t, x, _memo) for s in f.sous))
    _memo[id(f)] = r
    return r


def _frais(f):
    """Un nom de variable frais pour f (xk ∉ libres)."""
    libres = libres_f(f)
    k = 0
    while f"x{k}" in libres:
        k += 1
    return f"x{k}"


def chainer_existentiels(preuve_de, min_occ=2, cap_par_thm=3, budget_dag=200_000,
                         sautes=None):
    """∃-intro guidée : pour chaque ⊢φ clos, abstraire les sous-termes composites apparaissant
    ≥ min_occ fois (compte DÉPLIÉ, calculé en temps DAG) → ⊢(∃x)φ[t→x].
    Renvoie [(mode, source, descr(t), thm)] certifiés.

    `budget_dag` : garde de taille (nœuds DISTINCTS) au-delà de laquelle un fait
    est SAUTÉ — et rapporté dans la liste `sautes` si fournie, jamais en silence
    (un organe qui tronque sans le dire fabrique des « couvert » mensongers).
    Dédup par `_hash_dag` (non α-canonique, cf. sa docstring) : blake2b sur le
    DAG partagé, là où l'ancienne clé-chaîne mourait en MemoryError (ev.277)."""
    hmemo = {}
    connus = {_hash_dag(c, hmemo) for c in preuve_de if hasattr(c, "tag")}
    universels = universels_de(preuve_de)
    trouves, vus = [], set()
    for concl, (nom, thm) in preuve_de.items():
        if not hasattr(concl, "tag"):
            continue                                   # Assemblage : hors couche abrégée
        n_dag = _taille_dag(concl)
        if n_dag > budget_dag:
            if sautes is not None:
                sautes.append((nom, n_dag))
            continue
        occ = _occurrences_depliees(concl)
        cands = [(rep, n) for (rep, n) in occ.values() if n >= min_occ]
        cands.sort(key=lambda tn: (-tn[1], -_taille_dag(tn[0])))   # fréquent puis gros
        pris = 0
        for (t, _n) in cands:
            if pris >= cap_par_thm:
                break
            x = _frais(concl)
            R = _abstraire(concl, t, x)
            if R == concl:                             # rien d'abstrait (t sous τ uniquement…)
                continue
            cible = existe(x, R)
            cle = _hash_dag(cible, hmemo)
            if cle in connus or cle in vus or _est_instance_connue(cible, universels):
                continue
            try:
                tac = N.modus_ponens(thm, N.s5(R, t, x))   # ⊢ (∃x)R — S5 vérifie (t|x)R == φ
            except Exception:
                continue
            if tac.est_clos and tac.conclusion == cible:
                vus.add(cle)
                pris += 1
                trouves.append(("∃-intro", nom, f"t={_court(t)}", tac))
    return trouves


def _court(t):
    """Description bornée d'un terme SANS repr (qui déplierait le partage)."""
    return "%s/%s·%d nœuds-dag" % (t.tag, t.nom or t.lieur or "-", _taille_dag(t))


# ══════════════════════════════════════════════════════════════════════════════
#  DÉTACHEMENT CONJONCTIF (6 août 2026) — l'organe qui a permis à la machine de
#  REDÉMONTRER Goldbach(6) en consommant sa propre invention (pair(N6), ev.286).
#
#  Le détachement σ du conjectureur matche l'antécédent EN BLOC contre UN fait ;
#  or les antécédents réels sont des CONJONCTIONS (celui du Goldbach borné en a
#  cinq).  Ici : décomposer l'antécédent, chercher CHAQUE conjoint parmi les
#  faits, assembler par conjonction_intro, détacher.  Déterministe, sans
#  recherche ; le noyau juge l'assemblage ET le modus ponens.
#
#  ⚠️ LEÇON MESURÉE (1re passe de ND18) : LES DÉFINITIONS SONT ELLES-MÊMES DES
#  CONJONCTIONS — est_fini(a) = est_cardinal(a) ∧ ¬(a = a+1).  Un aplatissement
#  naïf descend DANS les définitions et réclame leurs sous-conjoints au lieu du
#  fait.  D'où l'ARRÊT-AUX-FAITS-CONNUS : si un nœud est un fait, ne pas
#  descendre.  C'est lui qui fixe le niveau de granularité — celui des FAITS.
# ══════════════════════════════════════════════════════════════════════════════
def _et_g(f):
    """Conjoint GAUCHE d'une formule et(a,b) = ¬(¬a ∨ ¬b)."""
    return f.sous[0].sous[0].sous[0]


def _et_d(f):
    """Conjoint DROIT."""
    return f.sous[0].sous[1].sous[0]


def _est_et(f):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et
    try:
        return f == et(_et_g(f), _et_d(f))     # reconstruction, jamais un tag deviné
    except Exception:
        return False


def conjoints_de(f, faits):
    """Aplatit une conjonction en S'ARRÊTANT dès qu'un nœud est un fait CONNU."""
    if f in faits:
        return [f]
    if _est_et(f):
        return conjoints_de(_et_g(f), faits) + conjoints_de(_et_d(f), faits)
    return [f]


def detachement_conjonctif(impl_thm, faits):
    """Γ ⊢ (C₁∧…∧Cₙ) ⇒ B  et  faits ⊢ chaque Cᵢ  ⟹  ⊢ B.

    `impl_thm` : théorème dont la conclusion est l'implication (∀ déjà dépouillé
    par `instancie`).  `faits` : {formule: (nom, Theoreme)}.
    Rend (théorème, [provenances]) ou (None, [conjoints manquants]) — jamais un
    échec silencieux : les manquants sont la liste de courses du tour suivant."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro,
    )
    ou_ = impl_thm.conclusion
    A = ou_.sous[0].sous[0]
    cj = conjoints_de(A, faits)
    preuves, manquants = [], []
    for c in cj:
        (preuves if c in faits else manquants).append(faits.get(c, c))
    if manquants:
        return None, manquants
    assemble = preuves[0][1]
    for (_, th) in preuves[1:]:
        assemble = conjonction_intro(assemble, th)
    assert assemble.conclusion == A, "l'assemblage ne recompose pas l'antécédent"
    return N.modus_ponens(assemble, impl_thm), [nom for (nom, _) in preuves]


# ══════════════════════════════════════════════════════════════════════════════
#  ∃-INTRO SÉLECTIVE (v1, 6 août 2026) — n'abstraire QUE dans UN CÔTÉ d'une égalité.
#
#  POURQUOI.  L'abstraction totale ne peut PAS inventer la parité : les numéraux
#  s'EMBOÎTENT (N6 contient N3 dans sa tour de successeurs), donc abstraire N3
#  partout dans « N6 = N3+N3 » toucherait aussi l'intérieur de N6 (ev.278).  En
#  n'abstrayant que dans le membre DROIT, le membre gauche garde ses occurrences
#  et S5 reste satisfait : (t|x)R == φ puisque la substitution ne réintroduit t
#  que là où on l'a retiré.  De ⊢ N6 = N3+N3 on tire ainsi EXACTEMENT
#  ⊢ (∃k)( N6 = k+k ) — la parité de 6, INVENTÉE depuis un fait de somme.
#
#  v1 bornée : formules ÉGALITÉ seulement, un côté à la fois, coût linéaire
#  (aucune énumération de sous-ensembles d'occurrences).  Les τ-termes sont
#  CANDIDATS ici (les numéraux en sont), contrairement au régime total.
# ══════════════════════════════════════════════════════════════════════════════
def chainer_existentiels_selectif(preuve_de, cote="droite", min_occ=1, cap_par_thm=4,
                                  budget_dag=200_000, lieur=None, sautes=None):
    """∃-intro un-côté : pour chaque ⊢ g = d clos, abstraire un sous-terme du côté
    choisi SEULEMENT → ⊢ (∃x)( g = d[t→x] ) (resp. gauche).  Certifié par S5+MP.

    `lieur` : nom du lieur de l'existentielle (défaut : frais).  Le passer permet
    de viser une formule d'énoncé EXACTE (ex. `parite.K_PAIR` pour est_pair).
    `min_occ=1` : contrairement au régime total, UNE occurrence suffit — le sens
    vient du côté, pas de la répétition."""
    hmemo = {}
    connus = {_hash_dag(c, hmemo) for c in preuve_de if hasattr(c, "tag")}
    universels = universels_de(preuve_de)
    trouves, vus = [], set()
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal
    for concl, (nom, thm) in preuve_de.items():
        # v1 : égalités seulement — détectées par RECONSTRUCTION (jamais par un
        # tag deviné : la prose n'est pas un contrat, le constructeur l'est).
        if not (hasattr(concl, "tag") and len(getattr(concl, "termes", ())) == 2
                and concl == egal(*concl.termes)):
            continue
        if _taille_dag(concl) > budget_dag:
            if sautes is not None:
                sautes.append((nom, _taille_dag(concl)))
            continue
        g, d = concl.termes
        vise, garde_ = (d, g) if cote == "droite" else (g, d)
        occ = _occurrences_depliees(vise)
        cands = [(rep, n) for (rep, n) in occ.values() if n >= min_occ]
        # ⚠️ ORDRE DE VISITE (mesuré, 1re passe du test-vitrine) : « les plus gros
        # d'abord » fait passer les morceaux d'ENCODAGE (somme_disjointe, produit)
        # avant les numéraux, et le cap s'épuise avant N3.  Le niveau arithmétique
        # du corpus, ce sont les τ-TERMES (Card, numéraux) : eux d'abord, par
        # taille décroissante ; les app répétés ensuite.
        cands.sort(key=lambda tn: (0 if tn[0].tag == "tau" else 1,
                                   -_taille_dag(tn[0]), -tn[1]))
        pris = 0
        for (t, _n) in cands:
            if pris >= cap_par_thm:
                break
            x = lieur if lieur is not None else _frais(concl)
            if x in libres_f(concl):
                continue                               # lieur imposé mais capturé
            vise_abs = _abstraire(vise, t, x)
            if vise_abs == vise:
                continue
            R = (egal(garde_, vise_abs) if cote == "droite"
                 else egal(vise_abs, garde_))
            cible = existe(x, R)
            cle = _hash_dag(cible, hmemo)
            if cle in connus or cle in vus or _est_instance_connue(cible, universels):
                continue
            try:
                tac = N.modus_ponens(thm, N.s5(R, t, x))   # S5 vérifie (t|x)R == φ
            except Exception:
                continue
            if tac.est_clos and tac.conclusion == cible:
                vus.add(cle)
                pris += 1
                trouves.append(("∃-sélectif/%s" % cote, nom, f"t={_court(t)}", tac))
    return trouves
