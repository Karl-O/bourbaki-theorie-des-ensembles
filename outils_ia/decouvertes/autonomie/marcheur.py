# -*- coding: utf-8 -*-
"""LE MARCHEUR — une marche sur les états de dérivation, le noyau en garde-fou
(21 août 2026, chantier A4).

LA PORTE QU'IL FRANCHIT (plan éditorial, 10 août) : fermer au moins un but que
le chaînage seul ne ferme pas. Mesuré le 21 août sur le banc ⊕ de v16-v18
(`a ⊕ b := (a+b)+1`, pool = les deux lois brutes sur `+`) :

  · but B4 = ((a⊕b)⊕c)⊕d = a⊕(b⊕(c⊕d)) en chaînage direct : ÉCHEC en 692 s
    (budget épuisé — la chaîne brute dépasse `max_pas=5`, borne mesurée v18) ;
  · la marche complète (miner → conjecturer → réfuter → certifier →
    re-essayer comprimé) : FERMÉ en 414 s de bout en bout.

UN PAS DE MARCHE (état = but + pool de faits certifiés) :
  1. MINER le but lui-même (`mineur.miner_motifs` — scindé le 21 août,
     limite des 300 lignes) ;
  2. CONJECTURER : schémas à un motif (comm/assoc/idem) et à DEUX motifs
     (distributivités croisées) — listes OUVERTES ;
  3. RÉFUTER à bas prix (`oracle_num.contre_exemple`) ;
  4. CERTIFIER (`besoins` — le noyau juge) : le pas de COMPRESSION ;
  5. RE-ESSAYER sur le pool comprimé, par ÉCHELLE de paliers.
     Rien de nouveau → s'arrêter et rendre les manques terminaux.

PRINCIPE DE SÛRETÉ INCHANGÉ (ev.374) : le marcheur SUGGÈRE, le noyau JUGE.
Un mauvais pas coûte une route morte, jamais un faux théorème. Aucun
`Theoreme` n'est construit ici : tout sort de `besoins`, donc du noyau.

⚠️ DETTE DE RANGEMENT, signalée et non masquée : `autonomie/` dépasse la
convention des 10 entrées ; l'éclatement (sous-paquet `euclide/`) est une
dette antérieure à ce fichier.
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[3]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_CORPUS = _V9 / "outils_ia" / "corpus"
if str(_CORPUS) not in sys.path:
    sys.path.insert(0, str(_CORPUS))

from outils_ia.decouvertes.autonomie.mineur import (  # noqa: E402  (ré-exports)
    miner_motifs, _appliquer,
)


#: schémas de lois essayés sur un motif BINAIRE — liste OUVERTE (règle
#: STYLE_ARTICLES §8) : rien ne prouve qu'il n'en faudra pas d'autres.
def conjectures_pour(motif, noms):
    """→ [(nom_schema, conjecture, noms_des_variables_libres)]."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, var,
    )
    if len(noms) != 2:
        return []
    x, y, z = var("xmarche"), var("ymarche"), var("zmarche")

    def F(u, v):
        return _appliquer(motif, noms, [u, v])

    return [
        ("commutativite", egal(F(x, y), F(y, x)), ["xmarche", "ymarche"]),
        ("associativite", egal(F(F(x, y), z), F(x, F(y, z))),
         ["xmarche", "ymarche", "zmarche"]),
        ("idempotence", egal(F(x, x), x), ["xmarche"]),
    ]


def conjectures_croisees(m1, m2):
    """Schémas à DEUX motifs binaires (21 août, chantier division) :
    F distribue-t-il sur G ? → [(nom, conjecture, libres)].

    Né d'un besoin du LIVRE : les identités de quotients de E III.39
    ((c+d)/b = c/b + d/b…) reposent sur la distributivité du produit sur la
    somme — un schéma qu'aucun motif SEUL ne peut exprimer. Liste OUVERTE,
    comme `conjectures_pour`."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, var,
    )
    if len(m1["noms"]) != 2 or len(m2["noms"]) != 2:
        return []
    x, y, z = var("xmarche"), var("ymarche"), var("zmarche")

    def F(u, v):
        return _appliquer(m1["motif"], m1["noms"], [u, v])

    def G(u, v):
        return _appliquer(m2["motif"], m2["noms"], [u, v])

    return [
        ("distributivite-gauche", egal(F(x, G(y, z)), G(F(x, y), F(x, z))),
         ["xmarche", "ymarche", "zmarche"]),
        ("distributivite-droite", egal(F(G(y, z), x), G(F(y, x), F(z, x))),
         ["xmarche", "ymarche", "zmarche"]),
    ]


def conjectures_morphisme(h1, g2):
    """Schéma (unaire, binaire) : H est-il un MORPHISME pour G ?
        H(G(y, z)) = G(H(y), H(z)).

    Né d'une mesure du 21 août : sur a·(b+c) = a·b + a·c, TOUTES les
    instances de produit partagent `a` — chaque paire ne diverge qu'en un
    point, le motif binaire complet du produit n'est PAS récupérable du but.
    Le motif UNAIRE H = a·(·) l'est (occ 3, gain 226), et la distributivité
    du but est exactement « H morphisme pour + ». Liste OUVERTE."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        egal, var,
    )
    if len(h1["noms"]) != 1 or len(g2["noms"]) != 2:
        return []
    y, z = var("ymarche"), var("zmarche")

    def H(u):
        return _appliquer(h1["motif"], h1["noms"], [u])

    def G(u, v):
        return _appliquer(g2["motif"], g2["noms"], [u, v])

    return [
        ("morphisme", egal(H(G(y, z)), G(H(y), H(z))), ["ymarche", "zmarche"]),
    ]


def marcher(but, faits_bruts, impls=(), rondes=3, profondeur=4,
            borne_oracle=8, trace=None, sonde=None, paliers_max=None):
    """La marche complète. → (Theoreme_ou_None, journal).

    Le journal est la DONNÉE du marcheur : chaque motif miné, chaque
    conjecture réfutée (et par quelle affectation), chaque lemme certifié,
    chaque re-essai — l'échec final rend les manques terminaux.

    ⚠️ Le re-essai se fait sur le pool COMPRIMÉ, par ÉCHELLE : les lemmes du
    motif de tête seuls, puis élargi motif par motif en cas d'échec. Mesuré
    le 21 août : B4 ferme en ~73 s sur le lemme dérivé seul, 962 s en pool
    cumulé, et le re-essai « tous les lemmes certifiés d'un coup » (6)
    dépassait 580 s — chaque fait de plus agrandit l'espace. L'essai sur
    pool cumulé n'est PAS fait ici — dit dans le journal, jamais en silence."""
    from outils_ia.arithmetique.oracle_num import contre_exemple
    from outils_ia.decouvertes.besoin import besoins

    journal = []

    def note(e):
        journal.append(e)
        if sonde is not None:
            sonde(e)

    #   battement de coeur pendant les LONGS appels besoins (règle du 21 août :
    #   jamais de calcul long sans sortie — deux morts silencieuses mesurées).
    #   Échantillonné : 1 ligne tous les 200 événements de route.
    _compte = {"n": 0}

    def _battement(e):
        _compte["n"] += 1
        if sonde is not None and _compte["n"] % 200 == 0:
            sonde({"type": "battement", "routes": _compte["n"],
                   "dernier": e.get("type")})
        if trace is not None:
            trace(e)

    derives = {}                       # conj → (nom, th, rang_du_motif)
    tentees = set()

    def _essayer(schema, conj, libres, rang, etiquette):
        """Réfuter puis certifier UNE conjecture. → 1 si lemme ajouté."""
        if conj in faits_bruts or conj in derives or conj in tentees:
            return 0
        tentees.add(conj)
        note({"type": "essai", "schema": schema, "motif": etiquette})
        aff = contre_exemple(conj, libres, borne_oracle)
        if aff is not None:
            note({"type": "réfuté", "schema": schema, "par": aff})
            return 0
        pool = dict(faits_bruts)
        pool.update((c, (n, t)) for c, (n, t, _) in derives.items())
        th, _ = besoins(conj, list(impls), pool, profondeur=profondeur)
        if th is not None and th.est_clos and th.conclusion == conj:
            derives[conj] = ("marche:" + schema, th, rang)
            note({"type": "certifié", "schema": schema})
            return 1
        note({"type": "non-certifié", "schema": schema})
        return 0

    extras = []
    for ronde in range(1, rondes + 1):
        motifs = miner_motifs(but, extras=extras)
        note({"type": "motifs", "ronde": ronde,
              "gains": [(m["occ"], m["gain"]) for m in motifs]})
        nouveaux = 0
        for rang, m in enumerate(motifs, start=1):
            for schema, conj, libres in conjectures_pour(m["motif"], m["noms"]):
                nouveaux += _essayer(schema, conj, libres, rang,
                                     (m["occ"], m["gain"]))
        #   schémas CROISÉS sur les deux motifs de tête (rang du palier =
        #   max des deux rangs : le lemme n'est disponible que quand ses
        #   deux motifs le sont)
        tetes = list(enumerate(motifs[:2], start=1))
        for r1, m1 in tetes:
            for r2, m2 in tetes:
                if m1 is m2:
                    continue
                for schema, conj, libres in conjectures_croisees(m1, m2):
                    nouveaux += _essayer(schema, conj, libres, max(r1, r2),
                                         (m1["occ"], m2["occ"]))
        #   schémas MORPHISME (unaire sur binaire) — l'arité 1 est minée à
        #   part : les motifs dont les occurrences partagent un argument
        #   n'existent QU'en arité 1 (mesuré le 21 août sur a·(b+c))
        unaires = miner_motifs(but, extras=extras, arite=1, top=2)
        note({"type": "motifs-unaires", "ronde": ronde,
              "gains": [(m["occ"], m["gain"]) for m in unaires]})
        for r1, h in enumerate(unaires, start=1):
            for r2, g in tetes:
                for schema, conj, libres in conjectures_morphisme(h, g):
                    nouveaux += _essayer(schema, conj, libres, r2,
                                         (h["occ"], g["occ"]))
        #   ÉCHELLE DE COMPRESSION (mesurée le 21 août) : re-essayer sur les
        #   lemmes du motif de TÊTE seuls, puis élargir motif par motif. Le
        #   re-essai « tous les lemmes d'un coup » (6 lemmes) dépassait 580 s
        #   là où les 2 lemmes du motif de tête suffisent — même loi que le
        #   pool cumulé : chaque fait de plus agrandit l'espace de recherche.
        if nouveaux:
            rangs = sorted({r for (_, _, r) in derives.values()})
            #   `paliers_max` : plafond du nombre de paliers essayés — les
            #   paliers sautés sont DITS au journal (jamais de cap silencieux).
            #   Mesuré le 21 août : trois exécutions en fond mortes sans trace
            #   (ni exit code, ni traceback, ni événement système), TOUTES
            #   dans un épuisement de re-essai à ≥ 4 lemmes ; cause non
            #   identifiée, corrélée à la taille du pool.
            if paliers_max is not None and len(rangs) > paliers_max:
                note({"type": "paliers-sautés", "essayés": paliers_max,
                      "sautés": rangs[paliers_max:]})
                rangs = rangs[:paliers_max]
            manques = []
            for k in rangs:
                palier = {c: (n, t) for c, (n, t, r) in derives.items()
                          if r <= k}
                note({"type": "re-essai", "ronde": ronde, "palier": k,
                      "lemmes": len(palier)})
                th, manques = besoins(but, list(impls), palier,
                                      profondeur=profondeur, trace=_battement)
                if th is not None and th.est_clos and th.conclusion == but:
                    note({"type": "FERMÉ", "ronde": ronde, "palier": k,
                          "pool": "comprimé (%d lemmes)" % len(palier)})
                    if trace:
                        trace(journal)
                    return th, journal
                note({"type": "ouvert", "ronde": ronde, "palier": k,
                      "manques": len(manques)})
            extras = [d["manque"] for d in manques
                      if d.get("manque") is not None]
        if nouveaux == 0:
            break
    note({"type": "terminal",
          "non-essayé": "pool cumulé (brut+dérivés) — coût mesuré 962 s sur B4"})
    if trace:
        trace(journal)
    return None, journal


__all__ = ["miner_motifs", "conjectures_pour", "conjectures_croisees",
           "conjectures_morphisme", "marcher"]
