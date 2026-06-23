"""§III.5.8 / §III.6.2 — GLUING factorielle : PIVOT DÉVERROUILLÉ + site résiduel EXACT.

════════════════════════════════════════════════════════════════════════════════
CE QUI A ÉTÉ DÉVERROUILLÉ (vérifié, exécutable).

Le diagnostic `ensembles_factorielle_gluing_diag` avait localisé la τ-capture du
gluing factorielle au PIVOT `reunion_graphes_fonctionnelle` (ensembles_restriction_somme) :
ses TÉMOINS étaient HARDCODÉS u,v,z (et le liant ∃ « y » de `antecedent_dans_domaine`),
or le graphe d'un pas de récursion factorielle BAKE des τ-binders cardinaux nommés
{u,up,v,y,z} (via cardinal/successeur/produit) ⇒ le témoin libre « v » substitué dans
un contexte « v »-lié force la capture-avoidance (@0) ⇒ `modus ponens : mineure ≠
antécédent`.

CORRECTIF APPLIQUÉ (commits `eff5ee5`, `2214c2d`, fichier restriction_somme SEUL) :
  • `reunion_graphes_fonctionnelle(g,h, u="u",v="v",z="z",y="y")` — témoins PARAMÉTRIQUES
    (défauts littéraux EXACTS, comportement byte-identique ; gate 497 passed/0 failed) ;
  • `antecedent_dans_domaine(u,v,f, y="y")` — liant ∃ PARAMÉTRABLE + α-pont (`alpha_bridge`)
    qui α-convertit le `(∃frais)…` vers le `(∃y)…` FIXÉ par AXIOME_DOM dès que `y≠"y"`
    (sinon aucun pont, byte-identique).

RÉSULTAT VÉRIFIÉ ICI (`pivot_factorielle_frais_ok`) : appelé avec des témoins FRAIS
`u="uglu",v="vglu",z="zglu",y="yglu"` (hors {u,up,v,y,z}) sur le VRAI graphe d'un pas
factoriel F = T_fac{u} (τ-lourd, binders {F,Z,u,up,v,y,z}), le pivot CONSTRUIT
PROPREMENT `est_fonctionnel(F ∪ {(x,v)})` (binders frais) — AUCUNE capture.  La
muraille « classe-VALEUR » (B) signalée IRRÉDUCTIBLE par `ensembles_recursion_hygienic`
est donc LEVÉE au niveau du pivot par la paramétrisation.

════════════════════════════════════════════════════════════════════════════════
CE QUI RESTE (site résiduel EXACT, honnête — NI faux, NI vacuous, NI postulé).

`factorielle_existe` (l'existence de la fonction f assemblée) reste NON CLOSE, pour
DEUX raisons distinctes, toutes deux situées DANS LE GLUING C60 DÉPOSÉ (non modifiable
sous la consigne courante — seul restriction_somme l'était) :

  (R-pivot)  Le pivot est invoqué, dans le chemin LIVE C62, à
                 bourbaki/ordre/ensembles_c60_existence_close.py:306
                     pivot = reunion_graphes_fonctionnelle(vp, S)   # TÉMOINS PAR DÉFAUT
             par `extension_un_pas_fonctionnelle`.  Cet appel n'est PAS encore threadé
             en témoins frais : il garde u,v,z,y par défaut ⇒ sur F τ-lourd il RE-capture.
             VÉRIFIÉ ici (`site_residuel_exact`) : la pile de capture du C62 factoriel est
                 c62_recursion_sur_N
                   → recursion_transfinie_existence_final  (c60_pont:374)
                     → …_complet → …_reduite → recursion_transfinie_existence (c60_final:729)
                       → heredite_couverture_realisee (c60_final:678)
                         → couvert_essai_depuis_famille (c60_final:573)
                           → extension_un_pas_depuis_coincidence (c60_final:303)
                             → extension_un_pas_union_fonctionnelle (c60_coeur:364)
                               → extension_un_pas_fonctionnelle (c60_existence_close:306)
                                 → reunion_graphes_fonctionnelle(vp,S)  ← TÉMOINS DÉFAUT
             Pour franchir : threader un BUNDLE de témoins frais (uglu/vglu/zglu/yglu)
             de `c62_recursion_sur_N` jusqu'à cet appel — soit 8 fonctions DÉPOSÉES sur
             6 fichiers (c60_existence_close, c60_coeur, c60_final, c60_realisation,
             c60_clauses, c60_pont).  Discipline non-breaking obligatoire (kwargs
             optionnels, défauts EXACTS, re-gate large à chaque palier).  HORS périmètre
             « restriction_somme seul » de la consigne courante ⇒ REPORTÉ, pas postulé.

             ⚠️ SUBTILITÉ STRUCTURELLE (à respecter lors du threading) : la conclusion
             du pivot est `est_fonctionnel(G∪H)` dont les LIANTS ∀ portent les NOMS des
             témoins (u,v,z).  Avec témoins frais, la conclusion devient
             `(∀uglu)(∀vglu)(∀zglu)…` — α-équivalente mais NON structurellement égale à
             la forme `est_fonctionnel(·)` attendue en aval.  Le threading doit donc soit
             α-NORMALISER la conclusion du pivot vers (u,v,z) avant de la rendre, soit
             propager les noms frais jusqu'aux comparaisons `assert …==est_fonctionnel(…)`.

  (O1)  Même (R-pivot) franchi, C60/C62 ne livrent que des ESSAIS (couverture par
        fonctions partielles), PAS la fonction f totale ASSEMBLÉE que quantifie
        `factorielle_existe`.  L'assemblage essais→f (gluing-de-famille +
        collectivisation, « chantier §III.2 distinct ») reste ouvert (cf. docstring de
        `recursion_transfinie_existence_final`).

CONCLUSION HONNÊTE : la paramétrisation déverrouille le PIVOT (la muraille (B) « valeur »
de `ensembles_recursion_hygienic` tombe).  `factorielle_existe` n'est PAS asserté : il
faudrait threader les témoins frais dans le gluing C60 déposé (R-pivot) PUIS résoudre
l'assemblage (O1).  theorie_ensembles = 22, noyau INTACT, rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import (
    reunion_graphes_fonctionnelle,
)


def _binders(t, acc):
    l = getattr(t, "lieur", None)
    if l:
        acc.add(l)
    for s in (getattr(t, "sous", None) or getattr(t, "termes", None)
              or getattr(t, "args", None) or ()):
        _binders(s, acc)
    return acc


def pivot_factorielle_frais_ok():
    """VÉRIFIE (exécutable) que le pivot paramétré construit PROPREMENT sur le VRAI
    graphe d'un pas factoriel F (τ-lourd, binders {F,Z,u,up,v,y,z}) avec des témoins
    FRAIS uglu/vglu/zglu/yglu — AUCUNE capture (la muraille « valeur » (B) est levée).

    Renvoie un dict de contrôle : binders de F, succès du build frais, ÉCHEC attendu
    du build par défaut (témoins u,v,z,y collisionnant {u,up,v,y,z}).  N'asserte AUCUN
    théorème sur la factorielle ; c'est une PREUVE DE DÉVERROUILLAGE du pivot."""
    T = regle_factorielle()
    Fterm = T(var("uu"))                    # un pas factoriel : (card(dom u)+1)·u(prev)
    H = E.singleton(E.couple(var("xg"), var("vg")))
    rapport = {"binders_F": sorted(_binders(Fterm, set()))}

    # build par DÉFAUT (témoins u,v,z,y) — capture attendue
    try:
        reunion_graphes_fonctionnelle(Fterm, H)
        rapport["defaut"] = "BUILD OK (inattendu)"
    except ValueError as ex:
        rapport["defaut"] = f"capture attendue: {ex}"

    # build FRAIS (témoins hors {u,up,v,y,z}) — doit RÉUSSIR
    th = reunion_graphes_fonctionnelle(Fterm, H,
                                       u="uglu", v="vglu", z="zglu", y="yglu")
    rapport["frais_concl_tag"] = th.conclusion.tag
    rapport["frais_nb_hyps"] = len(th.hypotheses)
    rapport["frais_ok"] = True
    # contrôle anti-vacuité du pivot : conclusion ∉ hypothèses
    rapport["non_vacuous"] = th.conclusion not in th.hypotheses
    return rapport


def site_residuel_exact():
    """Reproduit le chemin LIVE C62 factoriel et renvoie la pile EXACTE jusqu'au site
    résiduel (R-pivot) = l'appel `reunion_graphes_fonctionnelle(vp,S)` à TÉMOINS PAR
    DÉFAUT dans `extension_un_pas_fonctionnelle` (c60_existence_close:306), DÉPOSÉ.

    Ne POSTULE rien : expose l'obstruction résiduelle telle quelle (le build LÈVE la
    capture déposée, preuve que (R-pivot) est réel et hors périmètre restriction_somme)."""
    import traceback
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
        factorielle_essais_existe,
    )
    rapport = {}
    try:
        factorielle_essais_existe()
        rapport["statut"] = "BUILD OK (inattendu)"
    except ValueError as ex:
        tb = traceback.extract_tb(ex.__traceback__)
        # dernier cadre dans le gluing déposé qui appelle le pivot
        cadres = [(f.filename.replace("\\", "/").split("/")[-1], f.lineno, f.name)
                  for f in tb]
        rapport["statut"] = f"capture résiduelle: {ex}"
        rapport["site_pivot_defaut"] = next(
            (c for c in cadres if c[2] == "extension_un_pas_fonctionnelle"), None)
        rapport["pile"] = cadres[-10:]
    return rapport


__all__ = ["pivot_factorielle_frais_ok", "site_residuel_exact"]
