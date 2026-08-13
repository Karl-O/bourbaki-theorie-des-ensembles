"""§III.5.8 / §III.6.2 — GLUING factorielle DÉVERROUILLÉ + LA JOINTURE « 0!=1 ∧ (n+1)! ».

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
(R-pivot) ET (O1) SONT MORTS — mesuré le 26 juil. 2026.  ⚠️ CE PARAGRAPHE REMPLACE
UN TEXTE QUI A FAIT PERDRE DES JOURS ; ne pas le ré-écrire sans re-mesurer.

Ce fichier a longtemps déclaré `factorielle_existe` NON CLOSE « pour DEUX raisons,
toutes deux dans le gluing C60 déposé (non modifiable) », et chiffré le franchissement
à « threader un BUNDLE de témoins frais dans 8 fonctions DÉPOSÉES sur 6 fichiers ».
Les DEUX raisons sont fausses, et « non modifiable » était la consigne d'une SESSION
ANTÉRIEURE : seuls le noyau (i_2_theoremes/noyau) et `subst` sont intouchables.

  (R-pivot) — « l'appel `reunion_graphes_fonctionnelle(vp,S)` à témoins PAR DÉFAUT dans
        `extension_un_pas_fonctionnelle` RE-capture sur F τ-lourd ».  FAUX.  Le fix
        `subst` du 24 juil. (court-circuit CS : `(T|x)t = t` si x ∉ libres(t)) a
        supprimé le renommage GRATUIT qui faisait α-diverger les deux chemins.  Mesuré :
        `pivot_factorielle_frais_ok()` → defaut='BUILD OK' ; `site_residuel_exact()` →
        {'statut':'BUILD OK'} (aucune clé 'site_pivot_defaut', aucune pile) ;
        `ensembles_factorielle_gluing_diag.diagnostiquer_capture()` → {} (plus AUCUN
        point de rupture).  Le threading des 8 fonctions est du TRAVAIL VIDE.
        ⚠️ « BUILD OK » ne suffit pas seul : il faut vérifier que le pivot est bien
        TRAVERSÉ (sinon on prouverait le vide).  Trace `sys.setprofile` relevée sur le
        chemin LIVE (sonde du 26 juil., 20,6 s) : extension_un_pas_fonctionnelle 1×,
        reunion_graphes_fonctionnelle 3×, antecedent_dans_domaine 14×, tous à témoins
        par défaut, aucune fonction jamais appelée.  Le pivot est traversé.

  (O1) — « C60/C62 ne livrent que des ESSAIS, pas la fonction f ASSEMBLÉE ».  FAUX
        depuis le 25 juil. : `ensembles_factorielle_fonction.factorielle_fonction_existe`
        (3 hyps, 12,6 s) et `…factorielle_equation_restriction` (4 hyps, 12,2 s, la
        forme du LIVRE f(n)=T_fac(f|seg n)) construisent, non vacuous.

RESTE FACTUELLEMENT VRAI, et ne doit PAS être effacé : la COLLISION DE NOMS.
`ensembles_factorielle_gluing_diag.binders_arithmetique_cardinale()` donne toujours
_collision = ['u','v','y','z'] : l'arithmétique cardinale bake bien les binders que le
gluing hardcode.  Ce qui est mort, c'est sa CONSÉQUENCE (la capture), pas le fait.

════════════════════════════════════════════════════════════════════════════════
CE QUE CE FICHIER APPORTE MAINTENANT : LA JOINTURE (E III.41 L.30-32).

Le livre : « il est clair que, pour tout entier n, (n+1)! = n!(n+1).  Cette dernière
relation, JOINTE à la relation 0! = 1, caractérise le terme n! ».  Les deux moitiés
existaient depuis le 25 juil. mais personne n'avait tenté la JOINTURE — et la jointure
révèle un désalignement qu'aucun des deux fichiers ne pouvait montrer seul :

    factorielle_zero()             (6 hyps) était bâtie sur regle_factorielle()        → zcard="Zfac62"
    factorielle_succ_fallback()    (9 hyps) est bâtie sur regle_factorielle(zcard="Z") → liant CANONIQUE
                                            (imposé par le raccord à `prop5_intervalle_zero`)

MESURÉ : |HZ∩HS| = 2 seulement, union = 13 hypothèses — dont SIX règle-dépendantes
(essais_bien_formes, rule_codomain, essais_restriction) au lieu de trois.
`essais_restriction(T_Zfac62) ≠ essais_restriction(T_Z)` MAIS `alpha_egal(…)` est TRUE :
c'est la MÊME règle à un NOM DE τ-LIANT près, et c'est le NOYAU — qui n'identifie pas
les α-variants — qui rendait la conjonction informulable.  Diagnostic à retenir : un
désalignement de recollement peut n'être qu'un désaccord de NOMS ; le tester avec
`alpha_egal` en plus de `==` dit lequel des deux on a.
RÉPARATION : `zcard` devient un kwarg (défauts byte-identiques) et la jointure se fait
à zcard="Z" des deux côtés ⇒ |HZ∩HS| = 5, union = 10.  C'est `factorielle_caracterisation`.
(Alternative : trois `alpha_bridge` — plus coûteux, et rattrape au lieu de supprimer.)

theorie_ensembles = 22 avant ET après, noyau INTACT, rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    reunion_graphes_fonctionnelle,
)


def _t(t):
    """Coercion str/Terme → Terme (idiome du dépôt)."""
    return t if isinstance(t, Terme) else var(t)


def _binders(t, acc):
    l = getattr(t, "lieur", None)
    if l:
        acc.add(l)
    for s in (getattr(t, "sous", None) or getattr(t, "termes", None)
              or getattr(t, "args", None) or ()):
        _binders(s, acc)
    return acc


# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144
def pivot_factorielle_frais_ok():
    """VÉRIFIE (exécutable) que le pivot paramétré construit PROPREMENT sur le VRAI
    graphe d'un pas factoriel F (τ-lourd, binders {F,Z,u,up,v,y,z}) avec des témoins
    FRAIS uglu/vglu/zglu/yglu — AUCUNE capture (la muraille « valeur » (B) est levée).

    Renvoie un dict de contrôle : binders de F, succès du build frais ET du build par
    défaut (depuis le fix subst 2026-07-24, les témoins u,v,z,y homonymes des binders
    internes de F ne déclenchent plus de renommage gratuit ⇒ les DEUX builds passent).
    N'asserte AUCUN théorème sur la factorielle ; c'est une PREUVE DE DÉVERROUILLAGE."""
    T = regle_factorielle()
    Fterm = T(var("uu"))                    # un pas factoriel : (card(dom u)+1)·u(prev)
    H = E.singleton(E.couple(var("xg"), var("vg")))
    rapport = {"binders_F": sorted(_binders(Fterm, set()))}

    # build par DÉFAUT (témoins u,v,z,y) — OK depuis le fix subst (plus de renommage gratuit)
    try:
        reunion_graphes_fonctionnelle(Fterm, H)
        rapport["defaut"] = "BUILD OK"
    except ValueError as ex:
        rapport["defaut"] = f"capture: {ex}"

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
    """Rejoue le chemin LIVE C62 factoriel.  Depuis le fix subst (2026-07-24), le build
    PASSE (statut « BUILD OK ») : l'ancien site résiduel (R-pivot) — l'appel
    `reunion_graphes_fonctionnelle(vp,S)` à témoins par défaut dans
    `extension_un_pas_fonctionnelle` — ne capture plus (le renommage était GRATUIT).
    La branche except est conservée en sentinelle : si une capture réapparaissait,
    elle serait localisée exactement comme avant (pile + site)."""
    import traceback
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
        factorielle_essais_existe,
    )
    rapport = {}
    try:
        factorielle_essais_existe()
        rapport["statut"] = "BUILD OK"
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


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 LA JOINTURE — « (n+1)!=n!(n+1), jointe à 0!=1, caractérise n! ».
# ════════════════════════════════════════════════════════════════════════════
def factorielle_caracterisation_cible(e="Enat", G="Gle", V="Vfac62", n="nfsc"):
    """L'ÉNONCÉ-cible, reconstruit SANS dériver — la conjonction des deux équations.

    SOURCE UNIQUE de la forme : `factorielle_caracterisation` la compare à ce qu'elle
    construit, donc l'association de la conjonction (`et` binaire) ne peut pas se
    désaccorder silencieusement (le piège qui avait fait passer le (∃!f) de C62 pour
    acquis pendant un mois).  u := f|seg(succ n) est la restriction lue par la règle."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, egal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN, successeur
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale

    ve, vn = var(e), var(n)
    m = successeur(vn)
    f = fonction_globale(e, V)
    u = E.restriction(f, E.segment_extremite(_t(G), ve, m))
    return et(egal(E.valeur(f, ZERO), UN),
              egal(E.valeur(f, m),
                   produit_cardinal_binaire(successeur(vn), E.valeur(u, vn))))


# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« On a 0! = 1 … pour tout entier n, (n+1)! = n!(n+1). Cette dernière relation, JOINTE à la relation 0! = 1, caractérise le terme n! » — les deux relations en UN théorème, sur UNE seule lecture de la règle)
def factorielle_caracterisation(e="Enat", G="Gle", V="Vfac62", n="nfsc"):
    """🎯🎯🎯 { bo(≤,E), essais_bien_formes(T_Z), rule_codomain(T_Z,V),
              essais_restriction(T_Z,T_Z), ZERO∈E, seg(≤,E,ZERO)=∅,
              succ n∈E, seg(≤,E,succ n)=[0,n], ZERO∈seg(≤,E,succ n), est_entier(n) }
        ⊢  ( f(ZERO) = UN )  ∧  ( f(succ n) = (succ n) · u(n) ),
      u = f|seg(succ n),  f = ⋃𝔇_tot,  T_Z = regle_factorielle(zcard="Z").

    LA PHRASE DU LIVRE (E III.41 L.30-32) en un seul théorème : « (n+1)! = n!(n+1) …
    jointe à 0! = 1, caractérise le terme n! ».

    CE QUE LA JOINTURE A RÉVÉLÉ (et qu'aucune moitié ne pouvait montrer seule) : les
    deux équations étaient bâties sur DEUX α-VARIANTES de la règle.  `factorielle_zero`
    prenait `regle_factorielle()` (zcard="Zfac62", liant défensif hérité du verrou-τ
    mort) ; `factorielle_succ_fallback` prend `regle_factorielle(zcard="Z")`, imposé
    par le raccord à `prop5_intervalle_zero` (Card([0,n]) y est écrit au liant canonique
    de `cardinal`).  MESURÉ aux défauts : |HZ|=6, |HS|=9, |HZ∩HS|=2, union=13.
    ⚠️ NUANCE MESURÉE, à ne pas caricaturer : `essais_restriction(T_Zfac62)` et
    `essais_restriction(T_Z)` sont α-ÉQUIVALENTES (`alpha_egal` True) sans être `==`.
    Les deux moitiés parlaient donc bien de la MÊME règle — à un NOM DE τ-LIANT près —
    et c'est le NOYAU, qui n'identifie pas les α-variants, qui rendait la conjonction
    informulable.  Le prix restait réel : 13 hypothèses au lieu de 10, dont TROIS
    comptées deux fois sous deux noms de liant — un affaiblissement purement syntaxique,
    mais un affaiblissement.  À zcard="Z" des deux côtés : |HZ∩HS|=5, union=10.
    Réparation alternative possible : trois `alpha_bridge` ; unifier `zcard` est plus
    simple, plus lisible, et supprime la cause au lieu de la rattraper.

    Aucune hypothèse INUTILE : chacune des 10 est effectivement consommée par l'une des
    deux moitiés (5 partagées, 1 propre au cas 0, 4 propres au cas successeur) — elles
    figurent toutes dans les hypothèses NON DÉCHARGÉES du théorème du noyau.

    ⚠️ ÉCARTS DE FIDÉLITÉ, déclarés (mis à jour au recâblage du 2 août 2026) :
      • ~~FORME-FALLBACK~~ MORTE : la règle porte M(D u) réel (`terme_plus_grand`) et
        le facteur Déf.2 `card(dom u)` ; le cas successeur lit désormais
        f(succ n) = (succ n)·u(n) — facteur ET point du livre.  Le SEUL écart restant
        est `valeur(u, n)` vs `valeur(f, n)` (accord de la restriction sur son
        domaine, brique suivante) ;
      • E reste la VARIABLE `Enat` (≡ ℕ) : sur le TERME CLOS `ensemble_NN()` le résidu
        bo(≤,ℕ) se décharge (`bo_graphe_NN`, CLOS) — non fait ici ;
      • Def.2 du livre (n! := ∏_{i<n}(i+1)) reste un chantier « familles indexées ».

    ⚠️ COÛT : ~6,5 min (le cas successeur traverse `prop5_intervalle_zero`, donc C61)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_zero import factorielle_zero
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import factorielle_succ_fallback

    zero = factorielle_zero(e, G, V, zcard="Z")          # 6 hyps — LA RÈGLE CANONIQUE
    succ = factorielle_succ_fallback(e, G, V, n)         # 9 hyps — même règle
    partagees = frozenset(zero.hypotheses) & frozenset(succ.hypotheses)
    assert len(partagees) == 5, (
        "factorielle_caracterisation : %d hypothèses partagées au lieu de 5 — les deux "
        "moitiés ne parlent PAS de la même règle (vérifier zcard)" % len(partagees))

    res = conjonction_intro(zero, succ)
    assert res.conclusion == factorielle_caracterisation_cible(e, G, V, n), \
        "factorielle_caracterisation : ≠ cible (association de la conjonction ?)"
    assert len(res.hypotheses) == 10, \
        "factorielle_caracterisation : hyps ≠ 10 (%d)" % len(res.hypotheses)
    assert res.conclusion not in res.hypotheses, "factorielle_caracterisation : VACUOUS"
    return res


__all__ = ["pivot_factorielle_frais_ok", "site_residuel_exact",
           "factorielle_caracterisation_cible", "factorielle_caracterisation"]
