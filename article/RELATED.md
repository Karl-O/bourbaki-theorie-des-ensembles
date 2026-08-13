# RELATED WORK — synthèse de la passe systématique (2 août 2026)

*(4 zones, 57 requêtes, 69 références rendues, 33 marquées MENACE. Chaque réf vient d'un
résultat de recherche réel, avec la requête qui l'a produite — détail complet dans le journal
du workflow `wf_c93b3f9b-b82`. Ce document est la source du §7 de l'article ET la liste des
recentrages de claims qu'il impose.)*

## Verdict global

**Aucun claim n'est tué. Trois doivent être RECENTRÉS** (C1, C4, C6) — leur forme naïve n'est
plus neuve, leur forme précise l'est. C'est exactement ce qu'une passe adverse devait produire.

## Les 5 menaces majeures, et la démarcation de chacune

| menace | frappe | ce qu'ils font | la démarcation à écrire noir sur blanc |
|---|---|---|---|
| **Lignée Urban/Kaliszyk/Olšák/Jakubův** — features sémantiques (IJCAI'15), Property Invariant Embedding (1911.12073), ENIGMA (IJCAR'20) | **C7** (le plus exposé) | features structurelles de formules, invariantes au renommage, depuis 2015 — pour **ordonner la saturation** et le retrieval, par apprentissage | eux **scorent pour guider** (fonction apprise, intra-preuve) ; nous **détectons une coïncidence** inter-théories (WL exact, sans apprentissage, tâche de conformité). Citer Shervashidze comme outil, Olšák comme ingrédient |
| **M2F** (2602.17016) + Lean-GAP (2606.02588) | **C6** | provenance au **span près** vers le manuel source, auditée par humain | l'ancrage seul n'est **plus neuf**. Neuf : l'infidélité comme **verdict réfutable** — contradiction *dérivée* contre un livre imprimé préexistant (pas un blueprint écrit pour la formalisation), et la guérison **prouvée** |
| **Formalizing at Scale** (2605.29955) + Network Structure of Mathlib (2604.24797) + `is-my-lean-proof-vacuous` | **C5** | fermeture transitive des dépendances, axiomes/sorry cachés repérés, vacuité binaire | eux : **topologie** de la bibliothèque ou drapeau binaire ; nous : **dette quantifiée par dérivation** (observation de la règle `axiome` au noyau), classes de légitimité, et le cas mesuré « 0 hypothèse / 53 axiomes ». Aucune métrique nommée de « dette d'axiomes » publiée |
| **Learning to Disprove** (2603.19514) + lignée Nitpick (2011) | **C4** | la branche **réfutable** mécanisée à grande échelle | cesser de présenter la réfutation comme neuve. Neuf : l'**articulation** des trois branches en procédure de décision — et la branche **indépendante** n'existe nulle part |
| **Goedel-Architect** (2606.06468) + Self-Modifying Lean Agents (2607.17352) + ReasoningBank (2509.25140) | **C8** | boucles corpus→tâches avec retour d'échec ; « apprendre des échecs » est standard côté agents | leurs diagnostics sont du **texte LLM non vérifié**, leurs retours agrégés en scores ; les nôtres sont **certifiés noyau** et tracés **instance par instance** (quel échec → quel brief → quel théorème) |

Menaces secondaires à citer : Proof2Test/Petiot (l'échec SMT devient un test — précurseur de C2
côté programmes) ; APRIL 2602.02990 (l'objet-échec = message de compilateur) ; Aitken & Melham
2000, Petiot 3-causes, Hou FSE'25 (taxonomies voisines de C3, aucune certifiée) ;
Knuckledragger + LISA (un noyau « LCF en Python » / « LCF sur ZF » n'est pas neuf en soi → C1
recentré) ; Adams 2016 (proof auditing, manuel) ; Schulz et al. 2017 (inconsistances dans de
grandes bases FOL, sans texte source ni réparation) ; BlueprintRepair 2607.28110 (embryon de
trichotomie « lemme faux vs dépendance manquante ») ; Growing Mathlib (dédoublonnage syntaxique).

## Le cœur de nouveauté — les absences CONFIRMÉES par 4 chercheurs indépendants

Répétées dans les `non_trouve` de plusieurs zones (l'argument de nouveauté, semi-décidable
mais méthodique) :

1. **Aucun** échec de preuve certifié par un noyau *en tant qu'objet*, nulle part.
2. **Aucun** périmètre d'invalidation **calculé** d'un échec.
3. **Aucune** trichotomie opérationnelle avec branche *indépendante* ; aucun détecteur
   d'indépendance dans une théorie de travail.
4. **Aucune** mécanisation du chapitre I de Bourbaki (assemblages, liens, τ, critères) —
   ni du calcul ε/τ lui-même dans un assistant.
5. **Aucune** infidélité établie par **dérivation de contradiction** contre un texte imprimé
   ancré page/ligne ; aucun cas public de `False` dérivé dans une bibliothèque majeure.
6. **Aucune** métrique nommée de dette d'axiomes ; aucune application exécutable d'AGM à un
   développement formel réel.
7. **Aucun** WL-sans-apprentissage pour la détection d'axiomes jumeaux.
8. **Aucune** boucle corpus→briefs à retours tracés instance par instance avec échecs certifiés.
9. **Aucune** suite d'ABC (Bundy) depuis 2022 ; **aucune** reprise du chapitre I chez Gaia.

## Recentrages imposés (appliqués dans PLAN.md)

- **C1** : ~~« premier noyau LCF sur Bourbaki »~~ → « première **mécanisation du formalisme
  propre** de Bourbaki (τ, assemblages, critères C1–C62) » — le véhicule (LCF/Python) n'est
  pas la nouveauté, le **formalisme inhabité** l'est.
- **C4** : ~~« trichotomie »~~ → « **articulation décisionnelle** des trois branches, dont la
  branche indépendante, absente de la littérature » ; la réfutation seule est un acquis du
  domaine (Nitpick 2011 → 2603.19514).
- **C6** : ~~« fidélité au grain page/ligne »~~ → « l'infidélité comme **verdict dérivé et
  réfutable** contre une source imprimée préexistante, avec guérison certifiée » ; l'ancrage
  fin est désormais un standard (M2F).

## Fondations à citer (cadre, pas concurrents)

Popper/Lakatos/Mayo/AGM/Kelly (le cas limite à bruit nul) ; Shervashidze 2011 (WL) ;
Pease 2007 + HR (Lakatos computationnel — voisin philosophique, rien de certifié) ;
Hipster/QuickSpec (exploration de théorie, échecs jetés) ; survey Automated Conjecturing 2026
(point d'entrée bibliographique).

## Ajustements post-lecture (2 août — fiches dans `FICHES_MENACES.md`, PDF dans `sources/related_work/`)

- **C7** : menace ENIGMA/Olšák **rétrogradée** — leur invariance est un GNN *appris* pour le
  guidage (0 « Weisfeiler », 0 dédup dans 1911.12073) ; notre WL exact pour la coïncidence ne
  recoupe ni méthode, ni tâche, ni régime de garantie.
- **C6** : citation d'or trouvée — M2F p.8 : « statement faithfulness is enforced by a
  provenance-linked **manual audit** ». Le verdict humain vs notre verdict dérivé, verbatim.
- **C8** : le plus proche voisin est ATLAS (p.6 : « skill guides » relus obligatoirement par
  les workers) — la *forme* de la boucle est publiée ; notre claim porte sur la
  **certification des maillons** et le retour tracé, plus sur la boucle elle-même.
- **C4** : reformulé « la **troisième branche** » — Goedel-Architect articule déjà 2/3
  (réfutable certifiée compilateur + trop-dure, p.2) ; Learning to Disprove : **0 mention**
  d'un statut indépendant (mesuré sur le texte).
- **Concurrent n°1 à citer en tête du §7 : Goedel-Architect** — démarcation sur trois axes :
  forfeits LLM (« believes », p.3) vs certificats noyau ; par-run vs corpus persistant ;
  benchmark vs texte source.

## Reste à faire (S2, clôture)

1. Vérifier le survey 2026 (DOI 10.1007/s11390-026-6040-0) : classification opérationnelle
   des conjectures ouvertes ? (Seul risque résiduel sur C4.)
2. Traduire ce document + les fiches en §7 LaTeX avec les 69 réfs en BibTeX. (S3)
