# ARTICLE — plan de campagne (ouvert le 2 août 2026)

**Cible** : preprint arXiv AVANT septembre 2026 (NDA Thales) ; puis soumission AITP
(la communauté exacte), CPP ou CICM selon l'angle retenu. **Langue : anglais** (portée
arXiv/AITP) — le rapport V9 reste français.

**Titre de travail** : *Failure as a Theorem: Certified Error Objects, Fidelity Auditing,
and the Instrumented Last Mile in an LCF Kernel for Bourbaki's Theory of Sets.*

## La règle d'or de ce chantier

**Chaque phrase de l'article doit être adossée à un objet du dépôt** (théorème, mesure,
événement, source). Une affirmation sans ancre = une docstring qui ment, en public.
Le tableau ci-dessous EST l'article ; le LaTeX n'est que sa mise en forme.

## Table des revendications (claim → preuve → statut)

| # | revendication | preuve dans le dépôt | statut |
|---|---|---|---|
| C1 | Première **mécanisation du formalisme propre** de Bourbaki (τ, assemblages, critères C1–C62) — ⚠️ recentré 2 août : le véhicule « LCF en Python » n'est PAS neuf (Knuckledragger, LISA), le formalisme inhabité l'est | `bourbaki/i_*` ; 3 909 tests ; non-trouvé confirmé par 2 zones indépendantes | ✅ recentré |
| C2 | L'échec de preuve comme objet CERTIFIÉ : certificat = théorème du noyau, re-vérifié, périmètre CALCULÉ | `outils_ia/verite/echec.py` + README ; cas H-graphe : {H}⊢∅∈∅ mesuré, périmètre H2/H3 prouvées hors d'atteinte | ✅ mesuré |
| C3 | Taxonomie E1–E7 avec conditions de validité, chaque classe INSTANCIÉE par un cas réel | README verite §2 ; events.jsonl (91) : membre_but (E1), 0!=1 (E2), n_bien_ordonne 53 ax. (E4), bo (E5), produit+seg_ext (E6), sonde à noms devinés (E7) | ✅ mesuré |
| C4 | **Articulation décisionnelle** des trois branches — dont la branche INDÉPENDANTE, absente partout — + critère syntaxique réfuté comme suffisant. ⚠️ recentré 2 août : la réfutation seule est un acquis du domaine (Nitpick 2011 → Learning to Disprove 2603.19514) | `classer_residu.py` ; bo (contre-exemple mesuré) ; HW/HN (indépendance mesurée) | ✅ recentré |
| C5 | Dette Ax(D) : un théorème « 0 hypothèse » peut consommer 53 axiomes invisibles ; l'invariant « 22 » ne mesure pas ce qu'il prétend | `axiomes_consommes.py` ; mesures 4 capstones ; piège mémoïsation −62 % (protocole = partie de l'outil) | ✅ mesuré |
| C6 | L'infidélité comme **verdict DÉRIVÉ et réfutable** (contradiction au noyau contre une source imprimée préexistante, page/ligne) + **guérison certifiée**. ⚠️ recentré 2 août : l'ancrage fin seul n'est plus neuf (M2F 2602.17016 fait la provenance au span, auditée par HUMAIN — nous, le verdict est MÉCANIQUE) ; blueprints ≠ livre préexistant | @livre 2 033 notions ; D1 ; suite 3 909/3 909 post-réparation ; ACQUIS_AFFAIBLI ev. 93 (le coût honnête) | ✅ recentré |
| C7 | Détecteur vectoriel d'axiomes jumeaux (WL, cos ≥ 0,90 ∧ même terme caractérisé) : l'incohérence trouvée par enquête devient une requête de 1,7 s | scan du 31 juil : 43 axiomes, 24 paires, h_iso_max candidate ; calibrage sur paires connues (0,9521 vs 0,7437) | ✅ mesuré |
| C8 | La boucle de guidage M(s) a un retour MESURÉ : 10 instances tracées échec→réemploi (dont ratios mécaniques 1,7 s vs 1 h 35) + 3 contre-exemples honnêtes + menace de validité rédigée | **`C8_retours.md`** (consolidé le 2 août, chaque ligne cite ses événements) | ✅ consolidé |
| C9 | Positionnement : le cas limite À BRUIT NUL de la science expérimentale (Popper/Lakatos/Mayo/AGM/Kelly exécutables) | annexe substrat R1–R10 ; à écrire §discussion, PAS un claim central | 🟠 cadre, pas résultat |

## Ce que l'article NE revendique PAS (à écrire noir sur blanc)

- PAS « nous avons inventé la réparation de théories » (Bundy ABC), ni « la donnée d'échec »
  (REPLica, vague 2025-26), ni « la certification de fidélité » (Faithfulness Gap, juin 2026) —
  la nouveauté est la COMPOSITION certifiée-noyau + le domaine Bourbaki-τ + l'instrumentation.
- PAS une IA qui crée des théories : c'est l'horizon (§ future work), pas le résultat.
- La nouveauté est SEMI-DÉCIDABLE : « aucun contre-exemple après recherche méthodique »,
  jamais plus. La passe de related work systématique est OBLIGATOIRE avant soumission.

## Squelette (mappé sur l'existant — on assemble, on n'écrit pas de zéro)

1. Introduction + contributions ← ce tableau
2. Background : le formalisme de Bourbaki ; le noyau V9 (τ abrégé, MemoryError de A1, 4,5e12) ← rapport
3. Certified failure framework : définitions + E1–E7 + objets ← README verite (traduire/durcir)
4. Fidelity auditing : @livre, E6, les DEUX réparations avec dérivations ← CAMPAGNE_DEMOS + annexe erreurs
5. The guidance loop M(s) + vecteurs WL + détecteur ← VECTORISATION.md + scan
6. Case study: one instrumented week (tableau de chiffres) ← CAMPAGNE_DEMOS
7. Related work ← sources/INDEX.md (16 réfs cataloguées) + passe systématique À FAIRE
8. Limitations : opérateur unique, petit corpus, semi-décidabilité, ce qui n'est PAS mesuré
9. Conclusion : R1–R10, la route vers l'IA créatrice de théories

## Calendrier (contrainte dure : NDA septembre)

- **S1 (cette semaine)** : squelette LaTeX ✅ (ce tick) ; suite seg_ext verte (agent en cours) ;
  consolidation C8 (tableau avant/après depuis events.jsonl).
- **S2** : ✅ CLOS (2 août) — 4 zones / 69 réfs / 33 menaces (`RELATED.md`), 5 fiches PDF
  (`FICHES_MENACES.md`), 3 claims recentrés ; survey conjecturing vérifié (taxonomie
  orthogonale au statut logique — abstract seul, texte sous paywall, à télécharger si
  certitude totale voulue).
- **S3 : ✅ TERMINÉ (2 août)** — texte COMPLET, 15 pages, 0 stub : intro densifiée
  (« the opposite stance ») · §2 Background · §3 Certified Failure · §4 Fidélité ·
  §5 Boucle+vecteurs · §6 Case study · §7 Related work (45 réfs BibTeX, 0 non résolue) ·
  Limitations · Conclusion · 3 figures TikZ (preuve réelle de 0!=1, mur réel trichotomisé,
  extension de théorie).
- **S4 : relecture adverse ✅ FAITE ET APPLIQUÉE (2 août)** — verdict CORRECTIONS-MAJEURES,
  6 bloquants + 11 majeurs, tous re-vérifiés par le directeur puis appliqués (~35 edits) ;
  A1 : 33/39 chiffres traçaient, les 2 introuvables (6 700+, 62→95) remplacés par le mesuré ;
  .bib : 5 entrées vérifiées aux PDF + Knuckledragger ajouté ; polissage anglais (10
  gallicismes) fait. Recompilé 16 p., 0 réf cassée. Détail au journal CAMPAGNE_DEMOS.
- **Vérification .bib ✅ COMPLÈTE (2 août)** : les 10 entrées restantes vérifiées en ligne
  (arXiv ×8 + FSE 2025 + JCST) — corrections : hou2025versions (1ᵉʳ auteur Luan, 8 auteurs,
  titre complet), survey (Zhang & Tan, 41(1):46-66), 2 auteurs uniques (Khrulev,
  Vishnyakova). **46/46 entrées vérifiées, 0 (v?).** Notes de vérification déplacées en
  commentaires % (le champ `note` s'imprime).
- **RESTE avant le gel v1 arXiv** : (1) **Karl** : nom d'auteur/email/URL + **commit & tag du
  dépôt** (l'état instrumenté est non versionné depuis le 1ᵉʳ juil — le hash du tag va dans le
  \thanks ; sans lui, « no suite was silenced » n'est pas défendable) ; (2) relecture humaine
  de Karl ; (3) figer v1. Marge avant septembre.

## Décisions prises (déléguées, révocables par Karl)

- Anglais ; arXiv d'abord (horodatage), conférence ensuite.
- `article/` séparé de `rapport/` — deux artefacts, deux langues, deux publics.
- Les 3 schémas de la conversation passent en figures (refaits proprement).
