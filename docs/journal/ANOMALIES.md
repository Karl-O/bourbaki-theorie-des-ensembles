# Anomalies & écarts (mode boucle autonome)

Écarts entre le LaTeX/PDF et la réalité, docs périmés, incohérences — le **noyau fait foi**.

## 2026-06-23

- **`outils_ia/couverture.py` est PÉRIMÉ** : déclare « chap. II–IV non entamés » alors que II et III sont
  largement couverts. Ne pas s'y fier pour l'état ; audit réel : défs ~85 %, propositions ~38 %,
  théorèmes nommés ~26 % clos (11 agents, 2026-06-23). À remplacer par un suivi à jour.
- **README V9 référence un dossier `V7`** qui n'existe pas à la racine : la transcription LaTeX est en
  fait dans `../V6/V7/` (154 `Texte.tex`) ; le rapport ingénieur modèle est `../V6/V8/`.
- **Preuve LaTeX du Th2 (symétrie de =) diverge du PDF** (déjà noté dans le README V9). Quand un
  `Texte.tex` contredit le PDF ou se révèle faux, le noyau tranche ; consigner ici le cas précis au
  moment où on le rencontre.
- **BUG PRÉ-EXISTANT (suite déjà rouge avant migration) — `ensembles_familles_algebre.py:54`** importe
  `from bourbaki.ensembles.familles.ensembles_familles_reunion_props import (membre_image_reciproque,
  famille_reciproque, _val_recip, _membre_eq, _sym, _t)` mais **ce module n'existe pas** (supprimé ; un
  `.pyc` orphelin subsiste dans `__pycache__`). `ModuleNotFoundError` → `tests/ensembles/test_familles_algebre.py`
  échoue à la collecte. Les symboles n'ont pas de correspondance 1:1 (`ensembles_image_recip_famille_ii4`
  a `membre_image_recip`/`famille_image_recip`, noms différents). **Quarantaine** : le garde-fou de
  migration tolère cette unique erreur connue (`--continue-on-collection-errors`, baseline = 1 erreur).
  **À reconstruire en ÉTAPE B** (II.4 algèbre des familles, déjà PARTIEL dans l'audit).

## 2026-06-23 — RÉSOLU : familles_algebre

Le bug pré-existant ci-dessus est CORRIGÉ (1er résultat ÉTAPE B) : les 6 symboles du module supprimé  avaient déjà été reconstruits sous d'autres noms dans  (membre_image_recip, famille_image_recip, _val_recip, _membre_eq, _t ;  mort retiré). Import réparé par alias dans le module ET le test. **Gate collecte = 3011/0** (plus d'erreur). La baseline du garde-fou de migration passe de 1 à 0.

## 2026-06-23 - Commentaires PERIMES (Cantor)

Le corps de cantor_deux_exp levait NotImplementedError avec un commentaire pretendant que le pont set->cardinal n etait pas disponible. PERIME : equipotent_implique_inf_egal, le patron _card_le_set_t/_set_le_card_t/_le_trans_t (Hessenberg) et la Proposition 1 sont tous CLOS. Cantor 2^a>a au niveau cardinal est maintenant FERME (prop12_card/_cantor.py, 13 tests verts). Les docstrings REPORTE de ensembles_powerset_exp/_deux/_prop12_fin sont a relire (potentiellement perimees aussi).

## 2026-06-24 retraction_est_injection (II.3.8) ECARTEE
- L audit fan-out w1k1qywh0 a lui-meme signale que l enonce "une retraction est une injection" se reduit, sous forme close, soit a retraction_implique_injective (deja fait), soit a une tautologie P=>P (est_retraction(R,F,A) et est_section(F,R,A) sont la meme formule). Aucun contenu nouveau non vide certifiable sans postuler la surjectivite. Cible ecartee pour preserver l integrite (jamais de tautologie deguisee en theoreme). Le contenu reel est deja couvert par retraction_implique_injective.

## prop10_inter_produits (II.5.6) -- agent coupe, preuve cassee (2026-06-24)
- Agent aebdb1b33210af3c8 coupe (limite de session probable) en plein debogage. A laisse un
  module de 317 lignes (>300) SANS test, dont la preuve NE SE CONSTRUIT PAS : appeler le
  theoreme leve "modus ponens : mineure != antecedent" (~ligne 194, _inclusion_avant ;
  mismatch de binders dans la permutation de quantificateurs).
- LECON : l'assert de verification etait A L'INTERIEUR de la fonction (ne s'execute qu'a
  l'appel), pas au niveau module -> un import reussi NE PROUVE RIEN. Toujours APPELER le
  theoreme (ou lancer le test) avant de juger un orphelin "certifie".
- Orphelin supprime (jamais commiter une preuve cassee). Cible prop10 (distributivite
  produit/intersection, egalite complete) RESTE A FAIRE : permutation de quantificateurs
  delicate ; a re-deleguer a frais, ou livrer la forme inclusion seule (plus simple).

## Egalites de PRODUITS au niveau couple (ecart de portee systematique) (2026-06-24)
- Les formules d'egalite d'ensembles sur les produits (E.R.12 : (22) (X×Y)∪(X'×Y)=(X∪X')×Y,
  (23) (X×Y)∩(X'×Y')=(X∩X')×(Y∩Y'), etc.) sont formalisees au niveau APPARTENANCE D'UN COUPLE
  ((u,v)∈lhs ⇔ (u,v)∈rhs), PAS comme egalite d'ensembles pleine (∀z, z couple ou non).
- Raison : il manque la brique << tout z∈E×F est un couple z=(pr1 z, pr2 z) >> + l'extensionnalite
  poussant les ∃p,q de AXIOME_PRODUIT a travers ∨/∧. Le module dual ensembles_produit_distributif.py
  a le meme report (docstring l.17-18).
- A FAIRE (1 fois, debloque (22)(23) et les autres) : prouver couple_decomposition
  (z∈E×F ⇒ z=(pr1 z, pr2 z)) puis un lemme produit_egalite_par_couples
  ((∀ couple) (u,v)∈A ⇔ (u,v)∈B, A,B⊂E×F ⇒ A=B). Ensuite remonter les couple-level en egalites d'ensembles.

### RESOLU (2026-06-24) : ecart de portee des produits
- Brique produit_egalite_par_couples + couple_decomposition (ii_2_couples_produit/ensembles_produit_extensionnalite.py) livree -> (22) est desormais une EGALITE D'ENSEMBLES pleine. La meme brique permet d'upgrader (23) (X×Y)n(X'×Y')=(XnX')×(YnY') et les autres egalites de produits du couple-level vers l'ensembliste. Caveat binder : z != 'w' (w reserve par composer_egalites/symetrie).

## Retrofit @livre Chap II (2026-06-25) -- deux constats a traiter
Pendant la pose des marqueurs @livre (passe 1) et le passage du detecteur de trous (passe 2,
outils_ia/audit/gen_trous_livre.py), deux anomalies sont apparues :

1. **Marqueurs @livre sur de l'infra LLM (E I.22 / logique).** Les def `executer_preuve` et
   `prouver_par_llm` portent un `# @livre Ch.I §2.2 Def.-` mais ce sont des fonctions
   d'INFRASTRUCTURE (exécution de preuve / appel LLM), pas des notions Bourbaki. A RECLASSER :
   soit retirer le @livre (ce ne sont pas des notions du livre), soit -- si le module illustre
   vraiment la notion de << demonstration >> (§2.2) -- le retagger en Demo/Rem explicite. Le
   detecteur les compte a tort comme couverture de E I.22.

2. **7 vrais candidats de trous en logique (criteres C non formalises entre deux nommes).**
   gen_trous_livre sur bourbaki/logique signale, entre critères nommés consécutifs, des
   intervalles non couverts qui correspondent a des criteres Bourbaki PROBABLEMENT pas encore
   formalises (a confirmer page par page) : CF5 (entre cf4 et cf6, E I.19 L.24-25) ; gros trou
   E I.20 L.6-27 (entre cf7 et cf8) ; E I.25 L.16-31 (entre mono_droite et syllogisme, C7-C11?) ;
   E I.26 L.24-30 ; E I.27 L.8-30 ; E I.28 L.14-17 (entre c17 et c18) ; E I.31 L.17-26 (C24?,
   entre c23_ou et c25_premier). A COMBLER par une passe d'implementation (UN agent a la fois,
   jamais pendant une autre tache d'agent ; primitives N.* only, theorie==22, enonce==livre).

## Offset PDF du Chap IV corrige : +202 -> +203 (2026-06-25)
En posant les @livre du Chap IV (IV.1 structures/isomorphismes), un ecart d'offset PDF a ete
detecte puis verifie par lecture directe des en-tetes imprimes :
- **PDF p.203 = `E III.99` (BIBLIOGRAPHIE, fin Chap III)**, PAS du Chap IV.
- **PDF p.204 = `CHAPITRE IV / Structures`, §1, « 1. Echelons » = `E IV.1`** ; p.205 = `E IV.2`
  (CST1/CST2) ; p.206 = `E IV.3` (CST3). Donc **offset Chap IV = +203**, pas +202.
L'ancien `+202` (CLAUDE.md, pdf_index.md, et l'enonce de mission) etait **FAUX d'1 cran** ;
son ancre « E IV.101 = phys 303 » etait fantaisiste (le Chap IV n'a pas 101 pages). CORRIGE dans
CLAUDE.md et outils_ia/pdf/pdf_index.md. Les 32 marqueurs IV.1 sont cales sur la page physique
REELLE (E IV.p / PDF p.(p+203)), donc verifiables. Tout le Chap IV restant + le stray
`ensembles/fonctions/hors_ii_3/iv_structures` doivent utiliser +203.

Constat connexe : **derive de pagination dans le Chap III**. E III.7 = phys 110 et E III.66 =
phys 169 donnent +103 (verifie en-tetes) sur TOUT le domaine formalise (E III.1-66), mais la
biblio E III.99 = phys 203 donne +104 : une page non numerotee est inseree dans la queue
exercices (E III.67-99), HORS domaine formalise. Aucun marqueur Chap III commite n'est affecte
(verifie : tous a +103, jusqu'a E III.66=169). Rien a corriger cote code.

Trou de couverture confirme (IV.1) : les **criteres CST1-CST7** (E IV.2-10) ne sont PAS formalises
comme enonces NOMMES autonomes -- seulement cites en docstring et derives conditionnellement
(CST2/CST5 avec CST1/CST2/CST3 en hypotheses reportees). A inscrire dans la carte de couverture
Chap IV (candidats d'implementation futurs, comme les trous logique ci-dessus).

## Docstrings Chap IV §3 : mauvaise pagination interne (2026-06-25, NON corrige)
En posant les @livre des modules `bourbaki/structures/ensembles_universel_applications.py` et
`ensembles_structures_complements.py` (applications universelles), l'agent a constate -- et j'ai
verifie a l'en-tete imprime -- que leurs docstrings renvoient de facon repetee a de FAUSSES pages :
elles citent « IV.3, p. 16 » / « IV.3.1 » / « IV.3.2 » pour (QM)/(AU)/(CU)/CST22/CST23, alors que
le **§3 APPLICATIONS UNIVERSELLES commence reellement a E IV.22 (PDF p.225)**, pas E IV.16 (p.219,
qui est encore §2 « Structure induite », CST11/CST12). Localisations reelles verifiees a l'en-tete :
§3.1 (QM_I/QM_II)/alpha-application = E IV.22 (p.225) ; (AU)/(AU_I')/(AU_II') = E IV.23 (p.226) ;
(CU_I/CU_II)/Sigma-permise = E IV.23 (p.226) ; (CU_III)/CST22/CST23 = E IV.24 (p.227) ; exemples
(libre/corps fractions/produit tensoriel) = E IV.25 (p.228) ; Stone-Cech = E IV.26 (p.229). Les
**marqueurs @livre sont poses sur ces pages REELLES** (verifiables) ; seules les DOCSTRINGS gardent
l'ancienne pagination fausse -> a corriger lors d'une passe de fidelite docstrings (separee, car
toucher au code/docstring sort du perimetre @livre-only). Idem : la def `solution_isomorphisme_unique`
cite « IV, p. 12, CST8 » (CST8 est bien a E IV.12/p.215, confirme), mais formalise un contenu expose
a E IV.23/p.226 qui INVOQUE CST8 ; le marqueur pointe sur l'enonce CST8 (E IV.12).

Trou de couverture structurel (E IV.26) : les EXEMPLES du livre -- Extension d'un anneau d'operateurs
(IV), Completion d'un espace uniforme (V), Groupes topologiques libres (VII), Stone-Cech -- n'ont
AUCUNE def Python (releve de topologie/algebre hors theorie des ensembles pure). A inscrire comme
trous structurels assumes dans la carte de couverture Chap IV.

## BUG DE CAPTURE DE LIANT dans `est_reticule` / `borne_superieure` (2026-06-25, A CORRIGER)
Decouvert en tentant `totalement_ordonne_implique_reticule` (PLAN_ETAPE_C). L'agent a REFUSE de
bricoler ; capture CONFIRMEE empiriquement (libres_f).

**Le bug.** `borne_superieure(G, A, m, E, x="x", y="y")` (ensembles_ordre_relation.py L.169) :
  borne_superieure(G,A,m,E) := majorant(G,A,m,E)  et  (∀y)(majorant(G,A,y,E) ⇒ (m,y)∈G)
le 6e parametre `y` est le liant du « plus petit majorant ». Or `admet_borne_sup_inf`
(ensembles_ordre_monotone.py L.159) appelle `borne_superieure(G, {x,y}, vs, E, u)` : il passe `u`
pour le liant de `majorant` (OK, pas de capture la), MAIS **laisse le 6e au defaut `"y"`**. Comme la
paire passee est `paire(var('x'), var('y'))` (les `x,y` du `(∀x)(∀y)` externe de `est_reticule`), le
`(∀y)` du « plus petit majorant » **CAPTURE le `y` de la paire**. La clause devient
`(∀y)(y majore {x,**y**} ⇒ (s,y)∈G)` au lieu de `(∀m)(m majore {x,y_externe} ⇒ (s,m)∈G)`.
Idem `borne_inferieure` / « plus grand minorant ». Verifie : `libres_f(borne_superieure(G,{x,y},m,E))`
ne contient PAS la bonne structure ; sur l'exemple canonique du treillis (chaine a<b<c) la clause
capturee est insatisfiable. **`est_reticule(G,E)` est donc MALFORME** (≠ « reticule » de Bourbaki).

**Impact.**
- BLOQUE `totalement_ordonne_implique_reticule` (E III.14) : conclusion = est_reticule(G,E) malformee,
  non prouvable honnetement. Cible remise a APRES correctif (cf. PLAN_ETAPE_C).
- FIDELITE de `reticule_implique_filtrant_droite_gauche` (commit 0c2e720, III.1.11) : SOUNDNESS intacte
  (certifie noyau), mais il ASSUME est_reticule et n'en extrait que le `majorant` (sain) — son
  hypothese est partiellement malformee, possiblement vacante pour un vrai treillis. A RE-VERIFIER /
  re-aligner apres correctif.
- Autres appelants de borne_superieure/inferieure/admet_borne_sup_inf/est_reticule (~12 fichiers :
  cardinaux sup, Zorn/Bourbaki-Witt, bornes_sup §III.1, prop12_sup_total, ordre_treillis_props) : le bug
  ne mord QUE si A contient des variables libres coincidant avec les liants par defaut x/y ; beaucoup
  utilisent d'autres conventions (liants frais, ex. prop12 = "ys12") et sont probablement SAINS — mais
  TOUS a re-verifier apres correctif.

**Correctif recommande (tache dediee, NON rushee en tick autonome — touche une def centrale + suite
complete a re-verter, tests lents cardinaux/Zorn inclus).** Rendre `borne_superieure`/`borne_inferieure`
capture-safe : freshir automatiquement le liant « plus petit/grand » s'il apparait libre dans A/m
(via libres_f) ; OU a minima, dans `admet_borne_sup_inf`, passer un liant frais distinct de x/y/u pour
le 6e arg. Puis re-aligner `reticule_implique_filtrant` (_bs/_bi + test) sur la nouvelle structure, et
lancer la suite COMPLETE verte avant commit. theorie==22 inchange (correctif structurel de def, 0 axiome).
