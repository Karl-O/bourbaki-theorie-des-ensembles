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

**→ CORRIGE le 2026-06-26.** Option minimale retenue (perimetre PROUVE etroit : `est_reticule`/
`admet_borne_sup_inf` ne sont consommes que par 3 fichiers — reticule_filtrant + 2 tests — TOUS dans
`ordre/` ; `borne_superieure` n'est PAS modifie, donc ses appelants directs cardinaux/Zorn restent
byte-identiques). `admet_borne_sup_inf` passe desormais un liant FRAIS `"mbs"`/`"mbi"` au 6e arg de
borne_superieure/inferieure ; `reticule_implique_filtrant._bs/_bi` + `test_admet_borne_sup_inf_forme`
re-alignes. CAPTURE ELIMINEE, verifiee par substitution : `admet(G,x,y,E)[y:=z] == admet(G,x,z,E)`
(et idem x) -> le y/x de la paire est cohérent dans toute la formule, y compris la clause « plus petit
majorant ». Non-regression : `tests/ordre/` ENTIER vert (Zorn + bornes_sup inclus), test reticule_filtrant
vert (la preuve re-ferme avec les nouveaux liants), `theorie==22`. La fidelite de
`reticule_implique_filtrant` est donc retablie (il assume desormais le vrai « reticule » de Bourbaki).

## 2026-06-26 — Ecart de fidelite (mineur, documente) : heritage ordre point-par-point (E III.6)

`iii_1_6_ordre_produit/ensembles_ordre_applications.py` formalise la DEF `ordre_pointwise`
(f<=g <=> (∀x∈E) f(x)<=g(x), E III.6, **presente VERBATIM** sur la page) + deux HERITAGES :
reflexivite et transitivite, chacun CLOS sous `{ est_ordre(GF,F) }` (verif independante :
conclusion==cible reconstruite depuis primitives, hyps=={est_ordre}, est_clos=False, theorie==22).

**Ecart :** Bourbaki affirme sur E III.6 que l'ordre produit « est une relation d'ordre, comme on le
verifie aisement », SANS detailler separement reflexivite et transitivite pour le cas point-par-point.
Les deux theoremes d'heritage sont donc un **developpement fidele** du « c'est un ordre » du livre, pas
la citation d'une Remarque dediee. Leur `@livre` pointe honnetement vers ce « comme on le verifie
aisement » (E III.6 L.31-33) plutot que vers un enonce Rem. distinct. Pas de sur-attribution : la DEF,
elle, est litterale. Antisymetrie globale (extensionnalite des applications) volontairement HORS scope.

## 2026-06-26 — IMPORTANT (frontiere de confiance) : "pas d'ensemble universel" depend du SCHEMA S8

`ii_1_collectivisantes/ensembles_pas_ensemble_universel.py` prouve `⊢ ¬(∃X)(∀x)(x∈X)` (E II.6 Rem.,
enonce VERBATIM ; conclusion verifiee == cible, sans τ libre). MAIS ce theoreme N'EST PAS derivable des
22 axiomes seuls : former l'ensemble de Russell `{x∈X0 | x∉x}` du pretendu ensemble universel exige le
**schema de selection S8** (c'est la preuve MEME de Bourbaki, E II.7 : « toute relation serait
collectivisante d'apres C52 » — C52 = consequence de S8). L'agent a CORRECTEMENT refuse la version
litterale « zero axiome » (impossible) et porte S8 par une **theorie dediee parametree**
`_theorie_russell_dans(X0)`, exactement comme `theorie_diagonale_cantor` (Cantor) — mecanisme present
dans **41 fichiers** (Cantor, C61 recurrence, recurrence transfinie, powerset…).

**Propriete du noyau a connaitre (verifiee dans noyau.py:177) :** `N.axiome(theorie, A)` renvoie
`Theoreme(frozenset(), A, ...)` — un theoreme CLOS (0 hypothese) — pour TOUT `A` figurant dans la
`theorie` passee, la theorie n'etant gardee que dans la **chaine de justification** (pas dans
`hypotheses`/`est_clos`/`==`/le check `theorie==22`). **Consequence :** `est_clos==True` et
`theorie_ensembles()==22` ne capturent PAS les dependances aux axiomes de theories dediees (instances S8).
La soundness de chaque tel axiome repose donc sur une **revue humaine/agent** qu'il s'agit bien d'une
instance LEGITIME de S8/A1 — ici verifie : `(∀x)(x∈R0 ⇔ (x∈X0 et x∉x))` = comprehension bornee
`{x∈X0 | x∉x}`, meme forme que la diagonale de Cantor. **Lecture honnete de "certifie" dans ce projet :**
« derivable des 22 axiomes + instances de schema S8/A1 revues », pas « des 22 axiomes seuls ». C'est un
argument concret pour un **verificateur croise externe** (cf. discussion durcissement du noyau) : un
second checker devrait recenser les axiomes de theories dediees employes et confirmer que chacun est une
instance de schema admissible. Pas un bug — une propriete de conception (S8 est un vrai schema de
Bourbaki) — mais a tracer explicitement pour le corpus.

## 2026-06-26 — Ecart d'ETIQUETTE "CST8" : DEUX fonctions nommees CST8 encodent en fait IV.3.1

Le vrai **CST8 de §IV.2.1** (E IV.12 : « un σ-morphisme inversible bilatere est un isomorphisme, et
l'inverse est l'iso reciproque ») etait **ABSENT**. Il est desormais formalise dans
`iv_2_morphismes_structures_derivees/ensembles_cst8_inversible_iso.py` (`cst8_morphisme_inversible_est_iso`,
clos-conditionnel : `{morph(E,𝒮,E',𝒮',f), morph(E',𝒮',E,𝒮,g), g=f⁻¹} ⊢ est_iso_morph(E,𝒮,E',𝒮',f)`,
verifie : conclusion==cible reconstruite depuis primitives brutes, hyps EXACTES = ces 3, theorie==22,
5 tests verts). La clause d'inversibilite bilatere `g∘f=Id_E ∧ f∘g=Id_E'` est resumee FIDELEMENT par
son consequent `g = f⁻¹` (= contenu du **corollaire II p.18**, caracterisation des bijections par
inverse bilatere), fourni en hypothese EXPLICITE — meme convention de « brique reportee » que CST3/CST12/CST20.

**MISMATCH a corriger (rapporte, NON corrige a ce stade) :** deux fonctions code portent le nom « CST8 »
mais encodent le critere IV.3.1 (« unicite de la solution universelle a un isomorphisme unique pres »),
PAS le CST8 d'inversibilite de §IV.2.1 :
- `bourbaki/structures/ensembles_structures_complements.py:324` (`solution_isomorphisme_unique`) porte un
  `@livre` FAUTIF `Ch.IV §2.1 Crit.CST8 | E IV.12 | PDF p.215` alors que son propre docstring dit
  « Critere CST8 (IV.3) ». Correction suggeree : `Ch.IV §3.1 Crit.CST8 | E IV.27 | PDF p.~230` (page a
  confirmer sur le PDF avant de figer — offset Ch IV +203 place IV.3 vers p.227+).
- `bourbaki/structures/iv_2_morphismes_structures_derivees/ensembles_structures_props.py:377-379`
  (`solution_universelle_iso_unique`) : bandeau commentaire `CST8, IV.3.1` correct sur le fond (c'est
  IV.3.1) mais nom « CST8 » en collision avec le vrai CST8 de §IV.2.1. Pas de `@livre` machine-lisible
  fautif ici ; nom ambigu a clarifier.
A auditer cote PDF (rendre E IV.27 / p.~230) pour confirmer si Bourbaki nomme effectivement « CST8 » le
critere d'unicite de §IV.3, ou si c'est une derive interne du code. Le module neuf documente deja ce
mismatch dans son docstring.

**→ RESOLU le 2026-06-26 (PDF verifie).** Rendu E IV.22-23 (PDF p.225-226) : §IV.3.1 « Ensembles et
applications universels » commence en E IV.22 ; le resultat d'unicite (« Soient (F'_E,φ'_E) et
(F''_E,φ''_E) deux solutions… une solution… est UNIQUE A UN ISOMORPHISME UNIQUE PRES ») est en **E IV.23**.
Bourbaki l'y demontre EN INVOQUANT le critere CST8 : « **Par suite (IV, p. 12, critere CST8)**, f₁ est un
isomorphisme… ». Donc (a) CST8 = bien le critere d'INVERSIBILITE de E IV.12 §2.1 (confirme aussi par la
Remarque de E IV.22 : « la conclusion resulte du critere CST8 ») ; (b) le resultat d'unicite de §IV.3.1
**n'est PAS numerote CST8** — il l'utilise comme outil. Ce n'etait donc PAS « E IV.27 » (l'estimation de
l'agent etait erronee ; pdf_index : §3.1 = E IV.22, §3.2 existence = E IV.23-… ; offset Ch IV +203).
CORRECTIONS appliquees :
- `ensembles_structures_complements.py` `solution_isomorphisme_unique` : @livre FAUTIF
  `§2.1 Crit.CST8 | E IV.12 | p.215` → **`§3.1 Cor.- | E IV.23 L.6-18 | PDF p.226`** (calé sur les defs
  (AU)/(AU_I')/(AU_II') deja citees a E IV.23 dans `ensembles_universel_applications.py`). Bandeau +
  1re ligne de docstring de-misnommes (« §IV.3.1 unicite, PAS le critere CST8 »).
- `ensembles_structures_props.py` `solution_universelle_iso_unique` (fragment : conclut seulement
  l'inversibilite croisee, pas de @livre machine) : bandeau « (CST8, IV.3.1) » → « (§IV.3.1, E IV.23 ;
  conséquence de CST8, PAS le critere lui-meme) ».
Plus aucune collision de citation : `E IV.12 p.215` = UNIQUEMENT le vrai CST8
(`ensembles_cst8_inversible_iso.py`). 172 tests structures verts (edits commentaire/docstring seulement).

## 2026-07-26/27 — RÉSOLU : `AXIOME_PRODUIT_FAM` avait perdu le conjoint du livre (INFIDÉLITÉ, classe E6)

**LA FAUTE.** `ensembles_abrege.AXIOME_PRODUIT_FAM` (l'un des 22) encodait la Déf. 1 du produit d'une
famille (E II.32, PDF p.83) par ses seuls TROIS derniers conjoints :

    F ∈ ∏(f,I)  ⇔  ( est_fonctionnel(F) ∧ dom F = I ∧ (∀ι)(ι∈I ⇒ F(ι) ∈ X_ι) )

Le conjoint de TÊTE — « F est un élément de 𝔓(I × A) », A = ⋃_{ι∈I} X_ι, que Bourbaki écrit dans le
PRÉAMBULE de la Déf. 1 pour justifier la sélection S8 — avait été perdu à la transcription. Le
commentaire du code annonçait pourtant « sélection dans P(I×A) », et l'axiome FRÈRE `axiome_exposant`
(F^E, E II.5.2) avait, lui, correctement gardé son « G ⊂ E×F ».

**LA MESURE, à 0 hypothèse.** `est_fonctionnel` n'est QUE l'univocité : elle ne dit rien des éléments
de F qui ne sont pas des couples. Le témoin `{∅}` (qui ne contient aucun couple, un couple de
Kuratowski (a,b)={{a},{a,b}} contenant {a} n'étant jamais vide) satisfaisait donc les trois conjoints
retenus, et le corpus démontrait, CLOS :   ⊢ {∅} ∈ ∏(u,∅)   puis   ⊢ ¬( ∏(u,∅) = {∅} ).
Or E II.32 dit, MÊME PAGE : « Si I = ∅, l'ensemble ∏_{ι∈I} X_ι ne possède qu'un seul élément, savoir
l'ensemble vide. » **Le corpus RÉFUTAIT le livre.** Défaut de FIDÉLITÉ, pas de soundness — le noyau
ne garantit que la seconde.

**LA RÉPARATION** (remplacement, PAS un ajout : `theorie_ensembles()` = 22 avant et après ; noyau et
`subst` intouchés). Conjoint rétabli EN TÊTE, forme du livre :

    F ∈ ∏(f,I)  ⇔  ( F ⊂ I × ⋃_{ι∈I} X_ι ∧ est_fonctionnel(F) ∧ dom F = I
                     ∧ (∀ι)(ι∈I ⇒ F(ι) ∈ X_ι) )

Placement EN TÊTE choisi sur mesure comparative : 18 théorèmes à ré-adresser contre 33 en queue
(facteur 1,8) ; en tête, les accesseurs `dom F = I` (chemin g,d) et `(∀ι)…` (chemin d) sont
LITTÉRALEMENT inchangés. Précédent exact : `AXIOME_INTER_FAM`, même journée.

**CE QUI A DÛ MOURIR, ET POURQUOI C'ÉTAIT OBLIGATOIRE.** `hypothese_graphes_produit_vide_refutee`
montrait { (∀F)(F∈∏(u,∅) ⇒ est_un_graphe F) } ⊢ ∅∈∅. Après réparation cette hypothèse est
DÉMONTRABLE (`produit_graphe`, CLOS) : la garder à côté de sa réfutation aurait rendu la théorie
INCOHÉRENTE. Supprimés avec elle : `singleton_vide_dans_produit_vide`,
`produit_vide_n_est_pas_singleton(_enonce)`, `hypothese_graphes_produit_vide`. Ils sont remplacés par
leur MIROIR `singleton_vide_hors_produit_vide` : ⊢ ¬( {∅} ∈ ∏(u,∅) ), CLOS — le corpus cesse de
contredire E II.32.

**LA DÉRIVE SILENCIEUSE (leçon d'outillage).** Sans ré-adressage, `produit_fonctionnel` et
`_fonctionnel_imp` SE CONSTRUISENT ENCORE et restent CLOS : leur conclusion devient
« F∈∏ ⇒ (F ⊂ I×⋃X_ι et fonct F) ». Aucun garde-fou du noyau ne le signale. De même `membre_but`
(iii_3_5) change de conclusion sans rien casser, et son test n'assertait que `est_clos`. **Un test
qui ne vérifie que « ça construit » ne verrouille RIEN** : les cibles sont désormais RECONSTRUITES À
LA MAIN dans les tests, hors des modules testés.

**RIPPLE.** `outils_ia/verite/classer_residu.py` perdait son unique schéma de réfutation certifié
(H-graphe). Il a été REMPLACÉ, pas supprimé, par H-univ := (∃X)(∀x)(x∈X) réfutée par Russell
(`pas_ensemble_universel`) — sans quoi le registre `SCHEMAS_REFUTATION` serait vide et la machinerie
de certification ne serait plus mesurée. ⚠️ DETTE DÉCLARÉE : ce certificat consomme, outre les 22
axiomes, l'instance de sélection S8 de R_b = {x∈b | x∉x} (théorie DÉDIÉE) — l'ancien tenait sur T₀
seule. À composer avec `verite.axiomes_consommes.invariant_reel` (classe E4).


## 2026-07-31 — RÉSOLU : `segment_extremite` avait perdu son PARAMÈTRE D'ORDRE (INCOHÉRENCE, classe E6)

**LE DÉFAUT.** `segment_extremite(R, e, x)` rendait `app("seg_ext", e, x)` : le paramètre d'ordre R
(un *callable* Python) N'ENTRAIT PAS dans le terme.  Deux ordres différents — typiquement un ordre
et son OPPOSÉ — produisaient donc LE MÊME terme.  `axiome_segment_extremite(R)` n'avait aucune
garde et `theorie_segment_extremite(R)` rendait `N.Theorie("Segment-extremite", [ax])` avec un NOM
CONSTANT : autant de théories deux à deux INCOMPATIBLES que de relations R, toutes portant sur le
même terme.  Conséquence dérivée par gestes purs du noyau, 0 hypothèse : `⊢ ∅ ∈ ∅`.  La théorie
ambiante était CONTRADICTOIRE.

**POURQUOI UNE GARDE N'AURAIT RIEN RÉPARÉ.**  Mettre l'axiome sous « R est un ordre sur E » ne
change rien : un ordre ET son opposé satisfont tous deux la garde et se contredisent encore.
L'axiome avait perdu un PARAMÈTRE, pas une condition — la réparation est STRUCTURELLE.

**LA RÉPARATION.**
1. `segment_extremite(G, e, x)` prend le GRAPHE DE L'ORDRE **en tant que TERME** et rend
   `app("seg_ext", G, e, x)` ; une garde `TypeError` REFUSE bruyamment tout callable (aucun site
   non migré ne peut passer en silence).
2. `axiome_segment_extremite()` est désormais une formule **CLOSE**, ∀-close sur G aussi :
   `(∀G)(∀E)(∀x)(∀y)( y ∈ seg_ext(G,E,x) ⇔ ((y∈E et (y,x)∈G) et y≠x) )`, `libres_f == ∅`.
3. `theorie_segment_extremite()` n'a plus de paramètre : UNE théorie, UN axiome clos.
   `theorie_ensembles()` reste à **22** (l'axiome vit dans sa théorie DÉDIÉE).
**Effet dérivé** : plus de variable libre dans l'axiome ⇒ plus de CONSTANTE de théorie ⇒ le défaut
C27 (généralisation sur une constante) disparaît DE CE SITE.

**LA DÉRIVE VOULUE.**  Toute conclusion contenant un terme `seg_ext` change de forme (un argument G
en plus).  Les cibles des tests ont été RECONSTRUITES depuis les primitives, jamais recopiées depuis
la sortie des modules.

**⚠️ CE QUE LA RÉPARATION A RÉVÉLÉ — LE « GATE ℕ » DE III.4 REPOSAIT SUR LE DÉFAUT.**
Trois preuves de `iii_4_entiers_finis/ordinal_cardinal/realisation_segment/` éliminaient `(∃Ro)`
(Zermelo) en s'appuyant EXPLICITEMENT sur le fait que « `seg(a,·,t)` ne porte pas Ro syntaxiquement
— terme `seg_ext(a,t)` » :
  * `ensembles_realisation_segment_preuve.bon_ordre_intervalle_depuis_realisation` (L.324) ;
  * `ensembles_realisation_segment_close.bon_ordre_intervalle_depuis_subset` (L.533).
⚠ NUANCE MESURÉE : `ensembles_gate_onto_top._bon_ordre_intervalle_close_raw` (L.869), qui
élimine AUSSI un `(∃Ro)`, **SURVIT** (test_gate_onto_top VERT) : il DÉCHARGE la garde AVANT de
généraliser, si bien qu'aucune hypothèse résiduelle ne contient Ro.  C'est le BON patron, et il
montre que la réparation proposée ci-dessous est réalisable.  Le résultat capstone
`bon_ordre_intervalle_close` (CLOS, 0 hyp) est donc **INTACT**.
Le segment portant maintenant son graphe, l'hypothèse résiduelle (`realisation_segment_garde` /
`realisation_hypothese` / `subset_realise_segment`) est Ro-DÉPENDANTE, et le noyau REFUSE la
généralisation : `ValueError: généralisation : 'Ro' libre dans une hypothèse` (C27).  **Ces résultats
n'étaient donc démontrables que grâce à l'incohérence.**  16 tests de ce dossier échouaient (sur 391 dans tout `tests/iii_4_entiers_finis` : 375 verts) ;
c'était le signal HONNÊTE, et il a conduit à la réparation ci-dessous.
**RÉPARATION FAITE ET MESURÉE (2026-08-01).**  L'hypothèse Ro-paramétrée est remplacée par sa
forme Ro-CLOSE, dans les deux modules :
  * `ensembles_realisation_segment_preuve.realisation_hypothese_close(a)` :=
    `(∃Ro)( bo_form(Ro,a) ∧ (∀c) realisation_segment(Ro,a,c) )` ;
  * `ensembles_realisation_segment_close.subset_realise_segment_close(a)` :=
    `(∃Ro)( bo_form(Ro,a) ∧ subset_realise_segment(Ro,a) )`.
Le schéma de preuve : on passe le maillon EN ANTÉCÉDENT (et plus seulement `bo_form`), ce qui rend
l'implication CLOSE ; la généralisation sur Ro est alors autorisée et `existe_elimination` passe.
C'est l'IDIOME DÉJÀ EN PLACE au dépôt — `hyp_transport_ordinal` (E III.24) met déjà le bon ordre et
la propriété demandée sous LE MÊME ∃.

**⚠️ CE QUI EST PERDU, NOMMÉMENT.**  ZERMELO SEUL NE SUFFIT PLUS pour ces deux réductions : il donne
un bon ordre, pas la réalisation des segments PAR ce bon ordre ; les deux doivent être demandées
ensemble.  L'ancien énoncé (hypothèse Ro-libre + Zermelo) était STRICTEMENT PLUS FORT et n'était
démontrable que par le défaut.  **En revanche le capstone `bon_ordre_intervalle_close`
(`ensembles_gate_onto_top`, CLOS, 0 hypothèse) est INTACT** — il décharge sa garde AVANT de
généraliser, donc aucune hypothèse résiduelle ne porte Ro (test_gate_onto_top : 13 passed, mesuré).
Ces deux modules restent donc des réductions intermédiaires, désormais plus faibles.

**TESTS.**  `test_garde_est_Ro_independante` est REMPLACÉ (son objet a disparu : la
Ro-indépendance était l'artefact) par
`test_garde_depend_bien_de_Ro_et_le_GATE_la_clot_sous_existe`, qui épingle la garantie NOUVELLE :
(a) garde et maillon DÉPENDENT de Ro, (b) le GATE les referme sous ∃ (hypothèse Ro-close),
(c) l'axiome de segment est CLOS et la fabrique de théorie n'a plus de paramètre.  Les cibles
d'hypothèse sont RÉASSEMBLÉES dans les tests depuis les primitives (`existe`/`et`/`_bo_form_canon`),
jamais recopiées du module ; sonde adverse : 18 contrôles, tous MORDENT (voisin permuté, voisin sans
`bo_form`, ancienne forme Ro-libre, conjonction non close, α-variant).


## 2026-08-01 — DÉFAUT INTRODUIT PUIS CORRIGÉ pendant la migration seg_ext (traçabilité)

`ensembles_factorielle_existence_vrai.factorielle_caracterisation_cible` appelait
`E.segment_extremite(_t(G), ve, m)` alors que ce module n'avait **pas** de helper `_t` (il
n'importait que `var`) : `NameError: name '_t' is not defined`, 5 tests rouges.  Ce n'était PAS une
cible périmée mais un vrai défaut du module migré.  Corrigé en ajoutant le helper `_t` (idiome du
dépôt : `Terme` importé, `return t if isinstance(t, Terme) else var(t)`).  Les tests de mutants du
fichier meurent de nouveau sur une INÉGALITÉ de formule (`MIROIR-CONCLUSION` /
`MIROIR-HYPOTHESES`), jamais sur une exception — vérifié.
Leçon d'outillage : un remplacement textuel `R` → `_t(G)` appliqué par lot doit être suivi d'un scan
AST « le helper existe-t-il dans CE module ? ».  Le scan a été écrit et rejoué : plus aucun module
n'utilise `_t` sans le définir.


## 2026-08-04 — ÉCART DE FIDÉLITÉ : `est_systeme_projectif` omet le TYPAGE des transitions

**LE LIVRE** (§III.7.1, transcription V7 `7_Limites.../1_Limites_projectives/Texte.tex`, fidèle
au scan) : « Pour tout couple (α, β) d'indices de I tels que α ≤ β, soit f_{αβ} **une application
de E_β dans E_α**. On suppose que les f_{αβ} vérifient les conditions suivantes : (LP_I) … (LP_II) … »

Le typage « application de E_β dans E_α » est posé AVANT (LP_I)/(LP_II) et fait donc pleinement
partie de la donnée d'un système projectif.

**LE CODE** (`iii_7_limites/ensembles_limites.py:101`) :
```python
def est_systeme_projectif(f, leq, i, ...):
    return et(cocycle_projectif(...), identite_projectif(...))
```
— soit (LP_I) et (LP_II) SEULEMENT.  **Le typage des transitions est absent.**

**CE QUE ÇA COÛTE, concrètement.**  Toute preuve qui a besoin de « f_{αβ}(z) ∈ E_α pour z ∈ E_β »
ne peut pas l'obtenir de `est_systeme_projectif` et doit la porter comme hypothèse séparée.  C'est
exactement ce qui bloque l'INCLUSION RÉCIPROQUE de la surjectivité de la Prop. 3 (§III.7.2) : pour
placer le prolongement x̃ dans lim←_I il faut x̃_α = f_{αβ(α)}(x_{β(α)}) ∈ E_α, et rien ne le donne.

**AMPLEUR MESURÉE** : 9 références à `est_systeme_projectif` dans `bourbaki/` + `tests/`, dont une
DÉRIVATION (`ensembles_cofinal.py:341` : « {sys. projectif relatif à I filtrant} ⊢
est_systeme_projectif »).  Renforcer la définition rendrait les théorèmes qui la SUPPOSENT encore
valides (hypothèse plus forte) mais casserait cette dérivation et les tests qui épinglent la forme.

**DÉCISION (assumée) — documenter et fournir, PAS modifier en cours de chantier.**  Changer une
définition consommée par neuf sites au milieu d'un autre chantier, c'est prendre le risque de
réparer sous pression des dérivations qu'on n'a pas le temps d'auditer.  La condition manquante est
donc fournie comme constructeur nommé et portée en hypothèse HONNÊTE là où elle sert.  Le
renforcement de `est_systeme_projectif` lui-même est un chantier à part, à faire d'un bloc avec
l'audit de sa dérivation.

**RÈGLE GÉNÉRALE QUI EN SORT** : une définition du livre encodée comme conjonction de ses
*conditions numérotées* peut avoir perdu le TYPAGE énoncé en prose juste avant — le typage n'a pas
de numéro, donc il ne saute pas aux yeux à la relecture.  Vérifier, pour chaque définition
structurée, que la prose introductive n'apportait pas une condition non numérotée.


### 2026-08-05 — RÉSOLUE : le typage des transitions est maintenant DANS la définition

L'écart consigné la veille est **comblé**.  `est_systeme_projectif` porte désormais les TROIS
conditions du livre — le typage des transitions, (LP_I) et (LP_II) — au lieu des deux numérotées.

**Ce qui a rendu la correction possible, et ce que ça apprend.**  La signature ignorait `Efam` :
on ne peut pas énoncer « f_{αβ} envoie E_β dans E_α » sans nommer la famille.  **Le manque était
inscrit dans le TYPE de la fonction, pas seulement dans son corps** — d'où son invisibilité à la
relecture.  La signature a donc gagné `Efam` en tête.

**Ampleur réelle, mesurée avant l'opération** (l'estimation de la veille, « neuf sites dont une
dérivation », était juste mais alarmiste) : la définition composite n'est ASSUMÉE par aucun
théorème du dépôt — les preuves utilisent `cocycle_projectif` directement.  Elle n'est que
*composée* (`est_systeme_projectif_filtrant`) et *projetée*
(`systeme_projectif_filtrant_est_systeme`).  Or renforcer le conjoint droit d'une conjonction ne
casse pas sa projection : la dérivation reste valide telle quelle.  Le renforcement était donc sûr.

**Fait** : `Efam` threadé dans `est_systeme_projectif`, `est_systeme_projectif_filtrant` et les
deux projections ; `transitions_typees` reste exposée séparément, parce que la plupart des preuves
n'ont besoin QUE d'elle et que la porter seule est plus honnête que de supposer tout le système.

**Le test a été INVERSÉ, pas supprimé** : `test_transitions_typees_condition_non_numerotee`
épinglait l'ABSENCE du typage ; il devient
`test_definition_systeme_projectif_est_fidele_au_livre` et épingle sa PRÉSENCE, plus celle des deux
conditions numérotées.  C'est le même test qui garantit qu'on ne reperdra pas le typage.
156/156 iii_7_limites, theorie_ensembles()=22.

**Règle qui en sort** : quand une définition du livre paraît incomplète, regarder d'abord si sa
SIGNATURE peut seulement exprimer ce qui manque.  Un paramètre absent est un symptôme plus fiable
qu'une relecture du corps.


### 2026-08-05 (soir) — la résolution du matin était PARTIELLE : « application » dit TROIS choses

Le comblement consigné plus haut ajoutait `transitions_typees` — « f_{αβ} envoie E_β dans E_α ».
C'est **un tiers** de ce que Bourbaki écrit.  « f_{αβ} une **application** de E_β dans E_α » veut
dire : graphe **fonctionnel**, **défini sur tout** E_β, à **valeurs** dans E_α.

**Comment le manque s'est révélé** — et c'est la partie utile : en tentant l'inclusion réciproque
de la Prop. 3, les hypothèses résiduelles indémontrables se sont avérées être des conditions de
DOMAINE, « (∃y)((t,y) ∈ f_{αβ}) », c'est-à-dire « f_{αβ} est définie en t ».  Elles ont été
identifiées non pas en devinant, mais en **rappelant les briques sources aux mêmes arguments et en
lisant leurs hypothèses**.

**Ajouté** : `transitions_applications` — (∀α)(∀β)((α,β∈I et α≤β) ⇒ f_{αβ} ∈ (E_α)^(E_β)) — et
`transitions_fonctionnelles_et_totales`, qui en tire fonctionnalité et domaine par
`axiome_exposant`.  `transitions_typees` reste : la plupart des preuves n'ont besoin que d'elle.

**⚠️ PIÈGE D'ENCODAGE, à ne pas rater** : c'est l'**exposant** (E_α)^(E_β) — l'ensemble des
GRAPHES fonctionnels — et **non** 𝓕(E_β;E_α), qui est l'ensemble des TRIPLETS ((G,E),F).  Les
transitions du dépôt sont manipulées comme des graphes (`valeur(f_{αβ}, t)`, sans `graphe_de`) :
prendre 𝓕 donnerait un terme qui ne se raccorde à rien, et l'erreur n'apparaîtrait qu'au premier
modus ponens, loin de sa cause.

**RÈGLE** : un comblement de fidélité peut être PARTIEL.  Vérifier qu'on a capturé tout ce que le
mot du livre implique — pas seulement le conjoint qui manquait à la preuve du jour.

## 8 août 2026 — Snapshot lemme_17 (auto-découvert) périmé par le fix subst
`test_tous_les_lemmes_se_recertifient` ROUGE : le lemme 17 (transitivité
couple_egal_si_composantes ∘ coincidence_meme_graphe) se re-certifie CLOS,
mais `repr(conclusion)` ≠ snapshot `_CIBLES[17]` (juillet). Cause : le
court-circuit `(T|x)t = t si x∉libres(t)` (fix subst du 24 juillet) supprime
des renommages gratuits → les lieurs canoniques `@n` de la conclusion
re-dérivée diffèrent (2611 → 2597 caractères). α-variants ≠ dans ce noyau :
le snapshot est re-calé sur la forme ACTUELLE (commentaire daté en place),
l'ancienne repr est perdante par construction. Seul le NOM des lieurs change ;
la certification (clos, 22 axiomes) n'a jamais cassé. Les 19 autres snapshots
sont inchangés. Leçon : les catalogues à snapshot-repr sont fragiles aux
changements de canonicalisation — re-vérifier après tout fix de subst.

## 2026-08-10 — `est_premier` ne contraint pas p à être un entier (FIDÉLITÉ)

**Constat** (`outils_ia/conjectures/goldbach.py:95`) :
`est_premier(p) := ¬(p=1) ∧ (∀d)((Fini d ∧ divise_propre(d,p)) ⇒ (d=1 ∨ d=p))`.
La garde `est_fini` porte sur le **diviseur** d, jamais sur **p**. Or
`divise_propre(d,p)` = `(∃q)(Fini q ∧ p = Card(d×q))` exige que p soit
littéralement un terme `Card(·)`. Si p n'est pas un cardinal, **aucun d ne le
divise**, la clause (∀d) est vacuously vraie, et « p premier » se réduit à
« p ≠ 1 ».

**Mesuré (noyau, scratchpad `PB32_audit_premier.py`)** :
`A1 : ⊢ ( ¬(p=1) ∧ (∀d)¬divise_propre(d,p) ) ⇒ est_premier(p)` — CLOS.
Autrement dit : *tout objet indivisible et ≠ 1 est « premier »*.

**Portée.** Soundness INTACTE (aucun faux théorème : les preuves existantes
construisent des témoins numéraux). C'est un défaut de **fidélité** :
`goldbach()` et `decomposition(2n)` quantifient sur des témoins non
contraints à être des entiers, donc l'énoncé formalisé est **plus faible**
que la conjecture de Goldbach. Même famille que l'incohérence de
l'intersection (26 juil.) : le noyau garantit qu'on ne prouve rien de faux,
pas qu'on prouve la bonne chose.

**Symptôme rencontré** : blocage du sens retour de GG18 (forme crible) — on
ne peut pas placer un témoin p dans [0,2k] sans savoir qu'il est un cardinal.

**Correction proposée** (NON APPLIQUÉE — décision d'énoncé = Karl) :
`est_premier_ent(p) := est_fini(p) ∧ est_premier(p)`. Mesuré `A2` : la garde
est **gratuite** sur les numéraux (`fini_num(2) ∧ est_premier_num(2)`, clos),
donc la correction ne coûte rien aux acquis — elle ajoute une obligation
`Fini(p)` là où les témoins sont construits, ce qui est déjà le cas partout.

## 2026-08-11 — L'associativité de « + » sur les cardinaux n'est PAS au format attendu

**Constat.** `somme_cardinale_associative(A,B,C)` (exposée par
`iii_3_3_somme/ensembles_arith_somme.py`, ré-export de
`ensembles_somme_associe.py`) démontre

    Card((A⊔B)⊔C) = Card(A⊔(B⊔C))

et sa docstring annonce « = (a+b)+c = a+(b+c) ». **Ce n'est pas le même
énoncé.** Avec `SC(x,y) := Card(x⊔y)`, la forme itérée s'écrit

    SC(SC(A,B),C) = Card( Card(A⊔B) ⊔ C )

— il y a un `Card` **de plus** au niveau interne. Les deux termes sont
distincts pour le noyau ; aucune des deux formes ne se réécrit en l'autre sans
un lemme d'invariance (la somme cardinale ne change pas si l'on remplace un
argument par un ensemble équipotent).

**Portée.** Soundness intacte : le théorème prouvé est vrai et clos. C'est un
écart **prose / code** (le piège déjà rencontré sur `prop2_sous_fini`, dont la
docstring annonçait une forme conjonctive et le code une forme curryfiée) —
*la prose n'est pas un contrat, le code l'est*.

**Conséquence mesurée** (script `ALG2_associativite.py`, 11 août) : la machine
ne peut pas établir l'associativité d'une opération dérivée `a ⊕ b := (a+b)+1`,
non par manque d'organe, mais parce que **le lemme requis n'est pas au dépôt**.
Le premier diagnostic (« il manque un moteur de réécriture ») était donc
incomplet : l'organe v17 fonctionne (vérifié sur des chaînes à 1 et 2 pas), le
pool est vide de ce qu'il faudrait enchaîner.

**Reste à faire** : démontrer `SC(SC(a,b),c) = SC(a,SC(b,c))` sur les cardinaux
(via l'invariance de `Card` par équipotence), ou documenter que seule la forme
« sommes disjointes sous Card » est disponible. Chantier non ouvert.

## 2026-08-11 — L'associativité ITÉRÉE de « + » manquait (COMBLÉ)

**Constat.** Le dépôt démontre `somme_cardinale_associative` :
`Card((A⊔B)⊔C) = Card(A⊔(B⊔C))` — l'associativité au niveau des sommes
**disjointes**. Ce n'est PAS la forme itérée dont tout calcul a besoin :
`SC(SC(a,b), c)` vaut `Card( Card(a⊔b) ⊔ c )`, avec un `Card` **de plus à
l'intérieur**. Aucun théorème du dépôt ne permettait de le résorber.

**Le chaînon absent** — l'invariance de la somme par équipotence :

    Card( Card(X) ⊔ Z ) = Card( X ⊔ Z )        (et le symétrique à droite)

Preuve : `Eq(Card X, X)` (symétrie de `equipotent_son_cardinal`) et `Eq(Z,Z)`
donnent `Eq(Card X ⊔ Z, X ⊔ Z)` par `eq_somme_invariant` ; la Prop. 1 conclut.

**COMBLÉ** (scratchpad `ASSOC1_somme_cardinale.py`, 6 s) :

    ⊢ SC(SC(a,b), c) = SC(a, SC(b,c))          CLOS, 0 hypothèse, theorie == 22

**Portée.** Avec la commutativité (déjà au dépôt), le neutre `0` et cette
associativité, les cardinaux forment un **monoïde commutatif** — la première
structure algébrique complète disponible pour la machine.

**Promotion suggérée** : ce résultat est **dans Bourbaki** (III.3.3), il a donc
sa place dans `bourbaki/iii_3_3_operations_cardinaux/iii_3_3_somme/`, PAS dans
`recherche/`. Deux lemmes à exposer : `invariance_somme_gauche/droite`, puis
`somme_cardinale_associative_iteree`.

**PIÈGE MESURÉ (coûteux).** `equipotence_symetrique` et `eq_somme_invariant`
portent des liants de graphe **canoniques** (`F`, `G`). Les généraliser puis
instancier les α-renomme et fait échouer un modus ponens **interne** à la
fonction. Ces deux fonctions acceptent des TERMES en argument : il faut les
appeler **directement**, jamais via `generalisation`/`instancie`.

---

## 12 août 2026 — DÉFAUT D'OUTILLAGE : un organe écrit DEUX FOIS

**Constat.** L'organe v17 (réécriture par les égalités du pool) existait en
deux exemplaires, écrits à un jour d'intervalle et par la même main :

| fichier | date | moteur | testé |
|---|---|---|---|
| `autonomie/reecriture.py` | 11 août | largeur d'abord, bornes explicites | oui (`test_organe_v17_chaine_de_reecritures`) |
| `autonomie/congruence.py` | 12 août | profondeur d'abord, via la récursion de `besoins` | non |

`besoin.py` appelait **les deux**, sous le même alias `_fpr`, l'un après
l'autre. Aucun test ne l'a vu : les deux sont *corrects*, donc la suite
restait verte — le doublon coûtait du temps de calcul, pas de la justesse.

**Conséquence mesurable.** `congruence.py` était passé à **356 lignes de code**,
au-delà de la barre de 300 fixée par les conventions du projet.

**Cause.** Le second a été écrit à partir du diagnostic (« il faut chaîner des
égalités ») sans relire le contenu du dossier `autonomie/` — dont le nom de
fichier `reecriture.py` disait pourtant exactement ce qui existait déjà.

**Réparé.** Un seul moteur, celui de `reecriture.py` (mieux conçu : largeur
d'abord, donc chaînes courtes en premier ; bornes `max_pas`/`max_noeuds`
explicites ; test dédié). L'apport propre du second — l'instanciation des lois
— y a été porté, et **amélioré au passage** : au lieu d'énumérer les instances
à l'avance, la loi est matchée *au moment d'être appliquée* (`_instances`),
ce qui est moins cher et couvre les termes intermédiaires que l'énumération
initiale ne pouvait pas voir.

| fichier | avant | après |
|---|---|---|
| `congruence.py` | 356 | **235** |
| `reecriture.py` | 128 | **167** |
| `besoin.py` | 299 | **285** |

**Garde à retenir** (généralisable, c'est là l'intérêt) : *avant d'écrire un
organe, lister le dossier `autonomie/`*. Les noms de fichiers y sont la table
des matières des capacités de la machine — `congruence.py`, `reecriture.py`,
`general.py`, `premiers.py`. Un organe dont le nom existe déjà est un organe à
enrichir, pas à réécrire.

---

## 12 août 2026 — LES LIANTS CANONIQUES : deux familles, deux traitements OPPOSÉS

Ce piège a mordu **trois fois en une matinée**, sous deux formes contraires.
Il vaut donc une règle de détection, pas une note de plus.

**Le symptôme est toujours le même** : `ValueError: modus ponens : mineure ≠
antécédent`, levé **à l'intérieur** du lemme appelé — pas dans notre code. La
cause est un liant que la généralisation ou l'instanciation a α-renommé, alors
qu'une étape interne du lemme comptait dessus.

**FAMILLE A — appeler DIRECTEMENT, jamais généraliser.**
`equipotence_symetrique`, `eq_somme_invariant`. Ces fonctions acceptent des
TERMES pour leurs arguments mathématiques ; leurs liants canoniques (`F`, `G`)
ne servent qu'aux graphes internes. Les généraliser puis instancier renomme les
graphes et casse un modus ponens interne.

```python
eq_somme_invariant(f="F", g="G", a=A, b=B, a1=A1, b1=B1)   # ✅ direct
```

**FAMILLE B — appeler sur SES PROPRES noms, puis généraliser, puis instancier.**
`simplification_additive_finie` (récurrence, liant `aSA`), `prop2_sous_fini`
(variables `a`/`b`/`c` libres). Ces fonctions sont prouvées AVEC leurs noms ;
leur passer un terme court-circuite la construction.

```python
gen = N.generalisation("aSA", simplification_additive_finie("aSA"))  # ✅
simp = instancie(gen, mon_terme)
```

**LA RÈGLE DE DÉTECTION, actionnable avant d'écrire une ligne.** Lire la
signature :

| ce qu'on voit | famille | traitement |
|---|---|---|
| des paramètres qui acceptent des TERMES (`a=A`, `x=u`) **et** des paramètres de liant séparés (`f="F"`) | A | appel direct |
| tous les paramètres sont des NOMS de variables (`a="aSA"`, `a="a"`) | B | propres noms → généraliser → instancier |

Autrement dit : **si le lemme sait déjà prendre un terme, donne-lui le terme ;
s'il ne prend que des noms, ne lui donne jamais un terme.** Le mélange des deux
est ce qui coûte du temps — les deux traitements sont l'exact inverse l'un de
l'autre, donc appliquer le mauvais échoue à tous les coups.

**Contexte des trois occurrences** : `ASSOC1` (famille A, `F`/`G` — associativité
itérée) ; `symetrie.py` (famille A, pont-α gardé) ; `DEMI1` (famille B, `aSA` —
simplification additive). Les deux premières ont été résolues en appelant
direct, la troisième en faisant l'inverse.

---

## 12 août 2026 — LOI : LES TERMES SONT OPAQUES, LES FORMULES NE LE SONT PAS

**Découverte en construisant l'oracle numérique, et valable pour tout futur
évaluateur, simplificateur ou analyseur de termes.**

Dans ce noyau, `N(7)` et `N(3) + N(4)` sont **tous deux** des τ-termes de
`tag == 'tau'` avec **un seul argument** (une formule). Il n'y a donc rien à
décomposer dans un terme arithmétique : `SC(a, b)` n'est PAS un nœud binaire
d'enfants `a` et `b`.

**Conséquence** : aucun évaluateur ne peut fonctionner par descente dans les
termes. La seule voie est la **reconstruction** — bâtir le terme attendu et
comparer. C'est praticable parce que les assemblages sont hashables et que
l'égalité est en O(1) ; c'est impraticable si l'on reconstruit à chaque appel.
D'où : **une table bâtie une fois**.

**Les FORMULES, en revanche, se décomposent normalement** (`¬`, `∨`, `∃`, `=`).
Et comme `et`, `⇒`, `∀` en sont des abréviations, évaluer les primitives les
donne gratuitement. La frontière « formule décomposable / terme opaque » est
la structure obligée de tout outil de ce genre.

**Mesure** : descente naïve 333 s → table 3 s, **facteur 100**, sur le même
jeu de six évaluations.

**J'ai fait l'erreur DEUX FOIS en vingt minutes** — d'abord sur les termes,
puis sur la reconnaissance des prédicats, où je naviguais à coups de
`.sous[0].sous[1].sous[0]`. La seconde fois, appliquer la loi qu'on venait
d'écrire a marché du premier coup. C'est le même défaut que
`PIEGES_MESURES` §9 (« ne pas naviguer dans les sous-formules ; reconstruire
et asserter »), généralisé : **ne jamais supposer une structure, la regarder.**
Une introspection de trois lignes (`type`, `tag`, `len(args)`) a réglé en
quelques secondes ce que deux hypothèses successives avaient coûté.


## 2026-08-19 — NUMÉROTATION DE LIGNES DILATÉE sur 8 pages (109 marqueurs)

**Trouvé en cherchant systématiquement les marqueurs qui désignent des lignes
inexistantes**, après en avoir corrigé un à la main (`Prop.2 | E II.31 L.41-44`
alors que la page compte 37 lignes — commit 5bb1e59).

**Le fait.** 36 marqueurs revendiquent une ligne `L.≥50`. Une page imprimée de
Bourbaki en compte 35 à 49. Ils se concentrent sur 8 pages, qui portent en tout
**109 marqueurs** :

    Ch.II  p.59 (E II.8)   p.73 (E II.22)  p.74 (E II.23)  p.84 (E II.33)
    Ch.II  p.86 (E II.35)  p.89 (E II.38)
    Ch.III p.132 (E III.29)
    Ch.IV  p.208 (E IV.5)

**Le cas d'école, E II.22 (PDF p.73), 34 marqueurs.** Ils situent la Définition 1
(réunion) en `L.31-36` et la Définition 2 (intersection) en `L.49-53`. Page
ouverte et comptée : la Déf. 1 est en **L.15-18**, la Déf. 2 en **L.27-30**, et
la page se termine vers **L.37** sur une note de bas de page. L'échelle est
donc dilatée d'un facteur ~2 au début et ~1,8 plus loin — non constant, donc
pas un simple décalage.

**Conséquence mesurée.** Les marqueurs d'une même page restent COHÉRENTS ENTRE
EUX (26-30, 31-36, 38-40, 49-53 forment une suite croissante) ; c'est le rapport
au livre qui est faux. `gen_trous_livre.py` signale alors des intervalles vides
de cette échelle fantôme — les « trous » L.37-37 et L.41-48 de la p.73 n'existent
pas dans le livre. Une part des 177 trous restants vient de là.

**POURQUOI JE NE CORRIGE PAS.** Renuméroter 109 marqueurs d'après mon propre
comptage de lignes sur un scan introduirait probablement plus d'erreurs que
cela n'en retire — j'ai déjà commis une erreur de comptage le 18 août (trois
`Demo.-` posés sur des clôtures d'énoncé, corrigé en 452f071). Cette correction
demande le livre en main et une passe délibérée, page par page, pas un script.

**CE QUE ÇA COÛTE EN L'ÉTAT.** Rien pour la soundness : ces marqueurs ne
touchent aucune preuve, la suite reste verte et `theorie_ensembles()` vaut 22.
Le coût est sur la FIDÉLITÉ (un `@livre` doit caler la notion sur le livre) et
sur le SIGNAL du détecteur de trous, qui reste bruité tant que ces 8 pages ne
sont pas recalées.

**COMMENT LE RETROUVER.** Les pages suspectes se listent en une commande : tout
marqueur dont la borne haute atteint 50 est fautif, et un décrochage brutal
entre le max et le 2ᵉ max des bornes d'une même page trahit le même défaut à
plus petite échelle.

## 2026-08-19 (2) — LA CONVENTION `L.x-y` N'EST PAS LA MÊME D'UNE PAGE À L'AUTRE

**C'est la racine du travail de marqueurs restant, et elle interdit de le
poursuivre au jugé.** `CLAUDE.md` définit `L.<l1>-<l2>` comme « les lignes sur
CETTE page ». Quatre pages ouvertes et comptées à la main aujourd'hui donnent
quatre décalages différents entre le marqueur et la ligne physique :

| page | notion repère | marqueur dit | ligne physique | décalage |
|---|---|---|---|---|
| E II.6 (p.57) | Th. 1 | L.24-27 | L.24-27 | **0** |
| E II.10 (p.61) | Déf. 2 | L.6-8 | L.6-8 | **0** |
| E II.7 (p.58) | Prop. 1 | L.3-4 | L.5-6 | **−2** (le comptage semble démarrer au titre « §2. COUPLES ») |
| E II.22 (p.73) | Déf. 1 | L.31-36 | L.15-18 | **×2 environ**, non constant |

Un marqueur de E III.46 porte d'ailleurs la mention « lignes RECOMPTÉES sur le
PNG le 27 juil. 2026 » : quelqu'un avait déjà buté sur le problème et recalé
cette page-là seule.

**CE QUE ÇA IMPLIQUE.** Tant que la convention n'est pas tranchée, poser ou
élargir un marqueur revient à choisir arbitrairement l'un des comptages — et
produit un travail plausible mais faux, que la suite de tests laissera passer
sans broncher (le noyau juge la soundness, jamais la fidélité). Sur E II.7,
« élargir l'ancre pour couvrir le trou » donnerait un résultat différent selon
qu'on suit le comptage physique ou celui des deux marqueurs déjà en place.

**LA DÉCISION À PRENDRE, et elle appartient à Karl** — trois options :
1. **La ligne physique imprimée** (en-tête courant exclu, titres et notes de
   bas de page inclus). C'est ce que dit CLAUDE.md aujourd'hui. Coût : recaler
   les pages fautives, dont les 8 « dilatées » (109 marqueurs) et celles à
   décalage constant.
2. **Assouplir la spécification** : `L.x-y` devient un repère *relatif et
   cohérent par page*, pas une coordonnée absolue. Coût nul, mais on perd la
   possibilité de vérifier un marqueur contre le scan.
3. **Rendre le détecteur tolérant** : ne signaler un trou que s'il dépasse une
   largeur (3-4 lignes), ce qui absorbe le bruit de comptage sans rien
   corriger. Palliatif, pas remède.

**EN L'ÉTAT, le chantier des marqueurs restants est SUSPENDU à cette
décision.** 25 des 45 marqueurs non-démo du tri du 18 août sont concernés.
Ce qui a pu être corrigé sans ambiguïté l'a été (commits 452f071, 5bb1e59,
3f0ee94, 0b5e515) ; le reste attend la règle.

---

## 2026-08-20 — La convention `L.x-y` des `@livre` : DEUX références coexistent

**Statut : MESURÉ, non corrigé.** Ceci clôt la question laissée en suspens le 19 août
(« quelle convention adopter ? »). Ce n'était pas une décision à prendre : c'était une
mesure à faire.

### Ce qui a été trouvé

`E II.22` (PDF p.73) a été comptée à la main : **36 lignes imprimées** en tout, en-têtes
et note de bas de page comprises. Déf. 1 y occupe les lignes **15-18**, Déf. 2 les
lignes **27-30**.

Les marqueurs du dépôt disent `L.31-36` (Déf. 1) et `L.49-53` (Déf. 2). Le second
**dépasse la page**. Mais dans la transcription V7
(`Chapitre_II.../4_Reunion_et_intersection.../1_Definition.../Texte.tex`), la ligne 53
est exactement `\paragraph{Définition 2}` : **ces marqueurs indexent le `Texte.tex`, pas
le livre.**

Sur `E II.7`, c'est l'inverse : le marqueur `L.3-4` de la Prop. 1 est proche de la ligne
imprimée (5-6, écart −2) et ne correspond pas à V7 (la Prop. 1 y est en 6-8).

### Le chiffre

Sur les **1 992** marqueurs portant un intervalle :

| seuil | marqueurs | part |
|---|---:|---:|
| fin > 36 (≈ une page pleine) | 243 | **12,2 %** |
| fin > 45 | 64 | 3,2 % |
| fin > 55 | 6 | 0,3 % |
| maximum | 63 | — |

Le gros de la distribution a la forme d'une page imprimée ; la queue de 12 % ne peut pas
en être une.

### Conséquence, et ce qu'on en fait

- **La PAGE est fiable.** C'est elle qui porte les 5 parties « complètes sur
  l'intervalle » et les 0 marqueur non conforme de `gen_livre_manifestes`.
- **L'intervalle de LIGNES ne l'est pas, de façon non uniforme.** Les trous intra-page de
  `gen_trous_livre.py` restent une **heuristique de localisation** — utile pour savoir où
  regarder, sans valeur de mesure.
- `CLAUDE.md` a été corrigé : la convention y est maintenue pour ce qu'on écrit
  désormais, avec l'avertissement que l'existant ne la tient pas.
- L'article A1 a été recalé en conséquence : il revendique la traçabilité **à la
  granularité de la page**, et présente les intervalles comme heuristiques. C'était une
  revendication trop forte, et c'est le propre thèse de A1 retournée contre lui — aucun
  test n'attrape un marqueur qui décrit mal le livre.

### Ce qui reste ouvert

Le recalage des ~243 marqueurs hors-page n'est pas fait, et il demande d'ouvrir les
pages une à une. Rien ne presse : aucun résultat n'en dépend, puisque plus rien ne
s'appuie sur l'intervalle.
