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
