# Relecture avant commit — état au 10 août 2026, 10h05

**Rien n'est commité** (règle du projet : Karl commite lui-même). Ce document
dit **quoi relire, où, et pourquoi** — pas plus.

---

## 1. Le point important : ces fichiers ne sont pas *modifiés*, ils sont *neufs*

`git status` les donne **untracked** (`??`) — ils n'ont jamais été versionnés.
Il n'y a donc **aucun diff à lire** : c'est une relecture de code neuf.

| Fichier | Lignes | Code seul | Statut git |
|---|---:|---:|---|
| `outils_ia/decouvertes/besoin.py` | 311 | **259** | untracked |
| `outils_ia/decouvertes/autonomie/general.py` | 91 | — | untracked |
| `outils_ia/decouvertes/test_autonomie.py` | 450 | 385 | untracked |
| `outils_ia/conjectures/primalite_negative.py` | 147 | — | untracked |
| `docs/articles/` (4 fichiers) | — | — | untracked |
| `docs/journal/ANOMALIES.md` | +281 | — | modifié |

⚠️ **Limite de taille** : `besoin.py` est à 259 lignes de code (barre : 300).
Il reste de la marge, mais le prochain organe la consommera — prévoir
l'éclatement (`besoin.py` + `besoin_organes.py`) plutôt que d'attendre.

---

## 2. `besoin.py` — les neuf organes, dans l'ordre du fichier

Chaque organe est né d'un **diagnostic mesuré**, jamais d'une intuition. Le
commentaire au-dessus de chacun cite l'événement qui l'a motivé.

| Ligne | Organe | Ce qu'il fait | Né de |
|---:|---|---|---|
| 85 | **v9** | but `t = t` fermé par réflexivité | route JUMELLE traînant `2k = 2k` |
| 100 | **v4** | instancie les faits-∀ du pool | `S{n}` de la descente restait inerte |
| 129 | **v8** | but-conjonction décomposé puis recomposé | cœur additif de Goldbach |
| 155 | **v7** | ∃-descente à témoins proposés | aucun but `∃` n'était attaquable |
| 194 | **v5** | les faits-∀ d'implication deviennent des routes | idem, côté implications |
| 213 | **v6** | proposeurs de témoins (point d'extension) | manque terminal `¬(n=n)` |
| 269 | **v2** | conjoints re-soumis + recomposition ∧ | PB14-15 : jamais re-soumis |

**Points de vigilance pour ta relecture** :
1. **v9 est le plus intrusif** — il ferme un but avant tout le reste. Garde
   stricte `but.termes[0] == but.termes[1]` ; le noyau juge quand même
   (`N.reflexivite`). *Effet de bord mesuré* : deux tests utilisaient
   `egal(y,y)` comme échafaudage commode et se trouvaient court-circuités ;
   ils ont été réécrits avec des buts `∃`, intention intacte.
2. **v7 jette les manques** des routes-témoins qui échouent (choix assumé :
   sinon le reporting explose). Si un jour un manque paraît « disparu », c'est
   là qu'il faut regarder.
3. **v6/v7 sont des points d'extension** : les proposeurs (v10, v11) sont des
   *fonctions passées en paramètre*, `besoin.py` ne les connaît pas.

---

## 3. `test_autonomie.py` — 13 tests

Trois anciens (imprimeur, besoin, chaîne miniature) et **dix** qui protègent
les organes, dont les deux derniers écrits ce matin :
`test_organe_v10_proposeur_par_appartenance` et
`test_organe_v11_proposeur_par_schema`.

**Non-régression vérifiée** : suite complète `outils_ia/decouvertes/` =
**22 passed en 28:50** (le test lent d'Euclide inclus).

---

## 4. Décisions qui t'appartiennent

**(a) L'énoncé de `est_premier`** — c'est la plus importante.
L'audit (`ANOMALIES.md`, 10 août) montre que `est_premier(p)` ne contraint pas
`p` à être un entier, donc `goldbach()` est **plus faible** que la conjecture.
La correction `Fini(p) ∧ est_premier(p)` est gratuite sur les numéraux, et
c'est elle qui **débloque** le sens ⇒ de l'équivalence crible (GG19).
Migrer touche : `primalite.py`, `goldbach_borne*.py`, les archives ≤ 86, et
tous les GG. **Je n'ai rien modifié.**

**(b) L'accueil des théorèmes GG** — `outils_ia/conjectures/` est **plein**
(10 entrées). Les promouvoir suppose de l'éclater, par exemple :
`conjectures/goldbach_crible/` (P₂ₖ, miroir, GG19–GG24) et
`conjectures/goldbach_tau/` (GG9, GG10, générateur de routes-témoins).
Les scripts vivent en scratchpad en attendant — ils sont rejouables via
`CAPSTONE_crible.py` (9 maillons, 8 s, « tout compose »).

**(c) La marge de `besoin.py`** — éclater maintenant ou au prochain organe.

---

## 4 bis. Plan de promotion des théorèmes GG (prêt à exécuter)

Les scripts vivent en scratchpad (~1200 lignes pour l'arc crible). Voici où
chacun irait, si tu valides l'éclatement de `conjectures/`. **Rien n'est
déplacé.**

**Nouveau dossier `outils_ia/conjectures/goldbach_crible/`** (5 entrées) :

| Fichier proposé | Contenu | Source scratchpad | Lignes |
|---|---|---|---:|
| `ensembles_premiers_bornes.py` | `P_b`, axiome dédié, GG14/GG14b/GG15 | `PB29a` + `PB29b` + `PB29c` | ~250 |
| `ensembles_crible_equivalence.py` | `Q_b`, GG19a/GG19b | `PB33` | ~215 |
| `ensembles_crible_structure.py` | GG22, GG23, GG25 | `PB38` + `PB40` + `PB44` | ~280 |
| `ensembles_crible_synthese.py` | GG21, GG24 | `PB36` + `PB39` | ~200 |
| `LIVRE.md` | généré | — | — |

**Nouveau dossier `outils_ia/conjectures/goldbach_tau/`** (3 entrées) :

| Fichier proposé | Contenu | Source | Lignes |
|---|---|---|---:|
| `ensembles_pont_tau.py` | GG9, GG10 (Goldbach sans ∃) | `GG9_pont_tau` | ~172 |
| `ensembles_routes_temoins.py` | générateur `route_temoin(T,Q)` + famille | `PB28` | ~130 |
| `LIVRE.md` | généré | — | — |

**Tests** : `tests/outils_ia/conjectures/goldbach_crible/` en miroir, plus
`CAPSTONE_crible.py` converti en test d'intégration (12 maillons, 43 s —
marqueur `slow`).

**Travail réel de promotion** : les scripts sont des `_main()` avec prints ;
il faut les convertir en fonctions nommées rendant des `Theoreme`, ajouter les
marqueurs `@livre` (ces énoncés ne sont **pas** dans Bourbaki — il faudra
convenir d'un marqueur « hors-livre » ou d'un dossier `recherche/` distinct
de la formalisation du livre). **C'est le point à trancher en premier** :
l'arbre `bourbaki/` calque le livre, or Goldbach n'y est pas.

---

## 5. Ce qui est déjà garanti

- `theorie_ensembles()` = **22 axiomes** à chaque exécution de chaque script.
- Noyau, `subst`, `outil_formule` : **intouchés**.
- Aucun `_CLE`, aucun `Theoreme(...)` fabriqué, aucun monkeypatch.
- Chaque théorème cité est **clos** (0 hypothèse non déchargée).
