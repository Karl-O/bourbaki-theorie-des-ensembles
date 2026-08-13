# Système d'IA auto-améliorant sur noyau LCF + corpus Bourbaki

*Point d'entrée : `python outils_ia/corpus/tour.py`. Frontière de confiance : le noyau seul juge,
invariant `theorie_ensembles() == 22 axiomes`. Aucun outil ne mute `bourbaki/` (dry-run/préflight).*

## 1. La vision

Un système qui **s'auto-améliore** en mathématiques formelles : il ne se contente pas de *prouver*,
il **invente des notions** qu'on ne lui a pas données et **trouve des problèmes qu'il résout**, en
boucle, chaque tour bâtissant sur le précédent. Le tout **sans jamais pouvoir se tromper** : le noyau
LCF certifie chaque objet, donc « le système découvre » n'entame pas « aucun théorème faux ».

Deux moitiés (le **volant wake-sleep**), chacune avec son **compounding** (elle *compose*, ne se
contente pas d'accumuler) :

```
        ┌─────────────────────── NOYAU LCF (récompense parfaite, 22 axiomes) ───────────────────────┐
        │                                                                                            │
   ABSTRACTION  ── invente des notions par compression ──►  compose en NOTIONS D'ORDRE 2             │
   (flywheel)        (motif récurrent → tactique nommée)     (une notion bâtie sur une notion)       │
        ▲                                                                                            │
        │                                                                                            ▼
   DÉCOUVERTE  ── trouve des problèmes & les résout ──►  découvre en PROFONDEUR CROISSANTE            │
   (conjecturer)     (chaîne des théorèmes, à σ près)      (un théorème bâti sur un théorème)        │
        └────────────────────────────────────────────────────────────────────────────────────────────┘
```

## 2. Les organes (fichiers `outils_ia/corpus/`)

| Fichier | Rôle | Statut |
|---|---|---|
| **`antiunif_notions.py`** | Anti-unificateur : détecte les *slots* (paramètres) d'un motif récurrent = dual du remplisseur-de-slots du TreeNN | ✅ |
| **`promo_notion.py`** | Promeut un motif en tactique dérivée nommée + **gate noyau (MDL)** : garde ssi corpus plus court & 0 théorème faux | ✅ |
| **`flywheel.py`** | Un tour d'abstraction : mine→anti-unifie→promeut, mesure le **compounding** (portée-CAP + macros d'ordre 2), écrit la biblio | ✅ |
| **`notions_apprises.py`** | Bibliothèque de notions apprises (auto-générée, régénérée chaque tour) | ✅ (généré) |
| **`conjecturer.py`** | Découverte régime ⇒ (transitivité + détachement, **matching σ**, dédup α, **tri par intérêt**, itération `--rounds`) + CLI + ré-exports | ✅ |
| **`conj_base.py`** | Briques pures : matching σ, 4 détecteurs de forme, clé α-canonique, intérêt, **subsomption** (anti-collapse) | ✅ |
| **`conj_regimes.py`** | Régimes **=, ⇔, ⊂** (transitivités dérivées noyau) + **pont S6** `=→⊂` + compounding des égalités | ✅ |
| **`conj_existe.py`** | Régime **∃** : ∃-intro par témoin (S5), abstraction des sous-termes récurrents | ✅ |
| **`tour.py`** | Orchestrateur : **un tour complet** (abstraction + découverte), journal unifié | ✅ |
| **`test_antiunif_notions.py`**, **`test_conjecturer.py`** | Tests (AST pur + chaînage noyau) — **10 verts** | ✅ |
| `flywheel_journal.jsonl`, `tour_journal.jsonl` | Trace des tours (métriques) | ✅ (généré) |

*Substrat réutilisé (méta-algo, pas 1-41)* : `proto_library_learning.py` (mineur AST, 1223 macros),
`repair_learned.py`, `export_corpus.py`, `proto_mutation_verify.py`, `gen_paires_corruption.py`
(harnais de re-vérification noyau `_statut`), `proto_synth_*.py` (TreeNN, courbe CAP).

## 3. Comment ça invente des notions (axe ABSTRACTION)

4 étages, tous kernel-safe (jamais un axiome ajouté) :
1. **Extraction** — le mineur AST sort les sous-DAG récurrents inter-modules (motifs à ≥k occurrences).
2. **Anti-unification** — aligne les N instances (α-normalisées) ; les positions divergentes = les
   *paramètres* de la notion. Détecte exactement les slots prédits : `{pr1,pr2}`, `{AXIOME_*}`, `'x'/'y'`.
3. **Promotion + nommage** — le motif paramétré devient une tactique dérivée ; le lemme est prouvé
   **une fois** par le noyau (reste dérivé → 22 axiomes intacts).
4. **Gate MDL** — on ne garde la notion que si le corpus re-typé **rétrécit strictement** ET repasse
   le noyau (sinon rollback). Le noyau ne laisse jamais passer un faux.

**Compounding** : une notion promue = 1 primitif ; à budget-noyau fixe (CAP), des preuves plus courtes
passent sous le budget (portée-CAP mesurée) ; et re-miner le corpus compressé fait émerger des **macros
d'ordre 2** (une notion utilisée dans un motif de plus haut niveau).

## 4. Comment ça trouve & résout des problèmes (axe DÉCOUVERTE)

Régime guidé par **terme partagé** (le seul qui « fire », cf. pas 39-41), tranché par le noyau :
- **Transitivité** : `T1:A⇒B`, `T2:Bp⇒C` avec `σ(Bp)=B` → conjecture `A⇒σ(C)`, prouvée en 4 pas noyau.
- **Détachement** : `T:A⇒B` et `K⊢φ` avec `σ(A)=φ` → `σ(B)`.
- **Matching relâché σ** : l'antécédent s'unifie à *σ près* (variables libres), σ appliqué par le noyau
  (`generalisation`+`instancie`). *Soundness garantie* : le noyau construit le théorème final et on
  vérifie sa conclusion — un mauvais match ne peut que RATER une découverte, jamais en fabriquer une fausse.
- **Dédup α-canonique** + **tri par intérêt** (pont inter-modules · symboles disjoints · parcimonie).

**Compounding** : `conjecturer.iterer(--rounds N)` — les théorèmes du tour t deviennent des briques du
tour t+1 → **découverte en profondeur croissante** (théorème bâti sur théorème).

## 5. Comment lancer

```bash
# Un tour complet (abstraction + découverte), journal unifié :
python outils_ia/corpus/tour.py --essais 155

# Découverte seule, avec conjecture itérée (profondeur) et top par intérêt :
python outils_ia/corpus/conjecturer.py --rounds 3 --montre 12

# Un tour d'abstraction seul (compounding détaillé) :
python outils_ia/corpus/flywheel.py --essais 155

# Tests :
python -m pytest outils_ia/corpus/test_antiunif_notions.py outils_ia/corpus/test_conjecturer.py -q
```

## 6. Résultats mesurés (corpus rapide : logique + ensembles, 490 preuves)

- **Abstraction** : 155 candidates → funnel {75 désalignées, 57 gate-fail, 21 gain≤0, **2 promues**} ;
  compounding +2 preuves sous CAP 10 et 15 ; **18 macros d'ordre 2**.
- **Découverte, LES 5 RÉGIMES DU LANGAGE (tour #7 = 20 506 découvertes certifiées)** :
  `⇒` 106 (itéré 3 tours : 431, profondeur 1→3) · `=` 178 (compounding 12/19/147) · `⇔` 20
  caractérisations · `⊂` **20 102** (6 ⊂-corpus + 434 dérivées du **pont S6** `=→⊂` — le
  multiplicateur) · `∃` 100 (∃-intro S5 sur sous-termes récurrents). Filtre de **subsomption**
  (anti-collapse) : les σ-instances de théorèmes connus sont écartées avant composition.
- **Catalogues durables** : 20 lemmes ⇒ (`lemmes_decouverts.py`) + 24 lemmes =/⇔/⊂
  (`lemmes_algebre.py`), re-certifiés au noyau à chaque appel.
- **Frontière** : `theorie == 22 axiomes`, re-vérifiée à chaque tour. **20 tests verts.**

*Honnêteté* : les gains d'ABSTRACTION sont petits car le corpus rapide est petit (verrou triangulé sur
3 frames) — le levier exogène reste **formaliser plus** (`bourbaki/`). Les énoncés DÉCOUVERTS gagnent en
complexité avec la profondeur → le filtre d'intérêt (parcimonie) est essentiel.

## 7. Front-ouvert (recherche, prototypables sans point d'arrêt net)

- **Signal de FÉCONDITÉ prospectif** — MDL et « intérêt » récompensent le *présent* (fréquence, pont),
  pas la *réutilisation future* d'une notion/théorème. Une vraie notion « Galois » apparaît d'abord une
  fois (compression nulle) → un signal prospectif (appris) manque. C'est le vrai verrou de l'invention féconde.
- **Anti-collapse POET** — pression de nouveauté/diversité pour éviter que le générateur ne pose que ce
  qu'il sait déjà.
- **Définitions conservatives** — introduire un symbole *nouveau* par définition non-créatrice (le geste
  Galois/Grothendieck), pas seulement des lemmes dérivés.
- **GFlowNet / diffusion-DAG** — échantillonner l'espace des preuves/théories (plus data-hungry).

## 8. Frontière de confiance (invariant absolu)

Tout `Theoreme` n'est bâti qu'avec les **primitives du noyau** (`N.*` : `assume`, `modus_ponens`,
`loi_deduction`, `generalisation`, `instancie`, `s1..s7`, `axiome`…). Jamais de `Theoreme(...)` forgé,
jamais de `_CLE`, jamais d'axiome ajouté. `theorie_ensembles() == 22`. Le noyau garantit la *soundness*
(aucun faux théorème) même sous auto-modification — c'est ce qui rend l'auto-amélioration **sûre**.

Voir aussi : `CAMPAGNE_TROUS.md` (journal détaillé + leçons), mémoire `bourbaki-jalon1-organe-abstraction`.
