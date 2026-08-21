# A4 — les mesures, prises le 21 août 2026

**Pourquoi ce document.** Leçon de A2 (huit chiffres sur huit avaient dérivé) :
AUCUN chiffre n'entre dans l'article sans re-mesure du jour. Ce document fait
foi ; le journal de session ne fait jamais foi.

Banc : ⊕ de v16-v18 — `a ⊕ b := (a+b)+1`, pool brut = {associativité itérée
de `+`, commutativité de `+`}, `profondeur=4`, machine de Karl, Python 3.13.

## 1. La porte (plan éditorial, 10 août) — MESURÉE DES DEUX CÔTÉS

But **B4** := `((a⊕b)⊕c)⊕d = a⊕(b⊕(c⊕d))`.

| expérience | pool | verdict | durée |
|---|---|---|---:|
| EXP1 — chaînage direct | brut (2 lois `+`) | **ÉCHEC** (1 manque) | **692,54 s** |
| EXP2 — lemme ⊕-assoc certifié à part | brut | FERMÉ | 3,84 s |
| EXP2 — B4, pool CUMULÉ (brut + lemme) | 3 faits | FERMÉ (clos, 0 hyp) | **962,42 s** |
| EXP3 — lemme ⊕-assoc (re-mesure) | brut | FERMÉ | 7,36 s |
| EXP3 — B4, pool COMPRIMÉ (lemme SEUL) | 1 fait | **FERMÉ** (clos, 0 hyp) | **72,59 s** |
| EXP3 — garde-fou : variante fausse F4 | comprimé | ouvert (bien) | 79,13 s |

Lectures honnêtes :

- **La porte tient** : le chaînage seul épuise son budget en 692 s (la chaîne
  brute dépasse `max_pas=5`, borne mesurée par v18) ; la marche — certifier le
  lemme (4-7 s) puis fermer sur pool comprimé (73 s) — ferme le même but.
- **La compression est un REMPLACEMENT, pas un ajout** : cumuler le lemme aux
  lois brutes coûte 962 s ; le lemme SEUL, 72,6 s — facteur **13,3**. Ajouter
  du savoir AGRANDIT l'espace de recherche ; le pas de compression n'est
  rentable que si les lois brutes sont mises de côté.
- Variance : le même lemme certifié deux fois → 3,84 s puis 7,36 s (≈ ×2 selon
  l'état des caches). Citer « quelques secondes », pas un chiffre unique.
- `theorie_ensembles()` == 22 après toute la campagne.

## 2. Le mineur de motifs (P3) — y compris son PREMIER RATÉ

- **v1 (top-24 des sous-termes par taille) : RATE ⊕.** Les développements τ
  sont énormes (un ⊕ à trois étages ≈ 13 700 nœuds) : le top-24 ne contenait
  que des fragments internes, et le motif de tête était un contexte à 3 slots
  de gain 13 737 — inutilisable, et ⊕ absent de la liste. *Le classement par
  taille sélectionne le bruit.*
- **v2 (appariement par signature de racine, occurrences sur toutes les
  sources)** : motif de tête `occ=6, gain=4045, 2 slots`, et son application
  à `(a, b)` **EST** `⊕(a, b)` (égalité d'assemblages, O(1)) — la machine
  retrouve l'opération sans qu'on la lui nomme. Mineur : **1,10 s** sur B4.

## 3. L'oracle étendu (P4)

- **Trou mesuré avant extension** : la table ne contenait ni `succ(somme)` ni
  aucun terme d'opération dérivée → toute conjecture ⊕ rendait `None`
  (invisible, ni réfutable ni autorisée).
- **Extension : UNE couche `successeur`** sur la table existante
  (`oracle_num.table`). `valeur(succ(2+3)) = 6` en 0,02 s.
- Sur les conjectures du mineur : **idempotence ⊕ réfutée en < 1 ms** ;
  commutativité non réfutée en 1,33 s ; associativité non réfutée en 1,07 s
  (borne 8). Le schéma faux meurt AVANT tout appel noyau.
- **Limite dite** : une couche seulement — un terme dérivé imbriqué
  (`succ(succ(a+b)+c)`) reste hors table ; la clôture complète coûterait
  |table|². Les conjectures fausses à imbrication profonde ne seront pas
  réfutées par l'oracle : elles coûteront un échec de certification (mesuré
  au journal de marche).

## 4. La marche de bout en bout (EXP4) — EN COURS

`marcher(B4, brut)` : miner → conjecturer → réfuter → certifier → re-essayer
sur pool comprimé. Résultats à coller ici À LA LECTURE, pas de mémoire.

## 5. Ce qui N'EST PAS mesuré (à ne pas écrire dans l'article)

- Aucune généralité au-delà du banc ⊕ (un seul banc à ce jour).
- Le coût d'une conjecture fausse PROFONDE (hors de portée de l'oracle) —
  à mesurer si EXP4 en rencontre une.
- Rien sur Goldbach : le marcheur n'y a pas encore été pointé (P6).
