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

## 4. La marche de bout en bout (EXP4) — FERMÉE en 414,24 s

`marcher(B4, brut)`, chronologie lue dans exp4_b4.out (sonde horodatée) :

| phase | fenêtre | durée |
|---|---|---:|
| minage (4 motifs : gains 4045/1771/1155/895) | 0 → 4,0 s | 4,0 s |
| 12 conjectures : **6 certifiées**, 2 réfutées oracle, 4 non-certifiées | 4,0 → 53,2 s | 49,2 s |
| · ⊕-comm certifiée | | 20,2 s |
| · ⊕-assoc certifiée | | 16,8 s |
| · idempotence ⊕ réfutée (x=0) / SC (x=1) | | < 0,1 s |
| re-essai palier 1 (2 lemmes du motif ⊕) | 53,2 → 414,2 s | **361,0 s** |
| **TOTAL — FERMÉE, est_clos, ==B4, 0 hyp, 22 axiomes** | | **414,24 s** |

Lectures :

- **La marche ferme en 414 s ce que le chaînage met 692 s à NE PAS fermer.**
- La loi du remplacement se raffine : 2 lemmes (⊕-comm + ⊕-assoc) = 361 s
  là où ⊕-assoc SEUL = 72,6 s (EXP3). MÊME un lemme VRAI et thématique en
  trop coûte ×5. L'échelle de compression (re-essai par paliers de motif)
  est née de cette mesure : le premier jet « tous les lemmes certifiés d'un
  coup » (6) dépassait 580 s — la marche échouait par sa propre richesse.
- Les 2 morts silencieuses des lancements en fond (aucune sortie, aucun
  code) sont restées inexpliquées ; l'exécution instrumentée (sonde
  horodatée, avant-plan) a tout donné. Règle retenue : jamais de calcul
  long sans battement de sortie.

## 4bis. Le garde-fou F4 (variante fausse) — et ses trois morts

`marcher(F4, brut)` (exp4_f4.out, sonde horodatée) :

- certifications : 35,0 s (les mêmes lemmes — ils parlent de ⊕, pas du but) ;
- palier 1 (2 lemmes) : **échec PROPRE en 788,2 s**, 1 manque nommé, rien fermé ;
- palier 2 (4 lemmes) : **processus MORT sans trace** — ni code de sortie,
  ni traceback, ni événement système (Event Log 2004 vérifié : rien depuis
  juillet). TROISIÈME mort identique de la journée (les deux lancements de
  la marche avec re-essai à 6 lemmes ont péri pareil). Corrélation : POOLS
  ≥ 4 lemmes ; les exécutions à ≤ 3 lois (dont 962 s en avant-plan) survivent.
  CAUSE NON IDENTIFIÉE — on l'écrit tel quel, on ne présume pas.

Conséquence d'ingénierie : `paliers_max` dans `marcher` — le test garde-fou
plafonne à 1 palier et ASSERTE que le journal déclare les paliers sautés
(« paliers-sautés ») : contournement DIT, jamais cap silencieux.

## 5. Ce qui N'EST PAS mesuré (à ne pas écrire dans l'article)

- Aucune généralité au-delà du banc ⊕ (un seul banc à ce jour).
- ~~Le coût d'une conjecture fausse profonde~~ MESURÉ par EXP4 : les 4
  « non-certifiées » (assoc/idem des motifs 3-4, hors de portée de l'oracle
  à une couche) ont coûté 3,2 + 7,8 + ~0,3 s d'échecs de certification —
  le prix de l'aveuglement de l'oracle est de l'ordre de 11 s sur 414.
- ~~Rien sur Goldbach~~ MESURÉ (exp5_goldbach.py, exp5.out) : sur le but
  général goldbach(), le marcheur mine 4 motifs (tête occ=8 gain=1127 =
  la somme de 2n=p+q), CERTIFIE comm+assoc (vrais, sur l'addition de
  l'énoncé — 18,6 s), réfute 2 idempotences (x=1, x=2), re-essaie
  (palier 1 : ouvert, 1 manque, 16 s), ronde 2 : rien de neuf →
  \u00ab terminal \u00bb en **35,70 s**, rien de fermé, 22 axiomes. P6 ✅ :
  des lemmes vrais sur les opérations d'une conjecture ne déplacent pas
  la conjecture.
- Le coût COMPLET d'un échec (toute l'échelle) : non mesurable à ce
  jour — les paliers ≥ 2 tuent le processus (§4bis).

## 6. APRES PUBLICATION (21 août, soir) — le banc 2 fait tomber trois lois

Le banc 2 (distributivité pure a·(b+c) = a·b + a·c, chantier division) a fait
perdre TROIS fois le test du schéma croisé — chaque perte est une mesure :

1. **Le MDL préfère le substrat.** Les motifs de tête ne sont pas PCB/SC mais
   `paire` et le produit ensembliste — l'intérieur des développements τ bat
   les opérations de surface au gain. Le banc ⊕ marchait parce que ⊕ y était
   SEUL. (La machine surfaçait au passage la notion de COUPLE — un vrai objet
   du livre.)
2. **Argument partagé ⇒ arité 1.** Toutes les instances du produit du but
   partagent `a` : chaque paire ne diverge qu'en un point, le motif binaire
   complet n'est PAS récupérable du but. Le motif UNAIRE a·(·) l'est (occ 3,
   gain 226) — d'où le schéma MORPHISME H(y+z) = H(y)+H(z) (unaire, binaire),
   qui EST la distributivité du but.
3. **La signature de racine confond les τ.** Tous les τ-termes ont la même
   racine (tau/Z/1 arg) : la paire (SC(b,c), SC(PCB,PCB)) — positions 2 et 4
   d'un groupe de 5 — n'était jamais essayée par l'appariement (i−1, 0).
   Correctif : descente vers le bas jusqu'à la première anti-unification
   compatible (cap 12 essais / 2 rencontres, dit dans le code).

Verrouillé par test : `test_marcheur_schemas_croises_distributivite`
(2 passed en 19,66 s avec le test ⊕ — aucune régression). Ces lois sont
POST-publication : l'article reste à l'état 414 s ; elles nourrissent la
suite (A4', ou le papier du mineur).

### EXP6 (21 août, soir) — le banc 2 : la machine NOMME le pont manquant

`exp6_pont_distributivite.py` : but = PCB(a, SC(b,c)) = SC(PCB(a,b), PCB(a,c)),
pool = {distributivite_cardinale (niveau ENSEMBLES), comm+, assoc+}.

- direct : échec en 6,4 s, 1 manque ;
- marche (2,78 s) : SC-comm et SC-assoc CERTIFIÉS (<1 s), SC-idempotence
  réfutée (x=1), **4 conjectures morphisme toutes NON-CERTIFIÉES** (~0,3 s
  chacune), re-essai ouvert, ronde 2 rien de neuf → terminal. 22 axiomes.

LECTURE : la distributivité au niveau des OPÉRATIONS n'est pas dérivable du
théorème niveau-ensembles par les organes actuels. Le chaînon manquant est le
PONT du respect de l'équipotence : PCB(a, SC(b,c)) = Card(a × Card(b⊔c))
demande « le produit ne voit que le cardinal de son facteur » (Eq(Card S, S)
+ produit/somme respectent Eq). C'est une BRIQUE DU LIVRE (§III.3.3) que la
machine vient de désigner — le mode de croissance du projet depuis ev.373,
cette fois pointé sur le programme du LIVRE lui-même. Chantier ouvert.
