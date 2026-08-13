# CAMPAGNE DÉMOS — suivi, en ORDRE LIVRE (maj 12 août 2026, 8h30)

## 🎯 MATINÉE DU 12 AOÛT — L'ARC MIGRÉ, ET CE QU'IL NE CONTIENT PAS (ev.413-417)

**LE RÉSULTAT DE LA MATINÉE N'EST PAS UN THÉORÈME DE PLUS, C'EST UNE MESURE SUR
LES NÔTRES.** `recherche/additif/` reprend la construction du crible avec le
prédicat en **PARAMÈTRE** (fonction `Terme → Formule`). La symétrie et la
restriction au demi-intervalle y ferment **sans jamais ouvrir `S`** :

| `S` | symétrie | restriction |
|---|---|---|
| `x ∈ 𝕊`, opaque, aucune propriété | CLOS 5 s | CLOS 351 s |
| `est_premier(x)` — **Goldbach** | CLOS 4 s | CLOS 131 s |
| `est_pair_propre(x)` — trivial | CLOS 4 s | — |

**Verdict** : les quatre grandes réductions de la carte (composés, crible,
symétrie, demi-intervalle) **ne portent aucun contenu arithmétique**. Une
démonstration qui ne distingue pas les premiers d'un ensemble sans structure ne
peut pas démontrer Goldbach. Ça **absorbe** les deux voies déjà refermées —
§7 comptage, §8 équationnel — et les explique : aucune ne regarde *quels*
entiers sont premiers. Détail : `CARTE_GOLDBACH.md` §12.

**L'ARC EST MIGRÉ.** Fini les 50 scripts de scratchpad : `recherche/goldbach/`
= 9 modules testés (10 entrées, LIMITE atteinte), `capstone.verifie_chaine()`
rejoue **18 maillons jugés PAR LE NOYAU** (l'ancien validait deux d'entre eux
par recherche de « CLOS: True » dans un `stdout` — reformater un `print` le
faisait passer au vert). Suite `tests/recherche/` : **26 passed en 19 min**.
Organes : **20 passed**, aucune régression.

**DEUX THÉORÈMES NEUFS AU PASSAGE** : l'associativité ITÉRÉE de l'addition
cardinale (promue au dépôt, `bourbaki/…/ensembles_somme_iteree.py`, trou réel
comblé) et le **demi-intervalle** — d'une paire sommant à `2k`, l'un des deux
est `≤ k`, donc chercher dans la moitié suffit. Le second utilise le premier,
démontré trois heures plus tôt sur un chantier sans rapport.

**TROIS ORGANES CONSOLIDÉS** : v16 congruence, v17 réécriture, v18
instanciation des lois. Un doublon d'organe résorbé, une borne `max_pas`
recalibrée 3→5 **sur mesure** (la chaîne minimale fait 5 pas).

**PROCHAIN JALON, s'il y en a un** : le postulat de Bertrand — première
arithmétique véritable dans la carte. Prérequis : démontrer les coefficients
binomiaux de §III.5.8 (énoncés formalisés, preuves non dérivées) ; le quotient
n'est pas un terme du dépôt ; et Bertrand **ne démontre pas** Goldbach.

---
# CAMPAGNE DÉMOS — suivi, en ORDRE LIVRE (maj 10 août 2026, 11h20)

## 🎯 MATINÉE DU 10 AOÛT — LA FORME CRIBLE, UN AUDIT, ET UNE VOIE FERMÉE (ev.379-390)

**GG19 (2 s, les DEUX sens)** : `⊢ ∀k( ∃m(m∈P_2k ∧ m∈Q_2k) ⇔ 2k somme de deux
premiers )` — Goldbach est équivalent à une **rencontre** entre l'ensemble des
premiers ≤ 2k et son miroir. Chemin : P_2k construit, **non vide** (GG14) et
**fini** (GG15) ; générateur `route_temoin(T,Q)` (toute stratégie = un couple
de termes) ; organe **v9** (réflexivité).

**⚠️ L'audit qui débloque** : le sens ⇒ refusait de se fermer — la cause
n'était pas un lemme manquant mais un **énoncé infidèle**. `est_premier(p)` ne
garde que le diviseur : un p non-cardinal n'est divisible par rien, donc
« premier » s'y réduit à p ≠ 1 (certifié). `goldbach()` quantifiait donc sur
des témoins **non entiers**. Avec l'énoncé gardé, le sens ⇒ se ferme — et il
consomme exactement la garde. *Un blocage persistant est un signal sur
l'énoncé, pas sur la preuve.*

**Une voie fermée pour de bon** (mesure, pas preuve) : le critère des tiroirs
`2·π(2k) > 2k+1` **ne tient pour aucun k ≥ 2** (π/k passe de 0,50 à 0,18),
alors que le nombre réel de décompositions croît (2 → 1417). Le comptage brut
ne peut structurellement pas fermer la rencontre : il faut la **répartition**.
Décision : ne pas formaliser l'inclusion-exclusion pour Goldbach.

**Et la boucle se referme** : re-sondé sur la nouvelle forme, l'organe nomme
mot pour mot la rencontre comme son unique manque.

## 🌅 MATIN DU 10 AOÛT — GOLDBACH SANS ∃ : LA FORME CANONIQUE (ev.375-377)

**GG9 : ⊢ ∀k( decomp(k+k) ⇔ premier₁(T) ∧ premier₂(Q) ∧ k+k = T+Q )** avec
T := τp(∃q mat) et Q := τq(mat[p:=T]) les témoins CANONIQUES — le pont ∃⟺τ
était déjà deux primitives du noyau (existe_temoin / s5, E I.32), 0 s.
**GG10 : ⊢ H ⇔ H_τ = ∀k(A(k) ⇒ C(k))** — la conjecture SANS ∃ : « les deux
τ-termes nommés sont premiers et somment ». Mesure PB25a : GG9 versé comme
FAIT-∀ à l'organe → les manques deviennent les 6 OBLIGATIONS CANONIQUES
(T≠un, diviseurs de T, Q≠un, diviseurs de Q, somme) — le bruit σ (¬(n=n),
ev.373) a DISPARU. Et en ouverture de matinée (ev.375) : organes v7
(∃-descente à témoins proposés) + v8 (but-∧) + PROPOSEUR-GOLDBACH — test
d'intégration VERT 58 s : decomposition(N16) fermée de bout en bout par
témoins proposés (couple 3, complément 13), suite 12 passed. Honnêteté :
GG9/GG10 sont de la logique — prouver premier(T_k) ∀k RESTE la conjecture ;
l'acquis est la reformulation machine sans ∃ + des manques enfin exacts.

## 🏆🏆 NUIT DU 10 AOÛT — LA CARTE MACHINE DE GOLDBACH ET L'ORGANE CRÉATIF (ev.362-374)

L'arc complet, en une nuit : **GG7 : goldbach ⟺ ses instances COMPOSÉES**
(tiers-exclu premier/composé via GG6 pont-α et GG2′ famille {2p}) ; **GG8 :
la récurrence forte BRANCHÉE (⊢ pas ⇒ conjecture)** — et la machine ÉCRIT le
pas ∀n(S{n}⇒R{n}) comme son manque, puis le DÉCOMPOSE (structure fractale
premier/composé). **CINQ ORGANES améliorés sur diagnostics mesurés** (v2
conjoints recomposés, v3 manques fusionnés, v4 ∀-faits instanciés, v5
∀-implications = routes, v6 PROPOSEURS DE TÉMOINS — 10 tests verts). Le
manque terminal, écrit par la machine : σ ne propose que p:=n (¬(n=n)
impossible) — **il lui faut un générateur de témoins créatif** : la
frontière chaînage/marcheur tracée par elle-même, et l'ébauche v6 y répond
(le noyau juge, le proposeur suggère). Sondes du pas : 14→8→6→4 manques →
LA BORNE seule ; sans béquille : « il me manque k premier ». Goldbach RESTE
OUVERT — mais son contenu est désormais une CARTE machine-lisible à trois
portes certifiées équivalentes, et la machine sait dire ce qui lui manque
pour chacune.

## 👑👑 10 AOÛT 4h00 — GOLDBACH ⟺ GOLDBACH-SUR-LES-COMPOSÉS (ev.367)

**⊢ HC ⇒ H et ⊢ H ⇒ HC** (0 s, premier coup) : la conjecture, déjà ⟺ à sa
forme moitiés H, est désormais certifiée ÉQUIVALENTE à HC = ses seules
instances composées — ∀k((Fini k ∧ k≠0 ∧ k≠1 ∧ ¬premier k) ⇒ k+k somme de
deux premiers). Tiers-exclu sur premier(k) : la branche premier passe par la
famille {2p} (GG2′) via le pont-α GG6 (premier₁⇒premier₂ — ∀-α + ∃-α enfoui
contravariant, le double-habit levé) ; la branche composé est l'hypothèse.
La machine avait nommé le manque (« k premier », ev.364) ; c'est maintenant
un théorème d'équivalence. Chaîne : goldbach() ⟺ H ⟺ HC, invariant 22.

## 📸 10 AOÛT 1h23 — LA MACHINE RÉDUIT GOLDBACH À UN MANQUE (ev.356-363)

Nuit du cas général, forme moitiés (goldbach ⟺ ∀k decomp(k+k), équivalence
close) : quatre sondes de l'organe (PB13→19) font passer ses manques de
14 formules opaques à **LA BORNE SEULE** (∃F…dom(F)=k+k, l'injection du ≤).
Entre les sondes : GG4 (cardinal/parité-gensym/distinct, 178 s), GG5a (k+k≠0,
4 s), GG5b (k+k≠2, 47 s, cascade successeur_ordre 100 % acquis), fait
Fini(x+x) — ET DEUX AMÉLIORATIONS DE L'ORGANE nées de diagnostics mesurés
(besoin.py v2 : conjoints re-soumis + recomposition ∧-intro ; reporting des
seuls récalcitrants — suites vertes). Avec GG2 (famille {2p}, 0 s : H est
FAIT pour k premier), le théorème n≤84 et GG1 (pairs Goldbach arbitrairement
grands) : la conjecture est encadrée, réduite aux k composés, et son contenu
exact — l'écart borné→libre — est désormais dit par la machine en une formule.

## 👑 9 AOÛT 19h53 — GG1 : LES PAIRS DE GOLDBACH SONT NON BORNÉS (ev.354)

**⊢ ∀n( Fini n ⇒ ∃m( pair m ∧ n ≤ m ∧ ∃p∃q( premiers ∧ m = p+q ) ) )** — clos,
0 hyp, 1362 s dont 3 s de couture (le reste = rebuild infinitude). Le premier
théorème NON BORNÉ des sommes de deux premiers : l'infinitude (ev.344) donne
p ≥ n, m := p+p est pair par témoin RÉFLEXIF, prop2 curryfié + transitivité,
témoin-jumeau à matrices explicites en deux étages. Avec le borné n ≤ 84, la
conjecture est ENCADRÉE : tous les pairs jusqu'à 84, des pairs arbitrairement
grands — il manque TOUS les pairs à tout n : l'écart EST Goldbach.

## 👑 9 AOÛT — GOLDBACH : LA FRONTIÈRE 6→84 ET LE MANQUE QUI LA SUIT (ev.347-351)

**⊢ Goldbach pour tout n ≤ 84** (goldbach_borne_n(84), CLOS, ==cible(84)) —
la frontière bornée est passée de 6 à 84 dans la journée (12→78s, 20→96s,
30→117s, 50→341s, 70→1108s, 84→1896s ; ~23 premiers certifiés à la volée par
est_premier_num). Falaise : B=92 = RecursionError (hash τZ-profond, garde de
pile réelle Python 3.13, immune à threading.stack_size 64 Mo — 512/256 Mo
refusés par Windows ; driver scratchpad/gb_driver.py). **PB10/PB11 (la machine
re-interrogée sur goldbach() tout-n, pool enrichi Euclide puis + borne 50)** :
non fermé (attendu), et le manque nommé RESTE la borne — mais il SUIT la
frontière (chaînes borne_n(6)[n] ET borne_n(50)[n] dans la trace PB11) : la
machine localise en machine-lisible la structure de la conjecture — les
théorèmes bornés montent, le cas libre reste hors de portée, l'écart EST
Goldbach. L'infinitude ne l'aide pas ici (elle produit des premiers AU-DELÀ
de n, rien sur les SOMMES) — dit par l'organe, pas par nous. **Sanité
sémantique COMPLÈTE** : ¬premier(0) 20s [témoin 2, 0=2·0], ¬premier(1) 2s
[le pont N(1)=un() réfute le conjoint gauche], + 4/6/9 d'hier — est_premier
démontre les premiers ET réfute tous les non-premiers de base. Conjectureur
sur la moisson lancé pour la nuit (CONJ1, rounds=3, cap 3×taille(goldbach)).


## 👑👑👑👑👑👑 8 AOÛT 18h14 — L'INFINITUDE DES PREMIERS : EUCLIDE EST COMPLET (ev.344)

**⊢ ∀n( Fini n ⇒ ∃p( premier p ∧ Fini p ∧ n ≤ p ) )** — assemblage 1377 s,
0 hypothèse, invariant 22, **conclusion == enonce_infinitude() : True** (l'énoncé
EXACT que la machine a exigé le matin, ev.325). PREMIER COUP. L'argument
d'Euclide verbatim dans le noyau : m = succ(n!) [= n!+1 LITTÉRALEMENT :
successeur(a) := somme(a,{∅})], m≠0 (spie), m≠1 (1≤n! + Prop.8 succ injectif),
diviseur premier p de m (théorème ev.335), comparabilité(p,n) — si p≤n : G
donne p|n!, H donne p=1, contre premier p ; sinon n≤p = le témoin (∃-intro
« pep »). LES 6 BRIQUES DU JOUR (euclide_c61/) : F fini_factorielle 354 s,
G2 d|a⇒d|a·b 226 s, G3 b|a·b 1 s, G (d≤n∧d≠0)⇒d|n! 609 s (récurrence,
cas-split successeur_ordre), H (d|a∧d|succ a∧d≠0)⇒d=1 382 s (comparabilités
imbriquées + produit_succ_distribue + additive_order_cancel), minorant 1≤n!
493 s — toutes premier coup SAUF H (2 runs : lieur de graphe Eq CANONIQUE
« F » exigé). Pièges neufs au tableau : pont-α qdiv↦w1H/w2H (témoin var-même
sous lieur frais, 4 gestes) ; UN := succ(ZERO) et succ(a) := somme(a,{∅})
sont des LITTÉRAUX (des réflexivités, pas des ponts) ; « ≠0 » se dérive
PARTOUT par le spie-pattern (0≤x + Leibniz + succ_pas_inf_egal) sans lemme
neuf ; un_egale_card_singleton EST le pont UN=un() goldbach. La boucle est
bouclée : la machine a nommé son manque le matin (ev.325), le théorème-outil
à midi (ev.335), Euclide au soir (ev.344) — même journée.


## 👑👑👑👑👑 8 AOÛT 15h40 — LE DIVISEUR PREMIER UNIVERSEL EST CLOS (ev.335)

**⊢ ∀n( Fini n ⇒ [ (n≠0 ∧ n≠1) ⇒ ∃p( premier p ∧ Fini p ∧ p|n ) ] )** — 304 s,
0 hypothèse, invariant 22, test vert (euclide_c61/envelope.py). Récurrence
FORTE assemblant les 4 briques closes LE MÊME JOUR (producteur, transitivité,
extraction, borne) + micro-F2 (d≠0 : ZERO==Card(∅) par réflexivité) + résidu
C61 déchargé (predecesseur_fini_universel prouvé). PREMIER théorème de théorie
des nombres de la machine — sur la campagne qu'ELLE a exigée le matin même
(ev.325 : « une route non-bornée »). 4 itérations, chaque échec attrapé par un
garde-fou du noyau (lieur qep littéral ; fic conclut est_cardinal directement ;
décharge du résidu). Reste : n!+1 → infinitude (route : n!+1 a un diviseur
premier p [CE théorème] ; p>n sinon p|n! ∧ p|(n!+1) ⇒ p|1 absurde ; briques
requises : d|n! pour d≤n, différence de divisibilité).


## ⚔️ 8 AOÛT APRÈS-MIDI — EUCLIDE : TROIS BRIQUES CLOSES LE JOUR DE LA DEMANDE (ev.329-333)

La machine a exigé la route non-bornée le matin (ev.325-328) ; l'après-midi,
ses trois premières briques sont closes dans decouvertes/autonomie/ :
**producteur** (∀n((Fini n ∧ premier n) ⇒ ∃p(premier ∧ p|n)) — la forme que PB7
déclarait introuvable, témoin n, 12 s), **transitivité** ((card b ∧ b|a ∧ a|c)
⇒ b|c — couloir de 7 réécritures + double ∃-élim à lieurs LITTÉRAUX, 224 s,
premier run), **extraction** ((¬(n=1) ∧ ¬premier n) ⇒ ∃d((Fini d ∧ d|n) ∧
(d≠1 ∧ d≠n)) — 0,5 s). Trois pièges au tableau : dne = couche 0 (→ _dne
abrégé tiers_exclu+cas) ; neg_intro exige cible ¬f ; LES DEUX « ou »
(_ou encodé de est_premier ≠ ou primitif — la décharge ne matche pas et la
généralisation refuse). Suites : 160 verts + 5/5. Reste : borne d≤n (route
mesurée), enveloppe C61, n!+1 → PASSATION.


## 👑👑👑 8 AOÛT ~10h30 — LA MACHINE SE DIRIGE : CHAÎNE AUTONOME PROMUE (ev.317-323)

Philosophie Karl (« on ne formalise que ce que l'algo juge nécessaire ») rendue
EXÉCUTABLE. ORGANE DE BESOIN (chaînage à rebours, fermetures jugées noyau,
manques nommés ÉCLATÉS EN CONJOINTS, affichés via l'IMPRIMEUR formule→code) +
COMBLEURS (les organes promus répondent : ∃-intro sélectif, pont-réécrit,
card/fini/ne/le) + ASSEMBLEUR (detachement_conjonctif) = `fermer_par_besoin()`.
**decomposition(N32..N40) : 5/5 fermées en 4,2 min, pool d'UNE implication,
faits VIDES — Goldbach machine-vérifié 6..40, les 5 derniers SANS script
manuel.** Pour Goldbach(32) la machine avait d'abord DICTÉ ses manques (dont le
MUR N32≤N6 : la borne). Promu : outils_ia/decouvertes/{imprimeur,besoin,
combleurs}.py + test_autonomie (3/3 en 64 s, dont fermeture-miniature N8).
Détail → PASSATION (ev.317-323).

## 🌀👑 8 AOÛT MATIN — LA BOUCLE DE COMPOUNDING TOURNE ET S'OBSERVE (ev.308-315)

Directive Karl : boucle en continu + « voir où ça en est pendant ». Livré :
**streaming du conjectureur** (trace JSONL : tour / source / découverte /
briques_sautées) qui a localisé en minutes deux gels de dépliage (`_cle_canon`,
`_taille` → réécrits EN PARTAGE) ; **cap_brique** contre les briques-monstres ;
5 tours passent de 3h20 gelées à **10,2 min** (64 découvertes). Puis le cycle
complet a payé LE MATIN MÊME : 3 lemmes de **profondeur 2** promus
(lemmes_conjectures_2.py — le premier dérivé À TRAVERS un lemme machine) →
tour #15 = **18 notions, gain 80** (progression 4→12→16→18), 42 preuves
raccourcies, 96 macros d'ordre 2. En prime : **IMPRIMEUR formule→code** validé
7/7 aller-retours exacts (matching inverse) = la brique de l'auto-promotion.
Article : paragraphe (v) « La machine compose » fr+en. Détail → PASSATION.

## 👑👑 7 AOÛT SOIR — CAMPAGNE GATING PARAMÉTRÉ (ev.299-303) : LE VOLANT PROMEUT SUR L'ÎLOT

En ~2 h, sur directive Karl : le gate du volant étendu aux prouveurs PARAMÉTRÉS
(36/43 preuves de l'îlot l'étaient — stérilité mesurée aux tours #2-4). Cinq
pièces, chacune précédée d'une mesure (GP1-GP7) et suivie d'un test : contrat
`<name>_instances()` (module définissant), voile de caches déclarés (_ns_gate —
le prouveur-triche `return _FINI[k]` MEURT), refus des divergences d'opérateur
(somme `+` vs produit `*` = deux lois), appel-Expr (blocs asserts-seuls), et le
fix décisif : renommage inverse des slots (p{k}/_v{k} → noms réels, NameError
mesuré GP7).

- 👑 **1re notion machine de l'îlot** : `notion_loi_deduction_3p_2` — l'idiome
  maison « clore l'implication et vérifier l'énoncé », re-prouvée par le noyau
  dans les 3 lemmes machine (8→6 pas, CAP 6 franchi), 6 macros d'ordre 2.
- **Tour #11 unifié : 12 notions, gain MDL 33** (×3 vs avant le fix), 20 preuves
  raccourcies (image_reciproque_difference 46→38…), 63 macros d'ordre 2.
- Suite 152 verts + 23 tests corpus verts ; invariant 22 ; détail → PASSATION.

**Nuit du 7-8 août — AUTOPSIE DES 54 GATE_FAIL (ev.304-307, directive Karl)** :
méthode GP7 généralisée (traceback réel par candidate). Validation des slots
(dataflow interne + imports refusés dès _construire) puis RÉPARATION DÉPÔT :
3 compagnes cible_* périmées débusquées par balayage (2 antécédents manquants
dans ii_3_2_reciproque + 1 lieur τ non canonique dans section_unique) — le
volant AUDITE la fidélité du dépôt en passant. **gate_fail 54→1 ; 16 notions,
gain 69 ; 41 preuves raccourcies ; 99 macros d'ordre 2 ; 0 stale.** Suites :
235 verts (ii_3) + 175 verts (outils_ia+corpus).

## 🌀 7 AOÛT 2026 — LE VOLANT EN WORKFLOW (ev.291-294) : 486 inventions, Goldbach 6..30

Workflow 4 agents (volant / moisson / chaînage / sceptique), lancé sur directive Karl,
run wf_79e8c090-99f en deux passes (leçon harnais : dans un sous-agent, JAMAIS
run_in_background — le process meurt avec le tour ; runs ≤10 min en AVANT-PLAN).

- **👑 Goldbach vérifié machine pour TOUS les pairs 6..30** : borne_n(30) chauffée une
  fois (109 s) puis 10/10 decomposition(N12..N30) CLOS 0 hyp à 0,1 s pièce — parité
  INVENTÉE par le sélectif, assemblage detachement_conjonctif, MP à travers le borné.
- **Moisson élargie** : 81 faits somme ≤20 → **486 inventions** kernel-certifiées
  (2 passes : K_PAIR + lieur frais), 9/9 parités N4..N20 EXACTES par ==.
- **Volant à VIDE (honnête)** : 43 preuves îlot scannées, 0 gatable — les compagnes
  cible_* existantes sont PARAMÉTRÉES (fn() → TypeError → None dans _cible_de) et
  parite.py sans __all__ n'est pas scanné. 76 n-grammes partagés existent (run 1).
  → chantier « rendre l'îlot gatable » : compagnes zéro-arg + __all__, puis re-tour.
  Effet de bord réparé : _ecrire_biblio réécrit TOUT notions_apprises.py → les 2
  notions du tour #1 effacées, RESTAURÉES depuis l'index git.
- **Sceptique process frais** : les 3 phases CONFIRMÉES sur sorties brutes (dépôt
  intact, 0 motif interdit, invariant 22, recomptes conformes champ à champ).

**Suite du soir (ev.295-297)** — déverrouiller le gate, mesure par mesure :
- 3 compagnes `*_cible` zéro-arg posées et VÉRIFIÉES par == (pont_un 1,5 s,
  pont_deux 43 s, antecedent_satisfait 249 s) ; garde-fou `_ecrire_biblio`
  (tour vide = biblio inchangée, testé en réel) ; correctif `_candidats`
  (instance sans cible ÉCARTÉE, plus la candidate entière — tout-ou-rien mesuré
  fatal sur corpus à 36/43 paramétrés). Tests gate 21 verts, suite 152 verts.
- Verdict mesuré en 3 tours : îlot seul = 0 candidate même corrigé (3 gatables
  sans motif commun) ; corpus MIXTE = **525 candidates formées (vs 0 avant le
  correctif)** mais --essais 12 et 100 trop petits (les viables sont noyées
  sous les grosses hétérogènes : 297 none au total).
- **👑 Tour #7 à budget COMPLET (600) : 4 notions promues** — les 2 motifs de
  juillet RE-DÉRIVÉS sur l'arbre restructuré (modus_ponens_2p, instancie_3p)
  + 2 NEUFS (et_3p, loi_deduction_3p) ; gain MDL 6, 12 preuves raccourcies,
  3 franchissent un CAP, **39 macros d'ordre 2**. Biblio 2 → 4, surclassement
  strict. **Prochaine campagne recommandée : gating PARAMÉTRÉ + ranking par
  homogénéité** (candidat n°0 de PASSATION) — le déverrouillage du volant sur
  les corpus machine, dont l'îlot.

## 🔢 6 AOÛT 2026 — L'ARITHMÉTIQUE PORTE ENFIN (ev. 247-253)

**⊢ est_premier( N(p) ) CLOS pour p = 2, 3, 5, 7, 11, 13, 17**, 0 hypothèse, conclusion
égale — au caractère près — à `goldbach.est_premier(N(p))` reconstruit depuis le module
d'énoncé. Et en dessous : **⊢ ¬( N(i) | N(p) )** pour tout couple avec i ∤ p (les cinq de
7, plus 14 autres jusqu'à (9,11) et (4,13)).

**Pourquoi ce n'est pas `est_premier(2)` en plus grand.** Pour 2, l'énumération donnait
{0,1,2} et les cas autorisés étaient {1,2} : il ne restait que zéro à écarter, sans aucune
arithmétique. C'était un accident de petitesse. À partir de 7, la conclusion dépend de la
VALEUR des nombres.

**Le pas décisif** : appliquer `diviseur_majore` **au QUOTIENT** et non au diviseur. La
commutation du produit transforme q en diviseur, donc un lemme d'ORDRE en outil de CALCUL.

**Coût — le troisième mur dissous de la campagne.** Le facteur 466 des TERMES (`numeraux.py`)
se transpose aux THÉORÈMES : aucun générique du dépôt n'est mémoïsé, tout était repayé à
chaque pas. Généralisés une fois, `non_divise(2,3)` passe de 490,7 s à 0,3 s et
`non_divise(2,7)` de « pas de fin en 600 s » à 51,9 s.

**Deux gardes, dont une que j'ai d'abord ratée.**
- *Fidélité* : `N(1) != goldbach.un()` en tant que TERMES (mesuré). Réparation par le PONT
  `un_egale_card_singleton` du dépôt — **pas** en réécrivant l'énoncé pour qu'il colle.
- *Non-universalité* : mon premier contrôle adversarial était FAUX — `garde` n'était pas
  propagé, l'échec venait d'une garde Python. Corrigé : gardes OFF à tous les étages, la
  machine meurt dans `ne_num` (il faudrait ¬(N(9)=N(9))), et p = 7 continue de clore.

**Promu au dépôt** : `outils_ia/arithmetique/machine_num.py`, `.../non_divisibilite.py`,
`outils_ia/conjectures/primalite.py`, + 2 fichiers de tests. `tests/outils_ia` réorganisé
(11 entrées → 8, calqué sur `outils_ia/`).

**Reste vers Goldbach** : la somme `N(p) + N(p') = N(n)` est déjà là (`somme_num`) ; ce qui
manque est l'instance *décomposée* — pour n donné, exhiber le couple et refermer
l'existentielle double. n = 4 est fait ; 6, 8, 10 sont désormais mécaniques.

---

### 👑 Et dans la foulée : **GOLDBACH QUANTIFIÉ** (ev. 254-255)

**⊢ (∀k)( ( Fini k ∧ k≠0 ∧ k≠1 ∧ k ≤ N(K) ) ⇒ (∃p)(∃p')( p, p' premiers ∧ k+k = p+p' ) )**,
CLOS, 0 hypothèse, pour K = 2, 3, 5, 10 — **tous les pairs de 4 à 20, en UNE formule**.
Le corps existentiel est vérifié ÉGAL à celui de `goldbach.goldbach()` (reconstruction
complète, pas une variante commode).

C'est la différence entre « j'ai vérifié » et « j'ai démontré » : n = 4 était clos depuis
le 5 août, mais un théorème par nombre n'est pas un théorème sur les nombres.

**Le coup, c'est le changement de variable** : paramétrer par la MOITIÉ rend la parité
gratuite. Écrit sur n, il aurait fallu écarter les impairs — démontrer ¬(∃m)(N(3) = m+m),
un chantier entier sans rapport avec Goldbach.

**Ce que la borne coûte (le vrai apport).** La preuve tient parce que `enum` rend le
domaine FINI : K+1 branches, chacune fermée par un témoin exhibé. L'enlever casse les deux
piliers — plus d'énumération, plus de témoin. La borne n'est pas une commodité, **c'est la
frontière du problème ouvert**, et le corpus la rend mesurable.

Promu : `outils_ia/conjectures/goldbach_borne.py` + tests (21 verts, 90,8 s).

---

### 🔴 Et le prix a payer : **MON ÉNONCÉ DE GOLDBACH ÉTAIT FAUX** (ev. 256-257)

`goldbach()` disait « n pair et n ≠ 2 ». L'antécédent est **satisfait en n = 0**, et je
l'ai démontré dans le noyau, clos et sans hypothèse :

    ⊢ pair( N(0) )          (témoin k := 0, car ⊢ 0 + 0 = 0)
    ⊢ ¬( N(0) = 2 )         (par ⊢ 1 + 1 = N(2) et ⊢ ¬( N(0) = N(2) ))

L'énoncé affirmait donc que **0 est somme de deux nombres premiers**. Pas une difficulté
de preuve : une conjecture qui disait autre chose que la conjecture.

**La soundness ne protège pas de ça.** Le noyau garantit qu'on ne démontre pas de faux
théorème ; il ne dit rien sur le fait qu'un énoncé NON démontré dise ce qu'on croit. Tous
les tests portaient sur la FORME (clos, sans symbole libre, verdict « inconnu »), aucun sur
le CONTENU.

**Règle qui en sort** : pour tout énoncé conjectural, chercher activement une instance où
l'antécédent est prouvable et le conséquent manifestement faux. Bon marché, et ça vient de
payer.

**Et ce n'est pas « adapter l'énoncé à la preuve ».** La même journée a produit les deux
gestes : pour `est_premier`, REFUS d'aligner l'énoncé sur les numéraux (pont explicite) ;
pour `goldbach`, CORRECTION. Ce qui les sépare est la DIRECTION de la justification — vers
la preuve (interdit), vers la source (obligatoire).

---

### 🔴 Et une SECONDE fois, plus profond (ev. 258-259)

`goldbach()` quantifiait `(∀n)` **sans garde de finitude**. Or `pair(n)` force n à être un
CARDINAL — n = Card(k⊔k) — mais pas un ENTIER. Pour tout cardinal infini a, **a + a = a** :
a est donc « pair » au sens de l'énoncé, et a ≠ 0, a ≠ 2. L'énoncé affirmait aussi que tout
cardinal infini est somme de deux premiers.

Réparé par `est_fini(n)`. ⚠️ **Honnêteté** : ce défaut-ci est ARGUMENTÉ, pas démontré — le
corpus a a² = a (Hessenberg) mais pas a + a = a pour a infini. Le test ne fige que la
présence de la garde, et le dit.

**C'est la MÊME faute qu'hier** sur le `(∀d)` de `est_premier`. Deux fois en deux jours : un
quantificateur posé sur les ensembles quand on le croit posé sur les entiers. Ce n'est pas
un accident, c'est un motif — à chercher sur CHAQUE quantificateur d'un énoncé arithmétique.

### 👑 Et l'observation qui vaut argument pour tout le projet

**L'énoncé PROUVÉ portait déjà la bonne garde ; l'énoncé NON PROUVÉ avait dérivé.**

`goldbach_borne` a `est_fini(k)` depuis le premier jet — non par vigilance, mais parce que
`enum` EXIGE `est_cardinal(k)`. La preuve a imposé l'hypothèse que l'énoncé avait oubliée.
Les deux ont vécu côte à côte dans le même dépôt, l'une correcte, l'autre fausse.

*Démontrer force à nommer les hypothèses ; énoncer ne force rien.* À porter dans l'article.

---

### 👑 LA FORME EN n — c'est la conjecture elle-même, bornée (ev. 262-264)

**⊢ (∀n)( ( Fini n ∧ pair n ∧ n≠0 ∧ n≠2 ∧ n ≤ N(B) ) ⇒ (∃p)(∃p')( premiers ∧ n = p+p' ) )**
CLOS, 0 hypothèse, pour B = 6, 8, 10, 20.

La forme en k parlait des MOITIÉS. Celle-ci parle de n : c'est l'énoncé de `goldbach()`,
restreint. Fidélité établie par **PRÉLÈVEMENT** et non par reconstruction — j'extrais ANTE
et DEC de `goldbach()` lui-même, je vérifie que la recomposition redonne `goldbach()` à
l'identique, puis que la conclusion vaut `impl(et(ANTE, n≤N(B)), DEC)`. Rien n'est recopié.

Deux pièces neuves, closes : le **pont de cardinalité** ⊢ Card(m⊔m) = Card(Card m ⊔ Card m)
pour un terme ARBITRAIRE, et la **réfutation de parité** ⊢ ¬(∃m)(N(i) = m+m) pour i impair.

### 🔴 Et le chiffre qu'il faut annoncer avec : la DETTE D'AXIOMES

Mesuré en process frais : **Ax(D) = 67 axiomes distincts**, dont **14 des 22** de la théorie
de référence et **53 étrangers** (Graphe-terme 52, D-Knaster-Tarski 1). Les 52 sont UNE
règle — le critère C54 (E.II.46) — instanciée à 52 couples concrets. Ce n'est pas 52
hypothèses indépendantes, mais C54 est un THÉORÈME chez Bourbaki et un AXIOME de théorie
dédiée ici.

**« 0 hypothèse » + « invariant 22 » ne veut pas dire « ne dépend que des 22 ».** Le noyau
ne compte que les hypothèses du séquent ; les axiomes entrent par `axiome` et disparaissent.
Un résultat honnête s'annonce en TROIS nombres : hypothèses résiduelles, axiomes de
référence consommés, formules étrangères.

### 🔴 Mon propre piège, troisième fois dans la journée

Première mesure : « Ax(D) = 0 en 1 s ». Faux — le théorème sortait du cache. La règle était
écrite de ma main dans `numeraux.py`. Même motif que le contrôle adverse non propagé et que
la vérification en `print` au lieu d'`assert` : **un instrument qui ne peut pas détecter ce
qu'il mesure**. Contre-mesure : avant de croire une mesure, demander « qu'est-ce qui ferait
échouer cet instrument, et l'ai-je exclu ? »

---

### 👑👑👑 LA RÉDUCTION SANS BORNE (ev. 265) — Goldbach sur TOUT n

**⊢ ( (∀k)( (Fini k ∧ k≠0 ∧ k≠1) ⇒ (∃p)(∃p')( p,p' premiers ∧ k+k = p+p' ) ) ) ⇒ goldbach()**

CLOS, 0 hypothèse, 175,7 s. **Aucune borne, aucune énumération, aucun cas sur n** (sonde :
0 occurrence de enum/disj/cas dans la preuve). Les deux formules sont PRÉLEVÉES du dépôt.

Le théorème dit : *passer aux moitiés ne perd rien, pour tout n*. La conjecture entière est
ramenée à UN énoncé, et ce qui manque est isolé en un point unique — la décomposition.

Clé de la preuve : le témoin m de « n pair » est un ensemble QUELCONQUE ; le pont de
cardinalité le remplace par Card m, et le fini-descendant (Prop. 2 §III.5 close +
fini_downward déchargé) donne Fini(Card m). Reste : goldbach() ⇒ H (la réciproque) pour
l'ÉQUIVALENCE, et la promotion au dépôt.

---

### 👑👑👑 L'ÉQUIVALENCE (ev. 266) — goldbach() ⇔ forme moitiés, sur TOUT n

**⊢ ( H ⇒ goldbach() ) ∧ ( goldbach() ⇒ H )** — CLOS, 0 hypothèse, 317,6 s.

La conjecture de Goldbach EST la forme moitiés : interdérivables dans le noyau, sans borne,
sans cas sur n. La réciproque passe par la CHARNIÈRE « Card k = k sous est_cardinal k »
(qui transforme Card k ≤ k+k en k ≤ k+k), Fini(k+k) par la Prop. 1 §III.5.1 close, et le
PRÉLÈVEMENT DYNAMIQUE du lieur α-renommé (on lit le nom frais sur le théorème instancié au
lieu de le prédire). Unique analyse de cas : k ∈ {0,1,2}, taille fixe, sur la constante 2
de l'énoncé — déclarée, pas cachée ; l'aller n'en a aucune.

Reste : promotion au dépôt (pont_cardinal, parite, goldbach_borne_n, goldbach_reduction).

---

## ✅✅✅ CAMPAGNE GOLDBACH (5-6 AOÛT 2026) — TERMINÉE (ev. 226-270)

**Le résultat : ⊢ ( H ⇒ goldbach() ) ∧ ( goldbach() ⇒ H )** — l'ÉQUIVALENCE, close,
0 hypothèse, sur TOUT n, sans borne, où H = (∀k)( (Fini k ∧ k≠0 ∧ k≠1) ⇒
(∃p)(∃p')( p,p' premiers ∧ k+k = p+p' ) ). La conjecture EST sa forme moitiés ; ce qui
manque au problème ouvert est isolé en un point unique — produire la décomposition.

**L'échelle des acquis, du bas vers le haut** :
- `⊢ N(m)+N(n)=N(m+n)`, `⊢ N(m)·N(n)=N(m·n)` — l'arithmétique certifiée des numéraux ;
- `⊢ ¬(N(i)|N(p))` paramétrique (le premier calcul réel du corpus) ; `⊢ est_premier(N(p))`
  pour p = 2..17 ; courbe de coût MESURÉE : ~p² sur le plus grand premier requis ;
- Goldbach borné en k (K ≤ 30, cumul 498 s) puis en n (B ≤ 20, littéralement goldbach()
  plus UN conjoint, fidélité par PRÉLÈVEMENT) ;
- la réduction sans borne, puis la réciproque, puis l'ÉQUIVALENCE.

**Deux défauts d'énoncé DÉMONTRÉS dans le noyau** (0 « somme de deux premiers » ; ℕ+ℕ
aussi) — le motif « un ∀ posé sur les ensembles cru posé sur les entiers », commis deux
fois. L'énoncé PROUVÉ portait la garde ; l'énoncé NON prouvé avait dérivé : démontrer
force à nommer les hypothèses, énoncer ne force rien.

**La dette en TROIS nombres** (process frais) : borné = 0 / 14 sur 22 / 53 étrangères
(2 théories) ; ÉQUIVALENCE = 0 / 14 sur 22 / **73 étrangères sur 21 théories** — enlever
la borne se paie en BON ORDRE (Zorn/Zermelo/Bourbaki-Witt via le fini-descendant).

**Modules** : outils_ia/arithmetique/{numeraux, machine_num, calcul_num, non_divisibilite,
pont_cardinal, parite}.py ; outils_ia/conjectures/{goldbach, primalite, goldbach_borne,
goldbach_borne_n, goldbach_reduction, goldbach_equivalence, defaut_infini}.py.
**Tests** : tests/outils_ia/{arithmetique×4, conjectures×6} — suite 150 verts (437,8 s),
l'équivalence REDÉMONTRÉE en process frais. **Article** : sec:goldbach dans main.tex et
main_fr.tex, latexmk exit 0. Invariant 22 partout ; noyau intouché ; rien commité.

**Chantiers possibles ensuite** (décision Karl) : dériver C54 de S8+A1 pour éteindre les
52 formules étrangères ; mesurer la dette des autres capstones ; OUVERTS du III.7.

---

## 🤖 ÉTAGE 2 — CRÉER DES THÉORIES SUR L'ÎLOT GOLDBACH (6 août, ev.272-281) : CONSOLIDÉ

**La boucle invente → certifie → promeut a tourné sur un problème réel, de bout en bout.**

- **Indexation WL** du morceau manquant D(k) : plus proches voisins clos = prédécesseur
  (0,9922, chirurgie) et division euclidienne (0,9833, récurrence forte) ;
- **Anti-unification** (AST des preuves) : 2 motifs transversaux — « ∃-intro par témoin
  vérifié » et « pas de récurrence forte gardé » — CONVERGENTS avec le WL par une voie
  indépendante ;
- **Gate MDL** : 0 promotion sur 8 essais, verdict PROPRE (à 2-3 occurrences, définir coûte
  plus que compresser) ;
- **Conjectureur** (régime composé main — la découverte auto ne voit pas les fabriques
  paramétriques Python) : **60 théorèmes certifiés** (15/31/14, briques D#k réutilisées),
  dont 4 universels = la colle écrite à la main pendant la campagne, retrouvée seule ;
- **Organe ∃ réparé** (leçon partage ev.277 : somme_num(2,2) déplié > 400k nœuds, DAG ~50) :
  42 ∃ certifiés, RAM stable, témoin de régression tour 2^24 ; limite identifiée =
  l'ABSTRACTION SÉLECTIVE d'occurrences (les numéraux s'emboîtent) ;
- **4 lemmes-machine PROMUS** : outils_ia/arithmetique/lemmes_conjectures.py, 1re entrée du
  dépôt d'origine machine, prouvés en process frais, suite complète **151 verts**.

**Leçons d'étage** : la prose n'est pas un contrat (2 écarts docstring/code) ; jamais pytest
dans un pipe (2 récidives) ; tout organe s'écrit contre la structure PARTAGÉE ; 9 instruments
aveugles attrapés sur la journée. **EN ATTENTE (décision Karl)** : abstraction sélective v1
((∃x)(x+x=N6) exact, linéaire) ; tactique existe_temoin_verifie.

---

### 👑👑 CAPSTONE DE L'ÉTAGE 2 (ev.282-286) — la machine invente PUIS consomme

**⊢ decomposition(N6) redémontré par chaînage d'une INVENTION machine** : somme_num(3,3)
→ sym → sélectif (pair(N6) INVENTÉE) → ∧-assemblage (organe neuf : détachement
conjonctif, arrêt-aux-faits-connus) → MP à travers goldbach_borne_n(6). Clos, 0 hyp, 22.

En dessous : l'organe SÉLECTIF v1 (abstraction dans UN membre — S5 satisfait malgré
l'emboîtement, ~1 s/passe) a inventé est_pair(N4/N6/N10) EXACTS + 57 ∃ ; la tactique
existe_temoin_verifie née de la convergence WL+AST, câblée, testée ; leçons : le niveau
arithmétique est τ (2 organes piégés), les définitions sont des conjonctions (assembleur
= arrêt aux faits). Article sec:goldbach complet (i-iv). Suite 152 verts.

**FAIT depuis (ev.287-289)** : detachement_conjonctif + conjoints_de PROMUS dans
conj_existe (17 tests corpus verts) ; capstone INDUSTRIALISÉ (ND19 : decomposition
N6/N8/N10 à 0,1 s pièce après chauffe borne_n(10) 139 s) ; les 2 derniers sites
doubles-S5 de goldbach_borne(.py/_n.py) réécrits via existe_temoin_verifie
(11 tests verts, 82 s). Suite complète 152 verts (ev.288). Prochain : volant en
Workflow à 22h (directive Karl du 7 août).

---

## 🗺️ TICK EN COURS (2 août ~12h40, ev. 108+) — DÉRIVATION DES PONTS : LA ROUTE EST OUVERTE
**Insight mesuré** (en-tête assemble, note R2) : le blocage « iso ⇒ structure de graphe »
ne vaut que pour un φ ARBITRAIRE — or dom_h_initial_sous_val ET img_h_initial_sous_temoin
n'appliquent les ponts qu'aux φ-TÉMOINS du cœur (h_membre_donne_temoin, 8 conjoints), qui
PORTENT déjà {est_fonctionnel(φ), dom φ=S, φ⊂S×T} — les preuves les PÈLENT déjà (Hfunc,
Hdom, Hgraph). Et `val_dans_F_depuis_structure` (ensembles_trichotomie_pont_val, PONT CLOS)
dérive val_dans_F SOUS prémisse structurelle renforcée. **PLAN** : (1) lire pont_val en
entier (l'énoncé exact du renforcé + valeur_dans_codomaine) ; (2) définir les versions
RENFORCÉES val_dans_F_r / temoin_dans_S_r (prémisse += les 3 conjoints structure) et les
DÉRIVER CLOSES — val : déjà fait (pont_val ?) ; temoin : surjectivité depuis est_bijective
(grep sa déf + briques bijective→surjective ; la structure donne image(φ)=T ? sinon le
conjoint surjectif de est_bijective directement) ; (3) RECÂBLER dom_h_initial_sous_val et
img_h_initial_sous_temoin : instancier les versions renforcées au témoin et FOURNIR les 3
conjoints depuis le cœur (déjà pelés) ⇒ les hypothèses conditionnelles DISPARAISSENT ;
(4) min3 : **Th.3 à {bo(R,E), bo(R',F), maximalité} — 3 hypothèses, celles du LIVRE plus
la maximalité Zorn**. Briques incrémentales, un test par étape, dossiers au CAP (pont_val
et img_segment ont-ils de la place ? wc -l d'abord).
**MESURES FAITES (~12h50)** : pont_val = 238 l (place ✓) et livre `valeur_iso_dans_T`
{φ⊂S×T, dom φ=S, p∈S} ⊢ φ(p)∈T et `valeur_iso_dans_F` {+seg(T,Rp,F)} ⊢ φ(p)∈F — côté DOM
le recâblage est GRATUIT : remplacer Hval/val_inst dans dom_h_initial_sous_val par
valeur_iso_dans_F instancié au témoin, ses 4 hyps = Hgraph/Hdom/Hy_in_S/Hseg_T (déjà pelées)
→ coupes → val_dans_F MEURT. Côté IMG : est_bijective(f,a,b) = et(injective_dans(f,a),
est_surjective(f,a,b)) (abrege:357) — la surjectivité est un CONJOINT DIRECT de l'iso
(Hiso → décomposer est_isomorphisme_ordre jusqu'à est_bijective — lire sa déf dans
ordre_vocab pour l'ordre des conjoints — → elim droite → est_surjective(φ,S,T)) ; lire la
DÉF de est_surjective (forme ∀∃ ou image= ?) → extraction du témoin p à u∈T ; u∈T =
valeur_iso_dans_T au témoin x (t=φ(x)∈T) + initialité de T (conjoint droit Hseg_T instancié
(t,u)) ; p∈E = conjoint gauche Hseg_S (S⊂E) instancié → temoin_dans_S MEURT aussi.
ORDRE D'EXÉCUTION : (i) recâbler dom (gratuit, tester) ; (ii) lire est_surjective + iso,
écrire l'extraction, recâbler img (tester) ; (iii) min3 + test ; (iv) ev. 109 + bilan.
**🧱 TICK EN COURS — HESSENBERG STEP B : ÉTAT MESURÉ + PLAN DU RE-CÂBLAGE RÉUNION (2 août).**
ÉTAT RÉEL (mieux que la carte) : B0 FAIT (chaine_falsum_sous_temoins, falsum sous
12 hyps témoins {S₀,φ₀,Ucadre,ψ,uwit}) ; **B1 FAIT** (stepb2:178
negation_strict_sous_temoins_UF — ψ et uwit ÉLIMINÉS, testé) ; **B2 BLOQUÉ à un
MUR MÉCANIQUEMENT CLASSIFIÉ** (stepb2:251 b2_blocker_classification, testé) :
sur les 9 hyps-Ucadre de B1, 5 déchargeables (briques citées : cadre_card_trois_b,
corps du transport, maximal-data img, Z⊂E) mais 4 = MUR somme-disjointe
(S₀²∪cadre⊔=Z² FAUSSE au niveau ensembliste car cadre⊔ tagué paire(∅,∅) ;
dom-disj ; 2× ¬(∃X) non-extension) ⇒ existe_elimination("Ucadre") interdite.
**DÉBLOCAGE DOCUMENTÉ (stepb2:271-275)** : re-câbler `cadre_ensemble`
somme_disjointe → RÉUNION — la brique `s0sq_cadre_reunion_egale_carre`
(entiers_cardinaux/ensembles_produit_union_carre.py:315) est **DÉJÀ CLOSE, 0 hyp** :
(S₀×S₀)∪((S₀×U)∪((U×S₀)∪(U×U))) = (S₀∪U)×(S₀∪U). B3 s'appuie sur
card_S0_egal_card_E (frame_zorn/ensembles_frame_extension_finale.py:643 — statut
à vérifier au prochain tick). RAYON : 10 modules consomment
cadre_ensemble/phi_etendue_bijection (frame_extension_finale + cadre_plat +
structural_discharge + p5/stepb/stepb2/classify + 3 assemblage_vrai).
**MESURES COMPLÉMENTAIRES (2 août, ~14h30)** : (a) cadre_ensemble:147 =
somme_disjointe(S₀×U, somme_disjointe(U×S₀, U×U)) ; les 3 produits sont DEUX À
DEUX DISJOINTS sous U∩S₀=∅ (chaque intersection force un élément de S₀∩U) ⇒ la
variante réunion a le même cardinal ; (b) la passerelle Card(réunion disjointe)=
somme cardinale VIT dans prop13_complement (props_restantes — Card E=Card A+
Card(E∖A), manipule Eq(réunion, somme-taguée), cf. _somme_disjointe_cardinal_t
et l.218) — à réutiliser, PAS à réinventer ; (c) recollement/ensembles_dom_image_
reunion.py (dom_reunion_egale_cible:70, image_reunion_egale_cible:109) = les
briques dom/image d'un recollement RÉUNION — serviront à phi_etendue version
réunion (φ₁=φ₀∪ψ est DÉJÀ une réunion de graphes, seul le CODOMAINE/cadre était
tagué) ; (d) les 2 hyps ¬(∃X) ne sont PAS dans extension_finale ⇒ elles naissent
dans stepb.py (B0) — LIRE stepb.py:1-143 EN PREMIER au prochain tick (les 12 hyps
exactes de B0 sont la spec des variantes réunion) ; (e) ⚠️ extension_finale:4-11
AVERTISSEMENT : hessenberg_a_carre_egal_a (l'ANCIEN montage) est VACUUX (trio
contradictoire avec le lock) — les pièces sont saines, ne JAMAIS réutiliser le
montage final ; la route saine = stepb/stepb2 (B0→B4).
**👑👑 CHANTIER 5 — PLUS AUCUNE HYPOTHÈSE BLOQUANTE SUR L'INCLUSION
RÉCIPROQUE (5 août, ev. 221-222)**
`transition_valeur_dans_E`, pendant exact de `transition_definie_en` : de
`transitions_typees` + la prémisse d'indices + « t ∈ E_β », tirer
« f_{αβ}(t) ∈ E_α » (3 hypothèses). 169/169.
**BILAN MESURÉ SUR LES INSTANCES RÉELLES — tout est fournissable** :
· **6/6** conditions de domaine ← `transition_definie_en` ;
· **3/3** points-de-transition ← `transition_valeur_dans_E` ;
· **2/2** coordonnées de y' ← clause des valeurs de y' ∈ ∏_{β∈J} E'_β,
  et leurs prémisses « B ∈ J » sont **déjà au contexte** (témoins cofinaux).
· restent **11 conditions universelles** = les conditions du système projectif
  lui-même, donc des hypothèses HONNÊTES de la proposition, à laisser.
**👑 LA LEÇON DU TOUR** : **les deux moitiés du typage sont chacune porteuse,
à des endroits différents** — le DOMAINE couvre 6 hypothèses, les VALEURS en
couvrent 3, aucune ne rend l'autre superflue. C'est la justification CHIFFRÉE que
le comblement partiel du 4-5 août ne *pouvait* pas suffire, et la raison pour
laquelle le manque était invisible : tant que le domaine bloquait, le besoin de
valeurs ne se manifestait pas. *Un écart de fidélité se mesure par ce qu'il
empêche de DÉMONTRER, pas par ce qu'un test de forme accepte.*
**PIÈGE** : sonder les résidus par NATURE, pas par compte. Les 5 « hypothèses de
point » avaient deux origines distinctes que la forme syntaxique commune
(« t ∈ X ») masquait ; les traiter en bloc aurait mené à chercher une brique
unique pour les cinq, et à échouer.
**RESTE** (assemblage, plus de mur identifié) : câbler les neuf coupes dans
`prolongement_dans_lim` et conclure x̃ ∈ lim←_I, puis la chaîne déjà écrite au
report (G(x̃)=y → y ∈ G⟨lim←_I⟩ → double inclusion → Prop. 3 CLOSE).

**🔓 CHANTIER 4 — LA CONDITION DE DOMAINE EST TUÉE (5 août, ev. 219-220)**
`transition_definie_en` (ensembles_limites.py, 15 lignes) : du typage COMPLET on
tire « f_{αβ} est définie au point t », soit `(∃y)((t,y) ∈ f_{αβ})`, sous
**3 hypothèses honnêtes**. Route = celle de `hyp_applicative_de_application`
(E.R.9) : `dom f_{αβ} = E_β` → S6 transporte « t ∈ E_β » en
« t ∈ dom f_{αβ} » → AXIOME_DOM donne l'existentielle. 168/168 sur iii_7_limites.
**L'APPARIEMENT EST PROUVÉ, PAS SUPPOSÉ** : sonde sur les instances réelles de
`prolongement_coherent`, **6/6** — `port.conclusion == h`, pas une ressemblance.
C'est la différence entre « j'ai une brique qui ressemble » et « la coupe passera ».
**⚠️ LIANT** : l'existentielle porte le liant `y` d'AXIOME_DOM ; le paramètre `y`
de la fonction est documentaire. Deux α-variants sont DISTINCTS pour le noyau —
la cible doit être produite par l'axiome, jamais réécrite à la main.
**📏 ÉTAT CHIFFRÉ APRÈS COUPE** : 18 → **22** hypothèses (couper AUGMENTE le
compte : chaque coupe injecte les hypothèses de la brique — le bon indicateur
n'est pas le compte brut mais la partition *fournissable / honnête*). Non
fournies par le contexte : **16** = **5 hypothèses de POINT** (`pr_β(y') ∈ E'_β`)
+ **11 conditions UNIVERSELLES** qui sont les conditions du système projectif
lui-même, donc des hypothèses HONNÊTES de la proposition — à laisser telles
quelles. **Le prochain pas est donc les 5 points, pas les 11**, et la vraie
question y est que β parcourt J alors que certains indices utilisés sont des
témoins τ de I. Report mis à jour dans `ensembles_prolongement_terme.REPORTES`.
**LEÇON** : le déblocage n'a pas été de forcer la preuve bloquée mais de réparer
la DÉFINITION en amont — une fois « application » dit en entier, la brique
manquante s'écrit par une route déjà connue du dépôt.

**✅ TOUR DE TROIS CHANTIERS (5 août, ev. 215-218) — bilan groupé**

**CHANTIER 1 — 👑 LA MOITIÉ GAUCHE DE L'IDENTITÉ (ev. 215-216).**
Nouveau module `prop1_proj/ensembles_prop2_identite.py` :
`point_dans_produit_fibres` (z ∈ ∏ M_α, **2 hyps**) →
`point_dans_limite_fibres` (z ∈ lim← M_α, **2 hyps**) →
`point_dans_limite_depuis_u` (branché sur les coordonnées de u(z), **3 hyps**).
165/165.
**LE POINT QUI FAIT TOUT** : la condition (1) d'une limite projective ne dépend
que de **f, ≤ et I** — jamais de la famille d'ensembles. Les deux membres de
l'identité vivent donc au-dessus de LA MÊME condition (1) : on la lit une fois
sur `z ∈ lim←_I` et on la réutilise telle quelle, au lieu de la redémontrer.
C'est ce qui rend l'assemblage court.
**PIÈGE MESURÉ** : pour un z QUELCONQUE (non construit), les trois clauses de
bonne formation ne sont pas CLOSES comme dans les chantiers voisins — elles sont
DÉDUITES de `z ∈ lim←_I` (`point_limite_est_graphe` + les clauses du produit
sur E). Même résultat, raison différente : ne pas transposer mécaniquement
« objet construit ⇒ clauses gratuites », vérifier D'OÙ vient la gratuité.
**RESTE** (report honnête, dans `REPORTES`) : le côté DROIT, c'est-à-dire
l'extensionnalité du produit sur E' pour passer de « u(z) = x' » à
« (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α) », puis la double inclusion.

**CHANTIER 2 — 🔴 LE COMBLEMENT DE FIDÉLITÉ DU 4-5 AOÛT ÉTAIT PARTIEL (ev. 217).**
« f_{αβ} une APPLICATION de E_β dans E_α » dit **TROIS** choses : graphe
FONCTIONNEL, DÉFINI sur tout E_β, à VALEURS dans E_α. `transitions_typees`
n'en capturait qu'UNE (les valeurs). Découvert en butant sur l'inclusion
réciproque de la Prop. 3 : les hypothèses résiduelles non démontrables étaient
des conditions de **DOMAINE** — « (∃y)((t,y) ∈ f_{αβ}) ».
AJOUTÉ dans `ensembles_limites.py` : `transitions_applications` (f_{αβ} dans
l'EXPOSANT (E_α)^(E_β)) et `transitions_fonctionnelles_et_totales`, qui en tire
`est_fonctionnel(f_{αβ})` et `dom f_{αβ} = E_β` par `axiome_exposant`
(2 hyps chacun). 395/395 ; `docs/journal/ANOMALIES.md` mis à jour.
**⚠️ ENCODAGE, piège coûteux** : c'est l'EXPOSANT (E_α)^(E_β) — les GRAPHES
fonctionnels — et **non** 𝓕(E_β;E_α), qui est l'ensemble des TRIPLETS. Les
transitions du dépôt sont manipulées comme des graphes (`valeur(f_{αβ}, t)`
sans `graphe_de`) : se tromper des deux donne un terme qui ne se raccorde à rien.
**LEÇON DE MÉTHODE** : un écart de fidélité peut être comblé à MOITIÉ et le
test qui l'épinglait passer au vert. Le test inversé
(`test_definition_systeme_projectif_est_fidele_au_livre`) garantissait la
présence du typage, pas sa COMPLÉTUDE — il a fallu buter sur un blocage de
preuve pour voir le trou. Un test de fidélité doit épingler chaque conjoint.
Ce chantier **débloque l'inclusion réciproque de la Prop. 3**.

**CHANTIER 3 — ✅ L'OPAQUE `prod_ent` : DIAGNOSTIC INVERSE (ev. 218).**
L'audit le listait comme « à construire ». Mesure faite : le produit cardinal
binaire **existe déjà** (`produit_cardinal_binaire`, iii_3_3_produit) et la
divisibilité FIDÈLE **existe déjà** (`divise_propre`, bâtie sur Card(b×q)).
Ce qui restait n'était pas un manque de construction mais deux **RÉSERVES
PÉRIMÉES** dans les docstrings de `divise` et de
`condition_division_euclidienne`, affirmant que le produit binaire « n'est pas
un terme disponible ». Corrigées : la forme opaque est conservée non par
nécessité mais parce que les théorèmes de `ensembles_division_multiples`
en dépendent — les migrer est un refactor de PREUVES, borné et identifié.
**DÉCISION assumée** : NE PAS migrer dans ce tour (refactor de preuves vertes
≠ correction). Aucun code touché, seulement deux docstrings.
**LEÇON** : un item d'audit « opaque à construire » peut être PÉRIMÉ sans que
personne le sache — la brique manquante a été écrite ailleurs et le commentaire
ne l'a pas suivie. Vérifier en CODE avant de construire ; si la brique existe,
la vraie dette n'est plus la construction mais la MIGRATION des consommateurs.

**👑👑 LE CŒUR DE LA 2ᵉ ASSERTION, QUANTIFIÉ (5 août ~07h30, ev. 213-214)**
`fibres_partout ⊢ ( (∀α)(α∈I ⇒ pr_α z ∈ M_α) ⇔ (∀α)(α∈I ⇒ pr_α(u(z)) = x'_α) )`
sous **deux hypothèses** seulement : la famille des u_α fonctionnels et totaux,
et z ∈ lim←_I.
Le membre gauche est ce que réclame l'appartenance à lim← M_α ; le droit est ce
que donne « u(z) = x' ». **Les relier, c'est relier les deux ensembles de
l'identité** u⁻¹(x') = lim← M_α. Les hypothèses ponctuelles sont devenues une
hypothèse de FAMILLE — c'est ce qui rend la généralisation licite.
**Helper réutilisable écrit au passage** : `_equiv_sous_garde`, de
`G ⇒ (P ⇔ Q)` tirer `(G ⇒ P) ⇔ (G ⇒ Q)`. `congruence_pour_tout` réclame une
ÉQUIVALENCE, pas une implication vers une équivalence — le pas propositionnel
manquait. À ressortir dès qu'on quantifie une équivalence gardée.
**PIÈGE** : `lim_u_coordonnee` conclut `pr_α(u z) = u_α(pr_α z)`, soit le sens
INVERSE de celui qu'attend S6 pour remplacer `u_α(pr_α z)` PAR `pr_α(u z)`.
*Une égalité est orientée dans le noyau même si elle ne l'est pas en
mathématiques* — vérifier le sens avant chaque S6.
389/389 ; le module est à 283 lignes de code (marge faible, prévoir la scission).

**👑 LE CHAÎNON DE LA 2ᵉ ASSERTION, écrit en 20 lignes (5 août ~06h, ev. 211-212)**
`coordonnee_dans_fibre ⊢ ( pr_α z ∈ M_α ⇔ u_α(pr_α z) = x'_α )`, 3 hypothèses
honnêtes. C'est le **pivot des deux côtés** de l'identité u⁻¹(x') = lim← M_α :
il traduit l'appartenance à lim← M_α en l'égalité u(z)=x' lue coordonnée par
coordonnée. Construit par `membre_fibre_t` + `fibre_composante`, recollés par S6
sur la position ENSEMBLE.
*Le fait marquant : cette pièce était reportée depuis des mois, et une fois
l'accesseur `M_indice` rendu transparent elle s'écrit en vingt lignes. Le blocage
n'était pas mathématique, il était d'ENCODAGE — vérifier l'encodage avant
d'estimer la difficulté d'un énoncé reporté.*
**RESTE, et c'est de l'assemblage** : à gauche `appartient_limite_projective` sur
la famille construite, à droite `membre_fibre` + `lim_u_coordonnee` ; la
condition (1) sur z est COMMUNE aux deux côtés, donc à factoriser plutôt qu'à
prouver deux fois. 387/387.
**PIÈGE** : ne jamais nommer une variable locale comme un constructeur importé
(`equiv`, `et`, `impl`, `egal`) — l'erreur « Theoreme object is not callable »
surgit à l'appel *suivant* du constructeur, loin de sa cause.

**✅ DEUXIÈME OPAQUE LEVÉ EN DEUX JOURS — `M_indice` (5 août ~05h, ev. 209-210)**
`M_indice` était `app("M_indice", M, α)` : un **accesseur** opaque, sans axiome.
Rien n'était donc démontrable sur les M_α, et la 2ᵉ assertion de la Prop. 2
(« u⁻¹(x') = lim← M_α ») était hors d'atteinte **par construction** — exactement
le diagnostic de `restriction_systeme_indices`, à un jour d'intervalle.
**Remède identique** : Bourbaki écrit « une famille (M_α) de parties », et une
famille EST une fonction ⇒ `M_indice := valeur_famille`. Les **8 sites qui
recopiaient** `app("M_indice", …)` appellent désormais la définition (6 tests
aussi — ils recopiaient l'encodage au lieu de l'appeler).
**Dividende immédiat** : `famille_fibres` (la famille des fibres CONSTRUITE) et
`fibre_composante ⊢ M_α = u_α⁻¹⟨{x'_α}⟩`, **1 hypothèse** — le pont qui
manquait. Plus un test qui FIGE la transparence : si quelqu'un la reperdait, la
2ᵉ assertion redeviendrait indémontrable sans que rien ne le signale.
*Règle : quand le livre dit « une famille », l'encodage doit être une FONCTION et
l'accès une VALEUR — pas un `app()` dédié.*
**🔧 ET MON PROPRE OUTIL AVAIT UN FAUX POSITIF** : `audit_termes_opaques`
signalait ENCORE `M_indice` après correction — il scannait le TEXTE et comptait
les `app()` cités en **docstring** comme du code. Passé en lecture **AST** :
144 → 113 constructeurs, l'écart était entièrement du bruit. C'est son deuxième
faux positif (le premier : chercher le nom brut au lieu de l'enveloppe).
*Un audit qui crie au loup sur ses propres corrections perd toute valeur —
vérifier qu'il redevient silencieux est le test de l'outil lui-même.*
Restent 4 opaques partagés : `Sig`, `pr_indice`, `prod_ent`, `struct_induite`.
386/386.

**✅ L'ÉCART DE FIDÉLITÉ EST COMBLÉ — la définition du système projectif est
enfin celle du livre (5 août ~03h, ev. 207-208)** : `est_systeme_projectif` porte
désormais les **trois** conditions de Bourbaki — le typage des transitions,
(LP_I) et (LP_II) — au lieu des deux numérotées.
**Pourquoi le typage était tombé** : la signature `est_systeme_projectif(f, leq,
i, …)` ne prenait pas la famille `E`. Il était donc *impossible* d'y écrire
« f_{αβ} envoie E_β dans E_α » — **le manque était inscrit dans le TYPE de la
fonction, pas dans son corps**, ce qui le rendait invisible à toute relecture du
corps. La signature a gagné `Efam` en tête.
**Pourquoi c'était sûr** — et mon estimation de la veille était alarmiste :
mesure faite, **aucun théorème n'ASSUME** la définition composite (les preuves
utilisent `cocycle_projectif` directement) ; elle n'est que *composée*
(`est_systeme_projectif_filtrant`) et *projetée*. Or renforcer le conjoint droit
d'une conjonction ne casse pas sa projection. *Mesurer qui ASSUME vs qui COMPOSE
avant d'estimer le risque d'un renforcement.*
**Le test a été INVERSÉ, pas supprimé** : il épinglait l'ABSENCE du typage, il
épingle maintenant sa PRÉSENCE — c'est le même test qui garantit qu'on ne le
reperdra pas. Entrée de résolution ajoutée dans `ANOMALIES.md`.
384/384, 2168 notions, `theorie==22`.
**RÈGLE** : quand une définition du livre paraît incomplète, regarder d'abord si
sa SIGNATURE peut seulement exprimer ce qui manque. Un paramètre absent est un
symptôme plus fiable qu'une relecture du corps — et il est vérifiable
mécaniquement.

**🔓 LE VERROU DE FORME DE L'INCLUSION RÉCIPROQUE EST LEVÉ (5 août ~01h,
ev. 202-203)** : `appartient_limite_projective` et `limite_projective_relation_1`
étaient **non term-safe** — `var(Efam)` au lieu de `_t(Efam)`. Un `Efam` déjà
TERME devenait `var(Terme)`, doublement enveloppé, et l'énoncé ne s'appariait
plus. Conséquence : **toute la machinerie du prolongement était incapable de
viser la limite d'un système CONSTRUIT**. Corrigé à la source (neutre pour les
six appelants, qui passent tous des NOMS), puis `Efam` threadé dans
`prolongement_coherent` et `prolongement_coherent_universel` (défauts inchangés,
miroirs 18 et 4 vérifiés).
Résultat : `prolongement_coherent(f="f", x="yp", Efam=restriction_construite())`
porte **exactement** l'hypothèse « y ∈ lim←_J ». 383/383.
*Leçon : le double enveloppage `var(Terme)` n'est pas cosmétique — il INTERDIT
de viser un objet construit, donc il bloque des chantiers entiers. Le corriger à
la source est neutre quand tous les appelants passent des noms.*
**🧱 MUR DU TICK, honnête** : identifier les 14 hypothèses portant les indices
n'a **pas convergé**. Essayé et échoué : appartenances des quatre termes
(α, α', β(α), β(α')) dans I et dans J, ordres entre eux, prémisses composites de
la relation (1) et du cocycle, coupes par `temoin_cofinal` aux deux indices +
`cofinale_dans_inclusion` + `cofinale_dans_condition` — **zéro coupe**. Une seule
identifiée : la prémisse composite du cocycle en (α', β(α')). Structure mesurée :
8 cascades et 6 existentielles de liant « y ».
**PROCHAIN PAS, précis** : ne pas ré-énumérer des candidats — *remonter à
`_via_delta` et lire ce que ses deux briques ASSUMENT*, puis reconstruire ces
formes exactes depuis le contexte. Quand une identification par candidats échoue
en bloc, c'est la forme supposée qui est fausse, pas le catalogue qui est
incomplet.

**👑 x̃ DANS LE PRODUIT, et une PRÉVISION FAUSSE corrigée (4 août ~23h30,
ev. 199-201)** : `prolongement_dans_produit ⊢ x̃ ∈ ∏_{α∈I} E_α` sous **trois
hypothèses de contexte seulement** — transitions typées, J cofinale,
y ∈ lim←_J — et **aucune propre à x̃**. Chaîne : `coordonnee_de_y_dans_E`
(y_{β(m)} ∈ E_{β(m)}, lue sur y ∈ lim←_J via le pont du système restreint) →
`clause_valeurs_prolongement` (quantifiée, **assertée égale** à
`hypothese_valeurs(E, I, i, x̃)`) → pivot + les trois faits clos. 155/155.
**DEUX PIÈGES** : le pivot porte les **quatre** clauses en hypothèses — couper
les trois closes ne suffit pas, il faut aussi couper celle des valeurs *par sa
preuve* ; et le **nom du point d'évaluation** devient le liant de la clause des
valeurs, qui doit être celui de l'axiome du produit (« i ») — avec un autre nom
le modus ponens final échoue sans rien signaler.
**🔻 AUTOCORRECTION (ev. 201)** : j'avais écrit que la condition (1) restante ne
demandait « aucune difficulté mathématique, seulement de la forme ». **C'était
faux.** Mesurées une à une, les 14 hypothèses de `prolongement_coherent` portant
les indices sont **6 existentielles de témoin, 3 conditions universelles et
5 cascades** — les propriétés du témoin canonique et la relation (1) sur y, pas
des gardes d'appartenance. Les fournir depuis le contexte, c'est les
**démontrer**. Report corrigé.
*Leçon : ne pas qualifier un reste de « mécanique » sans avoir identifié ses
hypothèses une à une — le compte ne dit rien de leur nature, et un report trop
optimiste est pire qu'un report absent.*

**🔴 DEUX ÉCRITURES DE « J COFINALE » — la Prop. 3 tombe à UNE hypothèse
(4 août ~22h, ev. 196-198)** : en comptant les hypothèses d'une nouvelle brique,
une de trop. Cause : `temoin_cofinal` utilise `_gleq` (« (u,v) ∈ **Gleq** »)
tandis que `cofinale_dans_inclusion` a pour **défaut** `_R_defaut`
(« (u,v) ∈ **G** »). Tout théorème combinant les deux portait **deux hypothèses
de cofinalité** disant la même chose. Corrigé aux quatre sites d'appel en passant
`leq` explicitement.
**EFFET MESURÉ** : `coordonnees_egales_partout` 5→4, `prop3_g_injective` 5→4, et
surtout **les formes UNIVERSELLES passent de 2 à 1** — `prop3_g_injective_universelle`,
`injectivite_g_construite`, `g_injective_dans` **et
`g_bijection_sous_surjectivite`**. Autrement dit : *la Proposition 3 en
vocabulaire du dépôt ne tient plus qu'à **UNE** hypothèse de contexte.*
**RÈGLE** : ne jamais laisser une brique choisir sa relation d'ordre par défaut
quand le contexte en fixe une. Même famille que le double-enveloppage
`var(var('f'))` — deux écritures d'un même énoncé — et **le compte d'hypothèses
reste le détecteur**.
**ÉCLATEMENT** : `prop1_proj` était au cap de 10. **MAX_PATH mesuré AVANT**
(198 caractères avec un sous-dossier, contre 244 pour le plus long du dépôt et
260 de limite) → sous-dossier `prop3_surj/`, deux modules déplacés, tests scindés
en miroir, `prop1_proj` revient à 9.
**PROLONGEMENT** : `ensembles_prolongement_terme.py` — x̃ comme TERME
(`graphe_terme(I, x_tilde)`), trois faits CLOS, et `valeur_prolongement_dans_E ⊢
x̃(m) ∈ E_m` où `transitions_typees` figure **nommément** (le test l'épingle).
*L'écart de fidélité de l'ev. 195 se paie exactement là où il était prédit.*
380/380 (III.7 + IV).

**🔴 LE LIVRE DIT PLUS QUE LE CODE — écart de fidélité sur la définition même du
système projectif (4 août ~20h, ev. 195)** : en cherchant pourquoi l'inclusion
réciproque résistait, la cause n'était ni une tactique ni un liant : **c'est la
définition encodée qui est incomplète**. Bourbaki écrit, *avant* (LP_I) et
(LP_II) : « soit f_{αβ} **une application de E_β dans E_α** ». Ce typage fait
partie de la donnée du système ; `est_systeme_projectif` ne garde que les deux
conditions **numérotées**. Sans lui, « f_{αβ}(z) ∈ E_α » est indisponible — et
c'est exactement ce qu'il faut pour placer le prolongement x̃ dans lim←_I.
**LEÇON GÉNÉRALE** : *une définition encodée comme conjonction de ses conditions
numérotées peut avoir perdu le typage énoncé en prose juste avant — le typage n'a
pas de numéro, donc il ne saute pas aux yeux à la relecture.* À vérifier pour
chaque définition structurée du dépôt.
**FAIT** : anomalie documentée (`docs/journal/ANOMALIES.md`) avec l'ampleur
mesurée — 9 références dont une **dérivation** (`ensembles_cofinal:341`) ;
constructeur `transitions_typees` ajouté auprès de la définition qu'il complète ;
test qui épingle que le typage n'est PAS un conjoint de `est_systeme_projectif`.
**NON FAIT, ASSUMÉ** : renforcer `est_systeme_projectif` — modifier une
définition consommée par neuf sites au milieu d'un autre chantier, c'est réparer
sous pression des dérivations qu'on n'a pas auditées. Chantier à part.
**OUTILLAGE** : le PDF du livre est un **scan sans couche texte** et `pdftoppm`
est absent de l'environnement — passer par la transcription V7, fidèle et
lisible. 149/149.

**👑👑👑 UNE MOITIÉ ENTIÈRE DE LA SURJECTIVITÉ, À UNE HYPOTHÈSE (4 août ~19h,
ev. 191-193)** : `image_incluse_dans_limite ⊢ G⟨lim←_I⟩ ⊂ lim←_J`, **une seule
hypothèse** — la cofinalité de J, c'est-à-dire l'hypothèse même de la
Proposition. Plus ponctuel : une inclusion d'ensembles.
Chaîne : `restriction_construite`/`restriction_valeur` (déblocage) →
`clause_valeurs_restreinte` → `valeur_dans_produit_restreint` →
`condition_1_de_la_valeur` → `valeur_dans_limite_restreinte` (G(x) ∈ lim←_J) →
élimination du témoin d'AXIOME_IMAGE.
**LE RACCOURCI** : après avoir construit la restriction, le réflexe était de
démontrer l'égalité des deux produits. **Inutile** — il suffit de *refaire la
construction dans le bon système* : le pivot étant paramétré par la famille, le
⋃ de l'inclusion s'aligne tout seul. Chercher le raccourci que la construction
rend possible avant d'entreprendre l'égalité de deux objets.
**PIÈGES DU JOUR** : `alpha_existe` **avant** `existe_elimination` (le liant de
l'existentielle doit coïncider avec le nom du témoin) ; `inclus` lie « z » ; la
prémisse **composite** de la relation (2) doit être reconstruite pour être
coupée (ses trois conjoints séparément ne suffisent pas — déjà vu ev. 170) ;
évaluer G en son propre nom de liant libre est dégénéré.
**RESTE — SEULE PIÈCE DE TOUTE LA PROP. 3** : l'inclusion réciproque
lim←_J ⊂ G⟨lim←_I⟩, dont le témoin est le prolongement x̃ (route détaillée dans
`REPORTES`). 147/147 iii_7_limites ; chapitres I et II verts (1083).

**🔴 UN TERME OPAQUE *SANS AXIOME* — L'IMPASSE SILENCIEUSE (4 août ~17h,
ev. 187-189)** : `prop1_proj/ensembles_g_surjection.py`.
En attaquant la surjectivité ensembliste, la moitié (a) est tombée vite :
la famille (f_α(x))_{α∈J} étant CONSTRUITE, **trois des quatre clauses** de
l'appartenance au produit sont CLOSES (graphe, fonctionnel, domaine), et la
quatrième — la clause des VALEURS — est **démontrée** (`clause_valeurs`, 2 hyps
de contexte) : G(x)(ι)=f_ι(x), puis f_ι(x)=pr_ι(x), puis pr_ι(x) ∈ E_ι, la
réécriture se faisant par **S6**. D'où `valeur_dans_produit` :
{ x ∈ lim←_I, J cofinale } ⊢ G(x) ∈ ∏_{α∈J} E_α.
**Puis le raccord à lim←_J a buté sur autre chose qu'une difficulté** :
`restriction_systeme_indices` est un terme opaque **sans AUCUN axiome**
(`app("restr_indices", E, f, J)`), et c'est lui qui dénote le système restreint,
donc `lim←_J := lim_proj(restr_indices(E,f,J), f)`. **Aucun énoncé mentionnant
lim←_J n'est démontrable** — non par manque d'effort, mais parce que le terme
n'est caractérisé par rien. C'est pourquoi `valeur_dans_produit` conclut dans
`produit_famille(E, J)` : rien ne relie les deux termes.
*Même diagnostic que pour `application_canonique_g`, en pire — là il y avait au
moins un axiome. Un opaque SANS axiome est une **impasse silencieuse** : elle ne
se révèle qu'au moment du raccord.*
**DÉBLOCAGE ENGAGÉ** : `restriction_construite` (= `graphe_terme(J, E_α)`) et
`restriction_valeur` (⊢ (restr)_ι = E_ι sous ι∈J, **1 hypothèse**) sont écrits et
testés. Un détail d'encodage rend le pont immédiat : dans le dépôt
`valeur_famille(E, ι)` **EST** `valeur(E, ι)`. Reste l'égalité des deux produits
puis des deux limites, et la migration des consommateurs. 143/143.
*Leçon d'audit : distinguer les `app(...)` qui ont un axiome de ceux qui n'en ont
aucun — les seconds sont des impasses.*

**👑👑👑 LA PROP. 3 EN VOCABULAIRE DU DÉPÔT, À UNE PRÉMISSE NOMMÉE PRÈS
(4 août ~13h30, ev. 182-186)** : `g_bijection_sous_surjectivite ⊢
( G⟨lim←_I⟩ = lim←_J ) ⇒ est_bijection_de(G, lim←_I, lim←_J)`, sous les **deux
seules hypothèses de la Prop. 3** (J cofinale, système projectif).
Trois des quatre conjoints sont acquis **sur le terme construit** :
`est_fonctionnel` CLOS, `dom` CLOS, `injective_dans(G, lim←_I)` 2 hyps — ce
dernier avec les liants « u »/« up » du dépôt. Le quatrième, la surjectivité
ENSEMBLISTE, est porté en **prémisse explicite** au lieu d'être passé sous
silence : ses deux inclusions sont déjà acquises ponctuellement (⊆ par
`cofinal_canonique_compatible`, ⊇ par `prolongement_restitue` +
`prolongement_coherent_universel`), il ne manque que leur recollement par
`egalite_par_extension`. **Que la conjonction se forme PROUVE au passage que les
quatre conjoints portent sur le MÊME terme** — ce qu'un report en prose ne
garantirait pas. 137/137.
**MIGRATION FAITE** pour toute la chaîne d'injectivité : paramètres
`(gterme, formule_3)` threadés de `cofinal_canonique_coordonnee` jusqu'à
`prop3_g_injective_universelle`, tous rétro-compatibles (défaut = terme opaque),
**zéro test cassé**. Le noyau REFUSE le mélange incohérent (gterme construit +
axiome opaque) : la migration est sûre par construction.
**🔴 PIÈGE MAJEUR (ev. 182)** : **`graphe_terme` NE LIE PAS**. Son encodage est
`app("graphe_terme", A, T)` — le paramètre `x` de la signature est documentaire.
Donc `libres(graphe_g()) = {E, J, f, x, a}` : le terme construit porte ses deux
« liants » comme variables LIBRES. Le brancher dans la chaîne Prop. 3 (où « a »
est l'indice libre) fait que la substitution de « a » atteint le terme g, et
`coordonnees_egales_partout` échoue sur « prémisse non réduite (2) » — **deux
étages au-dessus de la cause**. Remède : noms FRAIS au site d'accueil
(`pt="s", idx="t"`). *Vérifier `libres_t()` d'un terme construit AVANT de le
brancher, au lieu de le supposer clos.*
**DÉFAUT CORRIGÉ (ev. 184)** : double enveloppage `var(var('f'))`.
`prop3_g_injective_pointwise` passait les TERMES à `limite_projective_relation_1`
qui fait `var()` en interne ⇒ le théorème portait **deux hypothèses
syntaxiquement distinctes disant la même chose** (« x ∈ lim←(E,f) » ET
« x ∈ lim←(var E, var f) »). Paramètres BRUTS ⇒ elles fusionnent : pointwise
8→6, `coordonnees_egales_partout` 7→5, `prop3_g_injective` 7→**5**.
*Le compte d'hypothèses est un détecteur de défaut de forme.*
**PIÈGE (ev. 185)** : `(∀x)R` est encodé `¬(∃x)(¬R)` — **trois** niveaux à
dépiler pour atteindre R, pas deux. Et « u » ne peut pas servir de liant en
cours de preuve (réservé du kit) : démontrer avec un nom sûr puis **α-renommer**
en fin de course, liant interne AVANT la généralisation externe.

**👑👑👑 L'AXIOME (3) DE LA LIMITE PROJECTIVE EST DÉMONTRABLE — g CONSTRUITE
(4 août ~11h, ev. 177-179)** : `prop1_proj/ensembles_g_construite.py`.
Le blocage réel de la Prop. 3 n'était ni l'injectivité ni la surjectivité (toutes
deux prouvées et quantifiées) : c'était que **g n'était pas un objet-fonction**.
`application_canonique_g` est un terme OPAQUE `app("g_restr_J", …)` dont la seule
caractérisation est un AXIOME définitionnel — la formule (3) — posé dans une
théorie dédiée. Rien ne donnait `est_fonctionnel(g)` ni `dom(g)`, donc rien ne
permettait d'écrire `est_bijection_de(g, lim←_I, lim←_J)`.
**La sortie n'est pas d'ajouter des axiomes, c'est de construire l'objet** avec
les fabriques du dépôt — deux `graphe_terme` emboîtés :
    famille(x) := graphe_terme( J, f_α(x) )          liant α
    g          := graphe_terme( lim←_I, famille(x) ) liant x
Et tout tombe :
  • `g_est_fonctionnelle`, `g_est_un_graphe`, `g_domaine` — **CLOS, 0 hyp** ;
    les deux premiers forment la moitié « (func ∧ dom=X) » de `est_bijection_de`,
    celle qui manquait ENTIÈREMENT ;
  • `g_formule_3` — **la formule (3) DÉMONTRÉE**, sous ses deux prémisses exactes
    {x ∈ lim←_I, α ∈ J}, ni plus ni moins ;
  • `g_formule_3_quantifiee` — sa forme quantifiée, **CLOSE**.
Donc `axiome_canonique_g` **était superflu** : un axiome démontrable est un
axiome de confort, pas une hypothèse sur le monde. theorie==22 inchangé (l'axiome
vivait dans une théorie dédiée, pas dans les 22).
**MIROIR TESTÉ, pas affirmé** : un unique constructeur `corps_formule_3(gterme)`
sert aux deux emplois — appliqué au terme OPAQUE il doit rendre
`axiome_canonique_g` **mot pour mot** (`formule_3_reproduit_l_axiome`), appliqué
au terme construit il donne la cible. Sans ce partage, « même énoncé » n'aurait
été qu'une lecture à l'œil. 131/131 iii_7_limites.
**MIGRATION, PREMIER PAS FAIT (ev. 180)** : `cofinal_canonique_coordonnee` n'est
plus câblée sur l'axiome — elle prend un paramètre `formule_3` (défaut = l'axiome,
donc rétro-compatible, zéro test cassé) et, passée `g_formule_3_quantifiee`, rend
le même énoncé sous les mêmes hypothèses **sur le terme construit**. Le test
asserte que les deux conclusions DIFFÈRENT — sans quoi on n'aurait pas montré
qu'on parle bien de deux termes. 132/132.
**⚠️ GARDE POSÉE (ev. 181), à ne pas oublier** : `func(g)` et `dom(g)` portent sur
le terme CONSTRUIT ; l'injectivité et la surjectivité de la Prop. 3 portent encore
sur le terme OPAQUE (câblé en dur dans `cofinal_canonique_compatible`,
`prop3_g_coordonnee_egale`, `prop3_g_injective_pointwise`, `prop4plus` ×2).
**NE PAS les conjoindre en `est_bijection_de` avant d'avoir unifié le terme** :
deux énoncés vrais sur deux termes différents ne se conjoignent pas. Le reste de
la migration est mécanique (paramétrer ces 5 sites, re-tester après chacun), pas
mathématique — c'est l'unique obstacle restant à « g bijective » littéral.
**LEÇON GÉNÉRALE** : chercher les `app(...)` opaques caractérisés par un axiome —
chacun est un candidat au même traitement.
**PIÈGE (ev. 179)** : le piège « paramètres BRUTS » a **deux sens**. Le kit C54
exige des NOMS et non des Termes pour le point d'évaluation
(`graphe_terme_valeur(A,T,var("p"),…)` échoue, `(…,"p",…)` passe) ; d'autres
briques veulent l'inverse. Quand un MP interne échoue sans raison mathématique,
tester la variante nom/terme AVANT de chercher une cause de fond.
**🔧 TACTIQUE PROMUE (ev. 177)** : `porter_aux_termes` quitte
`prop1_proj/ensembles_prolongement_cofinal` pour
`i_2_theoremes/tactiques/outil_portage.py` (le module d'origine le ré-exporte).
C'est une tactique, pas un fait de théorie : la laisser dans un module de limites
projectives obligeait le chapitre IV à importer le chapitre III. Elle remplace
`_dval_t` et `_nt` de `cst_criteres/ensembles_cst1_identite`, avec **miroir ==
vérifié sur les trois formes réellement utilisées** (conclusions ET hypothèses) ;
228 tests `iv_structures` verts.

**👑👑 UN LEMME DE 20 LIGNES RETIRE 9 HYPOTHÈSES SUR 4 THÉORÈMES (4 août
~10h, ev. 174-176)** : `prop1_proj/ensembles_lim_graphe.py` — « tout point de
lim← est un graphe », **CLOS** (`limite_points_graphes`, 0 hypothèse ;
`point_limite_est_graphe` n'en ajoute aucune à sa prémisse). La preuve tient en
un modus ponens : `_lim_dans_produit` (lim← ⊂ ∏) puis **`produit_graphe`, qui
était CLOS DEPUIS LE 26 JUILLET** — depuis la réparation de l'axiome du produit.
Le lemme était à portée de main depuis dix jours ; le travail utile n'était pas
la preuve mais **le raccord**.
Effets MESURÉS chez les consommateurs, où les conditions de graphe étaient
portées comme hypothèses honnêtes avec la mention « issues de l'appartenance à
la limite » — mention qui décrivait un théorème NON ÉCRIT :
  • `prop3_g_injective` **9 → 7** hyps ; la prémisse de la forme universelle ne
    porte plus de condition de graphe (vérifié structurellement, pas par
    comptage) — l'écart signalé en report à l'ev. 172 est **RÉSOLU** ;
  • `prop2_injectivite` **9 → 5** — les quatre conditions de bonne formation
    (y,z ∈ ∏ *et* graphes) se déduisent toutes de « y,z ∈ lim← », déjà supposée ;
  • `cone_unicite` **4 → 3** : la prémisse `cone_images_graphes` **disparaît de
    l'énoncé de l'UNICITÉ du cône** (Prop. 1 §III.7.2) — la preuve établissait
    déjà u(y), u'(y) ∈ lim← ;
  • `coordonnees_egales_points` **6 → 5** (même schéma).
124/124 iii_7_limites, theorie==22.
**LEÇON** : chercher dans les docstrings les mentions « découle de », « issu de »
portées sur une hypothèse — ce sont des **dettes**, pas des hypothèses : des
théorèmes non démontrés qui affaiblissent gratuitement les énoncés.
**PIÈGE (ev. 176)** : `est_un_graphe(g)` abrège (∀z)(z∈g ⇒ z est un couple) —
elle **lie « z »**. Un point NOMMÉ « z » est capturé : `est_un_graphe(var("z"))`
dit (∀z)(z∈z ⇒ …). Les noms libres doivent éviter les liants des ABRÉVIATIONS
qu'on leur applique, pas seulement ceux des briques appelées. Défaut passé à
« p », et un `pytest.raises` fige le garde-fou.
**👑 PROP. 3 — SURJECTIVITÉ SOUS FORME UNIVERSELLE (4 août ~09h15, ev. 173)** :
`prolongement_coherent_universel ⊢ (∀α)(∀α')( … ⇒ x̃_α = f_{αα'}(x̃_{α'}) )` —
4 hyps de contexte seulement, les quatorze qui portaient un indice étant
déchargées en prémisse. C'est la condition (1) pour la famille prolongée, donc
**x̃ ∈ lim←_I** universellement : la moitié « existence de l'antécédent » de la
surjectivité est maintenant quantifiée, comme l'injectivité (ev. 172).
Les deux sens de la Prop. 3 sont donc démontrés ET quantifiés. 120/120
iii_7_limites. Le motif « décharger ce qui porte la variable, puis généraliser,
puis vérifier par test qu'aucune hypothèse ne la contient plus » a servi trois
fois de suite (ev. 170, 172, 173) — il est devenu routine.
**👑 PROP. 3 — INJECTIVITÉ UNIVERSELLE, 2 HYPOTHÈSES (4 août ~09h, ev. 172)** :
`prop3_g_injective_universelle ⊢ (∀x)(∀x')( … ⇒ x = x' )` — les sept
hypothèses portant l'un des deux points sont déchargées en prémisse, puis on
généralise ; **ne subsistent que DEUX hypothèses de contexte** (J cofinale
dans I, et le système projectif) — celles qui ne dépendent d'aucun point.
Le test vérifie l'invariant qui rend la généralisation licite : aucun des deux
points ne reste libre dans une hypothèse. 119/119 iii_7_limites.
HONNÊTETÉ SUR LA FORME : ce n'est PAS littéralement `injective_dans(g, lim←)`
du dépôt — la prémisse porte en plus « x, x' sont des graphes », condition
qu'exige l'extensionnalité du produit. La retirer suppose le lemme « tout
point de lim← est un graphe » (vrai, car lim←⊂∏, mais non écrit). Ce report
est posé explicitement, avec le second ajustement restant (la surjectivité
sous forme universelle). Je préfère livrer un énoncé exact avec sa prémisse
visible plutôt qu'un énoncé qui ressemble à celui du livre au prix d'un flou.
**👑👑👑 PROP. 3 §III.7.2 — L'INJECTIVITÉ EST COMPLÈTE (4 août ~08h40,
ev. 171)** : `prop3_g_injective ⊢ x = x'` (9 hyps honnêtes) — la canonique
cofinale g est INJECTIVE, au sens plein : de g(x)=g(x') on tire l'égalité des
points, pas seulement de leurs coordonnées. Branchement de
`extensionnalite_produit` sur les coordonnées réduites (ev. 170), avec
`_lim_dans_produit` pour l'appartenance au produit — motif `cone_unicite`.
**Les DEUX SENS de la Prop. 3 sont désormais démontrés** : injectivité (ici) et
surjectivité (ev. 167), le tout sans axiome du choix. Ne reste que la
conjonction en un énoncé « g bijective » au vocabulaire est_bijection_de.
118/118 iii_7_limites.
PIÈGE DU TICK : `extensionnalite_produit` doit être construite **avec le même
index de quantification** que le ∀ des coordonnées (ici « lam ») — deux
formules qui disent la même chose ne s'apparient pas si leurs liants diffèrent.
Une ligne de diagnostic (comparer l'antécédent attendu au fourni) l'a montré ;
c'est la 4ᵉ fois cette nuit qu'un échec de modus ponens vient d'un LIANT et non
des mathématiques. Et report + en-tête ont été corrigés dans le même geste
(ev. 168) : le module annonçait encore ce branchement comme « à faire ».
**🎯🎯 PROP. 3 — PRÉMISSE RÉDUITE À « λ∈I » (4 août ~08h15, ev. 170)** :
`coordonnees_egales_partout` conclut désormais **(∀λ)( λ∈I ⇒ pr_λ x = pr_λ x' )**
(7 hyps) — la forme EXACTE qu'attend `extensionnalite_produit`. Ce qui
résistait aux coupes naïves a été identifié par sonde : la prémisse du cœur
pointwise n'est pas une conjonction de trois faits séparés mais une **prémisse
COMPOSITE** ((λ∈I et β(λ)∈I) et λ≤β(λ)) — et son deuxième conjoint porte
β(λ)∈**I**, pas ∈J. Les trois pièces se fournissent sous λ∈I : β(λ)∈J et
λ≤β(λ) par `temoin_cofinal`, **β(λ)∈I par l'inclusion J⊂I que porte la
définition même de la cofinalité** (est_cofinale_dans = A⊂E ET la condition de
majoration — l'inclusion était disponible depuis le début), puis la composite
est reconstruite par conjonction. 117/117 iii_7_limites.
LEÇON DE MÉTHODE : quand une hypothèse résiste à la coupe, ne pas insister à
l'aveugle — **sonder son identité** en la comparant aux candidats construits
(ici 4 essais ont suffi). La forme réelle était à un conjoint près de ce que je
supposais. ⚠️ Et l'en-tête du module, qui annonçait encore l'ancienne forme de
l'énoncé, a été corrigé dans le même geste (piège ev. 168 : un module peut se
contredire entre son en-tête et ce qu'il prouve).
**🎯 PROP. 3 — L'INJECTIVITÉ PASSE AU « POUR TOUT λ » (4 août ~07h50,
ev. 169)** : `prop1_proj/ensembles_prop3_injectif_total.py` :
**coordonnees_egales_partout ⊢ (∀λ)( … ⇒ pr_λ x = pr_λ x' )** (6 hyps).
L'obstacle était que le cœur pointwise du dépôt (`prop3_g_injective_pointwise`)
porte un témoin cofinal α LIBRE, qui dépend de λ — impossible de généraliser.
Le remède : substituer le **témoin CANONIQUE** β(λ) (ev. 163, sans axiome du
choix) par `porter_aux_termes`, ce qui rend la dépendance FONCTIONNELLE ; les
conditions de témoin deviennent alors déchargeables (elles sont fournies par
`temoin_cofinal`) et la généralisation devient licite. Le test vérifie
explicitement l'invariant qui rend la preuve valide : **λ ne reste libre dans
aucune hypothèse**. 117/117 iii_7_limites.
REPORT HONNÊTE POSÉ : l'assemblage final « g bijective » demande de réduire la
prémisse du ∀λ à « λ∈I » pour alimenter `extensionnalite_produit` (faire
entrer temoin_cofinal DANS le corps du quantificateur), puis de conjoindre les
deux sens. C'est un ajustement de FORME, pas un manque mathématique — les deux
sens sont prouvés.
**👑👑 PROP. 3 §III.7.2 — LA SURJECTIVITÉ EST DÉMONTRÉE (4 août ~07h25,
ev. 167)** : `prop1_proj/ensembles_prolongement_cofinal.py` livre les DEUX
pièces qui manquaient, et la Prop. 3 (canonique cofinale BIJECTIVE) n'a plus
de trou :
  • **prolongement_coherent ⊢ x̃_α = f_{αα'}(x̃_{α'})** (18 hyps honnêtes) — la
    famille prolongée x̃_α := f_{α,β(α)}(x_{β(α)}) satisfait la relation (1),
    donc **x̃ ∈ lim←_I** : l'antécédent existe ;
  • **prolongement_restitue ⊢ x̃_α = x_α pour α∈J** (2 hyps) — et il se projette
    bien sur le point de départ : **g(x̃) = x**.
Avec `prop3_g_injective_pointwise` (déjà au dépôt, 8 hyps), les deux sens de la
Prop. 3 sont acquis. Le tout **sans axiome du choix** : le majorant cofinal est
le témoin canonique τ (ev. 163), sa bonne définition est prouvée (ev. 165), et
les deux pièces d'aujourd'hui sont des assemblages de ces acquis.
115/115 iii_7_limites. **`porter_aux_termes` (ev. 166) a payé immédiatement** :
les deux preuves ne sont QUE des portages (bonne définition aux deux témoins,
cocycle au troisième indice + son point) suivis d'une composition — écrire
l'outil la veille a rendu ce tick presque mécanique.
**🔧 OUTIL : `porter_aux_termes` — LE MOTIF _cva_t RENDU AUTONOME (4 août
~07h05, ev. 166)** : `prop1_proj/ensembles_prolongement_cofinal.py` :
porter_aux_termes(thm, {nom: terme}) porte un théorème écrit AUX NOMS vers des
TERMES, en **découvrant lui-même** (via `libres_f`) les hypothèses qui portent
ces noms — il les décharge en antécédents, généralise, instancie, puis les
ré-assume substituées. C'est le motif noms→termes du projet (utilisé à la main
une dizaine de fois : _cva_t, _dval_t, _nt, membre_fibre_t…) transformé en
**une fonction générique et testée**. Vérifié sur le cas réel : la bonne
définition du prolongement portée aux deux témoins canoniques β(α), β(α′)
conserve exactement ses 13 hypothèses et change bien de conclusion. 113/113
iii_7_limites. Ce qui rendait le motif fastidieux — savoir QUELLES hypothèses
portent le nom — est désormais automatique.
**🔑 PROP. 3 : LE PROLONGEMENT EST BIEN DÉFINI (4 août ~06h50, ev. 165)** :
`prop1_proj/ensembles_prolongement_cofinal.py` : **prolongement_bien_defini ⊢
f_αβ(x_β) = f_αγ(x_γ)** (13 hyps honnêtes) — la valeur x̃_α := f_αβ(x_β) ne
dépend PAS du majorant cofinal β choisi. Preuve par le losange : les deux
branches passent par un majorant commun δ, chacune valant f_αδ(x_δ) via
relation (1) + cocycle LP_I. Avec le témoin canonique (ev. 163), les deux
ingrédients de la SURJECTIVITÉ de la Prop. 3 sont acquis : le choix (sans
axiome du choix) et sa bonne définition. Reste à assembler : montrer que la
famille x̃ ainsi définie satisfait elle-même la relation (1), donc appartient
à lim←_I, et que g l'envoie sur x. 112/112 iii_7_limites.
PIÈGE DU TICK : `cocycle_valeur_projectif` traîne des hypothèses de domaine
qui CONTIENNENT le point — les décharger en antécédents AVANT de généraliser
(motif _cva_t), sinon « xco libre dans une hypothèse ». Le helper écrit ici
(`_instancie_en`) détecte ces hypothèses par `libres_f` et les ré-assume après
instanciation : il est réutilisable pour toute brique à point nommé.
**📄 ARTICLE : DEUX DES QUATRE BLOCAGES LEVÉS (4 août ~06h30, ev. 164)** —
audit du dossier `article/` avant décision de publication. (1) **C8 réactualisé**
sur les **163 événements** du journal (il était consolidé sur 95) : deux
instances de non-repaiement neuves — la carte de reports périmée réparée par
un OUTIL (audit_reports.py) et l'hypothèse insatisfiable qui a déclenché un
audit systématique des 9 modules frères — plus **deux contre-exemples
honnêtes** : le même mur payé TROIS fois avant catalogage (une leçon ne
prévient le repaiement que si elle nomme la CLASSE de causes, pas le
symptôme) et la suite ralentie 4 h par un orphelin alors que la règle existait
déjà en mémoire (une règle n'agit que si elle est dans la checklist du geste).
(2) **La « passe systématique OBLIGATOIRE » de Related Work était FAITE**
depuis le 2 août (RELATED.md : 4 zones, 57 requêtes, 69 réfs triées, 33
menaces, 5 lues en entier) — l'ancre du .tex pointait vers un chemin
inexistant avec un compte périmé (16 réfs) : **c'est exactement le phénomène
des reports périmés du corpus, appliqué au papier**. Ancre corrigée, et la
vérification qu'elle promettait est désormais MÉCANIQUE :
`article/scripts/check_bib.py` — 47 citations ↔ 47 entrées .bib, aucune
orpheline des deux côtés, code de sortie exploitable en CI.
RESTE (côté Karl, non automatisable ici) : commiter + taguer, puis remplir les
trois placeholders de la page de titre (nom, email, URL+hash du dépôt).
**🔑 TÉMOIN COFINAL CANONIQUE (4 août ~05h55, ev. 163)** :
`prop1_proj/ensembles_temoin_cofinal.py` : β(α) := τ_y(y∈J et α≤y) et
**temoin_cofinal {J cofinale dans I, α∈I} ⊢ (β(α)∈J et α≤β(α))** — 2 hyps,
**sans axiome du choix**. C'est le chaînon qui manquait pour la SURJECTIVITÉ
de la Prop. 3 (§III.7.2) : prolonger un point de lim←_J à tout I demande de
choisir, pour chaque α, un majorant dans J — le τ de Bourbaki le fournit
uniformément (même motif que section_construite_par_tau E II.18 et que la
section de C57). Vert du 1er coup ; 111/111 iii_7_limites. La suite
(x_α := f_{α,β(α)}(x_{β(α)}) et sa cohérence) est maintenant la seule pièce
manquante de la surjectivité.
**👑 PROP. 2 §III.7.2, 1ʳᵉ ASSERTION DÉMONTRÉE (4 août ~05h40, ev. 162)** :
`prop1_proj/ensembles_prop2_fibres.py` : **fibres_systeme_projectif ⊢
f_αβ⟨M_β⟩ ⊂ M_α** — les fibres M_α=(u_α)⁻¹(x'_α) forment bien un système
projectif de parties — 8 hypothèses honnêtes {α,β∈I et α≤β ; x'∈lim← ;
diagramme commute_valeur_proj ; f_αβ, u_α, u_β fonctionnels et totaux}.
Preuve du livre telle quelle. Le report est retiré (il ne reste que la 2ᵉ
assertion, u⁻¹(x')=lim← M_α, qui exige le pont d'encodage famille-de-parties).
110/110 iii_7_limites. TROIS pièges vaincus dans ce seul théorème, tous
désormais catalogués : (1) collision de liants — objets nommés uf/ff/gg, pas
u/f/g, car u,v,z sont les liants de est_fonctionnel ; (2) paramètres BRUTS
pour limite_projective_relation_1 (var() en interne) ; (3) l'hypothèse de
domaine de C46 doit être déchargée AVANT l'élimination du témoin, sinon
« xw libre dans une hypothèse ».
**🔑 membre_fibre AUX TERMES + LE PIÈGE QUI BLOQUAIT (4 août ~05h20,
ev. 161)** : `membre_fibre_t` (relais noms→termes par décharge des hyps en
antécédents, motif _cva_t) — et surtout **la cause exacte du mur d'hier
soir est trouvée** : le terme passé ne doit contenir AUCUNE variable libre
nommée « u », « v » ou « z », **les liants de est_fonctionnel**. Une famille
notée u (u_indice(u,β) contient « u » libre) fait renommer le liant à la
substitution, et l'hypothèse ré-assumée ne s'apparie plus. MESURÉ : famille
« u » → ÉCHEC, famille « uf » → OK (2 hyps). Ce n'était donc ni la prémisse,
ni l'extraction, ni l'enveloppage : **une collision de liants classique**,
que trois diagnostics successifs avaient manquée. 109/109 iii_7_limites.
Les briques de la Prop. 2 sont désormais toutes disponibles AUX TERMES.
**🏁 SUITE COMPLÈTE VERTE : 3995 TESTS (4 août ~05h, ev. 160)** — la suite
INTÉGRALE du dépôt passe (`pytest tests/ -q`, 5 h 46 dont ~4 h de
ralentissement par un processus orphelin tué en cours de route). C'est la
certification globale de la nuit : Prop.6 intégrale, C57 gardé, décomposition
canonique bouclée, ponts, liants q/r, Prop.1 III.7.2, membre_fibre — **tout
tient à l'échelle du projet**, theorie==22. À relancer détaché après chaque
grosse session (compter ~2 h sans concurrence CPU).
**✅ VÉRIFICATION LARGE + SONDE DÉBLOQUANTE (4 août ~04h45, ev. 159)** :
**1311 tests verts** sur les chapitres I + II + IV (2 min) — tout le travail
de la nuit (décomposition canonique, C57 gardé, ponts, liants q/r) est validé
à large échelle. Et le mur de `fibres_systeme_projectif` est LEVÉ côté
diagnostic : **sonde verte** obtenue pour l'appariement de
`limite_projective_relation_1` — il faut lui passer les PARAMÈTRES BRUTS
(strings) pour Efam et f, car elle fait `var()` en interne et un Terme y
serait doublement enveloppé (piège déjà documenté dans
ensembles_limites_prop2_3_iii7:365-369) ; et **reconstruire** la prémisse
marche — c'est l'EXTRACTION depuis la conclusion qui échouait (impl=¬A∨B).
La sonde est recopiée dans le module : la reprise est immédiate.
**🎯 CHAÎNON DES FIBRES + REVERT HONNÊTE (4 août ~04h25, ev. 158)** :
`prop1_proj/ensembles_prop2_fibres.py` : **membre_fibre** {u fonctionnel, u
total} ⊢ (z ∈ u⁻¹⟨{b}⟩ ⇔ u(z)=b) — 2 hyps, le chaînon qui manquait au dépôt
pour passer de l'appartenance à une fibre à l'égalité des valeurs (grep
« fibre » ne donnait que les bergers de III.5). 108/108 iii_7_limites.
**REVERT** de `fibres_systeme_projectif` (1ʳᵉ assertion de la Prop. 2) : la
preuve du livre est claire et TOUTES les briques existent, mais mur
d'APPARIEMENT sur la prémisse de `limite_projective_relation_1` — ni
reconstruite, ni extraite (impl est encodée ¬A∨B ; même sous[0].sous[0]
échoue). Report honnête posé dans le module avec la route : **ne pas
reconstruire une prémisse — copier un usage RÉUSSI de la brique dans le
dépôt** (ensembles_limites_prop2_3_iii7 l'utilise déjà), exactement comme
pour les helpers privés de cone_unicite (ev. 152).
**👑👑 DÉCOMPOSITION CANONIQUE BOUCLÉE — LE PONT EST DÉMONTRÉ (4 août
~03h50, ev. 157)** : `ii_6_5_decomposition/ensembles_pont_theta.py` :
b_theta := **graphe_terme(Q, f(t), t)** — l'application déduite CONSTRUITE,
**sans section, sans caractérisation, sans axiome du choix** — et
**pont_au_point ⊢ b(θ(x)) = f(x)** (2 hyps), **pont_demontre ⊢ pont_valeurs_b**
(1 hyp : θ⟨E⟩⊂Q). Le PONT était l'HYPOTHÈSE de deux modules ; il devient un
THÉORÈME, d'où **b_construite_injective (1 hyp)** et **b_construite_surjective
(2 hyps)** : la bijection induite de la décomposition canonique f = i∘b∘p est
injective et surjective sans rien supposer d'autre que « les classes des
points de E sont dans Q ». 845/845 tests du chapitre II.
CLÉ (trouvée par la cartographie) : avec le codage classe-d'objets
θ(x)=τ_w(R_f{x,w}), **la classe est son propre représentant** (theta_temoin :
θ(x)∈E ET f(x)=f(θ(x))) — il suffit donc d'évaluer f EN LA CLASSE. Toute la
machinerie section/C57 était un détour.
DÉBLOCAGE TECHNIQUE : le raccord exige `N.alpha_tau` entre le liant « y » du
kit C54 et le liant de valeur des modules de décomposition — or ceux-ci
valaient « _vf »/« _vb », **refusés par alpha_tau (seules les LETTRES SIMPLES
sont α-valides : 'w' passe, 'vf'/'y2' non)**. Portés à « q »/« r » : 126 tests
ii_6 verts avant ET après, aucun changement mathématique. Leçon : choisir des
liants α-VALIDES dès l'écriture, sinon les termes du module deviennent
inconvertibles et le module s'isole du reste du projet.
**🚨 AUTO-CORRECTION MAJEURE : UNE HYPOTHÈSE INSATISFIABLE (4 août ~03h20,
ev. 155)** — trouvée par la cartographie parallèle (workflow 6 agents), puis
VÉRIFIÉE par moi. `hyp_quotient_caracterise` de mon C57 d'hier soir était
**NON GARDÉE** : « (∀x)(∀y)( p(x)=p(y) ⇔ R{x,y} ) ». Or hors du domaine,
p(x)=τy((x,y)∈p) porte sur une relation identiquement FAUSSE, donc **S7
identifie tous ces p(x) entre eux** : on a p(x)=p(y) sans R{x,y}. L'hypothèse
est donc INSATISFIABLE pour tout graphe p de domaine ≠ univers — et
c57_valeur_au_temoin, c57_application_deduite et factorisation_universelle
étaient **VACUEUX** (corrects sous leurs hypothèses, mais ces hypothèses ne
peuvent être satisfaites). Même famille de piège que l'incohérence de
l'intersection (26 juil) : une hypothèse « honnête » d'apparence, fausse en
réalité. **CORRIGÉ** : (a) la SECTION est gardée — s(t) := τz(z∈E ∧ t=p(z)),
ce qui fait tomber s(p(x))∈E du témoin lui-même (existe_temoin) ; (b) la
CARACTÉRISATION est gardée — (x∈E ∧ y∈E) ⇒ (p(x)=p(y) ⇔ R{x,y}) ; (c) les
deux gardes s'emboîtent exactement : celles de la caractérisation instanciée
sont x∈E (hypothèse) et s(p(x))∈E (fourni par le témoin gardé). Nouveaux
comptes : c57_valeur_au_temoin 3 hyps, c57_application_deduite 4,
factorisation_universelle 3, prop6_existence 8 (inchangé). 232/232 tests
(ii_6 + iii_7). **LEÇON** : un τ hors domaine n'est pas « un objet
quelconque » — c'est LE MÊME objet pour toutes les relations fausses (S7).
Toute hypothèse portant sur des valeurs doit être GARDÉE par le domaine.
**📋 CLAUDE.md REMIS À JOUR + TESTS IA VERTS (4 août ~02h50, ev. 154)** :
la section « Suivi de couverture » de CLAUDE.md (lue à CHAQUE session, donc
pilote réel) annonçait encore comme ouverts des chantiers FAITS depuis
longtemps — Hessenberg, division euclidienne, Cantor, CST1/CST2. Réécrite et
**vérifiée en code** : liste FAITS (Hessenberg, div. euclid., trichotomie,
Cantor, CST1/CST1-id/CST2/CST3/capstone, IV.1.5 réel, Prop. 6 intégrale, C57,
Prop. 1 III.7.2) vs OUVERTS (les 6 suspects de l'audit), + les DEUX outils à
relancer (gen_livre_manifestes, audit_reports) avec la consigne « tester en
code avant d'attaquer un report ». Par ailleurs : **93 tests outils_ia verts
en 5 min** — confirmation que la régression d'__init__.py (ev. 153) est bien
réparée. Un workflow de cartographie parallèle des 6 chantiers restants
tourne (6 agents : vérifier en code + lister les briques + estimer).
**🔧 OUTIL : AUDIT DES REPORTS PÉRIMÉS (4 août ~02h40, ev. 153)** :
`outils_ia/audit/audit_reports.py` — croise chaque entrée des listes REPORTES
avec les marqueurs @livre du dépôt et signale les **SUSPECTS** (un module
porte le même repère AVEC des définitions, et le texte n'annonce pas de
résolution). Verdict : **42 reports examinés, 6 suspects, 4 déjà annotés
résolus**. Motivation : QUATRE reports périmés trouvés à la main en 24 h
(Prop. 1 1°, Prop. 1 2°, Prop. 10 — ✅ celle-ci corrigée ce tick, elle était
prouvée dans iii_1_8_filtrants avec 3 hyps — et Prop. 6). Deux raffinements
appris en écrivant l'outil : (a) la **SECTION doit entrer dans la clé** (sans
elle « Prop. 5 » de §III.7.4 matchait celle de §III.1 : 12 faux positifs) ;
(b) un report déjà annoté « ✅ FAIT » n'est pas un suspect mais un RÉSOLU.
⚠️ RÉGRESSION ÉVITÉE : j'avais créé `tests/outils_ia/__init__.py`, ce qui
casse la résolution de `outils_ia.ia` pour les tests IA préexistants —
supprimé. Ne PAS ajouter d'__init__.py dans ce dossier de tests.
Les 6 suspects restants = les vrais chantiers ouverts de III.7 (Prop. 2, 3,
5, Th. 1) — la carte est maintenant pilotable et auto-vérifiable.
**🎯 PROP. 1 2° §III.7.2 — CRITÈRE D'INJECTIVITÉ PROJECTIF (4 août ~02h20,
ev. 152)** : `prop1_proj/ensembles_prop1_injectif.py` :
coordonnees_egales_points ⊢ **u(y) = u(z)** sous 6 hyps honnêtes {u∈𝓕(F;lim←),
relation (6), images-graphes, y∈F, z∈F, mêmes coordonnées} — la forme
CONTRAPOSÉE du 2° (« deux points de mêmes coordonnées ont même image »), qui
évite tout raisonnement par l'absurde ; l'injectivité de u donne alors y=z.
Assemblage transposé de cone_unicite (« deux applications en un point » →
« une application en deux points ») : coords_donnent_projections (CLOS) +
_lim_dans_produit + extensionnalite_produit. Report REPORTES corrigé.
Piège du tick : ces helpers attendent les paramètres BRUTS (noms), pas des
Termes pré-convertis — passer Efam/f/i tels quels. 106/106 iii_7_limites.
**§III.7.2 Prop. 1 : 1°-existence ✅, 1°-unicité ✅, 2° ✅.**
**🧹 CARTE CORRIGÉE : UN REPORT PÉRIMÉ DE PLUS (4 août ~02h, ev. 151)** :
le report « Prop. 1 1° UNICITÉ de u — REPORTÉ » de `ensembles_limites_iii7`
était **FAUX** : `ensembles_cone_unicite.cone_unicite` le prouve depuis
longtemps (4 hyps honnêtes, vérifié ce soir). Report réécrit + docstring du
module corrigée. C'est la N-ième illustration de la mémoire
« bourbaki-audit-verifier-en-code » : **greper le théorème EN CODE avant tout
effort** — j'allais réécrire un résultat déjà acquis. Reste réellement ouvert
en §III.7.2 : **Prop. 1 2°** (u injective ⇔ (∀y≠z)(∃α) u_α(y)≠u_α(z)).
ROUTE ÉCRITE (1 tick) : instancier `coords_donnent_projections` (CLOS,
généralisé sur z,z') aux points u(y), u(z) ; fournir l'appartenance au
PRODUIT via `_lim_dans_produit` (cone_unicite:260) ; conclure par
`extensionnalite_produit` ; puis l'injectivité de u donne y=z. Tous les
morceaux existent — c'est un assemblage, pas une découverte.
**🏁🏁 COUVERTURE PAGE-PAR-PAGE DU LIVRE : COMPLÈTE (4 août ~01h50, ev. 150)** :
`iii_7_limites/th1_proj/ensembles_th1_conditions.py` comble **E III.59**, qui
était le DERNIER trou de page du livre entier. Le manifeste dit désormais :
E I 14-46 complet · E II 1-48 complet · **E III 2-66, 87 complet** · E IV 1-26
complet · E R 3-32 complet — 2113 notions, 0 fichier à caler, 0 marqueur non
conforme. Contenu du module : les conditions (i) stabilité par intersections,
(ii) propriété d'intersection finie (écrite avec le SEUL prédicat de finitude
du projet, est_fini §III.4.1 — aucune hypothèse fantôme), (ii') forme
filtrante décroissante, (iii) fibres dans 𝔖_β, (iv) images dans 𝔖_α ; plus les
ÉNONCÉS cible_th1_a (relation (19)) et cible_th1_b — **preuves REPORTÉES et
déclarées** (liste REPORTES du module). ⚠️ HONNÊTETÉ : « couvert » = chaque
page du livre a ses notions formalisées ET marquées @livre ; cela ne veut PAS
dire que tout est démontré — les reports (Th.1 a/b, Prop.5, etc.) restent
listés. La carte est maintenant fiable pour piloter la suite : ce qui reste
n'est plus « des pages inconnues » mais « des reports nommés ».
**🎯 COR. 1 DE LA PROP. 6 (4 août ~01h20, ev. 149)** :
`prop6/ensembles_cor1_inductif.py` : cor1_relation_23 ⊢ **g_β(u_β(f_βα(x))) =
g_α(u_α(x))** (4 hyps : diagramme commutatif, relation (22) des canoniques,
u_α arrive dans F_α, prémisses d'étage) — c'est-à-dire : **la famille
(g_α∘u_α) vérifie (23)**, donc TOUTE la Prop. 6 (existence, unicité, 2°, 3°)
s'applique telle quelle et fournit l'unique u : E→F du corollaire. C'est
exactement la démonstration de Bourbaki (« on applique la prop. 6 à la
famille g_α∘u_α »). Vert du 1er coup ; 102/102 iii_7_limites.
**🎯 θ CARACTÉRISE R_f — LA RÉCIPROQUE (4 août ~01h, ev. 148)** :
`ii_6_5_decomposition/ensembles_theta_caracterise.py` : theta_temoin {x∈E} ⊢
R_f{x, θ(x)} (x est dans sa propre classe : R_f{x,x} vraie ⇒ (∃w) ⇒ le témoin
canonique τ_w la satisfait) et **theta_injectif {x∈E, y∈E, θ(x)=θ(y)} ⊢
f(x)=f(y)** — la RÉCIPROQUE du passage au quotient, qui manquait. Avec
passage_quotient_Rf (CLOS, sens facile), la caractérisation
« θ(x)=θ(y) ⇔ R_f{x,y} » est COMPLÈTE : c'est exactement l'hypothèse
« p caractérise R » de C57 pour la décomposition canonique. Vert du 1er coup ;
126/126 ii_6.
**🎯 FACTORISATION UNIVERSELLE (4 août ~00h30, ev. 147)** :
`ii_6_5_decomposition/ensembles_decomposition_c57.py` : (1)
compatible_avec_R_associee ⊢ f compatible avec R_f **[CLOS]** — tautologie
(R_f{x,y} contient déjà f(x)=f(y)), mais c'est ELLE qui rend la décomposition
canonique inconditionnelle ; (2) **factorisation_universelle** {p caractérise
R_f, p(x)∈Q} ⊢ H(p(x)) = f(x) — 2 hyps seulement : **toute application se
factorise à travers le quotient par la relation qu'elle induit**, avec H
CONSTRUIT. C'est le pont réclamé par ensembles_decomposition_effective
(b_injective_via_pont conditionnait l'injectivité de b à « b(Cl(x))=f(x) » —
désormais fourni). 124/124 ii_6.
**✅ C57 « ET UNE SEULE » (4 août ~00h10, ev. 146)** : c57_unicite ⊢
(∀t)(t∈Q ⇒ H(t)=H'(t)) sous {H factorise f, H' factorise f, p surjective} —
3 hyps honnêtes, du 1er coup. **Le critère C57 est désormais COMPLET
(existence + unicité)**, pour des graphes nus ; motif coincidence_sur_quotient
transposé. 122/122 ii_6.
**🏆🏆🏆 PROP. 6 §III.7.6 INTÉGRALEMENT FORMALISÉE (3 août ~22h30, ev. 145)** :
`prop6/ensembles_prop6_existence.py` : prop6_existence ⊢ **H(f_α(x)) = u_α(x)**
(8 hyps honnêtes) où H est le graphe CONSTRUIT par C57 — la relation (24) est
RÉALISÉE, plus aucun report. **TABLEAU COMPLET de la Prop. 6** : 1°-existence ✅
(ev. 145), 1°-unicité ✅ (138), 1°-compatibilité ✅ (141), 2° ✅ (139), 3° ✅ (140).
Un résultat entièrement REPORTÉ ce matin est aujourd'hui certifié de bout en
bout, ET son verrou amont (C57) est levé pour tout le projet. 223/223 tests
(iii_7_limites + ii_6). ⚠️ PIÈGE MAJEUR DÉCOUVERT — **« v » est un NOM RÉSERVÉ
du kit C54** (membre_graphe_terme l'utilise en dur pour la 2ᵉ composante du
couple) : un objet nommé « v » dans un terme passé au kit fait échouer la
décharge. Renommer (ici « vr »). À ajouter au playbook des collisions de
liants, avec « y » (obligatoire par défaut dès qu'un terme contient valeur).
**👑👑👑 C57 (II.6.5) COMPLET — L'APPLICATION DÉDUITE EXISTE (3 août ~22h,
ev. 143-144)** : `ii_6_5_decomposition/ensembles_c57_passage_quotient.py` :
**c57_application_deduite ⊢ H(p(x)) = f(x)** avec H := graphe_terme(Q,
f(τz(t=p(z))), t) — un graphe CONSTRUIT par le kit C54, 3 hyps honnêtes,
**SANS axiome du choix** (le τ de Bourbaki fait office de section canonique,
motif section_construite_par_tau E II.18). Deux étages : c57_valeur_au_temoin
⊢ f(s(p(x)))=f(x) (2 hyps : compatibilité + caractérisation du quotient),
puis emballage-graphe par relais noms→termes. **L'existence de l'application
déduite était REPORTÉE dans TOUT le projet** (application_deduite_quotient
le disait explicitement) — c'est levé ; le report y est réécrit (seule
l'UNICITÉ de h reste à écrire, motif coincidence_sur_quotient). 121/121 ii_6.
⚠️ AUTOCORRECTION IMPORTANTE : j'avais d'abord conclu à une « limite
structurelle du kit C54 avec les termes-valeur » — c'était FAUX. Le kit les
accepte ; le liant « y » doit simplement rester le DÉFAUT, car valeur(F,x)
EST τy((x,y)∈F) et l'existentielle de domaine (∃y)((u,y)∈F) doit matcher.
Leçon : avant de déclarer un mur structurel, tester le cas nominal.
**(section précédente conservée ci-dessous pour l'historique)**
**🎯 C57 (II.6.5) — LE CONTENU DU PASSAGE AU QUOTIENT (3 août ~21h40,
ev. 143)** : `ii_6_5_decomposition/ensembles_c57_passage_quotient.py` :
c57_valeur_au_temoin ⊢ **f( s(p(x)) ) = f(x)** avec s(t):=τz(t=p(z)), sous 2
hyps honnêtes {f compatible avec R, p caractérise R} — SANS axiome du choix
(le τ de Bourbaki suffit, motif section_construite_par_tau E II.18). C'est le
contenu mathématique du critère C57, jusqu'ici REPORTÉ dans tout le projet :
la valeur de f ne dépend que de la CLASSE et le témoin canonique la réalise ;
poser H(p(x)):=f(s(p(x))) donne l'application déduite AU POINT — ce qu'exigent
les consommateurs (Prop. 6 1°). **MUR TECHNIQUE IDENTIFIÉ ET DOCUMENTÉ** :
emballer H en GRAPHE via le kit C54 échoue car le terme f(s(t)) contient les
τ « y » de `valeur`, et `valeur_caracterisation` (C46) utilise « y » EN DUR —
deux issues possibles : variante y-paramétrée du kit C54, ou section définie
par appartenance ((z,t)∈P) au lieu de l'égalité t=p(z). 120/120 tests ii_6.
**👑👑 PROP. 6 §III.7.6 COMPLÈTE — MODULO LE SEUL C57 (3 août ~21h10,
ev. 142)** : `prop6/ensembles_prop6_assemblage.py` : relation_24_modulo_c57 ⊢
**h(f_α(x)) = u_α(x)** (la relation (24)) sous {v=h∘p, v coïncide, λ(x)=α,
α∈I, x∈E_α, x∈G + les 3 hyps de composition_valeur_t}, du 1er coup —
possible parce que f_α(x) EST littéralement valeur(p,x) (f_canon_ind =
application canonique de G sur G/R). **TABLEAU FINAL DE LA PROP. 6** :
1°-unicité ✅, 1°-compatibilité ✅ (démontrée), 1°-assemblage ✅, 2° ✅ (2 sens),
3° ✅ (2 sens) — **le SEUL manque est le critère C57 (E II.44), report du
CHAPITRE II** (« f compatible avec R ⇒ f = h∘p », existence de h = f∘s).
Autrement dit : le mur de la propriété universelle de la limite inductive
n'est pas en III.7, il est en II.6.5. REPORTES de limites_props2 réécrit en
conséquence. 101/101 iii_7_limites. **PROCHAINE CIBLE ÉVIDENTE : C57 lui-même**
(II.6.5) — il débloquerait d'un coup Prop.6 1°, et probablement Prop.1 1° et
d'autres passages au quotient du projet.
**🏆🏆 III.7 PROP.6 1° — LE CŒUR DE L'EXISTENCE DÉMONTRÉ (3 août ~20h45,
ev. 141)** : `prop6/ensembles_prop6_compatible.py` : compatible_v_coherence ⊢
**R{x,y} ⇒ v(x) = v(y)** (5 hyps honnêtes : (23) au point, v coïncide avec
u_{λ(x)} sur G, structure de la somme, x∈G, y∈G). C'est LA phrase de Bourbaki
« l'hypothèse entraîne que v est compatible avec la relation d'équivalence R »
— et elle est PROUVÉE, pas supposée, parce que
`relation_coherence_inductive` est une formule EXPLICITE (∃γ…) et non un
terme opaque : sous le témoin γ, v(x)=u_{λx}(x)=u_γ(f_{γλx}(x))=u_γ(f_{γλy}(y))
=u_{λy}(y)=v(y). Vert du 1er coup ; 100/100 iii_7_limites. **BILAN PROP.6 :
1°-unicité, 1°-compatibilité, 2°, 3° FAITS** ; ne reste que le passage au
quotient proprement dit (C57 : de la compatibilité, déduire u avec v=u∘f —
briques ii_6 application_deduite_quotient/c56_quotient_existe_ssi_pourtout).
LEÇON GÉNÉRALE DU BLOC III.7 : quand une notion est codée par une FORMULE
explicite (ici R) plutôt qu'un terme opaque, les « hypothèses » du livre
deviennent des théorèmes — vérifier ce statut AVANT de poser une hyp honnête.
**🏆 III.7 PROP.6 3° — CRITÈRE D'INJECTIVITÉ (3 août ~20h20, ev. 140)** :
`prop6/ensembles_prop6_injectif.py` : prop6_injectif ⊢ **(u injective ⇔
(∀α)(x,y∈E_α, u_α(x)=u_α(y) ⇒ (∃β≥α) f_βα(x)=f_βα(y)))** — LES DEUX SENS,
4 hyps honnêtes {(24), f_α⟨E_α⟩⊂E, **lemme 1 APPARIÉ** (deux éléments de E
s'écrivent f_α(x), f_α(y) au MÊME α — c'est LÀ que sert « I filtrant »),
lemme 2 (f_α(x)=f_α(y) ⇔ ∃β≥α …)}. Vert du 1er coup ; 99/99 iii_7_limites.
**BILAN PROP.6 : 1°-unicité + 2° + 3° FAITS** ; seule l'EXISTENCE du 1°
reste (recollement sur G=⊔E_α + passage au quotient). La leçon de fond : les
trois points « durs » du livre se réduisent à des hypothèses honnêtes bien
choisies (les deux lemmes 1/2, qui SONT le contenu « I filtrant + déf. de
R ») — isoler ces lemmes découpe la Prop. 6 en morceaux tous prouvables.
**🎯🎯 III.7 PROP.6 2° — L'ÉQUIVALENCE DE SURJECTIVITÉ (3 août ~20h, ev.
139)** : `prop6/ensembles_prop6_surjectif.py` : prop6_surjectif ⊢ **(u
surjective ⇔ F = ∪ u_α⟨E_α⟩)** — LES DEUX SENS — sous 3 hyps honnêtes {(24)
au point, lemme 1, f_α⟨E_α⟩⊂E}. ⇐ : témoin z:=f_α(x) ; ⇒ : lemme 1 sur le
témoin z + congruence. 98/98 iii_7_limites. Pièges du tick : (a)
congruence_terme a un trou NOMMÉ (kwarg w=, défaut « w ») — passer w="w6s"
quand le nom par défaut risque la capture ; (b) S5 emboîtés : le PREMIER
porte sur le corps NU (s5(corps, témoin, "xw")), le SECOND sur existe("xw",
corps) — pas sur la double existentielle ; (c) S6 donne une ÉQUIVALENCE,
congruence_terme donne l'ÉGALITÉ : composer_egalites exige la seconde.
**🎯 III.7 PROP.6 1° — « ET UNE SEULE » DÉMONTRÉ (3 août ~19h30, ev. 138,
1er tick Opus 5)** : `iii_7_limites/prop6/ensembles_prop6_unicite.py` :
prop6_unicite ⊢ **u = u'** sous 5 hyps honnêtes {(24) au point pour u, idem
pour u', lemme 1 « E=∪f_α⟨E_α⟩ », u∈𝓕(E;F), u'∈𝓕(E;F)} — le premier vrai
morceau de la propriété universelle de la limite inductive. Route =
`coincidence_sur_quotient` (C57) transposée : la surjectivité ponctuelle du
quotient devient le LEMME 1 (III p.62), posé en hypothèse honnête (c'est lui
qui fait de E une limite inductive) ; sous témoins (aw,xw) :
u(f_α(x))=u_α(x)=u'(f_α(x)) puis Leibniz z=f_α(x), puis extensionnalité
II.5.2. Vert du 1er coup ; 97/97 tests iii_7_limites (2,2 s). **REPORTES de
limites_props2.py CORRIGÉ** (l'unicité n'est plus reportée — honnêteté du
registre). Reste Prop.6 : 1° EXISTENCE (recollement sur G=⊔E_α + passage au
quotient — la machinerie ii_6 est repérée dans PASSATION_OPUS), 2° (surjectif
⇔ F=∪u_α⟨E_α⟩, canonique_ind_atteint aide), 3° (critère d'injectivité).
Lecture du livre : PDF = scan SANS couche texte ⇒ passer par V7 Texte.tex.
**👑 ÉQUIVALENCE COMPLÈTE (3 août ~18h15, ev. 137)** :
`cst3/ensembles_isomorphisme_compose_reel.py` : isomorphisme_compose_reel ⊢
**bij(⟨g∘f⟩^S, S(E), S(E'')) ∧ ⟨g∘f⟩^S(U)=W** (8 hyps honnêtes) — le composé
d'isos réels est un iso réel ET son graphe est lui-même une extension (CST1).
**L'ISOMORPHIE RÉELLE EST UNE ÉQUIVALENCE** : réflexive (ev. 136), symétrique
(ev. 135), transitive (ev. 137). Piège tué : composee_bijection_conjoints a
des internes noms-seulement ⇒ passer par la forme implicative CLOSE
composee_bijection aux noms Fc/Gc/Xc/Yc/Zc, gen ×5, instancier aux termes,
MP avec la conjonction des deux ponts. 69/69 cst_criteres (42 s).
**✅ AUTOMORPHISME-IDENTITÉ RÉEL (3 août ~17h55, ev. 136)** :
`cst3/ensembles_automorphisme_identite_reel.py` : automorphisme_identite_reel
{U∈S(E)} ⊢ bij(⟨Δ⟩^S) ∧ ⟨Δ⟩^S(U)=U (1 SEULE hyp — T5 clos + congruence
CST1-id + Δ(U)=U) ; sont_isomorphes_reel = l'existentielle par le témoin
⟨Δ⟩^S (réflexivité de l'isomorphie, réelle). 11/11 cst3. Le § IV.1.5 réel
est couvert : identité-automorphisme, auto-isomorphie, réversion d'iso.
**👑👑👑 RÉVERSION D'ISOMORPHISME RÉELLE (3 août ~17h40, ev. 135)** :
`cst3/ensembles_reciproque_iso_reel.py` : reciproque_isomorphisme_reel ⊢
**est_bijection_de((⟨f⟩^S)⁻¹, S(E'), S(E)) ∧ (⟨f⟩^S)⁻¹(V)=U** avec 6 hyps
honnêtes {Q(f_i), bornes CST1, U∈S(E), ⟨f⟩^S(U)=V} — la version réelle de
reciproque_isomorphisme_espece (IV.1.5) dont les 3 hyps explicites de
l'opaque (bij f⁻¹, CST3-appliqué) sont DÉRIVÉES, plus supposées. 4 briques
génériques base (tout G aux conjoints Q) : dom_reciproque_de_dom
{dom G=X}⊢dom(G⁻¹)=G⟨X⟩ ; image_reciproque_pleine {dom,img}⊢G⁻¹⟨Y⟩=X ;
injective_reciproque (u=G(G⁻¹u) via _recip_val, relais ub/wb) ;
bijection_reciproque (assemblage est_bijection_de(G⁻¹,Y,X)). Clause (4)
inverse = congruence CST3 ((⟨f⟩^S)⁻¹↦⟨f⁻¹⟩^S) + valeur_reciproque_identite.
66/66 tests cst_criteres, theorie==22. Toute la session verte du premier
coup sur les 3 derniers modules — la boîte à motifs est mûre.
**👑👑 DÉCHARGE VALEUR-NIVEAU FAITE (3 août ~17h15, ev. 134)** :
`valeur_reciproque_identite(s, fs, bases, bases_p, u)` ⊢
**⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U** (3-5 hyps honnêtes = Q(f_i) + bornes CST1 +
U∈S(E)) — LA 3ᵉ hypothèse de reciproque_isomorphisme_espece est dérivable.
Chaîne : composition_valeur_t (ses 3 hyps DÉCHARGÉES : U∈dom⟨f⟩ par Q-dom
[cst2], ⟨f⟩(U)∈dom⟨f⁻¹⟩ par Q-image + graphe_terme_domaine C54 CLOS sur le
top de ⟨f⁻¹⟩ [schéma non trivial exigé], func(∘) par transport S6 du
capstone sur func(Δ)) puis congruence-capstone puis Δ(U)=U (_dval_t). 7/7
tests cst3. Il ne reste pour le raccord complet des consommateurs iso que
l'assemblage fonction-sœur (mécanique : re-déclarer est_isomorphisme sur
les extensions réelles + conjonctions — niveau Opus).
**👑 CAPSTONE CST (3 août ~16h50, ev. 133 — dernier tick Fable)** :
`cst3/ensembles_cst3_corollaire.py` : (1) `composee_reciproque_diagonale`
{dom f=A, func f⁻¹} ⊢ **f⁻¹∘f = Δ_A** (base, 2 hyps ⊆ Q ; AXIOME_COMPOSEE α
p/r/y→pc/rc/yb — couple_reciproque interdit « p » —, univalence f⁻¹ force
pc=rc au sens →, témoin interne f(d0) au sens ←) ; (2)
`cst3_corollaire_identite(s, fs, bases, bases_p)` ⊢
**⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Δ_{S(E)}** = CST1(gs:=f⁻¹, sym) puis CONGRUENCE-FAMILLE
(trou = extension_canonique_reelle de la famille [Δ…, w, comp…] — le trou-
extension substitue TOUTES les occurrences d'un coup) puis CST1-identité.
Vert sur 𝔓E et 𝔓(E×E) ; hyps = Q(f_i) + bornes CST1, honnêtes listées.
63/63 tests cst_criteres, theorie==22. C'est LA 3ᵉ hypothèse de
reciproque_isomorphisme_espece (⟨f⁻¹⟩^S(⟨f⟩^S(U))=U s'obtient en appliquant
ce théorème à U — niveau valeur : composition_valeur_t ii_3_8:60 +
diagonale_valeur). Voir PASSATION_OPUS.md pour la suite exacte.
**🏆🏆🏆 CST3 GÉNÉRÉ — LA CAMPAGNE CST DU CH. IV EST COMPLÈTE (3 août
~16h10, ev. 132)** : sous-dossier `cst_criteres/cst3/` : (1) étage 𝔓
`reciproque_ext_parties` (4 hyps) via B2 avec G:=F⁻¹ — décharges par 2
briques GÉNÉRIQUES CLOSES `reciproque_est_graphe` (AXIOME_RECIP → est_couple,
motif S5 y,x) et `dom_reciproque_graphe` (dom(F⁻¹)=F⟨A⟩ par double extension,
témoins yb/xb α-renommés) + conjoints de Q (cst2) + hyp_valeurs par le
témoin-préimage ; (2) étage × `reciproque_produit_app` (8 hyps) — helper
`_recip_val` {p∈A'} ⊢ (f⁻¹(p)∈A ∧ f(f⁻¹(p))=p) (préimage pa α-renommée +
_valeur_de_couple sur f⁻¹ PUIS sur f) ; piège tué : T[wt] garde pr₁(wt) NON
réduit ⇒ projections aux TERMES (gen-inst de projection_premiere/seconde) +
2 congruences supplémentaires ; (3) `cst3_prouve(s, fs, bases, bases_p)` ⊢
reciproque(⟨f⟩^S) = ⟨f⁻¹⟩^S (extension des réciproques SUR LES BASES
D'ARRIVÉE) — récurrence à DOUBLE FIL (qs=Q comme cst2 + rs=réciproque avec
congruence-IH-dans-trou comme cst1), hyps résiduelles = EXACTEMENT les n
Q(f_i), vert sur 4 schémas dont 𝔓(𝔓(E×E)). 220/220 iv_structures (28 s),
theorie==22. **CST1 + CST1-id/T5 + CST2 + CST3 : FAITS.** Reste (prochain) :
raccord des consommateurs opaques (reciproque_isomorphisme_espece etc.,
motif fonction-sœur) — voir PASSATION_OPUS.md.
**🏆🏆 CST2 GÉNÉRÉ — LE CRITÈRE COMPLET (3 août ~15h10, ev. 131)** :
sous-dossier `cst_criteres/cst2/` (dossier parent était au CAP 10) :
(1) `ensembles_cst2_etage_produit.py` — produit_app_bijective_q, 8 hyps
honnêtes = Q(f)∖dom ∪ Q(g)∖dom ; func P⁻¹ par injectivité POINTWISE
(_inj_point : couple (p,f(p))∈f depuis dom → bascule couple_reciproque →
univalence f⁻¹) + _proj_forme (motif est_couple d'identite_produit) ; image
par valeur-dans-cible (→) et témoin (pa,qb) préimage par composante (←,
alpha_existe x→pa/qb pour ÉLIMINER 2 ∃ imbriqués de même liant) ; piège tué :
pr_dans interdit u=« x » (liants projections) ⇒ témoin α-renommé xa.
(2) `ensembles_cst2_genere.py` — cst2_prouve(s, fs, bases, bases_p) ⊢
Q(⟨f⟩^S_réel, S(E), S(E')) par récurrence, IH coupée conjoint par conjoint
(_q_conjoints) ; hyps résiduelles = EXACTEMENT les n Q(f_i) (l'hypothèse du
livre !) — vert sur 𝔓E(1), E₁×E₂(2), 𝔓(E×E)(1), 𝔓(𝔓(E×E))(1) ; +
pont_bijection_de : Q → est_bijection_de (E III.3.1) via injective_dans
dérivée de func F⁻¹ + dom (relais ub/wb→u/up). 57/57 tests cst_criteres,
theorie==22. **La TRILOGIE CST1 + CST1-id/T5 + CST2 est FAITE** ; restent
CST3 (réciprocité ⟨f⁻¹⟩^S = (⟨f⟩^S)⁻¹) et le raccord des consommateurs
opaques restants (reciproque_isomorphisme_espece etc.).
**🎯 CST2 ÉTAGE-𝔓 FAIT, 1er coup (3 août ~14h30, ev. 130 — TICK FINAL avant
pause quota)** : `cst_criteres/ensembles_cst2_briques.py` : invariant
Q(F,X,Y)=((func∧dom=X)∧(func F⁻¹∧F⟨X⟩=Y)) ; ext_parties_bijective_q(g,A,A',xi)
{func g, dom g=A, func g⁻¹, g⟨A⟩=A'} ⊢ Q(ext_P(g),𝔓A,𝔓A') — 4 hyps = Q(g)
moins dom, coupables par l'IH. Routes : injectivité via f⁻¹⟨f⟨·⟩⟩=Id
(image_reciproque_image_egal_si_injective, TERMES-antécédents !), surjectivité
via témoin g⁻¹⟨Z⟩ (inclus_domaine + image_image_reciproque_egal_si_surjective) ;
H_app dérivée de dom (helper _happ) ; α-discipline : relais Zq/uq/vq/zq AVANT
toute instanciation en z/x (liant d'inclus auto-rafraîchi = mine α). 53/53
tests dossier. RESTE CST2 : étage-× (pointwise-inj depuis func f⁻¹, valeurs
depuis couples — ~2 briques), générateur cst2_prouve (récurrence Q, cut IH),
pont Q→est_bijection_de (func F⁻¹+dom ⇒ injective_dans, ~25 l) ; dossier
cst_criteres à 10 entrées ⇒ ÉCLATER en sous-dossier au prochain ajout.
**🏆 T5 RÉEL FAIT — LE PREMIER CONSOMMATEUR CST DÉCHARGÉ (3 août ~13h50,
ev. 129)** : `cst_criteres/ensembles_echelon_identite_reelle.py` (~90 l) :
echelon_identite_bijection_reelle(s, bases) ⊢ est_bijection_de(⟨Δ⟩^S_réel,
S(E), S(E)) **CLOS (0 hyp)** sur 𝔓E, 𝔓(E×E), 𝔓(𝔓(E×E)) — les 2 hyps
explicites de l'opaque (transport_iso_props:286) TOMBENT : (1) bij(Δ_{S(E)})
— l'obstacle « S(E) est un terme composé » de l'opaque se dissout en
généralisant-instanciant les 4 paliers diagonale_* clos (noms→terme, _bij_
diagonale_t) ; (2) CST1-id ← cst1_identite_prouve (ev. 128). Décision pont
opaque↔réel : PAS de kwarg — fonction SŒUR (l'opaque reste pour ses
consommateurs, rien ne casse ; echelon() produit déjà les MÊMES termes réels
𝔓/×, seule l'extension différait). Du premier coup ; 210/210 iv_structures
(13,7 s), theorie==22. SUITE CST : CST2 (générateur bijectivité de ⟨f⟩^S si
f_i bijectives — B2/B3/F2 donnent déjà fonctionnel+domaine ; il faut
injectivité+image par étage) puis CST3 réciprocité.
**🏆🏆🏆 CST1-IDENTITÉ GÉNÉRÉ, CLOS — 0 HYPOTHÈSE (3 août ~13h30, ev. 128)** :
`cst_criteres/ensembles_cst1_identite.py` (~300 l) livre les 4 pièces de la
spec : (i) image_diagonale_sous {pt∈𝔓A}⊢Δ_A⟨pt⟩=pt (1 hyp honnête, extension
liant z via AXIOME_IMAGE+diagonale_membre) ; (ii) identite_parties
ext_P(Δ_A,A)=Δ_𝔓A **CLOS** ; (iii) identite_produit prod(Δ_A,Δ_B)=Δ_{A×B}
**CLOS** (est_couple(pw) ré-dérivé depuis AXIOME_PRODUIT — S5 q,p +
existe_elimination — puis couple_egal_projections + _valeur aux projections) ;
(iv) cst1_identite_prouve(s,bases) ⊢ ⟨Δ⟩^S_réel = Δ_{S(E)} **CLOS (0 hyp)**
sur 𝔓(E×E) ET 𝔓(𝔓(E×E)) — première famille CST entièrement SANS résidu.
48/48 tests cst_criteres verts (5,3 s), theorie==22. 3 pièges tués : (a)
_dval_t — diagonale_valeur PORTE une hyp ⇒ décharge en antécédent AVANT
généralisation (motif _cva_t), et instancier DANS L'ORDRE des ∀ (externe l'
abord — l'inversion donne « mineure ≠ antécédent ») ; (b) diagonale_graphe
(diagonale_bijection:46) est un CONSTRUCTEUR DE TERME graphe_terme(X,(x,x)),
PAS le théorème est_un_graphe(Δ_X) — la carte de la spec était fausse sur
cette case, brique dérivée sur place (_diag_est_graphe, AXIOME_DIAGONALE
∃d0 + S5 y,x + existe_elimination, CLOSE) ; (c) rien d'autre — (ii)-(iv) du
premier coup après ces deux fixes. RESTE : (v) T5 = brancher
echelon_identite_bijection (transport_iso_props:286) sur (iv) — pont
opaque↔réel, versions _reelles kwarg-gated.
**📐 SPEC GÉNÉRATEUR-IDENTITÉ (3 août ~11h50 — briques TOUTES localisées)** :
equipotence/ensembles_equipotence.py : diagonale_membre:53, _fonctionnelle:105,
_domaine:129, **_image:165 (Δ_X⟨X⟩=X PLEIN-ensemble seulement)**, _valeur:211
({u∈X}⊢Δ_X(u)=u), _injective:230 ; diagonale_graphe:46 (diagonale_bijection) ;
couple_egal_projections:227 (couple_caracterisation — z=(pr₁z,pr₂z) pour z
couple) — TOUTES noms-seulement (var(x)) ⇒ wrappers noms→termes aux stages.
À ÉCRIRE : (i) image_diagonale_sous_ensemble {X⊂A ou X∈𝔓A}⊢Δ_A⟨X⟩=X (~50 l,
membership y∈Δ_A⟨X⟩ ⇔ ∃x(x∈X ∧ (x,y)∈Δ_A) [AXIOME_IMAGE] + diagonale_membre
→ x=y — extension liant z ; pont X∈𝔓A→X⊂A via AXIOME_PARTIES) ; (ii)
identite_parties : ext_parties_reelle(Δ_A, A, xi) = Δ_𝔓A — B2 avec G:=Δ_𝔓A,
4 décharges {diagonale_graphe, _fonctionnelle, _domaine, hyp_valeurs ←
_valeur(𝔓A) + (i) + sym} → CLOS ; (iii) identite_produit :
produit_app_reelle(Δ_A, Δ_B, A, B, xi) = Δ_{A×B} — B2 avec G:=Δ_{A×B},
valeurs : Δ(pw)=pw [(_valeur A×B)] vs couple(Δ_A(pr₁pw), Δ_B(pr₂pw)) =
couple(pr₁pw, pr₂pw) [_valeur ×2 + pr_dans] = pw [couple_egal_projections
pour pw∈A×B : est_un_couple ← pr_dans-route ou produit-membre] → CLOS ;
(iv) cst1_identite_prouve(s, bases) : récurrence par étage (VARIABLE PAR
ÉTAGE xi !) : (0,b) refl ; (a,0) congruence-IH-dans-trou + (ii) ; (a,b)
2 congruences + (iii) → ⊢ ext-réelle(s,[Δ_{E_i}]) = Δ_{S(E)} attendu CLOS
(0 hyp !) ; (v) T5 : echelon_identite_bijection (transport_iso_props:286) —
décharger sa 2e hyp (CST1-id) par (iv) MODULO le pont opaque↔réel (les
consommateurs parlent en _transporte/extension_echelon OPAQUES → décision :
versions _reelles kwarg-gated des consommateurs, motif via_pont/via_reunion).
**🏆🏆 CST1 GÉNÉRÉ (3 août ~11h30, ev. 127) — LE MÉTATHÉORÈME DU CH. IV
RÉALISÉ** : cst1_termes_prouve(Schema) produit LE Theoreme noyau
⟨g∘f⟩^S = ⟨g⟩^S ∘ ⟨f⟩^S (extensions RÉELLES) par schéma concret, hyps honnêtes
listées — VERT sur 𝔓E (1 hyp), E₁×E₂ (4), 𝔓(E×E) (3), 𝔓(𝔓(E×E)) (4 étages,
récursion réelle), 5/5 tests, theorie==22. Dernier piège : les graphes
imbriqués partageaient xg → substitution externe corrompt les internes ⇒
**UNE VARIABLE-CONVENTION PAR ÉTAGE (xg1, xg2, …)** — complète la trilogie
convention-x (ev. 119) / relais-α (ev. 125) / variable-par-étage. + wrapper
_cva_t (noms→termes par décharge d'hyps en antécédents), assert set-égalité
(dédup a==b). RESTE DU CHANTIER CST : T5 (décharger axiome_CST1_* chez les
consommateurs : echelon_identite_bijection, CST3 — brancher les instances du
générateur + le pont extensions-réelles↔opaques OU re-déclarer les
consommateurs sur les réelles) + CST1-identité (générateur idem avec
diagonale_valeur + image_diagonale à écrire) + CST2 (bijectivité de ⟨f⟩^S si
les f_i bijectives — générateur analogue). Le plus dur est DERRIÈRE.
**🎯🎯 CST F2-TERMES FAIT (3 août ~10h50, ev. 126) — LES 2 CAS DE RÉCURRENCE
EN TERMES** : fonctorialite_produit_termes {est_application ×4} ⊢
(g×g')∘(f×f')=(g∘f)×(g'∘f') + pr_dans — 25/25 tests du dossier ii_3_6.
**B4 GÉNÉRATEUR (prochain tick)** : iv_2/cst_criteres/ensembles_cst1_genere.py
(vérifier CAP) — cst1_termes_prouve(s: Schema, fs, gs, bases, bases_p,
bases_pp) : récurrence Python sur s.couples construisant PAR STAGE l'égalité
⟨g∘f⟩-stage_i = composee(⟨g⟩-stage_i, ⟨f⟩-stage_i) : cas (0,b) → réflexivité
(composee(g_b,f_b) littéral) ; cas (a,0) → fonctorialite_parties_termes(stage-a)
PUIS réécrire l'IH-égalité DANS ext_P (congruence_terme sur l'argument) et
composer ; cas (a,b) → fonctorialite_produit_termes + IH×2 idem ; accumuler
les hyps (bornes/est_application par stage — les retourner listées) ; sonde
sur schema_relation() = ((0,1),(1,1),(2,0)) : E → E×E → 𝔓(E×E) (1 cas × sur
la base + 1 cas 𝔓). ⚠️ les stages composés : extension_canonique(s, [gi∘fi])
construit ext_P(prev-composé) — l'IH dit prev-composé = composee(...) →
congruence_terme(prev-composé, composee-prev, ext_P-ou-prod_hole(w)) pour
aligner PUIS la fonctorialité du stage. PUIS T5 : décharger axiome_CST1_*
(chap4_props_restantes:97/109) chez les consommateurs par les instances du
générateur + identités (reste : ident-termes ext_P(Δ)=Δ_𝔓 — après B4).
**🎯🎯 CST B3 FAIT (3 août ~10h20, ev. 125) — F1-TERMES SOUS 1 HYP** :
fonctorialite_parties_termes ⊢ ext_P(g∘f)=ext_P(g)∘ext_P(f) EN TERMES sous
{(∀pw)(pw∈𝔓A ⇒ image(f,pw)∈𝔓B)} SEULE — 5/5 tests. PIÈGE PROFOND résolu :
les termes-graphes portent xg LIBRE ⇒ élimination-xg de B2 bloquée quand G
contient des ext-graphes → **RELAIS-α xk** (caractérisation au binder frais +
ponts R⇔R_K 0-hyp s5+élim + composition d'équivalences + A1 au R-trivial
z∈G) — motif à retenir avec la convention-x. RESTE : **F2-termes** (même
squelette : produit_app_reelle(g∘f, gp∘fp, A, B) = composee(prod_g, prod_f)
— supports : composee_est_graphe ✓, composee_fonctionnelle+T1-prod-fonctionnels
✓, dom_composee_borne+graphe_terme_domaine(A×B) ✓, valeurs ← composition_
valeur_t + F2-val-machinerie (produit_app_valeur aux points + _pr_dans pour
les projections — les hyps est_application×4 de F2-val à porter ∀-closes)) ;
**identités-termes** (ext_P(Δ_A)=Δ_𝔓A : image_diagonale à écrire + B2 avec
G:=diagonale(𝔓A) — diagonale_valeur equipotence:211 ✓) ; **B4 générateur**
(récurrence Python sur Schema : cas 𝔓 = B3, cas × = F2-termes, base =
réflexivité ; les hyps ∀-closes s'accumulent par étage — retourner
(thm, hyps) ; sonde sur schema_relation()).
**✅ CST B3-SUPPORT FAIT (3 août ~09h55, ev. 124)** : composee_est_graphe CLOS
+ dom_composee_borne 2 hyps (ii_3_6/ensembles_composee_graphe_support.py),
verts du 1er coup. **B3-ASSEMBLAGE (prochain tick)** : fonctorialite_parties_
termes = egalite_graphe_terme(𝔓A, image(g∘f,xg), G:=composee(ext_g, ext_f))
avec les 4 décharges : (a) est_un_graphe ← composee_est_graphe CLOS ✓ ;
(b) est_fonctionnel ← MP(conj(T1-fonctionnels CLOS ×2), composee_fonctionnelle
implication-forme _tc termes ✓) ; (c) dom=𝔓A ← dom_composee_borne(ext_g, ext_f,
𝔓A) cut {dom ext_f=𝔓A ← graphe_terme_domaine (cantor:~105 CLOS — VÉRIFIER
signature/convention-x !), bornes-valeurs ← ∀-close honnête OU dérivée de
T1-valeur + image(f,X)∈𝔓B-borne} ; (d) hyp_valeurs ← F1-val ∀-clos (loi_deduction
2 hyps + generalisation Xf1 — le binder de hyp_valeurs est « pw » : ALIGNER
(F1-val au point pw OU α) ; l'hyp image(f,X)∈𝔓B reste ∀-close honnête ce tick).
Hyps finales attendues : ~2-3 ∀-closes structurelles. PUIS F2-termes (même
squelette) puis B4 générateur.
**🎯 CST B2 FAIT (3 août ~09h35, ev. 123) — L'EXTENSIONNALITÉ, CLEF DE VOÛTE** :
egalite_graphe_terme (ii_3_6/ensembles_graphe_terme_egalite.py) :
{est_un_graphe(G), fonctionnel(G), dom(G)=A, (∀pw)(pw∈A⇒G(pw)=T[pw])} ⊢
graphe_terme(A,T)=G — VERT DU 1ER COUP (~150 l), 3/3 tests. RESTE : **B3
F1/F2-TERMES** : ext_P(g∘f)=composee(ext_P g, ext_P f) = egalite_graphe_terme
appliqué à G:=composee(...) — il faut les 4 hyps pour LA COMPOSÉE : (1)
est_un_graphe(composée) [greper composee_est_graphe sinon écrire depuis
AXIOME_COMPOSEE] ; (2) est_fonctionnel(composée) ← composee_fonctionnelle
(ii_3_7, utilisé par composee_valeur_app ✓ existe) ; (3) dom(composée)=𝔓A
[greper dom_composee — sinon : dom(g∘f)⊇... exige image(f)⊂dom g — sous les
fonctionnels/dom des ext (T1 clos) + hyps de bornes] ; (4) valeurs ← F1-val
(ev. 120) MODULO la ∀-clôture (F1-val est au point Xf1 avec 2 hyps
d'appartenance-bornes : ∀-clore par loi_deduction+generalisation, la 2e hyp
image(f,X)∈𝔓B devra être DÉRIVÉE de X∈𝔓A + borne ∀-close image(f,A)⊂B —
lemme image-monotone à greper) ; PUIS B4 générateur.
**✅ CST B1 FAIT (3 août ~09h15, ev. 122)** : graphe_terme_est_graphe CLOS
(fonction_terme) — la forme-z de C54 était DÉJÀ l'axiome déposé (abrege:977,
∀w !) : pas de théorie set à construire. Pièges : liants ∃ canoniques
(ré-intro S5 aux témoins) ; **existe_elimination et NON monotonie_existe**
(qui enveloppe aussi la conclusion). PROCHAIN : B2 extensionnalité —
graphe_terme(A,T) = G pour G fonctionnel de domaine A et valeurs T[·]
(z-formes des deux côtés + A1/egalite_par_extension ; côté G : est_un_graphe(G)
en HYP + valeur_caracterisation ; graphe_terme_domaine EXISTE cantor:~105) ;
puis B3 F1-termes (G := composee(ext_g, ext_f) : est_graphe de composée à
greper/écrire, dom_composee à greper) ; B4 générateur.
**🧩 TROU DE CONCEPTION T3 DÉTECTÉ (3 août ~08h55) — LE PONT TERMES EST LE
CHEMIN CRITIQUE.** La récurrence du générateur CST1 doit RÉÉCRIRE l'IH DANS
l'argument d'ext_parties_reelle(ARG,·) (stage i+1 consomme le TERME du stage i) :
l'IH en forme VALEUR ne se substitue pas sous graphe_terme — il faut l'égalité
de TERMES ⟨g∘f⟩-stage = composee(⟨g⟩,⟨f⟩)-stage. ⇒ ROUTE CORRIGÉE (ordre) :
**(B1) FORME-Z de graphe_terme** (motif axiome_h_graphe RODÉ : théorie dédiée
theorie_graphe_terme_set avec z∈F ⇔ ∃u∃v(z=(u,v) ∧ corps-couple) qui ENTRAÎNE
la forme couple-only existante — conservatif ; puis graphe_terme_est_graphe
z∈F⇒z couple) ; **(B2) extensionnalité** : deux graphes fonctionnels de même
domaine et valeurs ∀-égales sont =-égaux (forme-z + AXIOME_DOM + A1 — motif
f|seg=p|seg de la factorielle) ; **(B3) F1/F2 niveau TERMES** : ext_P(g∘f) =
composee(ext_P g, ext_P f) par B2 + F1-val + dom_composee (dom(ext∘ext)=𝔓A à
établir : dom_composee brique à greper) ; **(B4) T3-générateur** en récurrence
sur Schema avec IH-termes (S6/congruence directes dans les stages) ; identités
(diagonale_valeur equipotence:211 EXISTE ✓ + image_diagonale à écrire) et
_pr_dans en chemin. Modules : frère iv_1/ensembles_extension_echelon_identites.py
(iv_1 à 8 entrées ✓ ; reelle à 287 l plein).
**✅✅ CST T2 F2-val FAIT (3 août ~08h45, ev. 121) — LE CAS × DE CST1 DÉRIVÉ** :
fonctorialite_produit_valeur, 8 hyps structurelles honnêtes (U∈A×B, 2 projections,
Kpt∈Ap×Bp, 4 est_application), vert du 1er coup, 8/8 tests module. LES DEUX
FONCTORIALITÉS DE CST1 SONT PRISES en forme valeur. RESTE T2 : identités-val
(lemme image(Δ_A,X)=X à écrire — image_diagonale n'existe pas — + l'analogue
produit) ; helper _pr_dans ({u∈A×B}⊢pr₁u∈A ∧ pr₂u∈B) pour décharger les
hyps-projections ; PUIS T3 : générateur cst1_composition_prouve (récurrence
Python sur Schema : cas base=réflexivité/composee directe, cas 𝔓=F1-val, cas
×=F2-val — produit des égalités de VALEURS ∀-closes par schéma concret).
**✅ CST T2 F1-val FAIT (3 août ~08h30, ev. 120) — LE CAS 𝔓 DE CST1 DÉRIVÉ** :
fonctorialite_parties_valeur {X∈𝔓A, f⟨X⟩∈𝔓B} ⊢ ⟨g∘f⟩(X)=⟨g⟩(⟨f⟩(X)), vert du
1er coup, 7/7 tests. Chaîne : T1-valeur ×3 points (dont le POINT-TERME
image(f,X) via _au_point) + image_composee CLOS + S6 au 2e arg de valeur.
RESTE T2 : F2-val (cas × : composee_valeur_app ii_3_8:170 aux points pr₁/pr₂
du couple — hyps est_application×4 attendues) + identités-val (image_diagonale
N'EXISTE PAS → lemme image(Δ_A,X)=X à écrire OU reporter) ; puis T3 générateur.
**⚠️🔧 T1 RÉPARÉ — PIÈGE DE FIDÉLITÉ C54 DÉCOUVERT ET CORRIGÉ (3 août ~08h15,
ev. 119) : LA CONVENTION-x DE graphe_terme.** Le terme graphe_terme(A,T) =
app(A,T) n'encode PAS sa variable ; l'axiome C54 (theorie_graphe_terme dédiée)
est paramétré par (A,T,**x**) — deux x différents sur le MÊME terme mintent
DEUX AXIOMES INCOMPATIBLES (lecture constante vs variable = le motif exact de
l'incohérence de l'intersection). Mon T1 initial MÉLANGEAIT (valeur en x="x"
constant, fonctionnel en x=xg) — réparé : **convention UNIQUE x=xg partout**.
2 pièges d'exécution en plus : (a) le POINT doit différer de la variable
(u≠x requis par C54 → point diagonal « pcs ») ; (b) membre_graphe_terme
n'accepte que des NOMS (famille coupe_membre) → helper `_au_point` (loi de
déduction → généralisation → instanciation → re-assume) qui transporte la
caractérisation à un POINT-TERME arbitraire — testé au point Y (test
discriminant de la lecture variable) et prêt pour F1 (point = image(f,X)).
6/6 verts. RÈGLE NEUVE : sur tout graphe_terme, UNE SEULE convention-x par
terme dans TOUT le code — auditer les callers existants de graphe_terme_valeur
à l'occasion (cantor/prop4 utilisent les défauts cohérents, OK présumé).
**🔧 CST T2 — MESURES + DÉCISION (3 août ~07h55)** : PAS de brique
« égalité de graphes fonctionnels » générique ; membre_graphe_terme
(fonction_terme:10) ⊢ ((u,v)∈F)⇔(u∈A ∧ v=T[u]) = caractérisation PAR COUPLES
seulement — l'égalité de TERMES-graphes exigerait la forme-z (z∈F ⇒ z couple),
même chantier que h_est_graphe (set-form). composee_valeur_app EXISTE
(ii_3_8/ensembles_composee_valeurs:170). DÉCISION : **T2 livré en FORME
VALEUR** (le repli prévu au plan) : F1-val {X∈𝔓A, bornes image} ⊢
ext(g∘f)(X)=ext(g)(ext(f)(X)) via T1-valeur + image_composee (ii_3_3:70) +
composee_valeur_app ; F2-val idem couples/pr ; identités-val
ext(Δ_A)(X)=X (image(Δ_A,X)=X — greper image_diagonale) ; le générateur T3
produira des égalités de VALEURS ∀-closes par schéma ; le PONT vers l'égalité
de termes (exigée par les formes CST1-opaques des consommateurs) = tick
ultérieur via la forme-z de graphe_terme (motif axiome_h_graphe : théorie
dédiée forme-SET si nécessaire — PAS dans theorie_ensembles). ⚠️ design F1-val :
appliquer T1-valeur de ext(g,B) au point image(f,X) exige image(f,X)∈𝔓B ⇒
hyp structurelle (image(f,A)⊂B ou f⊂A×B) — les prendre ∀-closes honnêtes
comme les données d'iso de la trichotomie.
**✅ CST T1 SONDÉ VERT + MODULE ÉCRIT (3 août ~07h40)** : le verrou-τ de juillet
NE MORD PAS sur les valeurs image/couple — graphe_terme_valeur ET
graphe_terme_fonctionnel passent au LIANT FRAIS « xg » (le rouge initial au
liant « u » = collision avec les liants canoniques {u,v,z} d'est_fonctionnel,
PAS le verrou-τ). F1 réel DÉJÀ CLOS : image_composee (ii_3_3 composee:70,
⊢ (G'∘G)⟨A⟩=G'⟨G⟨A⟩⟩). Module posé : iv_1_structures_isomorphismes/
ensembles_extension_echelon_reelle.py (ext_parties_reelle + produit_app_reelle
via graphe_terme, fonctionnel CLOS 0-hyp, valeur 1-hyp) + test miroir — suite
en cours. NOTE : l'écart n°86 (produit binaire de fonctions) tombe en réel.
RESTE : T2 (F1/F2 niveau APPLICATIONS : ext(g∘f)=ext(g)∘ext(f) — égalité de
GRAPHES via extensionnalité + valeurs ; identités ext(Δ_A)=Δ_𝔓A…), T3
générateur, T4 identité, T5 re-branchement.
**📐 PLAN CST COMPLET (3 août ~07h50 — mesure faite, especes_echelon.py LU en entier).**
Schémas = objets Python MÉTA (dataclass Schema, tuple de couples ; constructeurs
schema_base/parties/produit/relation ; construction_echelon/echelon =
récurrence méta → Termes réels via E.parties/E.produit ✓). MAIS
extension_canonique récurse sur DEUX BRIQUES OPAQUES : ext_parties(g) =
app("ext_parties",g) et produit_applications(g,h) = app("produit_app",g,h) —
LE mur récurrent de juillet (cf. mémoire frontière : « objets terme-définis
OPAQUES »). CST1 (⟨g∘f⟩^S = ⟨g⟩^S∘⟨f⟩^S) exige leur fonctorialité, indémontrable
sur l'opaque. ROUTE (multi-tick) : **T1** constructions RÉELLES via graphe_terme
(C54, infra CLOSE per mémoire tick 35) : ext_parties_reelle(g,A) :=
graphe_terme(𝔓A, image(g,u), u) ; produit_app_reelle(g,h,A,B) := graphe_terme(
A×B, couple(g(pr₁u), h(pr₂u)), u) + leurs caractérisations de valeur
(graphe_terme_valeur — ⚠️ verrou-τ de juillet était SPÉCIFIQUE aux valeurs
Card-valuées ; images/couples devraient passer — SONDER T1 en premier) ;
**T2** fonctorialités : F1 ext_parties(g∘f)=ext_parties(g)∘ext_parties(f)
(niveau réel = image(g∘f,X)=image(g,image(f,X)) — GREPER si image_composee
existe déjà clos) ; F2 produit_app(g∘f,h∘k)=produit_app(g,h)∘produit_app(f,k) ;
+ identités : ext_parties(Δ_A)=Δ_𝔓A, produit_app(Δ_A,Δ_B)=Δ_{A×B} ;
**T3** générateur méta cst1_composition_prouve(s, fs, gs, bases) : récurrence
Python sur s.couples, cas base=réflexivité, cas 𝔓=F1+congruence, cas ×=F2+
congruence — retourne un Theoreme noyau PAR SCHÉMA CONCRET (métathéorème façon
projet, JAMAIS de Theoreme du schéma général) ; **T4** cst1_identite_prouve
idem ; **T5** re-brancher extension_canonique (kwarg via_reel) + les
consommateurs (echelon_identite_bijection transport_iso_props:286, CST3) et
DÉCHARGER leurs hypothèses CST1 explicites. Gains : toute la pile transport
ch. IV + l'écart n°86 (produit binaire de fonctions) tombe en passant.
**🧭 PROCHAIN MUR CHOISI (3 août ~06h20) : IV CST1/CST2 EN GÉNÉRATEUR DE PREUVES.**
Mesures : III.7 = 6 REPORTÉS (props2:386-398 : cône universel Prop.1 1°, lim de u
Cor.1/Prop.6, Prop.3/8 bijectivité canonique, Prop.5 récurrence dénombrable,
Th.1b intersection finie) — chacun exige une INFRA neuve ⇒ diffus, plus tard.
IV CST1 (chap4_props_restantes:97/109) = hypothèses explicites dont la preuve est
« récurrence sur le schéma S » ⇒ **c'est un MÉTATHÉORÈME au sens du projet
(bourbaki-metatheoremes-vs-theoremes) : écrire un GÉNÉRATEUR Python récursif sur
la STRUCTURE du schéma d'échelon qui produit, pour CHAQUE schéma concret S, le
Theoreme noyau ⟨g∘f⟩^S(U)=⟨g⟩^S(⟨f⟩^S(U)) et ⟨Δ_E⟩^S(U)=U** — jamais un Theoreme
du schéma-en-général. Débloque : CST3 (réciprocité), echelon_identite_bijection
(transport_iso_props:286) et toute la pile transport ch. IV bâtie dessus.
PREMIÈRE ÉTAPE (prochain tick) : goal-grep la REPRÉSENTATION des schémas
(_transporte, echelon, constructeurs produit/parties — iv_1/iv_2) + lire
ensembles_especes:25 (« CST1-CST7 reportés ») + vérifier si un générateur
partiel existe déjà (règle des 5 cartes !).
**🏆🏆🏆 THÉORÈME 2 (HESSENBERG, E III.48) FAIT (3 août ~06h05, ev. 116) —
a²=a, CONCLUSION E-SEULE : `hessenberg_a_carre_egal_a_REEL(E)` ⊢
est_infini(Card E) ⇒ Card E·Card E = Card E, sous 4 RÉSIDUS ∀-clos TÉMOINS-
LIBRES : {principe_recurrence (C61), cardinal_pas_entre, 𝔉≠∅,
m_dans_frame_universel}. LE CLAIM Card S₀=Card E EST DÉRIVÉ (STEP B CLOS).**
Le mur architectural somme-disjointe (classé « IRRÉDUCTIBLE » par le blocker
mécanique) est tombé par le re-câblage RÉUNION : 11 sondes vertes en cascade
(L1-L5, L-inf, L4, B1', B2, B4 en 3+3 rounds). B4 = derive-callback d'unpack :
pièges finaux résolus : (i) maximal_hyp d'unpack porte sur mmx, pas (S,φ) →
re-assume du corps (même formule = même hypothèse, déchargée par la loi de
déduction d'unpack) + transport S6 (hole h6m) ; (ii) l'égalité mmx=(S,φ) est à
3× elim_gauche. Tests miroirs posés (test_extension_z_infini,
test_hessenberg_stepb3, test_REEL) — suite en cours. Chaîne du jour :
carte goal-first → comparabilité découverte close → retourne complement_grand
→ B2 ; les deux fils de la campagne se sont rejoints.
**🎯 B2 VERT (3 août ~05h45) — ¬(𝔟 < Card E) sous 7 hyps TOUTES Ucadre-LIBRES,
theorie==22 — L'ÉLIMINATION DE UCADRE A ABOUTI** (3 rounds : maximal_carre_egal
2-args→pont bien_defini ; assert mal placé avant la décharge du corps ; vert).
Hyps de B2 : {2 résidus ∀∀ (principe_recurrence C61, cardinal_pas_entre), bij₀,
element_maximal, (S₀,φ₀)∈𝔉, S₀⊂E, est_infini_ensemble(S₀)} = exactement la
conception. B4 écrit dans vrai_final (hessenberg_a_carre_egal_a_REEL : derive-
callback aux noms FRAIS Smx/phimx → B2(Sn,phin) + B3 (partie_inf_egal_card+
_pont+card_S0_egal_card_E) + endgame + coupes par les théorèmes du dépliage →
unpack_maximal) — sonde en cours.
**⏳ B2 ÉCRIT (3 août ~05h25) — stepb3.py negation_strict_sous_maximal_reunion,
sonde en cours** (~230 l : corps assumé → 9 décharges (d1-d9 selon la table,
rewrites S6 img/dom via congruence_terme+composer, d9 par absurde fini_zero) →
assert 0 hyp-Ucadre → élimination → amont h_lt→complement_grand (cuts h_SE,
𝔟+𝔟=𝔟←_deux_b(trio))→comparabilité généralisée-instanciée (X,Y)→cas/s2→
transport→alpha_existe VE→Ucadre→MP→contraposition+dni). Points fragiles
attendus si rouge : forme du trio-antécédent de deux_b (nesting et), forme de
fini_zero (Fini(Card∅) vs Fini(zero)), a_implique_a exporté de tactiques_abrege ?,
maximal_carre_egal signature/hyps, byte-alignements des rewrites.
**✅ L4 VERT (3 août ~00h05) — Card(F_r)=𝔟, 5 hyps** (la sonde a mis ~25 min :
machinerie somme-équipotence lourde, PAS pendue — patience). KIT COMPLET VERT :
L1-L5 + L-inf + L4 + B1'-réunion. **ANATOMIE COMPLÈTE DE B2 (stepb3, ~170 l,
à écrire fenêtre fraîche)** — negation_strict_sous_maximal_reunion() :
AMONT : h_lt=assume(inf_strict_card(𝔟, Card E)) ; cg=complement_grand (coeur/
ensembles_hessenberg_extension:119, {S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<CardE} ⊢ ¬(Card(E∖S₀)≤𝔟))
— couper S₀⊂E (maximal-data), 𝔟+𝔟=𝔟 ← deux_b_egal_b_inconditionnel
(descentes_inconditionnelles:329, trio standard), 𝔟<CardE=h_lt ;
**comparabilite_cardinaux (ordre_cardinaux:1415, CLOS 0 hyp — LA CASCADE de la
carte goal-first !)** instancié _tt4-défauts ["X","Y"]→(𝔟, Card(E∖S₀)) →
disj_syll avec ¬(c≤b) → 𝔟≤Card(E∖S₀) ; transport (realisation_segment/
ensembles_transport_sous_ensemble:76, {est_cardinal(c) ∧ c≤Card A} ⇒
∃V(V⊂A ∧ Card V=c), 0 hyp) avec est_cardinal(𝔟) (brique à greper dans
definitions_cardinaux : cardinal_est_cardinal / _cardinal_est_son_cardinal_t
prop13:98) → ∃VE(corps) → α-rename ∃VE→∃Ucadre (alpha_existe, motif B1 l.222).
AVAL (les décharges avant élimination) : partir de B1'(via_reunion=True) ;
PELER bij(φ₀,S₀²,S₀) (hyp maximal-data) → img0=(image(φ₀,S₀²)=S₀),
dom0=(dom φ₀=S₀²) ; S6-rewrite les hyps (1),(2),(5) [imgφ₀→S₀ via img0∘dom0 :
attention la forme est image(phi0, dom(phi0)) — composer dom0 puis img0] ;
décharger : (1)←inter_vide_depuis_disjonction(S₀,U)+corps ; (2)←réflexivité ;
(3)←s0sq ; (4)←L4+corps(Card U=𝔟 sym) ; (5)←L5 ; (7)←Z⊂E dérivée du corps
U⊂E∖S₀+S₀⊂E ; (8)←z_infini_derive ; (9) Card U≠Card∅ ← corps + fini_zero
(iii_4_1 ensembles_fini_zero:161) + est_infini(S₀) (si Card U=Card∅ alors
Card S₀=0 fini, contradiction — route ex falso marqueur) ; RESTE {U⊂E∖S₀,
Card U=Card S₀} = LE CORPS ⇒ loi_deduction(et(...)) selon la forme EXACTE du
corps du transport (vérifier : et(V⊂A, Card V=c) — ordre des conjoints !) ;
existe_elimination("Ucadre") ; MP → marqueur [maximal-data, h_lt, résidus ∀∀] ;
contraposition+dni(E=E) → **¬(𝔟<Card E) sous maximal-data + résidus Ucadre-libres**.
PUIS B3 : card_S0_egal_card_E (extension_finale:643, {𝔟≤𝔞, ¬(𝔟<𝔞)} ⊢ 𝔟=𝔞) —
𝔟≤𝔞 ← inf_egal_card_de_inclus_terme(S₀,E) (clause_plus_petit_monotonie:90) +
S₀⊂E ; B4 : brancher dans unpack_maximal (vrai_final:70) comme
hessenberg_vrai:191 mais avec Card S₀=Card E DÉRIVÉ → conclusion E-seule ==
enonce_hessenberg(E). Tests : stepb3 + réunion kwargs n'ont PAS cassé les
consommateurs (kwargs defaults False) — suite hessenberg complète à lancer à
la fin (17+ min, détachée).
**✅ B1'-RÉUNION VERT (2 août ~15h55) — 12 hyps, 9 Ucadre, FORMES MESURÉES + ROUTES B2** :
(1) inter(imgφ₀,U)=∅ → S6-rewrite imgφ₀→S₀ (img0 maximal-data) → inter(S₀,U)=∅
← inter_vide_depuis_disjonction ; (2) reunion(imgφ₀,U)=Z → rewrite → S₀∪U=Z
RÉFLEXIVITÉ ; (3) S₀²∪F_r=Z² ← **s0sq CLOS byte-visible** ✓ ; (4) τZ=τZ =
Card F_r=Card U ← L4 (Card F_r=𝔟) + Card U=𝔟 (corps, symétrisé) + composer ;
(5) (∀u)¬(u∈domφ₀ ∧ u∈F_r) → rewrite domφ₀→S₀² (dom0) → L5
carre_disjoint_cadre_reunion ; (6) U⊂E∖S₀ = CORPS, survit ; (7) Z⊂E ← U⊂E∖S₀
+ S₀⊂E (maximal-data frame) ; (8) ¬(∃X)τZ = Z-INFINI ← z_infini_derive ✓ ;
(9) ¬(τZ…) = **Card U ≠ Card ∅** (l'hyp d'U_non_vide) ← Card U=Card S₀ +
Card S₀≠0 (S₀ infini, maximal-data — brique à greper : infini⇒≠0 ou
cardinal_zero/deux_inf_egal). PIÈGE réparé : B1 hard-codait le F tagué à 2
endroits (_psi_free_residuals:135 + corps:202) → helper _cadre(via_reunion).
B2 = fonction suivante (~150 l) : peler maximal-data (img0/dom0 pour les
rewrites S6), décharger 1-9, existe_elimination("Ucadre") via
existe_sous_ensemble_cardinal_transporte (grep son corps exact + où il vit).
**⏳ KWARGS POSÉS (2 août ~15h45)** : cadre_ensemble_reunion + via_reunion dans
phi_etendue (:345), phi1 (chaine_vraie:64/84-91), les 4 wrappers _chainee
(9 substitutions scriptées), B0 (stepb:72) et B1 (stepb2:178). L4 v3 en sonde
(pièges rencontrés : eq_somme_invariant/equipotence_transitive α-NOMINALES —
casse même en noms exotiques, marche SEULEMENT aux noms PAR DÉFAUT → wrapper
_tt4 généraliser-les-défauts-puis-instancier). Sonde B1'-réunion lancée en
parallèle (compte des hyps-Ucadre attendu ≤ 9, formes réunion).
**✅ L-inf FAIT (2 août ~15h30) — z_infini_derive VERT, 3 hyps Ucadre-LIBRES**
(frame_zorn/ensembles_extension_z_infini.py : {est_infini_ensemble(S₀) +
2 résidus ∀∀ fini_downward_thm} ⊢ est_infini_ensemble(S₀∪U) ; l'α-identité
fini_downward_thm↔H de cor1 a TENU ; assert anti-Ucadre intégré). 7/7 sondes
vertes sur le chantier réunion.
**L4 — CONCEPTION RACCOURCIE (à exécuter)** : NE PAS re-dériver les cardinaux —
composer Eq(F_r, F⊔) puis Card(F_r)=Card(F⊔)=𝔟 par le cadre_card_trois_b EXISTANT :
(a) helper _impl_forme_de_negconj : (∀u)¬(P∧Q) → (∀u)(P⇒¬Q) SANS ex falso
(contraposition(loi_deduction(Q, conj_intro)) — 8 lignes) pour nourrir
inter_vide_depuis_disjonction depuis les sorties ¬∧ de produits_disjoints ;
(b) bridge1 : Eq(UxS∪UxU, UxS⊔UxU) ← _eq_reunion_disjointe_somme_t
(VÉRIFIER la forme de son antécédent : inter=∅ ou ∀ ?) sous UxS∩UxU=∅
(← produits_disjoints_seconde(U,U,S,U) flip + (a) + inter_vide) ; (c) congruence
Eq à travers ⊔ : GREPER eq_somme_invariant (cité dans _somme_disjointe_cardinal_t,
prop13:130) pour lifter bridge1 sous SxU⊔· ; (d) bridge2 : Eq(F_r, SxU⊔inner_r)
sous SxU∩inner_r=∅ (← L1×2 + L3-∀ + (a) + inter_vide) ; (e) composer Eq
(transitivité _eq via prop13 helpers) → Eq(F_r, F⊔) → _prop1_direct_tt →
Card F_r = Card F⊔ ; (f) composer_egalites avec cadre_card_trois_b (extension_
finale:155, hyps {CardS=CardU, bb=b, card b, inf b}) → Card F_r = 𝔟. Hyps L4
attendues : les 4 du cadre + (∀z)(z∈U⇒¬z∈S). Où : ensembles_extension_z_infini.py
(le module des dérivations-réunion, ~110 l actuellement).
**✅ L1-L5 FAITS (2 août ~15h20, ev. 114) — 5/5 VERTS, theorie==22** :
entiers_cardinaux/ensembles_produits_disjoints.py + test miroir. L1/L2 (1 hyp),
L3-∀ (2 hyps), L3-= inter(A,B)=∅ (1 hyp), **L5 carre_disjoint_cadre_reunion
(1 hyp : (∀z)(z∈U⇒¬z∈S)) = LA décharge de l'hyp 12 de B0**. La route ¬-intro
(ex falso marqueur ¬(A=A) → contraposition → dni) MARCHE ; motif _renomme_ex2
(témoins ∃∃ frais en 2 étages S5+monotonie_existe). Pièges rencontrés :
E.intersection (pas E.inter) ; egalite_par_extension EXIGE le liant canonique
« z » (A1) — séparer liant-extension et liant-hypothèse. RESTE : L-inf, L4,
kwargs, B2-B4 (specs ci-dessous inchangées).
**ROUTE ¬-INTRO POUR L1/L2/L5 (2 août ~15h10)** : cible (∀u)¬P avec P=et(u∈A×C,
u∈B×D). Sous Hu=assume(P) : u∈A×C → equivalence_avant(AXIOME_PRODUIT instancié
(A,C,u)) → ∃p∃q(et(et(u=(p,q), p∈A), q∈C)) [liants natifs p,q → témoins FRAIS
via renommage S5-exotique si besoin, motif ev.109] ; idem B×D (p2,q2) ;
egal((p1,q1),(p2,q2)) par composer_egalites(symetrie+…) →
couple_egal_implique_composantes (ii_2_1 ensembles_couples:112, ⊢ ((x,y)=(x',y'))
⇒ (x=x' et y=y')) → p1=p2 ; D instancié p1 → ¬(p1∈B) ; p2∈B + p1=p2 → s6 →
p1∈B ; EX FALSO s2 vers le MARQUEUR ¬(A=A) (motif _marqueur_faux stepb2:63) ;
existe_eliminations (témoins hors du marqueur) → ⊢ P ⇒ ¬(A=A) [sous D] ;
**contraposition (tactiques_abrege2:45)** → ¬¬(A=A) ⇒ ¬P ; il faut ¬¬(A=A) ←
réflexivité + tactique A⇒¬¬A : GREPER « non_non\|double_negation » dans
i_2/i_3 tactiques (existe sûrement, sinon dériver de s2/s3/s4). Puis
generalisation(u). L2 : même route, p-côté → q-côté (2de coord). L5 = L1(S₀²
vs U×S₀) + L2(S₀² vs S₀×U) + L1-ou-L2(S₀² vs U×U) + L3-∀ (réunion : u∈Y∪Z →
AXIOME_REUNION → cas ; chaque cas contredit ; ou-élimination — greper
« def ou_elimination\|disjonction_elim » tactiques).
**INGRÉDIENTS L-inf VÉRIFIÉS (2 août ~15h05)** : hyp 6 = est_infini_ensemble(Z)
= non(est_fini(cardinal(Z))) construite extension_finale:396 ; hyp 1 =
inclus(Z,E) :395. `fini_downward_thm` (recurrence_C61.py:430) est DÉRIVÉ :
{principe_recurrence(P), (∀c)(∀b)cardinal_pas_entre(b,c)} ⊢ (∀a)(∀x)((a≤x ∧
Fini x)⇒Fini a) — ses 2 résidus sont ∀∀-clos et **Ucadre-LIBRES** ⇒ ils
survivent à l'élimination SANS la bloquer (« Th.2 CLOS modulo C61-résidus »
honnête, à re-mesurer : C61/cardinal_pas_entre ont peut-être été clos en
juillet — grep avant). L-inf = {est_infini_ensemble(S₀) [maximal-data ? vérifier
la forme du corps frame : est_infini_ensemble ou est_infini(Card·)],
S₀⊂Z [_inclusion_reunion_gauche_t chaine_vraie:143 existe !], Card S₀≤Card Z
[BRIQUE À LOCALISER : « partie ⇒ Card ≤ » — grep def.*inf_egal dans
ordre_cardinaux/cardinaux_bornes/parties_equipotentes ; elle existe forcément
(arith cardinale l'utilise partout)]} + fini_downward_thm instancié (Card S₀,
Card Z) + contraposition (s2/s3) ⇒ non(Fini(Card Z)) ← non(Fini(Card S₀)).
**🎯 TABLE DE DÉCHARGE DÉFINITIVE (2 août ~14h55 — inventaire sonde B0, 12 hyps,
formes EXACTES imprimées ; AUCUN MUR RÉEL sous réunion)** :
| # | hyp B0 (forme sonde) | sort sous réunion |
|---|---|---|
| 1 | (∀z)(z∈S₀∪U ⇒ z∈E) | DÉRIVER ← U⊂E∖S₀ + S₀⊂E (maximal-data) |
| 2 | (∀z)(z∈U ⇒ z∈E∖S₀) | = CORPS du transport, SURVIT (support de l'élim) |
| 3 | (S₀,φ₀)∈𝔉 | maximal-data, Ucadre-FREE, survit |
| 4 | element_maximal(Γ𝔉,𝔉,(S₀,φ₀)) | maximal-data, Ucadre-FREE, survit |
| 5 | S₀²∪cadre⊔=Z² (l'ex-MUR) | MEURT ← s0sq CLOS (byte-ok si F:=réunion) |
| 6 | ¬(∃X)(τZ…)=… = **Z INFINI** (est_infini_ensemble, encodage Fini/τ) | MEURT ←
L-inf : est_infini(S₀) [maximal-data] + S₀⊂Z + monotonie Card + contraposée
fini_downward (N_collectivise) — la chaîne le documente ELLE-MÊME
(chaine_vraie:159 « dérivables de … S₀⊂Z+S₀ infini ») |
| 7 | imgφ₀∪imgψ=Z | ψ-free (B1) → S₀∪U=Z = RÉFLEXIVITÉ (Z littéral) |
| 8 | bij(ψ, cadre, U) | ∃-éliminée via cadre_bijection ← L4 Card F_r=Card U |
| 9 | bij(φ₀,S₀²,S₀) | maximal-data, Ucadre-free, survit |
| 10 | uwit∈U | témoin, éliminé en B1 ✓ (déjà fait) |
| 11 | imgφ₀∩imgψ=∅ | ψ-free → inter(S₀,U)=∅ ← U⊂E∖S₀ (forme ÉGALITÉ-∅ :
egalite_par_extension + AXIOME_VIDE) |
| 12 | (∀u)¬(u∈domφ₀ ∧ u∈domψ) | ψ-free → (∀u)¬(u∈S₀² ∧ u∈F_r) ← L5-∀
(L1 1re coord : S₀²vs U×S₀/U×U ; L2 2de coord : S₀² vs S₀×U ; L3-∀ réunion) |
Post-B2 : {corps transport (2 + Card U=Card S₀), maximal-data (3,4,9)} ⇒
existe_elimination(Ucadre) LICITE via existe_sous_ensemble_cardinal_transporte
⇒ B3 (card_S0_egal_card_E:643, {≤, ¬<} — le ¬< vient de la décharge du falsum) ⇒
B4 unpack_maximal. LEMMES : L1/L2/L3-∀/L3-=/L5 (nouveau module entiers_cardinaux/
ensembles_produits_disjoints.py) ; L-inf (où : infinis_descentes si CAP) ; L4
(calquer cadre_card_trois_b:155-265 avec ponts prop13). NOTE : lire
extension_dans_frame (extension_finale:373-427) pour la forme EXACTE du « Z
infini » (hyp 6) et de « Z⊂E » (hyp 1) telles que construites.
**CERTITUDES FINALES (2 août ~14h45, lecture chaîne complète)** : (a) le kwarg
via_reunion dans phi_etendue_bijection = UNE LIGNE (extension_finale:331 :
`Fcadre = cadre_ensemble_reunion(S,U) if via_reunion else cadre_ensemble(S,U)`) —
F n'apparaît QUE dans le GAP-A dom (dom_reunion_egale_cible(φ₀,ψ,S₀²,Fcadre,Z²),
hyps {dom φ₀=S₀², dom ψ=F, S₀²∪F=Z²}) ; le reste (fonctionnalité/injectivité/
image) est F-libre ; (b) Z = reunion(S,U) LITTÉRAL (chaine_vraie:130,
extension_finale:308) ⇒ le résidu S₀∪U=Z est une RÉFLEXIVITÉ ; φ₁=reunion(φ₀,ψ)
déjà réunion ; (c) cadre_bijection(F,U) prend F EN PARAMÈTRE (une seule hyp
Card F=Card U) ⇒ marche telle quelle avec F_reunion une fois L4 fait ; (d)
phi1_bijection_derivee:83+89 : passer F_reunion aux DEUX endroits (F local +
bijp assume) via kwarg ; steps 2-5 (dans_frame:154, ordre:178, force_egalite:214,
absurde:253) sont F-AGNOSTIQUES (consomment les steps précédents) — kwarg
pass-through ; (e) RESTE UNE INCONNUE : les 2 hyps ¬(∃X) non-extension naissent
dans extension_force_egalite (extension_finale §4c l.521-643, dépliage
element_maximal) — LIRE §4c AU PROCHAIN TICK avant d'écrire ; sous réunion elles
peuvent changer de statut (le blocker les classait MUR sous l'architecture
taguée) ; (f) les formes de disjonction dans phi_etendue sont : dom-disj =
(∀u)¬(u∈dom φ₀ ∧ u∈dom ψ) [∀-FORME] et img-disj = inter(...)=∅ [ÉGALITÉ] —
L1/L2/L3/L5 devront produire LES DEUX formes selon le résidu visé ; (g) où poser :
entiers_cardinaux à 6 entrées ✓ nouveau module ensembles_produits_disjoints.py
(produit_union_carre 346 l, plein).
**SPEC FINALE DU RE-CÂBLAGE (2 août ~14h35 — briques toutes identifiées)** :
ponts CLOS prêts : `eq_reunion_disjointe_somme(A,B)` : (A∩B=∅)⇒Eq(A∪B,A⊔B) +
wrapper capture-safe `_eq_reunion_disjointe_somme_t` (prop13_complement:155) ;
`_prop1_direct_tt` (Eq⇒Card=) ; `_somme_disjointe_cardinal_t` (:126) ;
`trois_b_egal_b_inconditionnel` ; s0sq (produit_union_carre:315, MÊME imbrication
que F_reunion := reunion(S×U, reunion(U×S, U×U)) ✓) ; dom/image recollement
réunion : dom_reunion_egale_cible:70 + image_reunion_egale_cible:109
(recollement/ensembles_dom_image_reunion.py). Chaîne à kwarguer (chaine_vraie
293 l) : phi1_bijection_derivee:64 (F=cadre_ensemble à l.83, résidus S₀²∪F=Z²/
S₀²∩F=∅/S₀∪U=Z/S₀∩U=∅) → dans_frame:154 → ordre:178 → force_egalite:214 →
absurde:253 → B0 (stepb:72, décharge U∩S₀=∅←U⊂E∖S₀ via U_disjoint_S0) → B1
(stepb2:178) → B2. **LEMMES À ÉCRIRE (dans l'ordre, sondes après chacun)** :
L1 produits_disjoints_1re : {A∩B=∅} ⊢ (A×C)∩(B×D)=∅ (1re coord ; membership :
z∈inter → z=(p,q) AXIOME_PRODUIT ×2 → p∈A∩B absurde) ; L2 variante 2de coord
{C∩D=∅} ; L3 inter_reunion_vide : {X∩Y=∅, X∩Z=∅} ⊢ X∩(Y∪Z)=∅ ; L4
cadre_card_trois_b_reunion : {CardS=CardU, 𝔟²=𝔟, card 𝔟, inf 𝔟, S∩U=∅} ⊢
Card(F_reunion)=𝔟 (2 ponts Eq+somme_cardinale puis trois_b, calquer
cadre_card_trois_b:155) ; L5 S₀²∩F_reunion=∅ ← L1/L2/L3 sous S∩U=∅ ; L6 =
dom/image de φ₁ réunion ← briques recollement EXISTANTES. PUIS variantes kwarg
via_reunion de la chaîne (les résidus géométriques deviennent : S₀²∪F=Z² ←
s0sq CLOS ; S₀²∩F=∅ ← L5 ; S₀∪U=Z réflexivité si Z:=reunion(S,U) littéral (À
VÉRIFIER dans phi_etendue:283 — Z terme ou variable ?) ; S₀∩U=∅ ← U⊂E∖S₀) ;
B0'/B1' ; B2 élim Ucadre (TOUTES les hyps-Ucadre devront dériver du corps
U⊂E∖S₀ ∧ Card U=Card S₀) ; B3 ; B4. Où poser L1-L3 : produit_union_carre.py
(vérifier lignes/CAP) ou entiers_cardinaux nouveau fichier si CAP le permet.
**ORDRE D'EXÉCUTION (prochain tick, pattern kwarg-gated « via_pont » : ne JAMAIS
casser les consommateurs — ajouter la variante réunion À CÔTÉ)** :
(i) lire frame_zorn/ensembles_frame_extension_finale.py EN ENTIER (cadre_ensemble,
phi_etendue_bijection, cadre_bijection, cadre_card_trois_b, card_S0_egal_card_E:643
— hyps exactes) ; (ii) écrire cadre_ensemble_reunion := reunion(S₀,U) + les
variantes réunion de phi_etendue/cadre_bijection (les 4 hyps-mur deviennent :
S₀²∪F_reunion=Z² ← s0sq CLOS ; dom-disj ← U⊂E∖S₀ (disjonction par différence) ;
les 2 ¬(∃X) à re-mesurer sur la forme réunion) ; (iii) B0'/B1' sur le cadre
réunion (mêmes chaînes, sondes détachées) ; (iv) B2 : décharger les 5 + les 4,
existe_elimination("Ucadre") ; (v) B3 : Card S₀=Card E via trichotomie/negation ;
(vi) B4 : unpack_maximal → hessenberg_a_carre_egal_a_REEL, conclusion E-seule ==
enonce_hessenberg(E). ⚠️ tests hessenberg = 13-18 min, TOUJOURS détachés.
**🗺️ CARTE GOAL-FIRST (2 août, ev. 112) — verdicts sourcés des 5 « gros chantiers ».**
Fan-out Explore (lecture seule, docstrings + tests miroirs), 2 SURPRISES 5-cartes :
1. **Comparabilité des cardinaux (a≤b ou b≤a) : FAIT-CLOS, 0 hyp** —
   ordre_cardinaux/ensembles_comparabilite.py:1415 `comparabilite_cardinaux`,
   Zorn sur les injections partielles (PAS la trichotomie §III.2) ; test asserte
   est_clos ET len(hyps)==0. (Seul point : @livre calé §3.2 Cor.1, E III.25.)
2. **Cantor 2^𝔞>𝔞 niveau CARDINAUX : FAIT-CLOS, 0 hyp** — prop12_card/_cantor.py:205
   `cantor_deux_exp` (« CLOS, 0 hyp ; theorie=22 ») + Card(𝔓X)=2^Card X
   (_bijection.py:311). ⚠️ dette : prop12_fin.py garde un stub NotImplementedError
   TROMPEUR (superseded par prop12_card/) — à nettoyer/documenter.
3. **Hessenberg a²=a : PARTIEL, 1 hyp** — assemblage_vrai/ensembles_hessenberg_vrai_final.py:191
   `hessenberg_vrai` : {Card S₀=Card E} ⊢ infini(Card E) ⇒ Card E·Card E=Card E.
   Le CLAIM = STEP B entier (dériver Card S₀=Card E dans la portée du maximal,
   chaîne extension/contradiction, ~12 hyps honnêtes internes avant
   existe_elimination) ; STEP A (unpack_maximal:70) CLOS = point d'attache prêt.
   + résidus amont frame_a_maximal (𝔉≠∅, m_dans_frame_universel) à re-mesurer.
4. **IV CST1/CST2 : OUVERT monolithique** — posés en HYPOTHÈSES explicites
   (cst_criteres/ensembles_chap4_props_restantes.py:97,109), preuve = récurrence
   sur le schéma d'échelon, MÉTA, reportée ; tout le chap. IV bâti au-dessus attend.
5. **III.7 limites : PARTIEL DIFFUS (le plus loin)** — Prop.6/7/9/10 + Th.1 b)
   ABSENTS (= la page E III.59 manquante, vérifiée au PDF : démo Th.1 §7,
   Σ inductif + Zorn 1°-4°) ; l'existant = sens faciles pointwise ; liste REPORTES
   dans ensembles_limites_props2.py.
**CHOIX DU PROCHAIN MUR : HESSENBERG STEP B** (critère : théorème NOMMÉ du livre
le plus proche de clôture — 1 hyp, point d'attache clos, chantier cerné non diffus).
**⚡ COUP DE THÉÂTRE (2 août, ev. 111) — TH.3 ÉTAIT DÉJÀ CLOS DEPUIS LE 20 JUILLET.**
`trichotomie_ordinaux_canon_close_v3` (h_coherences/ensembles_h_est_graphe.py,
daté 20 juil., **20 tests verts re-vérifiés ce jour, 12 min 10**) ⊢ Th.3 sous
**{bo(R,E), bo(Rp,F)} — LA PRÉMISSE PROPRE DU LIVRE, 0 résidu** — via l'axiome
SET fidèle (theorie_h_graphe : z∈h ⇔ ∃a∃b(z=(a,b) ∧ corps), S8-légitime,
conservatif : il ENTRAÎNE l'axiome couple-only déposé). JAMAIS JOURNALISÉ : ni
CAMPAGNE_DEMOS, ni events.jsonl (0/110), ni les docstrings d'assemble («le plus
serré = 5-6 hyps», FAUX depuis 13 jours), ni la mémoire. **CAS MAJEUR de la règle
des 5 cartes : le grep d'ouverture d'un chantier doit viser LE BUT (le théorème
final), pas seulement le mur courant — et TOUS les dossiers du théorème (v3
vivait dans h_coherences, pas assemblage).** Valeur RÉELLE du travail du jour
(routes complémentaires, non redondantes) : les 2 segments dom/img sont CLOS
sous l'axiome couple-only FAIBLE (v2/v3 les obtiennent seulement sous la forme
SET) ; min3/min4 montrent exactement ce que l'axiome faible achète ({bo,bo,max}
et {bo,bo,h⊂dom×img}) ; val_dans_F/temoin_dans_S mortes = carte assemble propre ;
motifs neufs (S6 double-trou, renommage ∃-témoin S5-exotique). OPTION non prise
(gold-plating) : min5 = min4 + h_graphe déchargée par h_est_graphe ⇒ 2e route
{bo,bo} sous forme SET — redondant avec v3, documenté ici seulement.
**🎯🎯🎯🎯 SUR-TICK (2 août, ev. 110) — MIN4 : LA MAXIMALITÉ ELLE-MÊME DÉRIVÉE.**
`trichotomie_ordinaux_canon_prouve_min4` (assemble) ⊢ Th.3 sous **{bo(R,E),
bo(Rp,F), h_graphe_hyp}** — sonde verte du 1er coup (4/4 aujourd'hui). Mesure-clé :
les hyps de `maximalite_donne_trichotomie_close` = {bo, bo, seg_dom[x,y],
seg_img[x,y], h_graphe} et les DEUX segments sont désormais les théorèmes CLOS
des ponts ⇒ close déchargée (α xx/ww→x/y côté dom, re-liant ta/ua→x/y côté img)
donne la disjonction sous {bo,bo,h_graphe}, qui décharge la maximalité de min3.
L'ULTIME hypothèse non-honnête du Th.3 = h_graphe_hyp (h ⊂ dom h × pr₂h,
structure du τ-h que l'axiome couple-only n'expose pas). PROCHAIN MUR unique :
dériver h_graphe du scaffold (re-carter l'axiome opaque de h_iso_max — attention
règle des 5 cartes, « NON extractible » date d'avant les ponts). Tests :
+test_min4_maximalite_dechargee (assemble). Suite 4 fichiers : 34 verts (16 min 50) ;
dom seul : 6 verts.
**🎯🎯🎯 TICK CLOS (2 août) — TH.3 TRICHOTOMIE AUX HYPOTHÈSES DU LIVRE : 3 HYPS**
`trichotomie_ordinaux_canon_prouve_min3` ⊢ Th.3 sous **{bo(R,E), bo(Rp,F),
maximalité (dom h=E ou pr₂h=F)}** — val_dans_F ET temoin_dans_S MORTES, les DEUX
segments (dom ET img) sont des THÉORÈMES CLOS (0 hyp), theorie==22, sondes vertes
du premier coup (les 3). Il ne reste à décharger QUE la maximalité (= Zorn).
Pièces : (a) `temoin_surjectif_dans_S` (pont_val, 10 hyps) = extraction complète
iso→bijective→surjective(φ⟨S⟩=T)→transport S6 (trou côté ensemble)→AXIOME_IMAGE→
témoin RENOMMÉ x→qim (S5 exotique + élim sur x, car x PRIS libre dans t=φ(x))→
couple_donne_valeur (§C46)+func φ→φ(qim)=u ; qim∈E par S⊂E instancié ; (b) img
via_pont : coupes des 8 conjoints pelés du coeur ⇒ `img_h_est_segment_prouve`
CLOS ; (c) min3 (img_segment) : maillon+3 → décharge seg_dom[x,w] par
`_dom_segment_aux_binders(via_pont=True)` (α-renommage xx/ww→x/w INCHANGÉ) puis
seg_img[x,w] par la preuve re-liée ta/ua→(x,w). Tests : +test_temoin_surjectif
(pont_val), +test_img_h_est_segment_prouve, +test_trichotomie_min3 (asserts
val_dans_F/temoin_dans_S ∉ hyps). MOTIFS neufs : transport S6 à trou
d'appartenance des DEUX côtés (élément puis ensemble) ; renommage ∃-témoin
S5-exotique quand le liant natif de l'axiome est PRIS par une variable libre du
séquent. DETTE lignes : pont_val ~330, img_segment ~390 (>300, dossier au CAP —
éclatement à planifier au prochain passage III.2).
**(i) ✅ FAIT (~13h05)** : kwarg via_pont + dom_h_initial_prouve/dom_h_est_segment_prouve —
**est_segment(dom h, R, E) CLOS, 0 hypothèse, sonde verte** — val_dans_F MORTE côté dom.
**(ii) CHAÎNE COMPLÈTE MESURÉE** : est_surjective(f,a,b) = egal(image(f,a), b) (abrege:352,
forme IMAGE-ÉGALITÉ) ; est_isomorphisme_ordre = et(est_bijective, compatible_ordre)
(ordre_vocab:175) ⇒ est_surjective(φ,S,T) = elim_droite(elim_gauche(Hiso)). EXTRACTION
dans via_pont d'img_h_initial : (1) u∈T : valeur_iso_dans_T(témoin x) → φ(x)∈T ; Ht_eq
t=φ(x) symétrisée + s6 → t∈T ; initialité de T (conjoint droit Hseg_T instancié (t,u),
prémisse (t∈T ∧ u∈F ∧ Rp{u,t})) → u∈T ; (2) u∈φ⟨S⟩ : est_surjective → φ⟨S⟩=T, symétrie,
s6 (trou z∈w) → u∈φ⟨S⟩ ; (3) ∃-témoin : AXIOME_IMAGE instancié (⚠️ GREP sa forme exacte
+ liant natif) → ∃x(x∈S ∧ (x,u)∈φ)-forme → elim témoin p → p∈S, (p,u)∈φ ;
(4) φ(p)=u : couple_donne_valeur (⚠️ GREP signature/hyps — vu dans c62 restriction) +
Hfunc ; (5) p∈E : conjoint gauche Hseg_S (S⊂E) instancié p. → le corps de temoin_dans_S
DÉRIVÉ ⇒ img_h_initial_prouve/img_h_est_segment_prouve CLOS ⇒ temoin_dans_S MORTE.
Puis (iii) min3 {bo,bo,maximalité} : refaire les décharges de la chaîne _min aux versions
_prouve (relire _dom_segment_aux_binders l.134 d'assemble pour le α-renommage aux binders
demandés — les _prouve devront s'y plier pareil).

## 🏆 2 août (ev. 106) — **Th.1 §III.5.6 DIVISION EUCLIDIENNE COMPLET** (existence + UNICITÉ)
Constat, pas construction : `_unicite` était DÉJÀ écrite (ensembles_division_unicite.py,
trichotomie + 2×_lt_chain + irréflexivité + translation injective) et **la photo du 2 août
(3 922 verts, sans filtre) l'a exécutée et certifiée**. Le « RESTE : unicite » ci-dessous
(l.~1685) était PÉRIMÉ — 5ᵉ carte périmée du jour. Statut : existence [~ CLOS modulo C61,
24 juil] + unicité [~ CLOS modulo C61] ⇒ **le Th.1 (E III.39) est entièrement démontré**.
⚠️ RÈGLE NOUVELLE (leçon des 5 cartes) : toute section RESTE/⏸ cite son tick d'écriture,
et sa lecture COMMENCE par un grep de l'état réel — le récit du journal est une prophétie,
seuls le code et les tests font foi.

### 📏 MESURE PROFONDE (tick ev. 106+, 2 août ~12h) — VERDICTS par grep des 🎯🎯 :
- **Hessenberg a²=a : PARTIEL-AVANCÉ** — `hessenberg_a_carre_egal_a_inconditionnel`
  (assemblage_vrai/ensembles_hessenberg_recollement_final.py:284) : a²=a JAMAIS supposé,
  ¬(𝔟<a) DÉRIVÉE/déchargée ; restent les hyps arithmétiques honnêtes (S₀⊂E…). À lire en
  détail pour lister les hyps exactes → candidat décharge.
- **Trichotomie/bon ordre : PARTIEL** — maillon_coherences_prouvees : TARGET 1 (fonctionnalité
  de h_iso_max PROUVÉE — ⚠️ c'est LE candidat 0,9912 du scan jumeaux de l'article !) +
  TARGET 2 maillon_final_h_plus3 à **6 hypothèses** (3 cohérences déchargées). Suivant : lire
  les 6 hyps, mesurer lesquelles se déchargent.
- **III.7 limites : AUCUN 🎯🎯** (cone_unicite/limites/limites_canoniques existent sans
  capstone marqué) — VRAI TROU de fond. **IV structures : AUCUN 🎯🎯** — idem (CST1/2).
- prop12/Cantor : à mesurer encore (le grep zone a rendu vide avec filtre — refaire sans).
**MESURE FINALE TRICHOTOMIE (tick ev. 106+, ~12h10)** : la zone va DÉJÀ plus loin que le
maillon — `trichotomie_ordinaux_canon_prouve_min` (ensembles_trichotomie_assemble.py:240) :
**5 hypothèses** {bo(R,E), bo(Rp,F), maximalité(dom h=E ∨ pr₂h=F), est_segment(pr₂h,Rp,F),
val_dans_F} — dom-segment DÉCHARGÉ (dom_h_est_segment_sous_val PROUVÉE sous val_dans_F),
residu_univ_app DÉRIVÉ. RÉSIDU STRUCTUREL documenté dans l'en-tête du fichier (rapporté,
jamais postulé). **PROCHAINE BRIQUE (design mesuré, tick ~12h10)** : `ensembles_trichotomie_img_segment.py`
— N'EXISTE PAS (vérifié find — le « REPORTÉ » de dom_segment l.44-46 était honnête) ;
dossier assemblage à 9/10 = une place. ⚠️ PAS une transposition mécanique : l'initialité de
l'IMAGE exige la SURJECTIVITÉ de φ (en-tête dom_segment). DESIGN (calqué sur le motif
val_dans_F, hypothèse explicite ∀-close, VRAIE, jamais postulée) :
  `temoin_dans_S(E,R,F,Rp)` := (∀u∀S∀T∀φ)( (u∈F ∧ seg(S,R,E) ∧ seg(T,Rp,F) ∧
    iso(φ,S,T,R,Rp) ∧ u∈T) ⇒ (∃p)(p∈S ∧ valeur(φ,p)=u) )   [= surjectivité-témoin].
CHAÎNE (miroir de l'IDÉE l.16-19 de dom_segment) : t∈pr₂h ⇒ ∃x,(x,t)∈h [axiome pr₂/img] ⇒
témoin (S,T,φ,x) [h_membre_donne_temoin] ∧ t=φ(x)∈T ; u∈F ∧ u R' t ⇒ u∈T [initialité de T,
segment de F] ⇒ ∃p∈S, φ(p)=u [temoin_dans_S] ⇒ (p,u)∈h [couple_iso_dans_h — codomaine
gratuit : φ(p)=u∈F déjà en main] ⇒ u∈pr₂h. LIVRABLES : img_h_initial_sous_temoin +
img_h_est_segment_sous_temoin (borne pr₂h⊂F = M.h_img_inclus_F INCONDITIONNELLE) ; puis
coupe dans un _min2 : est_segment(pr₂h) REMPLACÉE par temoin_dans_S — compte stable (5)
mais TROC d'une hyp de construction contre une ∀-close générale VRAIE (dérivable plus tard
de la décomposition de bijective, même sort que val_dans_F/pont R2). **MODÈLE LU EN ENTIER (l.80-348) — design AFFINÉ** : (α) `t∈T` se DÉRIVE sans hypothèse
neuve : cœur porte {t=valeur(φ,x), func φ, dom φ=S, φ⊂S×T, x∈S} ⇒ x∈dom φ ⇒ (x,φ(x))∈φ
[motif valeur_dans_graphe] ⇒ (x,t)∈S×T [φ⊂S×T] ⇒ t∈T [décomposition couple-produit] ;
(β) `p∈E` sort de S⊂E (conjoint gauche de Hseg_S, instancié) ; (γ) la SEULE hypothèse
neuve = temoin_dans_S (surjectivité) ; le témoin ∃p s'élimine comme vv dans le modèle
(prem_p := (p∈S ∧ valeur(φ,p)=u), s5 puis existe_elimination) ; (δ) couple_iso_dans_h
pour (p,u) : fournir {seg S, seg T, iso, p∈S, p∈E, u∈F, u=φ(p), func, dom, graphe} —
même liste que le modèle avec y↦p, vv↦u ; (ε) pièges de liants HÉRITÉS : zd≠« y »
(verrou liant valeur), liants natifs des axiomes, alpha_existe pour raccorder.
RESTE À MESURER avant d'écrire : le nom/liant NATIF de l'axiome pr₂ (comment t∈pr₂h se
décompose — grep « pr2\|AXIOME_IMG\|image » dans ensembles_abrege + scaffold M.h_img_inclus_F)
et la forme exacte de est_segment côté initialité de T (conjoint droit de Hseg_T, instancier
à (t,u)). PUIS : maximalité (Zorn) et dérivation val_dans_F/temoin_dans_S (pont R2 renforcé).

**(archive) CHOIX FAIT (tick ev. 106+, lecture des 2 jeux)** : **TRICHOTOMIE Th.3 §III.2.5**.
Lecture : maillon_final_h_plus3 survit à 5 hyps = {bo(R,E), bo(R',F)} — LES ANTÉCÉDENTS DU
LIVRE (« deux ensembles bien ordonnés »), à GARDER — + maximalité (dom h=E ∨ pr₂ h=F) +
2 segments (est_segment(dom h,R,E), est_segment(pr₂ h,Rp,F)) — propriétés de la CONSTRUCTION
h_iso_max (Zorn), à DÉCHARGER. CIBLE FINALE : **{bo(R,E), bo(R',F)} ⊢ trichotomie_ordinaux_canon**
= la forme exacte du Th.3. PLAN prochain tick : (1) grep les preuves des 3 dans la machinerie
Zorn/frame de trichotomie_ordinaux (candidats : *maximal*, *segment_dom*, zorn_zermelo/,
frame_*) — règle des 5 cartes : elles existent peut-être déjà ; (2) si oui → coupes par
appartenance (motif du jour, 8 réussites) dans un maillon_final_h_plus4 ; si non → construire
la plus courte d'abord (segments probablement : dom d'un iso partiel maximal est un segment =
lemme Zorn classique) ; (3) test fichier-seul détaché ; (4) journal+ev.+bilan.
(Hessenberg DIFFÉRÉ : jeu restant = intégration géométrique du cadre Zorn {Z=S₀, u∈U, U∩S₀=∅,
𝔟·𝔟=𝔟…} — chantier de construction, pas une décharge courte. Après la trichotomie.)

### 🗺️ (archive) RE-CARTE des restants (écrite au tick ev. 106+, 2 août ~12h — À VÉRIFIER PAR GREP)
Sondage de surface fait (fichiers existent PARTOUT — Hessenberg/Cantor : _cantor.py + ponts ;
bon ordre : trichotomie_ordinaux/assemblage ; limites III.7 : cone_unicite/limites_canoniques ;
CST : iv_1 especes/especes_deduction/isomorphismes). PROCHAIN TICK = MESURE PROFONDE : pour
chaque zone, trouver LE capstone (grep les 🎯 et les asserts est_clos/hypotheses des fichiers
d'assemblage + l'état des tests) et classer FAIT/PARTIEL/TROU — méthode : (1) grep "🎯🎯"
dans la zone ; (2) lire les asserts du plus haut théorème ; (3) grep son test ; (4) verdict.
Zones dans l'ordre du livre : trichotomie_ordinaux/assemblage (bon ordre des cardinaux ?
maillon_final + residuals à lire), prop12 (Cantor 2^a>a : _cantor.py), Hessenberg (a²=a —
quel fichier d'assemblage ?), III.7 limites (cone_unicite), IV CST. Aussi : n°88/89/91
(⋂_∅/double-famille — retrouver leur définition exacte à CAMPAGNE_DEMOS l.~2098) et n°26
stabilité multiples (re-tester pymupdf→PNG sur E III.40 d'abord — fidélité avant tout).

## 🏆🏆🏆 2 août — **TICK INSTANCIATION ℕ : ACQUIS — « n! EST UN ENTIER » SUR LE VRAI ℕ, 3 HYPOTHÈSES**

**`factorielle_entier_NN` : { essais_bien_formes, rule_codomain, essais_restriction } ⊢
(∀n)(Fini n ⇒ Fini(f(n))) à e=ℕ, G=G≤ — 2/2 verts en 7:39 (détaché).** Les DEUX moitiés
(R0)/(Rs) DÉRIVÉES, et TOUT le reste déchargé par des théorèmes CLOS : bo ← bo_graphe_NN,
0∈ℕ ← zero_dans_NN, H1..H4 ← donnees_ordre_NN (N1, 5/5 en 7:44), seg(ℕ,0)=∅ ← seg_zero_vide
(VERT 3:07 après fix). Les 3 hypothèses restantes = le prix honnête de « la règle factorielle
est bien formée ». LES SEPT COUPES par APPARTENANCE : toutes passées, zéro désalignement.
**LEÇONS** : (1) liant EXOTIQUE pour protéger la chaîne (inf_egal_card lie « z » en interne)
PUIS re-liant CANONIQUE à la sortie (instancie+generalisation — motif segment_succ) : les
deux moitiés du motif sont OBLIGATOIRES, l'exotique seul casse le raccord final (mesuré :
« mineure ≠ antécédent » au MP vers inclus) ; (2) détecter une hypothèse par heuristique
.tag = FRAGILE ; couper par appartenance de la conclusion d'un théorème CLOS = ROBUSTE.
**ET LE CHANTIER (∃!f) EST DÉJÀ FAIT** (mesuré au moment de l'attaquer — 4ᵉ carte périmée du
jour) : ensembles_c62_fonction_unicite.py (unicite_fonction_c62 {bo,ebf,rc},
existence_unicite_fonction_c62, est_un_graphe_fonction_globale CLOS) + ordre_NN_graphe.py::
existence_unicite_fonction_NN à **2 hyps** — tous dans la photo verte des 3 909. Le PLAN A2
(l.1340) est PÉRIMÉ, à ne plus consulter.
**PROCHAINS CHANTIERS RÉELS** : familles indexées (Def.2-produit ∏_{i<n}(i+1) + bergers
plein — le dernier écart de fidélité déclaré de la caractérisation) ; re-carter les ⏸.

### 🏆🏆🏆 FAMILLES PHASE 2 CLOSE — **PHOTO INTÉGRALE VERTE SOUS L'ENCODAGE FIDÈLE** (2 août, ev. 104)

**PHOTO COMPLÈTE : 3 922 passed / 2 failed en 2:42:50** — et les 2 rouges étaient les SONDES
DE L'INSTRUMENTATION VÉRITÉ ELLE-MÊME (test_classer_residu : SYMBOLES_T0 figé avec « fam » ;
« fam figure dans 4 axiomes ») — mises à jour (set mesuré = ancien MOINS fam, 20 symboles ;
test réécrit en TOMBEAU documenté de l'ancien encodage), re-test **18/18 en 5,8 s** ⇒ suite
INTÉGRALEMENT verte. theorie==22 partout. Total 3 924 collectés (+15 vs photo seg_ext).
**Zéro casse mathématique sur ~90 fichiers consommateurs** : 1 ligne d'accesseur + 3 sondes
textuelles. Les 4 axiomes de familles se reconstruisent sur le τ de `valeur` (bâti sur
`paire`, déjà présent — le set de symboles ne bouge que de « fam »).
**RÉSIDU NOMMÉ** : `test_pont_fam_valeur_independant` étiquette encore HW « independante »
(classifieur SANS prouveur, critère d'occurrence) alors qu'elle est désormais dérivable par
réflexivité — illustration vivante de la défaisabilité du 3ᵉ verdict (§3.3 du papier) ;
re-passer avec prouveur-réflexivité + mettre à jour le test au prochain tick outillage.

### 🚧 (archive) FAMILLES PHASE 2 — MIGRATION D'ENCODAGE valeur_famille := valeur (LE COUP DE LA FIG. 3)
**Recon (2 août ~07h20, mesures)** : valeur_famille(f,i) = app("fam",f,i) construit UNIQUEMENT
via l'accesseur Python (0 contournement code : "fam" n'apparaît qu'en 2 docstrings, aucun walker
sur le tag) ; valeur(f,x,b="y") = τ_b((x,b)∈f) ; consommateurs : 57 bourbaki + 32 tests.
famille_identite_ii4.py:19 documente l'indépendance (« symbole LIBRE qu'aucun des 22 axiomes ne
relie à valeur ») — c'est LA source du verdict indépendant de HW/HN.
**DÉCISION (déléguée, fidèle à la décision actée)** : migration (A) par REDÉFINITION DE
L'ACCESSEUR — une ligne, tout le dépôt se reconstruit à travers lui. Fidélité AMÉLIORÉE
(E.II.4.1 : une famille EST une fonction, X_ι EST sa valeur). HW/HN deviennent t=t
(réflexivité) ⇒ décharge triviale ensuite ⇒ factorielle_def2 à {n∈ℕ} seul.
**CLASSE DE CASSE ATTENDUE** : « verrou liant valeur » — les τ_y nouveaux dans des contextes
qui lient « y » (inf_egal_card lie y !) ⇒ renommages subst ⇒ miroirs α-décalés ; et les
théories dédiées dont l'axiome mentionne valeur_famille (theorie_somme_famille) rebuildent.
**PROTOCOLE TRANSACTIONNEL** : (1) backup ensembles_abrege.py → scratchpad .bak_fam ;
(2) redéfinir (docstring : décision, date, note b="y", pont devenu réflexif) ; (3) tests par
ZONES dans l'ordre : ii_4+ii_5 (familles cœur) → iii_3_6 familles → c62+factorielle 5_8 →
photo complète détachée EN DERNIER ; (4) casse : fixer site par site (motifs : b frais au lieu
de "y", re-liant canonique) ; MUR structurel (cascade de captures) ⇒ REVERT (.bak) et bascule
plan (B) extension-δ. JAMAIS d'état partiel : la ligne est atomique, le suite-vert est le juge.

### ✅ FAMILLES PHASE 1 ACQUISE (2 août, ev. 102) — H2/H3 DÉCHARGÉES, 2/2 verts 3:18, 1ᵉʳ coup
`ensembles_factorielle_def2_close.py` : **factorielle_def2_dechargee {n∈ℕ, HW, HN} ⊢
(succ n)!_déf2 = (n!_déf2)·(succ n)** — H2/H3 coupées par les instances CLOSES de
`produit_graphe` (liant « G » par PARAMÈTRE ff — le re-liant sans son coût, leçon).
Dossier familles au CAP (10). RESTE phase 2 : HW/HN (ponts fam↔valeur, INDÉPENDANTS —
l'exemplaire X_ι du papier) — recon migration valeur_famille:=valeur (décision l.1224,
~40 fichiers, séquentielle, préflight transactionnel) vs extension-δ locale ; PLAN AU
JOURNAL avant d'agir.

### 🗺️ (archive) TICK — FAMILLES phase 1 : DÉCHARGER H2/H3 de factorielle_def2_recursion
Carte re-mesurée (2 août, ~07h10) : `factorielle_def2_recursion` (iii_3_6_familles/
ensembles_factorielle_def2_rec.py:275) porte {n∈ℕ, H2, H3, HW, HN}. H2/H3 = « les membres
des produits ∏(W, seg(n)∪{n}) / ∏(W, seg n) sont des GRAPHES », héritées de T1b-2
(`produit_fini_recursion`) — les locaux h2/h3 apparaissent à l'assert l.333. **L'axiome
produit RÉPARÉ les rend dérivables** (conjoint de tête F⊂I×⋃X + `_inclus_produit_est_graphe`
application_valeur.py:163) et l'ev. 78 dit « H2 et H3 sont devenues des THÉORÈMES » (session
réparation 27 juil) — LOCALISER ces théorèmes (grep ii_5_produit_famille + iii_3_6 pour
« est_un_graphe » en conclusion d'implication depuis ∈∏) ; s'ils n'existent qu'en forme
générique, dériver l'instance. PLAN : (i) lire def2_rec l.290-336 (formules exactes h2/h3) ;
(ii) trouver/dériver `membre_produit_est_graphe` ; (iii) `factorielle_def2_dechargee` →
**{n∈ℕ, HW, HN}** (3 hyps — il ne restera que les ponts fam↔valeur INDÉPENDANTS, l'exemplaire
X_ι du papier) — dossier familles à 9 entrées (1 place) OU dans def2_rec si ≤300 l ;
(iv) test background (⚠️ T1b-1 → N_existe ~5 min). PHASE 2 (tick d'après) : résolution
HW/HN par le COUP DE LA FIGURE 3 du papier — extension-δ ou décision d'encodage
valeur_famille:=valeur (migration ~40 fichiers, SÉQUENTIELLE — décision déjà actée l.1224).

## 🗺️ 2 août — TICK (archive) : INSTANCIATION ℕ/G_ordre_NN (étape 5) — carte re-mesurée

**Constat d'entrée** : les étapes (1)-(4) du vieux plan l.1330 sont MORTES —
`ensembles_ordre_NN_graphe.py` EXISTE (iii_6_1) : `G_ordre_NN()` (terme opaque + axiome S8) et
**`bo_graphe_NN()` ⊢ est_bien_ordonne(R_G≤, ℕ) [CLOS]** (congruence par feuilles + alpha_bridge
+ MP n_bien_ordonne). Reste la VRAIE étape (5) : instancier `factorielle_entier_complet` /
`factorielle_rs` à **e := ensemble_NN(), G := G_ordre_NN()** et décharger tout ce qui se
décharge. **Cible : { ebf, rc, essais_restriction } ⊢ (∀n)(Fini n ⇒ Fini f(n)) à ℕ — les
données de la RÈGLE seules (3 hyps).**

**BRIQUES MESURÉES (toutes existantes, toutes CLOSES sauf mention)** :
- `appartenance_NN()` ⊢ (∀z)(z∈ℕ ⇔ Fini z) [CLOS] + variante TERME l.155 ; `zero_dans_NN()`
  [CLOS] ; `NN_clos_successeur()` ⊢ (∀n)(n∈ℕ ⇒ succ n∈ℕ) [CLOS] — ensembles_ensemble_NN.py.
- `bo_graphe_NN()` [CLOS] — décharge bo. `segment_succ_est_intervalle(k)` {k∈ℕ} ⊢
  seg(ℕ, succ k) = [0,k] — ensembles_pont_segment_iii5.py (cible : cible_segment_succ_intervalle,
  terme : segment_succ_NN). n∈[0,n] : REUSE `conjonction_elim_gauche(plus_grand_element_intervalle(n))`
  {est_cardinal n} (max_intervalle) ; est_cardinal n = conjonction_elim_gauche(Fini n) (Fini = et(card, ≠succ)).
  0∈[0,n] : axiome_intervalle_entiers instancié (motif _membre_intervalle de max_intervalle) +
  fini_zero + zero_inf_egal_cardinal + inf_egal_reflexif.
- ⚠️ à DÉRIVER encore : seg(ℕ, ZERO) = ∅ (« rien avant 0 » — dérivable au TERME, pas à la
  variable ; motif : z∈seg(0) ⇒ z<0 ⇒ absurde via caractérisation du segment + 0 minimal).

**PLAN D'EXÉCUTION** (2 briques, iii_6_1 à 8 entrées = 1-2 places) :
- **N1** `ensembles_donnees_ordre_NN.py` (iii_6_1) : les ∀-clôtures de `donnees_ordre_closes`
  DÉRIVÉES à (ℕ, G≤) — H1 (Fini n ⇒ succ n∈ℕ : appartenance⇐ + NN_clos_successeur),
  H2 (pont + Fini⇒∈ℕ), H3/H4 (z∈[0,n] puis transport ARRIÈRE le long de seg=[0,n] via s6),
  + seg(ℕ,0)=∅. ⚠️ Les formules doivent être ==  à `donnees_ordre_closes(ensemble_NN(),
  G_ordre_NN(), nb="nfac")` — asserts miroirs OBLIGATOIRES (piège variables vs termes clos,
  payé le 26 juil). ⚠️ PERF : tout est τ-lourd à ℕ (N_existe ~5 min 1er appel, mémoïsé après).
- **N2** `factorielle_entier_NN` : factorielle_entier_complet(e=ensemble_NN(), G=G_ordre_NN())
  + coupes bo←bo_graphe_NN, ZERO∈E←zero_dans_NN, seg(0)=∅←N1, H1..H4←N1 ⇒ **3 hyps**.
  ⚠️ vérifier que la chaîne accepte des TERMES pour e ET G (e=NN marchait ; G-terme = à
  confirmer sur `_graphe_R(G_ordre_NN())` — c'était l'étape (1) du vieux plan, jamais actée).
  ⚠️ B4 doit être VERT d'abord (tests b9p7bw9x2 en cours au moment d'écrire).

**ÉTAT** : B3 ✅ (2/2, 3:38) ; B4 ✅ (4/4, 8:53) ; **N1 ✅ (5/5, 7:44 — H1..H4 CLOSES aux
termes, miroirs == vérifiés)** ; **N2 ÉCRIT ET LANCÉ** (`ensembles_factorielle_entier_NN.py`,
iii_6_1 → 10 entrées = CAP) : base = factorielle_entier_complet(e=ℕ, G=G≤) puis coupes
bo←bo_graphe_NN, 0∈ℕ←zero_dans_NN, H1..H4←N1 ⇒ **4 hyps** {ebf, rc, essais_restriction,
seg(ℕ,0)=∅} — chaque coupe assertée par APPARTENANCE (un désalignement échoue nommément).
Test DÉTACHÉ (PID 14040, `V9/n2_test.log` — hors plafond 10 min de l'outil) ; suspects si
rouge : liants de est_bien_ordonne entre bo_graphe_NN et la chaîne, α-formes des hyps règle
aux termes, coût τ (tuer si >50 min : leçon des runs tués). Traduction FR ✅ LIVRÉE (17 p.,
0 réf cassée) ; légendes des 3 figures AJOUTÉES (EN+FR, demande Karl : décoder couleurs/
flèches) et les deux PDF recompilés (16 p. / 17 p.).

## 🎉🎉🎉 2 août — **(B3) LA PHRASE DU LIVRE DÉRIVÉE : f(succ n) = (succ n)·f(n)** — 2/2 verts, 3 min 38

`ensembles_factorielle_succ_vraie.py` (NOUVEAU fichier — le dossier 5_8 passe à 10 entrées =
**CAP ATTEINT**, prochain ajout ⇒ éclatement en sous-dossiers) :
**`factorielle_succ_vraie` : { …les 9 du recâblé…, n∈seg(succ n) } ⊢ f(succ n) = (succ n)·f(n)**
[10 hyps honnêtes] — E III.41 L.30-32, le facteur, le point ET la fonction du livre.
Chaîne : fallback recâblé + `restriction_valeur` (u(n)=f(n)) dont les 3 prémisses réglées :
func f ← `fonction_globale_fonctionnelle` [CLOS] ; n∈dom f ← n∈seg + seg⊂E [CLOS] + transport
dom f=E [résidus déjà au jeu] ; n∈seg(succ n) = l'UNIQUE hypothèse nouvelle (position honnête).
Test-miroir : cible reconstruite à la main. Cartes périmées tuées au passage : « dossier au
CAP » était FAUX (9 entrées mesurées, pas 10) ; est_entier(a) EST est_fini(a) (même formule,
synonyme — le pont d'antécédent de (Rs) est GRATUIT).

**(B4) ✅ ACQUIS — 4/4 verts en 8 min 53 (avec B3, 4 workers), PREMIER COUP** : `factorielle_rs` = (Rs) DÉRIVÉE, ∀-close —
{ bo, ebf, rc, essr, ZERO∈E, H1..H4 } ⊢ (∀n)(Fini n ⇒ f(succ n)=(succ n)·f(n)) [9 hyps
n-CLOSES] — les 4 données de position passent en ∀-clôtures H1..H4 (`donnees_ordre_closes`),
coupées sous Fini n supposé localement, est_entier absorbée par l'antécédent, généralisation
légale (C27). PUIS **`factorielle_entier_complet`** = LA DÉCHARGE : (∀n)(Fini n ⇒ Fini f(n))
sous 10 hyps n-closes, **AUCUNE moitié (R0)/(Rs) supposée** — (R0) déchargée depuis
c62_entier (kwarg zcard ajouté, défaut byte-identique, appel à "Z" : leçon α-variants),
(Rs) déchargée par factorielle_rs. Si verts : le « n! est un entier » du livre est CLOS
MODULO résidus C62 + données d'ordre ∀-closes — reste l'instanciation ℕ/G_ordre_NN qui les
décharge toutes.

## 🎉🎉 2 août — **RECÂBLAGE DE LA RÈGLE FACTORIELLE : n! (Déf.2) + M(D u) RÉEL — 44/44 VERTS 1ᵉʳ COUP**

**Constat d'entrée (règle ev. 64/65 appliquée)** : le « Tick 3B (prochain) » du journal était une
CARTE PÉRIMÉE — `u_non_vide` ET `factorielle_succ_fallback` déjà écrits, testés, VERTS (baseline
re-mesurée avant tout geste). Le vrai tick = le recâblage que la règle documentait elle-même
comme « correctif connu ». **Décision (déléguée) : les DEUX défauts en UNE passe de migration**
(mêmes ~8 énoncés publics touchés ; deux passes = coût double) :
1. **(B2) Décalage d'un cran MORT** : facteur `cardinal(Du)` (Déf.2 : f(z)=z·f(z−1) ⇒ **n!**),
   plus `successeur(cardinal(Du))` qui encodait (n+1)!.
2. **(B1) M(D u) RÉEL** : `prev = valeur(u, terme_plus_grand(inf_egal_card, Du, "m", "x"))`
   (le τ-terme E III.46 note 2, §III.1.7) — le fallback `u(dom u)` est mort. Liants "m"/"x"
   hors {F,u,up,v,y,z} liés dans inf_egal_card (piège du 27 juil. évité).
3. **Étape (6) GRATUITE** : `M([0,n]) = n` par `max_intervalle_vaut_n_entier` — son hypothèse
   `est_entier(n)` était DÉJÀ dans le jeu (partagée avec prop5) ⇒ compte inchangé (9).
**Conclusion nouvelle : `f(succ n) = (succ n)·u(n)` — le FACTEUR et le POINT du livre.**
Caractérisation réalignée : `f(0)=1 ∧ f(n+1)=(n+1)·u(n)`, 10 hyps (5 partagées), miroir à la
main concordant. iii5 : B1/B2 morts → restent **(B3)** valeur(u,n)=valeur(f,n) [accord de la
restriction, demande n∈seg(succ n)] et **(B4)** ∀-clôture de (Rs).
**Note technique** : la congruence-à-trou TRAVERSE le τ de M (le trou est LIBRE sous le lieur ;
substitués sans "m"/"x" libres ⇒ aucune capture — subst propre post-fix du 24 juil.).
**Tests : 44/44 verts, 4 lots parallèles, PREMIER COUP** — A succ+zero+existence 12 (5:59) ·
B fonction+gluing+pont 15 (7:57) · C caractérisation 10 (6:28) · D iii5 7 (9:48).
theorie==22 dans chaque lot. Zone génériques (zero, fonction, cibles C62) : AUCUNE édition
nécessaire, elles se sont adaptées — la forme n'était encodée en dur qu'aux 8 sites prévus.
**PROCHAIN TICK — (B3) → `factorielle_succ_vraie` = LA PHRASE DU LIVRE** — carte RE-MESURÉE
(2 août, post-recâblage) : **`restriction_valeur(t, A, i)` EXISTE** — ⊢ (t|A)(i) = t(i), vit
avec `restriction_dom_sous_inclusion` (ensembles_cantor_bernstein_bij), employée en série dans
iii_3_6_familles avec le motif de décharge `_dech(restriction_valeur(...), func_t, i∈A, i∈dom)`
(voir ensembles_produit_adjonction_briques.py:74). Route : instancier à (f, seg(succ n), n) ;
`func f` ← `fonction_globale_fonctionnelle` [CLOS] ; `n∈dom f` ← n∈E + dom f=E [résidus déjà
au jeu] ; `n∈seg(succ n)` = donnée de position HONNÊTE (nouvelle hyp, comme ZERO∈seg) ⇒
`valeur(u,n) = valeur(f,n)` ; composer avec le recâblé ⇒ **f(succ n) = (succ n)·f(n)**
(~10-11 hyps). PUIS (B4) ∀-clôture de (Rs) vers la décharge dans `factorielle_c62_entier`.
Fichier : ensembles_factorielle_succ.py (même fichier, dossier au CAP).

## 📄 2 août — **S4 : RELECTURE ADVERSE REÇUE ET APPLIQUÉE** (article 16 p., 0 réf cassée)

Verdict de l'agent : **CORRECTIONS-MAJEURES** — la base de preuve tient (33/39 chiffres
tracent exactement, le §7 n'invente AUCUNE absence, les 3 citations verbatim vérifiées aux
PDF), mais 6 bloquants + 11 majeurs. **Doctrine du 21/21 appliquée : chaque finding grave
RE-VÉRIFIÉ inline avant application** — tous confirmés (echec.py = 5 champs pas 6 ; « 6 700+ »
ne trace qu'à `couple_diagonale` 6 707 pas ; « 62→95 » introuvable, réel = 95 dont 37 avant le
26 juil ; photo = 2 h 43 pas ~5 h ; « 27 théories » appartient à `factorielle_def2_zero`).
~35 corrections appliquées par le directeur (l'agent n'a touché que le .bib) :
- **B1** 4 labels manquants → les 12 « Section ?? » du PDF morts. **B3/B4** chiffres
  introuvables remplacés par le mesuré. **B5** case E3 remplie (route « n−1 », ev. 84–85).
- **B6** l'asymétrie de la trichotomie ÉCRITE noir sur blanc (indépendance = absence de
  témoins, verdict défaisable — l'abstract ne promet plus un objet-noyau pour la 3ᵉ branche).
- **M2** le 3ᵉ défaut (AXIOME_INTER_FAM, ev. 38 : Résumé E.R.19 vs E II.22, portée 34)
  raconté au §4 — l'objection « votre T₀ était incohérente le 26 juil » est désamorcée.
- **M4/M5/M8** M2F cité sur sa citation d'or ; **Knuckledragger ajouté au .bib** (vérifié
  page GitHub — pas d'arXiv) ; AutoformBot/ATLAS démêlés. **M9** tuple Echec calé sur le code
  (5 champs). **M10** ¶ Reproducibility ajouté au §6. **M1/M6/M11** day-long→95 min,
  « quarter of cost »→237k vs 266k, ~5 h→2 h 43. + 10 gallicismes (S1–S10), « last mile »
  encaissé dans l'intro, m1–m11.
Recompilé : **16 pages, exit 0, 0 « ?? », overfull résiduel 6 pt (cosmétique)**.
**RÉSIDUS (honnêtes)** : (1) B2 — nom/email/URL auteur = Karl ; (2) B4 — le dépôt est
NON COMMITÉ depuis le 1ᵉʳ juil : **commit + tag AVANT soumission** (le hash va dans \thanks)
— action Karl, je ne commite jamais ; (3) ~~10 entrées .bib (v?)~~ **SOLDÉ (2 août, sur ordre
Karl)** : les 10 vérifiées en ligne (arXiv ×8, FSE/JCST ×2) — prises : `hou2025versions` 1ᵉʳ
auteur = LUAN pas Hou (8 auteurs, titre complet avec sous-titre Isabelle), survey = Zhang &
Tan JCST 41(1):46-66, BlueprintRepair et ContextEngineering = auteurs UNIQUES, Faithfulness
Gap = Mohammad (nom) Noor Islam S. (prénom) + Sheikh Tamim ; le pari « Li/Peng/Severini/
Shafto » de Mathlib Network était juste. **0 entrée (v?) restante** ; leçon au passage : le
champ `note` S'IMPRIME dans la biblio → traces de vérification déplacées en commentaires % ;
(4) ~~six/sept faux murs~~ **SOLDÉ (2 août, sur ordre Karl — ev. 97)** : le vrai compte est
**NEUF** énumérés (6 avant la semaine : ev. 1, 8, 9, 10, 36, 37 ; 3 pendant : ev. 61, 64, 65 ;
exclus 46/53/58 = autres modes) — le « 7× » de C8 venait d'un « + 5 antérieurs » compté de
mémoire, et le PAPIER était de surcroît MAL SCOPÉ en 2 endroits (intro + table §6 : murs
d'avant-semaine attribués à la semaine) ; corrigé partout, liste canonique au README verite
§4, papier recompilé 16 p. ; **leçon (ev. 97) : un compte nu dérive — la forme stable est
l'énumération + le critère** ; (5) ~~lien fig. 2 ↔ (n+1)!~~ **SOLDÉ (2 août, sur ordre Karl — ev. 98)** : la figure était
un **composite implicite** — but et mur réels, mais bo = route C62-existence (ev. 9/61) et
H = route cas-0 (ev. 67), pas la frontière du pas de récurrence, qui EXISTE noir sur blanc :
{n∈ℕ, H2, H3, HW, HN} (grep, l.395-396), H2/H3 tombées avec la réparation produit, HW/HN
(= X_ι) indépendantes → le vert et l'orange cohabitent sur la frontière RÉELLE. Légende
réécrite pour DIRE l'agrégation route par route + ancre machine-lisible posée sur le TikZ ;
recompilé 16 p. Cerise : le « ev. 30/31 » de ce résidu était lui-même une citation fausse
(ces événements parlent de décomposition canonique) — hygiène des résidus appliquée à
nos propres résidus.

## 🟢🟢🟢 2 août, 03h18 — **LA PHOTO PROPRE : suite intégrale 3 909 / 3 909, ZÉRO rouge**

Le dépôt entier sous l'axiome `seg_ext` réparé, en un seul run par zones :

```
I + IV + II                1 252 passed      33 s
III.1 + III.7 + outils_ia    383 passed    3:47
III.3 (équip. + opérations)  732 passed   10:18
III.2 bien-ordonnés          612 passed   24:24
III.4 entiers finis          391 passed   30:27     ← la zone des 16 ex-échecs
III.5 calcul entiers         232 passed 1:05:44
III.6 infinis / C62          307 passed   27:41
─────────────────────────────────────────────────
TOTAL                      3 909 passed, 0 failed   (00:35 → 03:18)
```

Avec : `theorie_ensembles()` = 22 · axiome ∀-clos (libres = ∅, 1 classe α) · fabrique sans
paramètre · **D1 structurellement morte** · ancienne API refusée (`TypeError`).
**C'est la photo de référence de l'article** — jalon S1 du PLAN.md **COMPLET** (✅ squelette,
✅ suite verte, ✅ C8 consolidé dans `article/C8_retours.md` : 10 instances tracées échec→réemploi
+ 3 contre-exemples honnêtes + menace de validité).

**S2 — passe de related work FAITE (2 août)** : 4 chercheurs parallèles (Opus/medium, 237 k tokens
au total — la grille de sobriété tenue), 57 requêtes, **69 réfs, 33 menaces**, synthèse dans
`article/RELATED.md`. Verdict : **aucun claim tué, trois RECENTRÉS** (C1 : le formalisme inhabité,
pas le véhicule LCF/Python ; C4 : l'articulation + la branche indépendante, pas la réfutation ;
C6 : le verdict dérivé mécanique, pas l'ancrage fin — M2F fait déjà la provenance au span).
Le cœur de nouveauté est **confirmé par les non-trouvés croisés de 4 chercheurs indépendants** :
échec certifié-noyau, périmètre calculé, branche indépendante, chapitre I de Bourbaki, verdict
d'infidélité par dérivation, dette d'axiomes nommée, WL-sans-apprentissage pour jumeaux, boucle
tracée instance par instance.

**S2 CLOS (2 août)** : les 5 menaces **lues au PDF** (déposés dans `sources/related_work/`,
fiches à la page dans `article/FICHES_MENACES.md`). Trois démarcations AJUSTÉES par la lecture :
C7 rétrogradée (Olšák = GNN appris, 0 « Weisfeiler », 0 dédup) ; C6 citation d'or (M2F p.8 :
fidélité par « **manual audit** » — notre verdict est dérivé) ; C8 recentré (ATLAS p.6 publie la
*forme* de la boucle — nos maillons sont certifiés). **Concurrent n°1 identifié : Goedel-Architect**
(2 diagnostics sur 3, forfeits LLM non certifiés, aucun corpus persistant). Reste : le survey
conjecturing (risque résiduel C4) + traduction §7 LaTeX (S3). L'incohérence découverte le 27 juil. est **close de bout en bout** :
détectée par dérivation, réparée structurellement, prouvée irréproductible, et son coût honnête
(deux acquis affaiblis) nommé et mesuré.

## ✅✅ 2 août — MIGRATION `seg_ext` TERMINÉE : 21/21 réparés, et **la contradiction était PORTEUSE**

**Les 21 rouges sont verts** : `realisation_segment` **81 passed** (16:26), `iii_5_8_factorielle`
**44 passed** (17:08), contrôle `gate_onto_top` 13 passed. `theorie` = 22, axiome ∀-clos, 1 classe α,
ancienne API refusée par `TypeError`. Sonde adverse : **18 contrôles, tous mordent**.

### ⚠️ MON DIAGNOSTIC ÉTAIT FAUX — 21 fois sur 21

J'avais pronostiqué « cibles de test périmées ». Mesuré : **aucun des 21**. Réalité : 5 = un
`NameError` introduit par l'agent lui-même (helper `_t` absent — corrigé + passe AST prouvant
0 autre cas) ; 16 = **les théorèmes ne se construisaient plus du tout** (C27 : « Ro libre dans une
hypothèse »). Leçon : le triage aussi se MESURE — un pronostic de directeur n'est qu'une docstring
de plus.

### 🔴 LA TROUVAILLE : deux « acquis » n'étaient démontrables QUE PAR le défaut

Les preuves de `bon_ordre_intervalle_depuis_realisation` / `_depuis_subset` éliminaient le `(∃Ro)`
de Zermelo **parce que** le terme segment ne portait pas son ordre — leur « Ro-indépendance »,
revendiquée en docstring, était **un artefact de l'incohérence elle-même**. La réparation de la
vérité a un PRIX, et il est nommé :

> **PERTE MESURÉE : « Zermelo seul » ne suffit plus** pour ces deux réductions — il donne un bon
> ordre, pas la réalisation des segments *par* ce bon ordre. Les hypothèses sont restaurées en
> forme **Ro-close** `(∃Ro)(bo ∧ réalisation)` (l'idiome déjà présent : `hyp_transport_ordinal`,
> E III.24). L'ancien énoncé, strictement plus fort, n'était prouvable que via le défaut.

**Le capstone `bon_ordre_intervalle_close` est INTACT** (CLOS, 0 hyp — il décharge sa garde AVANT
de généraliser). Rayon de casse borné par grep : aucun consommateur externe des deux énoncés
affaiblis.

C'est la **première instance mesurée** dans cette campagne du phénomène symétrique de la vacuité :
un théorème qui *meurt avec* le défaut qui le rendait possible. Pour l'article : la meilleure preuve
que la contradiction était VIVANTE, pas théorique (renforce C6).

Reste (cosmétique, coût d'un cycle de tests) : ~41 locaux morts `R = _graphe_R(G)`.
**Suite intégrale post-fix relancée cette nuit** — la photo propre pour l'article.

## ▶ (archivé) 1ᵉʳ août — MIGRATION `seg_ext` : code FAIT, vérification en cours

L'agent Opus est mort sur la limite de session **après l'essentiel**. État MESURÉ par le directeur
(1ᵉʳ août, 19h52) :

```
segment_extremite(G, e, x)          le terme PORTE son graphe          ✓
axiome_segment_extremite()          ∀-clos, libres = []               ✓
theorie_segment_extremite()         SANS paramètre — 1 seul axiome     ✓
deux jeux de liants                 alpha_egal = True (1 classe α)     ✓
collecte intégrale                  3 909 tests, 0 erreur d'import     ✓
theorie_ensembles()                 22                                 ✓
D1 (la contradiction)               STRUCTURELLEMENT MORTE — plus de fabrique paramétrique,
                                    plus de moyen de frapper deux axiomes sur un même terme
```

22 fichiers migrés après la source (III.2 segments/trichotomie/C60, III.4 réalisation-segment,
III.5 pont, III.6 C62/ordinaux + 8 fichiers de test). Manifestes régénérés : 2 033 notions,
0 marqueur non conforme.

**Reste : la preuve par les tests.** Suite INTÉGRALE relancée par zones (leçon des runs tués à
50 min), ~5 h à `-n 4`. Verdict `N passed / M failed` au retour. La leçon d'agent : un agent mort
après avoir écrit son travail n'a rien perdu — **mesurer l'état avant de relancer** (la reprise
aurait coûté des tokens pour rien, la vérification est du ressort du directeur).

## ▶ (précédent) TICK 31 juil — **MIGRATION `seg_ext` LANCÉE** — un seul agent Opus, séquentiel

**Changement de régime (feedback Karl, mémoire `sobriete-tokens-agents`)** : le fan-out de
cartographie à 6 agents max est mort sur la limite hebdomadaire (~266k tokens, 0 résultat). La
carto a été refaite **INLINE par le directeur pour un appel Bash** : signature réparée **validée
par sonde** (le terme porte G, libres = {G,E,x} ; axiome ∀-clos, libres = [] ; deux clôtures
α-égales ⇒ **1 seule classe α** ; `equiv` natif), 37 modules consommateurs mesurés (pas 43),
15 fichiers de test, **aucun entièrement faible** (filtre grossier, tri fin à faire).

Migration en cours : **un agent Opus (grille : assemblage = 4/6)**, ordre imposé source → 5 sites
instanciateurs → III.2 → III.4/5/6/7 → III.3.6 → tests. Danger n°1 inscrit au brief : **toute
conclusion contenant seg_ext change de forme** (un argument G en plus) — cibles à RECONSTRUIRE,
jamais à recopier. Obligation finale : re-jouer la sonde D1 et prouver que la contradiction n'est
**plus** dérivable.

## ⏸ (archivé — le fan-out prévu ci-dessous est mort sur la limite hebdo, remplacé par la carto inline ci-dessus)
### CARTOGRAPHIE DE LA RÉPARATION `seg_ext` (lecture seule)

**Rien d'autre ne compte** : une théorie contradictoire rend tous les autres chantiers sans objet.
Ce tick passe donc AVANT la factorielle, avant H2/H3, avant le recâblage de `regle_factorielle`.

Playbook du précédent `AXIOME_PRODUIT_FAM` (qui a marché) : **cartographie en lecture seule d'abord,
migration séquentielle ensuite**. 5 zones en parallèle + 1 synthèse :

| zone | objet |
|---|---|
| 1 source | le texte Python EXACT des 3 fonctions réparées, prouvé par `exec` dans une copie de l'espace de noms réel |
| 2 sites | les 5 constructions de théorie + 1 test : quel R leur est passé (variable libre ? terme clos ?) |
| 3 consommateurs | 43 modules — lesquels cassent à la **signature** (bruyant) vs à la **valeur** (dérive SILENCIEUSE) |
| 4 tests | 16 modules — **combien n'assertent que `est_clos` ou un `len`** et laisseraient passer une dérive |
| 5 autres | les 20 autres constructeurs : tri **VIVANT** (a un axiome caractérisant ⇒ contradiction tentée) / **DORMANT** |

**Le livrable de la zone 4 est un actif à part entière** : la liste des tests FAIBLES mesure la
qualité du filet, pas seulement son étendue.

⚠️ **Règle anti-optimisme inscrite au brief** : `AXIOME_PRODUIT_FAM` avait été estimé 1 h 30–3 h et
a pris **6 h 15**. Le coût dominant n'est pas l'édition, ce sont les tests.

## 🔴🔴🔴 27 juil — **INCOHÉRENCE DÉMONTRÉE** : un terme qui ne porte pas son paramètre. 21 constructeurs concernés.

**Ce n'est PAS un défaut de fidélité. C'est une INCONSISTANCE** — de ces axiomes on dérive ⊥, donc
tout. Vérifié **par le directeur lui-même**, indépendamment de l'agent :

```
axiome_segment_extremite(R₁) vs (R₂)   :  ==False , alpha_egal False   → DISTINCTS
segment_extremite(R₁,E,x) == (R₂,E,x)  :  True                         → MÊME TERME
theorie(...).nom                        :  'Segment-extremite' pour les DEUX
noyau :  th1 hyps=0 est_clos=True   /   th2 hyps=0 est_clos=True
```

Le terme rendu est `app("seg_ext", e, x)` : **zéro argument d'ordre**, `libres = {e,x}`, **R a
disparu**. L'axiome n'a **aucune garde** : R est un callable Python quelconque, jamais vérifié comme
ordre ni même comme relation sur E.

**Dérivation de l'absurde (D1), par gestes PURS du noyau, 0 hypothèse :**
avec `a₀=∅`, `b₀={∅}`, `E₀={∅,{∅}}`, `G_UN={(a₀,b₀)}`, `G_NUL=∅` —
les deux axiomes instanciés en `(E₀,b₀,a₀)` parlent du **même** `seg_ext(E₀,b₀)` ;
l'un donne `a₀ ∈ seg_ext(E₀,b₀)`, l'autre en tire `(a₀,b₀) ∈ ∅` ; or `⊢ ¬((a₀,b₀) ∈ ∅)`.
⇒ **`⊢ ∅ ∈ ∅`, CLOS.** `Ax(D1)` = 4 formules / 2 théories, dont 2 « Segment-extremite ».

### ⚠️ POURQUOI UNE GARDE NE RÉPARE RIEN — la leçon centrale

Mettre l'axiome sous hypothèse « R est un ordre sur E » **ne change rien** : deux ordres
**différents** sur le même E (un ordre et son opposé) satisfont tous deux la garde et se
contredisent encore.

> **« Axiome calé sur le Résumé » et « terme qui ne porte pas son paramètre » sont DEUX fautes
> distinctes. La seconde ne se soigne PAS par une hypothèse.**

C'est la différence avec le précédent de l'intersection (26 juil.) : là, l'axiome avait perdu une
**condition**, et la forme de sélection la rendait. Ici l'axiome a perdu un **paramètre**, et aucune
condition ne répare un terme qui n'a pas de case pour lui.

**RÉPARATION (une seule modification, ferme les deux défauts) :**
1. `segment_extremite(G,e,x)` prend le graphe en **TERME** → `app("seg_ext", G, e, x)` ;
2. `axiome_segment_extremite()` devient une formule **CLOSE, ∀-close sur G AUSSI** →
   les 4 classes α s'effondrent en **UNE** ; plus de variable libre ⇒ plus de **constante** ⇒
   **C27 redevient sain** et la seconde dérivation (D2) tombe avec la première.
   *Le point 2 est le vrai correctif ; le point 1 est ce qui le rend possible.*

### 🔴 LE DÉFAUT N'EST PAS PROPRE À `seg_ext` — passe AST sur tout `bourbaki/`

**21 constructeurs de terme perdent au moins un paramètre, dont 11 perdent le paramètre
d'ORDRE/RELATION.** Notamment :

| terme | paramètre perdu | statut |
|---|---|---|
| `seg_ext(e,x)` | l'ordre R | **CONTRADICTION DÉRIVÉE** |
| `interv_ff(e,a,b)` | le graphe G | **CONTRADICTION DÉRIVÉE** |
| `graphe_terme(A,T)` | le LIANT de T | 20 formules dans le capstone |
| `c60_Dfam_real(e,x,V)` | la RÈGLE vh | 5 formules ; socle C60 |
| `A_contre_exemple(n0)` | le PRÉDICAT P | socle **C61** |
| `A_contre_ex_transfinie(e)` | P | socle **C59/C60** |
| `interv_fo/of/igo/ido`, `ens_classes_obj` | R | vecteurs |

**NON fautifs, vérifiés** : `intervalle_entiers`, `restriction`, `valeur_famille`,
`terme_plus_grand` (le τ explicite **porte** l'ordre — c'est le bon patron).

**PORTÉE** : 5 sites construisent la théorie, 32 appels aux instanciateurs, **43 modules de
`bourbaki/` et 16 de `tests/`**. Toute la chaîne III.2 (segments, C59-C60, trichotomie), III.3.6,
III.4, III.5.8, III.6, III.7 passe par là.

### 🧨 DEUX DÉFAUTS SÉPARÉS, révélés par le même vecteur

1. **`N.generalisation` accepte de généraliser sur une CONSTANTE** d'une théorie dédiée (variable
   libre dans son axiome) — violation de la condition de bord de **C27**, que la docstring du noyau
   signale sans pouvoir la vérifier. Cause racine **identique à M1** : `Theoreme` ne porte aucune
   trace de sa théorie.
2. `axiome_intervalle_entiers('u','v','w')` **n'est pas α-égal** à `axiome_intervalle_entiers()` :
   les liants heurtent des liants internes ⇒ deux formules CLOSES α-distinctes sous le même nom.

### ✅ Nuance d'honnêteté, mesurée

Les 4 formules **effectivement consommées** par le capstone **ne se contredisent pas entre elles**
(trois portent un graphe variable, une un terme clos ; les séparer exige un pas de C27).
⇒ `max_domaine_restriction_succ` **n'est pas rendu faux aujourd'hui** par ses propres axiomes.
**C'est la THÉORIE dans laquelle il vit qui est contradictoire**, pas ce théorème-là.

### ✅ Et les 6 failles FRAGILE de B3 sont réparées

`bo` **déchargé** : capstone **4 → 3 hypothèses** (`BO in hypotheses` False ; le piège
variables/termes-clos n'a pas mordu, `dom_restriction_seg` était déjà appelé aux termes clos).
Fichier éclaté 340 → **250 + 207** (docstrings enrichies, pas rognées). Test corrigé : les 3 résidus
C62 sont désormais épinglés **par identité**, plus par `len`. `Crit.62` → `Crit.C62` (**9** sites,
le brief en annonçait 6). Glose recomptée sur PNG. **Dossier : 60 passed, 0 échec. `theorie` = 22.**



## ✅✅✅ 27 juil (nuit) — **`AXIOME_PRODUIT_FAM` RÉPARÉ** — le corpus ne réfute plus le livre

**L'axiome porte de nouveau la forme du livre** `F ⊂ I × ⋃_{ι∈I} X_ι`, en TÊTE (placement tranché
par mesure : 18 tests cassés en tête contre 33 en queue). **Remplacement, pas ajout — le compte
reste 22.** Vérifié par le directeur, indépendamment de l'agent, par égalité EXACTE à une cible
reconstruite à la main :

```
CORPS RÉPARÉ == CIBLE DU LIVRE ?        True    (3890 / 3890 caractères)
CORPS == ANCIENNE FORME (3 conjoints) ? False
theorie_ensembles()                     22      (avant ET après)
```

### 🎯 LE GAIN — H2 et H3 sont devenues des THÉORÈMES

`hypothese_graphes_total` et `hypothese_graphes_partiel`, qu'on traînait comme hypothèses, sont
maintenant **DÉMONTRABLES et CLOSES** (mesuré hors module : `(True, True)` pour les deux, à
22 axiomes). C'est exactement ce que la réparation promettait.

### NON-RÉGRESSION — la suite ENTIÈRE a tourné sous l'axiome réparé

| zone | résultat | durée |
|---|---|---|
| zones migrées (agent) | **2 779 passed, 0 failed** | — |
| `iii_2_bien_ordonnes` | **612 passed** | 23:40 |
| `iii_6_infinis` | **307 passed** | 1:34:30 |
| `iii_5_calcul_entiers` | **195 passed** | 1:12:56 |

**ZÉRO échec, nulle part.** Collecte **3 850 → 3 865** (+15) : le total MONTE — aucune suite
n'a été faite taire. Manifestes régénérés : **2 017 notions**, 0 fichier à caler.

⏱ **FAIT OPÉRATIONNEL À RETENIR : `pytest-xdist` FONCTIONNE (`-n 4`).** La suite complète coûte
**~5 h même à 4 workers**. Les runs longs sont TUÉS par l'environnement vers 50-57 min ⇒ **toujours
découper par zone** et conserver les résultats partiels au fil de l'eau.

### ÉTAPE 0 — la mort obligatoire, confirmée

5 fonctions supprimées de `ensembles_produit_famille_graphe.py` : `singleton_vide_dans_produit_vide`,
`produit_vide_n_est_pas_singleton_enonce`, `produit_vide_n_est_pas_singleton`,
`hypothese_graphes_produit_vide`, `hypothese_graphes_produit_vide_refutee` (+3 tests ; `.bak` dans
`scratchpad/bak_produitfam/`). `grep` sur tout le dépôt : **6 hits, tous en commentaire, aucun `def`**.
⇒ il ne subsiste NULLE PART de théorème réfutant H-graphe. **Pas d'incohérence.** Nouveau théorème
en remplacement : `singleton_vide_hors_produit_vide` ⊢ ¬({∅} ∈ ∏(u,∅)), CLOS.

### QUATRE DÉRIVES SILENCIEUSES attrapées (classe E1)

`produit_fonctionnel`, `_fonctionnel_imp`, `membre_but`, `membre_produit_famille/partiel`.
⚠️ **Le cas qui justifie toute la doctrine** : `membre_but` se construisait encore, restait CLOS, et
son test **n'assertait que `est_clos`** — il serait passé au vert avec une conclusion changée
(6 908 → 8 592 caractères). Réécrit en `test_membre_but_clos_et_exact`, cible reconstruite HORS du
module. Deux autres tests ont **échoué en ROUGE** à la réparation : preuve qu'ils verrouillaient.
Vérifiés INCHANGÉS par mesure (pas par supposition) : `produit_domaine`, `projection_dans_facteur`,
`_domaine_imp`, `restriction_dans_produit_partiel`.

### Fichier hors plan, justifié

`ii_5_definitions/ensembles_produit_ecriture.py` : les 11 sites ÉCRITURE ont la MÊME forme, et le
conjoint de tête **n'est pas transportable** (⋃Y_ι ≠ ⋃X_ι) — il faut le refaire au pivot à chaque
fois. Écrit 11 fois puis factorisé. Séparé des briques pour la limite de 300 l. Contient le SEUL
endroit du dépôt où les chemins d'accès `g,g,g / g,g,d / g,d / d` sont écrits.

### ✅ TICK CLOS (27 juil, matin) — `0! = 1` PAR LA DÉF. 2, **SANS RÉSIDU** — vérifié par un adversaire

**Trois théorèmes, tous CLOS à 0 hypothèse :**

| théorème | énoncé | fichier |
|---|---|---|
| `produit_famille_vide_est_singleton_vide` | ⊢ ∏(u,∅) = {∅}  (E II.32 L.22-23) | `ii_5_definitions/ensembles_produit_famille_vide.py` (NEUF, 206 l.) |
| `produit_cardinal_vide` | ⊢ Card ∏(u,∅) = 1 | `iii_3_6_familles/ensembles_famille_successeurs.py` |
| `factorielle_def2_zero` | ⊢ **0! = 1** sur le TERME RÉEL de la Déf. 2 (E III.41 L.30) | idem |

**La preuve révoquée hier est réhabilitée par déchargement, pas par contournement.** Mesuré :
l'hypothèse `H = (∀G)(G ∈ ∏(u,∅) ⇒ Gr(G))`, qui rendait le résultat VACUEUX, est **aujourd'hui
littéralement un théorème CLOS** (instance de `produit_graphe`). `H est-il un THÉORÈME ? True,
clos=True, hyps=0`.

**VERDICT ADVERSE : SOLIDE.** Quatre attaques menées par un agent distinct dont la mission était de
démolir :
- **A1 vacuité** — sans objet (0 hypothèse), donc version FORTE à la place : le produit d'index vide
  est prouvé **habité** (⊢ ∅ ∈ ∏(u,∅), CLOS) — l'égalité n'est pas entre deux termes dégénérés.
  Les 5 théorèmes du « coin dangereux » sont CLOS simultanément : aucun bas.
- **A2 dérive** — aucune. Cibles reconstruites À LA MAIN hors des modules, comparées par `==`
  SYNTAXIQUE (`alpha_egal` jamais utilisé comme critère). Vérifié aussi que le « 1 » est le UN
  canonique (`successeur(ZERO)`), pas `Card({∅})`.
- **A3 dette** — voir ci-dessous, **c'est là que le résultat est inégal**.
- **A4 mutants** — **14 mutants injectés, 14 TUÉS**, aucun kill par `TypeError` (un mutant qui meurt
  sur TypeError est un mutant CASSÉ, son kill ne prouve rien). Le mutant qui compte :
  `produit_cardinal_vide(famille_successeurs(0))` — théorème VRAI et CLOS, qui ne diffère de `0!=1`
  que par l'indice écrit `∅` au lieu de `seg(ℕ,0)`. Tué.

**⚖️ LA DETTE, PUBLIÉE (mesure M1, un process FRAIS par cible, en 1ʳᵉ position) :**

| théorème | Ax(D) | étrangers | dette | `invariant_reel` |
|---|---:|---:|---:|:--:|
| `produit_famille_vide_est_singleton_vide` | 7 | **0** | **0** | ✅ **VRAI** |
| `produit_cardinal_vide` | 14 | 2 (`Graphe-terme`) | 2 | ❌ |
| `factorielle_def2_zero` | 70 | **55, de 27 théories** | 55 | ❌ |

⇒ **le théorème du livre E II.32 est réellement clos sous les 22 SEULS.** Les deux autres héritent :
`factorielle_def2_zero` traîne les 4 Zorn, les 4 Zermelo, les 3 Bourbaki-Witt, `Infini(A4)`,
Knaster-Tarski… — dette **héritée** de la construction de ℕ, pas contractée ici.

**Tests** : 6 passed (fichier ii_5) · 8 passed en 333 s (fichier iii_3_6) · 43 passed (dossier ii_5)
· 35 passed en 618 s (dossier iii_3_6) · zone M1 60 passed. Collecte **3 865 → 3 875** (+10, soit
exactement les tests ajoutés) : **le total MONTE**. Diff contre les `.bak` : que des AJOUTS, aucun
test préexistant affaibli. Manifestes : **2 020 notions**, 0 fichier à caler.

**DEUX AFFIRMATIONS FAUSSES DU DÉPÔT, CORRIGÉES par le directeur après le verdict :**
1. `test_produit_cardinal_vide` disait « **SOUS LES 22 AXIOMES SEULS** » — **faux, mesuré** :
   12 `Ensembles` + 2 `Graphe-terme`. Docstring réécrite avec la mesure.
2. `singleton_vide_hors_produit_vide` calait E II.32 en **L.30-33** ; recomptage sur le PNG (p.83,
   en-tête confirmé) : la phrase est en **L.22-23**. Marqueur corrigé, les deux modules concordent.

⚠️ **PIÈGE MESURÉ** : « pour u QUELCONQUE » est en réalité « pour tout u dont aucun nom libre n'est
parmi **13 noms réservés** » — `PFV(var('u'))` ou `PFV(var('i'))` lève `AssertionError`. Échec
BRUYANT, soundness intacte, mais la docstring surénonce.

⚠️ **`ensembles_produit_ecriture.py` n'a TOUJOURS aucun test miroir** — et c'est le seul endroit du
dépôt où les chemins d'accès `g,g,g / g,g,d / g,d / d` sont écrits. Dette de test à combler.

**❌ NE PAS DIRE « la boucle Déf.2 est fermée ».** Le pas de récurrence
`factorielle_def2_recursion` porte toujours `{n ∈ ℕ, H2, H3, HW, HN}` (mesuré par grep sur ses
asserts L.332-335). Le livrable est **le cas de base seul**. HW/HN restent **INDÉPENDANTES**.

### ⚠️ TICK CLOS (27 juil) — **M([0,n]) = n POSÉ**, mais un ÉCART DE FIDÉLITÉ NOMMÉ : sup ≠ max

**Ce qui est construit** (verdict adverse : **SOLIDE**, 11 mutants injectés, 11 tués, 35 vérifications
de dérive, 0 échec) :

| théorème | énoncé | hyps |
|---|---|---|
| `terme_plus_grand_vaut` | `{pge(R,A,a), antisym(R,A)}` ⊢ M_R(A) = a | 2 — **Ax(D) = ∅, 0 axiome** |
| `antisymetrie_ordre_sur_intervalle` | ⊢ antisym(≤, [0,n]) | **0, CLOS** |
| `max_intervalle_vaut_n` | `{est_cardinal(n)}` ⊢ **M([0,n]) = n** | 1 |
| `max_intervalle_vaut_n_entier` | `{est_entier(n)}` ⊢ M([0,n]) = n — **la forme du livre** | 1 |

`terme_plus_grand_vaut` ne consomme **aucun axiome** : théorie de l'ordre pure. C'est le genre de
brique qui se réutilise partout.

### 🔴 L'ÉCART DE FIDÉLITÉ — à ne pas enterrer

Bourbaki écrit (E III.46 L.28-29, **relu en PNG par le directeur**, en-tête confirmé) :

> « Soit M(u) la **borne supérieure** de D(u) dans **N**. »

et sa **note 2** (L.36-38) précise que ce sup « désigne un terme du langage formalisé de la forme
τ_x(R{x}) » gardant un sens **même pour un ensemble non majoré**.

**Le module explicite le τ du PLUS GRAND ÉLÉMENT — un AUTRE terme**, qui ne coïncide avec le sup
que lorsque le maximum **existe**. Sur `[0,n]` (borné, non vide) ils coïncident, donc l'instance
est juste ; **le terme générique, non**. Le module nomme l'écart sur 15 lignes — c'est honnête,
et c'est la raison pour laquelle ce tick est **CLOS_MODULO** et non CLOS.

### 🆕 RÉSIDU B3 — le pont de domaine, la vraie brique suivante

C63 applique M au domaine de la **restriction** `f|[0,n[` — intervalle **SEMI-OUVERT** — alors que
le théorème porte sur le **fermé** `[0,n]`. Sans ce pont, `M(D u)` ne se réduit pas.
**Route recommandée : énoncer au point `succ(k)`** (le domaine est alors `[0,k]` et M = k
directement). ⚠️ La route « n−1 » est un **cul-de-sac connu** : `difference_entiers` est un terme
**OPAQUE**, sans axiome caractérisant.

⚠️ `regle_factorielle` **n'est PAS recâblée** (interdit par le brief) : cela change une conclusion
publique. Chantier séparé.

### 🧹 QUATRE MENSONGES DU DÉPÔT, CORRIGÉS (recomptés par le directeur sur les PNG)

1. **`E III.8 L.30-32` pour la Déf. 4 était FAUX** — la Déf. 4 est en **L.26-27** ; L.30-32 tombait
   sur le paragraphe suivant. La valeur fausse avait été **RECOPIÉE dans 5 sites** :
   *un marqueur erroné se propage par copie, c'est son mode de nuisance principal.*
2. **Conflit de marqueurs** : la même phrase de E III.46 était citée `L.14-15` et `L.15-16`.
   Recompté : **L.15-16** (L.14 est le titre de section). Les deux concordent désormais.
3. **`AXIOME_INTERV_ENT` cité 3 fois, DÉFINI NULLE PART** — symbole jamais codé, exactement le
   motif du résidu-fantôme. Le vrai nom est `axiome_intervalle_entiers`. Et c'est l'axiome dont
   **tout le capstone dépend**.
4. **`iii_1_7_plus_grand_plus_petit/__init__.py`** titrait « Résultats formalisés (…, **CLOS**) »
   alors que `terme_plus_grand_vaut` porte 2 hypothèses. ⇒ **règle : ne jamais écrire un statut
   COLLECTIF dans un en-tête de dossier**, il se périme au premier ajout.

**Tests** : 36 passed (2 fichiers) · 20 passed (`iii_1_7`) · 42 passed en 19 min 31 s
(`iii_5_intervalles_comptage`, `-n 4`). Collecte **3 875 → 3 911** (+36 = exactement les tests
ajoutés) : le total MONTE. `theorie_ensembles()` = 22 avant/après, mesuré dans 5 process.
⚠️ `iii_1_relations_ordre` est à **EXACTEMENT 10 entrées — SATURÉ**.

### ⚠️ TICK B3 (27 juil) — pont POSÉ, verdict adverse **FRAGILE**, et un **VECTEUR D'INCOHÉRENCE** trouvé

**Le pont est construit** (`iii_5_intervalles_comptage/ensembles_pont_domaine_iii5.py`) :

```
{k ∈ ℕ}                    ⊢ seg(≤,ℕ,succ k) = [0,k]          ← LE PONT (semi-ouvert = fermé)
{bo, ebf, rc, k ∈ ℕ}       ⊢ dom( f|seg(ℕ,succ k) ) = [0,k]
{bo, ebf, rc, k ∈ ℕ}       ⊢ M( dom( f|seg(ℕ,succ k) ) ) = k   ← LE LIVRABLE
                           ⊢ downward-closure de Fini (CLOS, 0 hyp)
```

La route `succ(k)` a bien évité la soustraction. Le mutant « oubli du pont » (membre droit
semi-ouvert) est **tué** par le test — c'est le piège nommé d'avance, et il mord.

**Recâblage mesuré à UNE ligne** : `ensembles_factorielle_existence.py:156`,
`prev = E.valeur(vu, Du)` → `prev = E.valeur(vu, terme_plus_grand(inf_egal_card, Du, "m", "x"))`.
Et la conclusion du pont **EST littéralement** l'hypothèse honnête `h_seg` de
`factorielle_succ_fallback` — à condition d'instancier à `e := ℕ` / `G := G_ordre_NN()`
(aux défauts « Enat »/« Gle » les formules DIFFÈRENT : c'est le piège VARIABLES vs TERMES CLOS,
déjà payé le 26 juil).

### 🔴🔴 LE VECTEUR D'INCOHÉRENCE — mesuré par le directeur

```
segment_extremite(R1,e,x) == segment_extremite(R2,e,x)  →  True
terme rendu : app("seg_ext", e, x)   —   0 argument d'ordre
libres : {e, x}          ← R A DISPARU
```

**Le terme « segment d'extrémité » ne porte pas sa relation d'ordre.** Deux ordres différents
produisent **le même terme**. Or la dérivation du capstone consomme **4 formules d'axiome
α-DISTINCTES** de la théorie `Segment-extremite` : quatre axiomes qui caractérisent **le même
terme**. Si deux d'entre eux parlent d'ordres différents, la théorie est **contradictoire**.

C'est **exactement la forme** du défaut de l'intersection du 26 juil : un axiome qui caractérise un
terme sans porter la condition qui le rend légitime. ⇒ **Enquête lancée** : tenter de dériver
l'absurde, et passer les autres termes au même crible (`intervalle_entiers`, `restriction`,
`graphe_terme`, `valeur_famille` portent-ils tous leurs paramètres ?).

### FAILLES FRAGILE — en réparation

1. **`bo` n'est PAS un résidu** : `bo_graphe_NN()` le démontre CLOS, 0 hypothèse. Le capstone porte
   donc une **hypothèse gratuite** — « aussi malhonnête qu'un test qui ment ». À décharger : 4 → 3.
2. **Docstring module FAUSSE** : « 31 théories dédiées à **1 axiome** » — mesure : **65 formules**
   étrangères sous 31 noms (Graphe-terme 20, Graphe-induit 7, Dfam-real 5, Segment-extremite 4…).
3. **Docstring de test FAUSSE** : promet l'égalité exacte de frozenset, fait `len(hyps) == 4`
   ⇒ les 3 résidus C62 ne sont épinglés par identité **nulle part**. C'est le TEST qu'on corrige.
4. **340 lignes** (336 hors `@livre`) : convention franchie.
5. `Crit.62` au lieu de `Crit.C62` (6 autres sites) — même notion sous deux clés, et
   `gen_livre_manifestes` ne le signale pas.
6. Glose `@livre` qui **sur-interprète** : attribue à L.12-13 une identification qui n'y est pas.

### ▶ APRÈS — recâbler `regle_factorielle` (une ligne, mais ~8 énoncés publics changent)

**Pourquoi celui-là plutôt que le déchargement de H2/H3** : décharger H2/H3 est mécanique et ne fait
avancer **aucun résultat du livre**. `sup_borne` est le **dernier verrou** avant l'équation du
successeur de la factorielle — et c'est un écart de FIDÉLITÉ, la faute la plus grave pour ce projet.

**Le défaut, mesuré (26 juil)** : le plus grand élément du domaine d'une fonction partielle n'existe
**sous aucun nom** — `[n for n in dir(E) if 'sup' in n or 'borne' in n] == []`, et rien hors du
§III.1.7 qui ne traite que le plus PETIT. Faute de quoi `regle_factorielle` se rabat sur
`prev := valeur(u, dom u)` (u appliquée à son **propre domaine**, sémantiquement vide) au lieu de
`u(n−1)`. **Ce que le dépôt démontre réellement est donc**

```
f(succ n) = (n+2) · valeur(u, [0,n])          et NON   (n+1)! = n! · (n+1)
```

⇒ **le C63 formalisé n'est PAS la règle d'itération de Bourbaki.** Référence : E III.46, **note 2**.

**Cible minimale qui débloque** (visée en priorité, elle suffit) : ⊢ `M(intervalle(0,n)) = n` —
arithmétique finie, bien plus accessible qu'une théorie générale de la borne supérieure.
⚠️ Dans un bien-ordre, une partie n'a **pas toujours** de plus grand élément : il faut la finitude
ou un majorant **atteint**. Ne pas promettre plus que ce qui est démontré, et NOMMER l'hypothèse.

⚠️ **`regle_factorielle` n'est PAS recâblée dans ce tick** : cela change une conclusion **publique**
consommée ailleurs ⇒ chantier SÉPARÉ avec ses propres tests. Ce tick pose la brique et la teste.

Forme : construction, puis **vérificateur ADVERSE** (vacuité / dérive / dette M1 / mutants /
fidélité PDF). Attaque principale attendue : la **dérive** — « plus grand » a-t-il glissé vers
« plus petit », « majorant », ou « borne supérieure non atteinte » ?

### ⏭ EN ATTENTE — décharger H2/H3 (mécanique, mais change des énoncés publics)

**Pourquoi celui-là et pas le déchargement de H2/H3 :** c'est le résultat que la réparation vient
d'ouvrir, et c'est un **résultat du livre** (E II.32 + Déf. 2), pas de l'outillage.

Route : la preuve **révoquée** hier soir (`scratchpad/REVOQUE_ensembles_factorielle_def2_zero.py`)
avait un **squelette correct** ; seule son hypothèse `H = (∀G)(G ∈ ∏(u,∅) ⇒ Gr(G))` était réfutable,
d'où la vacuité. **Cette hypothèse est aujourd'hui le théorème `produit_graphe`, CLOS.** Le chantier
se réduit donc à : reprendre le squelette et **décharger H au lieu de la supposer**.

Briques visées : `produit_famille_vide_est_singleton_vide` ⊢ ∏(u,∅) = {∅} (moitié (ii) —
« tout élément du produit est ∅ » — via `produit_graphe` + `dom(F)=∅` + extensionnalité des graphes :
c'est là que la réparation paie, cette moitié était indémontrable sans le conjoint de tête), puis
`Card({∅}) = 1`, puis `factorielle_def2(0) = 1`.

⚠️ **Piège de lecture déjà payé** : `{∅}` (le SINGLETON) n'est pas élément du produit — c'est `∅`
(la FONCTION VIDE) qui l'est. `singleton_vide_hors_produit_vide` dit la première chose, pas la seconde.

⚠️ **Ne PAS annoncer « la boucle Déf.2 est fermée »** — cette phrase exacte figure déjà au journal
comme une affirmation FAUSSE. Le pas de récurrence porte encore HW/HN, **INDÉPENDANTES**.

Forme : construction, puis **vérificateur ADVERSE** distinct (vacuité / dérive / dette M1 / les
mutants tuent-ils ?). C'est cette passe-là qui a démasqué la vacuité hier.

### ⏭ SUITE — chantier SÉPARÉ, ne pas mélanger

Décharger H2/H3 dans `ensembles_produit_adjonction_bij.py` (instancier `produit_graphe`) : mécanique,
mais **change une conclusion publique** ⇒ ses propres tests. Idem RISQUE 8 (alléger
`extensionnalite_produit` de 5 à 3 conjoints) : correct mathématiquement, casse 3 tests d'égalité
exacte, **chantier à part**.
Non mesuré : `invariant_reel` sur les capstones APRÈS réparation. Reste ouvert : `sup_borne` / M(D u)
(sans quoi l'équation du successeur n'est pas celle du livre) et le pont `fam ↔ valeur` (INDÉPENDANT).



## 🔴🔴 26 juil (nuit, tick M1) — **MESURÉ** : `n_bien_ordonne`, annoncé « CLOS, 0 hypothèse », consomme **53 axiomes étrangers**

M1 est construit ET a tourné. `outils_ia/verite/` : `axiomes_consommes.py`, `classer_residu.py`,
`echec.py` — **58 tests verts en 0,55 s**, `theorie_ensembles()` = 22 avant/après, les DEUX
implémentations de `axiome` surveillées (`noyau.py` ET `noyau_abrege.py` — n'en observer qu'une
serait un faux négatif en puissance).

**LA MESURE** (un process FRAIS par capstone, `run1` = premier appel du process) :

| capstone | hyps déclarées | Ax(D) | **étrangers** | **Dette** | invariant réel |
|---|---:|---:|---:|---:|:--:|
| `n_bien_ordonne` | **0** | 67 | **53** | **53** | ❌ |
| `factorielle_caracterisation` | 10 | 72 | 57 | 67 | ❌ |
| `existence_fonction_restriction_c62` | 4 | 17 | 9 | 13 | ❌ |
| `factorielle_c62_entier` | 7 | 97 | **82** | **89** | ❌ |

**Aucun capstone ne vérifie `Ax(D) ⊆ {T₀} × A_T₀`.** Un théorème annoncé à *zéro hypothèse* a une
dette réelle de **53 formules**. L'invariant « 22 » était vrai à chaque instant et n'a jamais rien
dit de tout cela.

**LA MÉMOÏSATION FAIT SOUS-COMPTER — mesuré, pas supposé.** Deuxième appel dans le même process :
`n_bien_ordonne` passe de **53 → 20 étrangers** (−62 %), `factorielle_c62_entier` de 82 → 66.
⇒ **M1 n'est valide qu'en PREMIER appel d'un process frais.** Toute mesure faite en second est un
sous-comptage silencieux. (Seul `existence_fonction_restriction_c62`, qui ne déclenche pas
`N_existe`, donne run1 == run2.)

**⚠️ CE QUE LA MESURE NE DIT PAS ENCORE.** « 53 axiomes étrangers » ≠ « 53 postulats illégitimes ».
L'inventaire (`scratchpad/theories.json`) donne **66 théories dédiées distinctes**, et leurs
docstrings les décrivent en majorité comme des **instances de schémas** (S8, C54) ou des **sélections
définissantes** — procédés légitimes. Mais ce sont des *docstrings*, et la leçon du jour est
qu'elles mentent. **La classification reste à FAIRE, une par une** ; elle est désormais finie et
énumérée. À vérifier en premier : **`Infini(A4)` — « Théorie contenant l'axiome A4 de l'infini »**,
un axiome authentique de Bourbaki qui vit **hors** des 22.

**DEUX CORRECTIONS aux définitions posées plus tôt cette nuit** (les deux mesurées) :
1. Le critère syntaxique d'indépendance **n'est PAS suffisant**. Mesure :
   `symboles_libres(bo(≤,ℕ)) = {'G_ordre_NN'}` — non vide — alors que `bo_graphe_NN()` la démontre
   **close à 0 hypothèse**. Le critère seul aurait fabriqué un **septième faux mur**. C'est un
   INDICE (un argument de réinterprétation est disponible), pas une preuve ⇒ il ne s'applique
   qu'**après** l'échec du prouveur.
2. « `fam` n'est relié à `valeur` par aucun des 22 axiomes » est **faux en occurrence** : `fam`
   figure dans **4** axiomes (RÉUNION_FAM, INTER_FAM, PRODUIT_FAM, COMPL_FAM). Le verdict
   « indépendante » sur HW/HN tient, mais le **témoin publié** est `{graphe_terme, seg_ext}`.
   L'argument correct est un argument de MODÈLE (position définissante), strictement plus fin que
   l'occurrence — et `symboles_libres` ne mesure QUE l'occurrence.

**Faille connue de `classer_residu`, refusée sciemment :** il ne mesure pas `Ax(D)` du certificat.
Un prouveur qui consomme une théorie dédiée serait classé « déchargeable » à tort — c'est une
classe **E4 (dette)**, pas un déchargement. Le couplage automatique avec `invariant_reel` a été
écarté pour cause de coût (`setprofile` ×1,5–×3 sur une preuve de 257 s).

**⏭ PROCHAIN TICK — classifier les 66 théories** en (a) instance de schéma S8/C54, (b) extension
définitionnelle conservative, (c) **vrai axiome ajouté**. Seul (c) est une dette au sens de Karl.
Commencer par `Infini(A4)`, `Dtot-C62`, `UnionFamille-C60`, `Dfam-real-C60`, `Graphe-terme`
(41 occurrences à lui seul dans `factorielle_c62_entier`).

**Deux agents perdus ce tick** : `mesure:dette` (API ENOTFOUND) et `integration` (limite de session).
Les mesures étaient déjà **sur le disque** — récupérées dans le scratchpad, rien n'a été refait.
Leçon : un agent qui meurt après avoir écrit ses résultats n'a pas perdu son travail ; **chercher
les fichiers avant de relancer**.

## 🔴 26 juil (nuit) — LE GARDE-FOU NE MESURE PAS CE QU'IL PRÉTEND MESURER

**Le fait, vérifié dans le noyau (lecture, rien modifié) :**

```python
# noyau_abrege.py:146-149
def axiome(theorie, f):
    ...
    return _t(frozenset(), f, f"axiome[{theorie.nom}]")     # ← hypothèses VIDES

Theoreme.__slots__ = ("hypotheses", "conclusion", "justification")   # ← AUCUN parent
```

Un axiome de théorie **dédiée** entre dans une preuve **sans laisser de trace** : ni dans les
hypothèses, ni dans `theorie_ensembles()` qui reste à 22. Et comme un `Theoreme` ne garde aucun lien
vers ses parents, **le DAG de dérivation est détruit à la construction** — l'information n'est
reconstructible depuis aucun objet.

Ampleur mesurée : `Theorie(` apparaît **301 fois dans 57 fichiers** (`ensembles_c60_realisation.py`
en compte 80 à lui seul, `c60_final` 29, Zorn et Zermelo 4 chacun).

⚠️ **Ce n'est PAS de la triche** — c'est un procédé établi du projet, et la justification garde
`axiome[nom]`. Mais la limite dure « rien postulé + `theorie==22` » **ne borne pas ce qui a été
supposé**. Les deux chiffres réunis ne disent rien de `Ax(D)`.

**Les six définitions posées avec Karl (elles fondent le chantier M1) :**

```
Ax(D)      := { (T, α) : la règle axiome(T,α) apparaît dans la dérivation D }
Dette(θ)   := H(θ) ∪ { α : (T,α) ∈ Ax(D), T ≠ T₀ }
« rien postulé »   ⟺  Dette(θ) = ∅
invariant CORRECT  ⟺  Ax(D) ⊆ {T₀} × A_T₀        (et NON |A_T₀| = 22)

Dechargeable(h) ⟺ A_T₀ ⊢ h      ⟹ le « mur » était FANTÔME
Refutable(h)    ⟺ A_T₀ ⊢ ¬h     ⟹ tout θ portant h est VACUEUX
Independante(h) ⟺ ni l'un ni l'autre
   critère syntaxique SUFFISANT : un symbole de h que nul axiome ne contraint ⟹ indépendante
Derive(R)       ⟺ R complète ∧ concl(R) ≠ cible        (égalité SYNTAXIQUE)
```

Application immédiate — la trichotomie **classe les trois trouvailles du jour** :

| résidu | classe | conséquence |
|---|---|---|
| `bo(≤,ℕ)` | déchargeable (0 hyp, 344 s) | mur **fantôme** |
| `𝓗` produit/∅ | **réfutable** | théorème **vacueux**, révoqué |
| `valeur_famille ↔ valeur` | **indépendante** | chantier **impossible** sans nouvelle brique |

**⏭ CHANTIER M1 OUVERT** (`outils_ia/verite/`, hors `bourbaki/` ⇒ pas de `@livre`) :
`axiomes_consommes.py` + `classer_residu.py` + `echec.py`. Observation par `sys.setprofile`
**uniquement** — `CLAUDE.md` interdit tout monkeypatch, donc on observe, on ne substitue jamais.
Décision : **M1 AVANT la réparation de `AXIOME_PRODUIT_FAM`** — un garde-fou qui ne voit pas ce
qu'il garde ne peut pas valider une migration de 162 sites.

**Vérifications du tick (faites par le directeur, pas déléguées) :** suite **fusionnée** des deux
dossiers édités *en concurrence* par deux agents frères — **83 passed en 687,06 s, 0 échec** ;
`theorie_ensembles()` = **22** ; `factorielle_c62_entier` et `existence_fonction_restriction_c62`
importent et sont dans `__all__` ; 9 entrées/dossier ; tout ≤ 300 l ; tout parse.
⚠️ Deux agents ont écrit dans le même dossier **sans isolation** : l'état fusionné n'avait été testé
par personne. À l'avenir, `isolation: 'worktree'` dès que deux agents partagent un dossier.

**Repère externe (Gaia / José Grimm, INRIA) :** la formalisation Coq de Bourbaki existe et couvre
E II + E III, exercices compris — mais elle **ne formalise pas les fondations** (τ, assemblages,
critères) : elle pose Coq + l'axiomatisation de Simpson. Raison mesurable : le « 1 » de Bourbaki
déplié fait **4 523 659 424 929 signes** (Mathias), **≈ 2,4 × 10⁵⁴** pour l'édition 1970 (Solovay).
Nos 5 min de `N_existe` sont **le même phénomène**, pas un défaut d'implémentation.
⇒ Gaia est une **carte de trous externe et fiable** (indexée sur la numérotation de Bourbaki), à
utiliser précisément parce que nos propres docs ont menti 78 fois aujourd'hui.

## ✅ 26 juil (soir) — CHANTIER 3 CLOS : le **(∃!f) de C62 sur le VRAI ℕ** (`existence_unicite_fonction_NN`), + un SECOND défaut de fidélité trouvé, + un théorème VACUEUX révoqué.

**Le capstone.** `existence_unicite_fonction_NN` est déposé dans
`iii_6_1_n_objet_existence/ensembles_ordre_NN_graphe.py` (308 l. brutes, **157 l. de code réel** ;
aucun fichier créé, dossier inchangé) :
`{essais_bien_formes(T), rule_codomain(T,V)} ⊢ (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g = f ) )` — **2 résidus**,
le bon ordre déchargé. `@livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149` (page **relue en
PNG**, en-tête `E III.46` confirmé). **10 tests verts en 499,62 s** (fichier seul), dont **3 mutants
rejetés** : substitution (prédicat à 3 conjoints), pollution (hypothèse parasite par gestes purs du
noyau), α-variante (liant existentiel renommé). `theorie_ensembles()` = 22 avant et après.

- **CE QUI MANQUAIT N'ÉTAIT ENCORE QU'UNE JOINTURE — deuxième fois en deux ticks.**
  `fonction_recursion_NN` déchargeait déjà `bo` sur l'**existence** ; le `(∃!f)` avait été clos le
  matin même. Personne n'avait appliqué le **même `_cut`** au second. Les deux moitiés dormaient au
  dépôt ; seul le joint manquait. La leçon d'hier — *greper le CAPSTONE, pas ses ingrédients* — vient
  de se vérifier une seconde fois, à 24 h d'intervalle. **En faire un réflexe d'ouverture de tick.**
- **LE POINT DUR, mesuré** : la décharge n'opère QUE si `unicite`/`existence_unicite` sont
  reconstruits à `e=ensemble_NN()`, `G=G_ordre_NN()`. Aux paramètres par défaut (`"Enat"`, `"Gle"`)
  la formule `bo` n'est ni `==` ni `alpha_egal` à ce que prouve `bo_graphe_NN` — l'écart est
  **VARIABLES vs TERMES CLOS** (9 388 vs 86 598 car.), *ni* liants, *ni* callable-vs-graphe.
  Reconstruite à ℕ, l'égalité est **syntaxiquement exacte** ⇒ modus ponens direct, **sans**
  `alpha_bridge`. Diagnostiquer un désaccord de formules par la TAILLE avant de soupçonner les liants.
- **RÉSIDU HONNÊTE conservé** : ce `(∃!f)` est au niveau **VALEUR-RÈGLE** `f(z)=T(z)`. Au niveau
  **LIVRE** `f(z)=T{f|seg z}` l'unicité n'est pas assemblable ainsi (récurrence transfinie sur la
  coïncidence `g|seg x = f|seg x`). Le qualificatif reste obligatoire.

**DEUX MURS DÉCLARÉS QUI N'EXISTAIENT PAS** (sondes croisées, chaque verdict re-mesuré par moi) :
- **(R-pivot)** prescrivait « threader un BUNDLE de témoins frais — 8 fonctions DÉPOSÉES sur 6
  fichiers ». **Faux** : `extension_un_pas_fonctionnelle` avec les témoins **par défaut**, sur le vrai
  graphe τ-lourd, construit proprement (2 hyps honnêtes, identiques au contrôle). Le fix `subst` du
  24 juil. l'avait tué sans que la carte soit refaite. Un chantier multi-sessions **et destructif**
  (édition de code qui marche) évité pour cause de carte périmée.
- **(O1)** disait « chantier §III.2 distinct » : il vit en fait dans le **même dossier**, 35 verts.
  Son résidu était écrit contre `factorielle_existe` — **un symbole jamais codé**. ⚠️ **Un résidu qui
  nomme un fantôme ne peut, par construction, jamais être coché** : il immobilise indéfiniment.
  *Vérifier par `grep` que tout symbole cité dans un résidu EXISTE, sinon le résidu est nul.*

**🔴 SECOND DÉFAUT DE FIDÉLITÉ — `AXIOME_PRODUIT_FAM` a perdu son conjoint « graphe ».**
Même famille que l'incohérence de l'intersection, **même jour** : une notion partielle totalisée sans
sa borne. Le commentaire L.1042-1043 annonce « sélection dans P(I×A) » ; **le corps n'en a aucune
trace** (3 conjoints : `fonctionnel ∧ dom=I ∧ (∀i)…`). L'axiome **frère** `axiome_exposant`
(L.993-1001) garde correctement son `G ⊂ E×F` — c'est un oubli **isolé** de transcription.
- **CONSÉQUENCE, re-mesurée par moi, CLOSE à 0 hypothèse** : `⊢ {∅} ∈ ∏(u,∅)` **et**
  `⊢ ¬(∏(u,∅) = {∅})`, `theorie == 22` avant/après. Or E II.32 (PDF p.83) écrit : « Si I = ∅,
  l'ensemble ∏ ne possède qu'un seul élément, savoir l'ensemble vide ». **Le corpus réfute le livre.**
- **Défaut de FIDÉLITÉ, pas de soundness** — la distinction tient : `est_fonctionnel` n'est QUE
  l'univocité, elle ne dit rien des éléments de F qui ne sont pas des couples ; `{∅}` passe les trois
  conjoints **vacuement**.
- **POURQUOI L'AUDIT DES 22 AXIOMES L'AVAIT MANQUÉ** — et c'est la leçon de méthode : il cherchait
  une **hypothèse absente sur I** (la forme de la panne de l'intersection) et a donc glissé sur un
  **conjoint absent dans le CORPS**. ⇒ **Critère de la « borne automatique », version élargie** :
  *la borne annoncée dans le commentaire (« sélection dans P(…) ») figure-t-elle littéralement dans
  la formule ?* À passer sur **les 22**, mécaniquement — un commentaire qui promet une borne que le
  corps n'a pas est le signe le plus fiable qu'on ait trouvé jusqu'ici.

**🔴 UN THÉORÈME VACUEUX, CRÉÉ PENDANT LE FAN-OUT, RÉVOQUÉ.**
`iii_3_6_familles/ensembles_factorielle_def2_zero.py` (+ son test) démontrait `0! = 1` sous
`H := (∀G)( G ∈ ∏(u,∅) ⇒ est_un_graphe(G) )`, qualifiée dans sa propre docstring de « RÉSIDU
HONNÊTE ». **Elle ne l'était pas : elle est RÉFUTABLE.**
- **LA MESURE QUI TRANCHE.** La première sonde a répondu « NON vacueux » — **verdict sans valeur** :
  elle comparait par égalité de formules contre `H_ref(u)` pour une **liste de noms devinés**, alors
  que l'hypothèse réelle porte sur le terme clos `famille_successeurs(0)`. La bonne question était
  ailleurs : `singleton_vide_dans_produit_vide(u)` est **CLOS pour `u` QUELCONQUE**, et
  `hypothese_graphes_produit_vide_refutee(u,g)` prend `u` et `g` **en paramètres** — **la réfutation
  est un SCHÉMA**. Instancié au terme réel : `H_agent(fam) == H_ref(fam,"G")` **True**,
  `{H_agent(fam)} ⊢ ∅ ∈ ∅` en 1 hypothèse, et `factorielle_def2_zero().hypotheses == {H_agent(fam)}`
  **True** (245,8 s). Par transitivité, **l'hypothèse du théorème EST la formule réfutable**.
  ⇒ **LEÇON D'OUTILLAGE** : *contre un énoncé PARAMÉTRÉ, on n'énumère pas des noms — on INSTANCIE le
  schéma au terme réel.* Une sonde qui devine des noms produit des faux négatifs silencieux.
- **LA VIOLATION.** Le fichier a été écrit à 18:07 par un agent de la phase de **sondage**, à qui la
  consigne disait « NE MODIFIE AUCUN FICHIER ». Il a aussi poussé `iii_3_6_familles` **à 10 entrées
  = CAP saturé**.
- **ET LE DÉPÔT L'INTERDISAIT DÉJÀ, NOIR SUR BLANC.** `ensembles_produit_famille_graphe.py`, écrit
  le matin même à 08:50, dit L.44-46 : « le cas de base 0! = 1 de la Déf. 2 n'est **PAS** atteignable
  par cette route, **et ne doit pas l'être** — il faut réparer l'axiome ». L'agent a construit à 18:07
  exactement ce qu'un module du dépôt proscrivait neuf heures plus tôt.
  ⚠️ **Un fan-out ne lit pas les interdits déposés par le fan-out précédent.** Les contre-théorèmes
  doivent entrer dans le SOCLE des briefs, pas rester dans un fichier qu'on espère voir lu.
- **RÉVOQUÉ** : les 2 fichiers supprimés (copies conservées en scratchpad `REVOQUE_*`), dossier
  ramené à **9 entrées**. Le travail n'est pas perdu : il redeviendra valide **après réparation**.
- **DÉGÂTS CONFINÉS, mesuré** : H2 (`hypothese_graphes_total`, index `I∪{j}` — jamais vide, il
  contient `j`) et H3 (`hypothese_graphes_partiel`, index **variable** `Iq`) sont **hors d'atteinte**
  de cette réfutation, car `singleton_vide_dans_produit_vide` code l'index `∅` **en dur** et le témoin
  `{∅}` a `dom = ∅`. Seul un produit d'index **littéralement ∅** est réfutable — c'est-à-dire
  exactement le fichier révoqué. **Aucun autre résultat du corpus n'est vacué.**

**⏭ CHANTIER OUVERT — RÉPARER `AXIOME_PRODUIT_FAM`** (remplacement, pas ajout ; **le compte reste
22**). Rétablir la forme du livre `F ⊂ I × ⋃_{ι∈I} X_ι`, celle-là même qu'`axiome_exposant` a gardée.
Précédent exact : la réparation de `AXIOME_INTER_FAM` le 26 juil. **Ripple mesuré : 50 occurrences
sur 22 fichiers** (17 `bourbaki/` + tests + docs). Bénéfice : H, H2 et H3 deviennent des **théorèmes**
et se déchargent — `0! = 1` redevient atteignable **sans résidu**, et le §III.3.6 se referme.
Cartographie du ripple lancée en fan-out lecture seule (`ripple-axiome-produit-fam`).


## ✅ 26 juil — CHANTIER 2 CLOS : le **(∃!f) de C62** existe enfin (`existence_unicite_fonction_c62`).
**Ce n'était ni un verrou-τ, ni le fix `subst` du 24 juil. : c'était un désalignement de conjonction
jamais recollé.** Les DEUX moitiés étaient au dépôt depuis le 25 juil. et personne n'avait remarqué
qu'elles ne se joignaient pas — un `BLOQUE_FAUX` de la famille « l'assemblage est supposé fait parce
que ses deux moitiés le sont ».

- **LE DÉSACCORD, mesuré** : `fonction_recursion_c62` (existence) conclut sur **TROIS** conjoints
  `func ∧ dom=ℕ ∧ éq`, tandis que l'antécédent de `unicite_fonction_c62` en exige **QUATRE** —
  il ajoute `est_un_graphe`. Deux prédicats distincts ⇒ **(∃!f) non formable tel quel**.
  `grep existence_unicite|c62_existe_unique|existe_unique_fonction` : **aucun hit** dans `bourbaki/`.
- **LE PIÈGE, et il est MATHÉMATIQUE** : la tentation est d'aligner en **retirant** `est_un_graphe(g)`
  de l'unicité. **Ce serait FAUX.** `est_fonctionnel`, `dom` et `valeur(·,x)=τy((x,y)∈·)` ne **lisent**
  que les couples : `g` et `g∪{a}` avec `a` non-couple ont **mêmes** fonctionnalité, domaine et
  valeurs, en étant **DIFFÉRENTS**. La règle est donc : **RENFORCER L'EXISTENCE, jamais AFFAIBLIR
  L'UNICITÉ.**
- **ET LE RENFORCEMENT EST GRATUIT** : `est_un_graphe_fonction_globale` est **CLOS à 0 hypothèse**
  sur le **MÊME** témoin `f = ⋃𝔇_tot`. Le 4ᵉ conjoint ne coûte rien. **Bonus de fidélité** : chez
  Bourbaki une *application* EST un graphe fonctionnel — le prédicat à 4 conjoints est **plus proche
  du livre** que celui à 3.
- **LIVRÉ** dans `iii_6_2_recursion_c62/ensembles_c62_fonction_unicite.py` (266 l., 127 l. de code ;
  dossier laissé à 10 entrées, **aucun fichier créé**) : `c62_predicat`, `c62_existe_unique_cible`,
  `existence_unicite_fonction_c62`. Énoncé obtenu, `@livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 |
  PDF p.149` (page **relue en PNG** : en-tête `E III.46` confirmé, et la dernière phrase de C62 est
  bien « L'ensemble U et l'application f sont alors **déterminés de façon unique** par cette
  condition. ») :
  `{bo, essais_bien_formes, rule_codomain} ⊢ (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g=f ) )`,
  `P(t) = est_fonctionnel(t) ∧ est_un_graphe(t) ∧ dom(t)=ℕ ∧ (∀z∈ℕ)(t(z)=T(z))`.
  **Aucune hypothèse nouvelle** vs les deux moitiés ; `theorie_ensembles()` = 22 avant et après.
- **REMÈDE STRUCTUREL — la source unique.** `c62_predicat` construit désormais l'antécédent de
  l'unicité **ET** les deux occurrences du (∃!f). Comme `et` est **binaire et gauche-associatif**,
  un parenthésage divergent produisait une formule différente pour le noyau et un échec silencieux
  en assert ; la factorisation rend le désaccord **structurellement impossible**.
- **TEST QUI MORD** (`tests/…/test_c62_fonction_unicite.py`, 6 verts) : la conclusion est
  **reconstruite à la main** hors du module (sinon on compare le module à lui-même), les hypothèses
  sont assertées par **égalité EXACTE de frozenset** (un `len(...)==3` ne dit pas *lesquelles* et
  laisserait passer un résidu de complaisance). **5 mutations distinctes vérifiées rejetées** :
  binder d'équation, binder existentiel, prédicat affaibli sans `est_un_graphe`, association à
  droite, faux résidu. 81 verts sur les deux zones.
- **RÉSIDU HONNÊTE, et il est important** : ce (∃!f) est au **niveau VALEUR-RÈGLE** `f(z)=T(z)`.
  L'unicité y est facile *précisément parce que* `T` est appliquée au POINT : `g(x)=T(x)=f(x)` est
  immédiat. Au **niveau LIVRE** `f(z)=T{f|seg z}`, l'argument de `T` **diffère** entre `g` et `f`
  (`T{g|seg x}` vs `T{f|seg x}`) : l'extensionnalité ne conclut plus rien et `graphe_egal_par_valeurs`
  ne s'applique pas. Il faudra une **RÉCURRENCE TRANSFINIE** sur la coïncidence `g|seg x = f|seg x`
  — vrai travail, pas un assemblage. **Asymétrie nette** : existence niveau-livre **OUI**
  (`equation_restriction_fonction`, 4 hyps), unicité niveau-livre **NON**. Annoncer « (∃!f) de C62
  FAIT » sans ce qualificatif serait un faux positif de plus.
- **LEÇON TRANSFÉRABLE** : un désalignement de conjonction ne produit **aucun** message d'erreur tant
  que le recollement n'est pas tenté — les deux moitiés passent leurs tests séparément, pour
  toujours. **Vérifier qu'une pièce existe ne dit RIEN de sa jointure : greper le CAPSTONE, pas ses
  ingrédients.** Et le corollaire de méthode : le pont restriction (25 juil.) n'a **rien** à voir ici
  — `graphe_egal_par_valeurs` date du 3 juil., vit en **II.3**, et le **PRÉCÈDE** de trois semaines.


## ✅ 26 juil — INCIDENT CLOS : `theorie_ensembles()` était CONTRADICTOIRE, elle ne l'est plus.
**Réparé, migré, audité, mesuré le même jour** — axiome de sélection en place, `theorie_ensembles()`
toujours à 22, zone 391 verts / 0 échec, amont 381 verts, incohérence morte, 18/18 modules déclarés
HONNÊTES par audit adversarial `.bak`-contre-courant. **Le corpus est de nouveau certifié dans une
théorie qu'on a des raisons de croire cohérente**, et les résultats antérieurs à l'incident
redeviennent valides tels quels (87 % du périmètre n'a pas eu à être retouché).
Le récit ci-dessous est conservé INTÉGRALEMENT : c'est le substrat — le « pourquoi » et les erreurs
valent autant que les preuves. Ce qui est daté d'avant la réparation se lit comme un état passé.

- **LA PREUVE** : `outils_ia/audit/preuve_incoherence_inter_vide.py` (tourne seul, ~2 s) dérive
  `⊢ (∃X)(∀x)(x∈X)` **et** `⊢ ¬(∃X)(∀x)(x∈X)`, tous deux CLOS, 0 hypothèse, dans la MÊME théorie.
  Deux contrôles inclus : (1) le noyau refuse bien les non-axiomes — **le noyau est HORS DE CAUSE**,
  la frontière de confiance a tenu ; (2) `AXIOME_INTER_FAM` est bien l'un des 22. C'est le JEU
  D'AXIOMES qui est fautif, pas la machine qui le vérifie.
- **LA FAUTE** : `AXIOME_INTER_FAM` (ensembles_abrege.py L.1061-1066) posé **sans la restriction
  I ≠ ∅**. Pour I = ∅ le membre droit est vide-vrai pour tout z, donc ⋂_{ι∈∅} X_ι contient TOUT
  objet : ensemble universel, qui contredit `pas_ensemble_universel` (Russell, déjà CLOS au corpus).
- **CE QUE DIT BOURBAKI** (E II.22 Déf. 2, PDF p.73, lu en PNG) : « Soit (X_ι)_{ι∈I} une famille
  d'ensembles **dont l'ensemble d'indices I n'est pas vide**. » Et en petits caractères, notre
  panne annoncée mot pour mot : « Si I = ∅, la relation (∀ι)((ι∈I) ⇒ (x∈X_ι)) **n'est pas
  collectivisante en x** : […] car ce serait l'ensemble de tous les objets (cf. II, p. 6,
  Remarque). » — et II p.6 Remarque, c'est exactement le théorème qui nous a explosé à la figure.
  **Bourbaki n'est PAS en cause. La faute est 100 % la nôtre.**
- **CAUSE RACINE, et c'est la leçon transférable** : le `@livre` de `inter_famille`
  (ensembles_abrege.py L.224) pointe sur **E.R.19 / PDF p.322 — le RÉSUMÉ**. Or le Résumé traite
  l'intersection dans le monde des familles de **parties de E** (Déf. 3), où ⋂_{ι∈∅} X_ι = E.
  On a croisé **la formule de la Déf. 2** (sans le « x ∈ E ») avec **la totalité de la Déf. 3**
  (valable pour tout I). Ce croisement n'existe **nulle part** dans le livre, et c'est le seul
  des quatre qui soit contradictoire. La condition I ≠ ∅ est précisément la charnière qui rend
  les deux définitions compatibles — Bourbaki le dit : pour I non vide « l'intersection ne dépend
  ni de E, ni de l'ensemble d'arrivée ».
- **RÈGLE NOUVELLE, mécaniquement vérifiable** : **un marqueur `@livre Ch.R` sur un AXIOME est un
  défaut de fidélité par construction.** Un résumé condense et suppose le contexte acquis ; il ne
  peut pas servir de source à un axiome. Sur une notation pure (couple, pr₁, produit) `Ch.R` reste
  légitime. Le critère d'audit est donc étroit et net : *la définition du chapitre porte-t-elle une
  hypothèse que le Résumé laisse tomber ?*
- **LE CORRECTIF** (route Grimm B5, `@source sources/grimm_gaia/RR-6999-v7.pdf p.35 §2.7` :
  « Taking for E the union of the family solves the problem ») : l'intersection cesse d'être un
  postulat inconditionnel et devient une **sélection dans la réunion** —
  `z ∈ ⋂_{ι∈I} X_ι ⇔ ( z ∈ ⋃_{ι∈I} X_ι ∧ (∀i)(i∈I ⇒ z∈X_i) )`, légitimée par S8 + A1 exactement
  comme AXIOME_QUOTIENT (sélection dans P(E)) et AXIOME_PRODUIT_FAM (sélection dans P(I×A)).
  ⋂_{ι∈∅} = ∅ devient gratuit. On **REMPLACE** l'axiome, on n'en retire pas : **`theorie_ensembles()`
  reste à 22** — l'invariant tient, et le nouvel axiome est strictement plus faible dans le cas
  pathologique.
- **MIGRATION** : 34 sites d'usage. La direction d'ÉLIMINATION (z∈⋂ ⇒ (∀i)…) est **inchangée** —
  cette moitié-là migre gratuitement. La direction d'INTRODUCTION exige désormais un témoin
  d'indice ; les sites qui disposent de I ≠ ∅ la retrouvent par le lemme de caractérisation
  `(∃i)(i∈I) ⇒ (∀z)(z∈⋂ ⇔ (∀i)(i∈I ⇒ z∈X_i))` = l'ancien axiome récupéré sous l'hypothèse du
  livre. Les sites qui l'utilisent SANS I ≠ ∅ énoncent quelque chose de **faux** : à ré-énoncer.
### ✅ AUDIT DES 22 AXIOMES — FAIT (26 juil.). Pas de deuxième bombe.
Chacun relu sur la page du **chapitre** (PNG), pas du Résumé. **1 `ABSENTE_CRITIQUE`** (celui-ci),
**10 `PROSE_SEULE`**, **11 `OK`**. Détail : `scratchpad/audit_axiomes.json`.
- `AXIOME_INTER` (∩ binaire) est **OK** : l'ensemble d'indices y est `{A,B}`, jamais vide — le cas
  binaire échappe structurellement au bug.
- `AXIOME_REUNION_FAM` **OK**, et Bourbaki y traite explicitement I = ∅ ⇒ ⋃_{ι∈∅} = ∅ : validation
  externe de la route de réparation. `AXIOME_PRODUIT_FAM` **OK** (I = ∅ est un *cas*, pas une
  exclusion).
- **LOI DÉGAGÉE, décidable, à appliquer avant toute totalisation** : 4 des 10 `PROSE_SEULE`
  (QUOTIENT, APPCANON, COMPL_FAM, RESTRICTION) ont la MÊME forme d'erreur que l'intersection — on
  a totalisé une notion partielle. Ils ne tuent pas parce que l'objet défini a une **borne
  automatique** (`E/R ⊂ P(E)`, `E∖A ⊂ E`, `dom(G) ⊂ pr₁-image`). L'intersection est la seule dont
  la borne DISPARAÎT quand I = ∅ — d'où la double précaution de Bourbaki (« I ≠ ∅ » Déf. 2,
  « ⊂ E » Déf. 3). ⇒ **Avant de totaliser une définition partielle : l'objet a-t-il une borne
  automatique ? Sinon, il faut la fournir.** (Dette de fidélité restante : ces 4 axiomes sont plus
  FORTS que ceux du livre ; un théorème qui exploiterait la force en trop ne serait pas de
  Bourbaki. Ne bloque rien, à reprendre.)

### ✅ RÉPARATION CONSTRUITE ET APPLIQUÉE (26 juil.)
`ii_4_reunion_intersection_famille/ii_4_intersection_fondation/` — 2 modules (186 + 212 l.),
17 tests verts. **8 théorèmes vérifiés CLOS, 0 hypothèse** (contrôle indépendant, hors tests de
l'agent : `scratchpad/verdict_reparation.py`) : `membre_inter_selection`, `inter_donne_membres`,
`inter_inclus_reunion`, `inter_par_membres_si_temoin{,_terme}`, `reunion_intro_terme`,
`caracterisation_inter_famille_non_vide` (= L'ANCIEN AXIOME récupéré sous `(∃i)(i∈I)`, c'est LA
clé de migration), `caracterisation_inter_famille_indices_non_vide` (forme `¬(I=∅)` du livre),
`inter_famille_vide_est_vide`, `inter_famille_vide_egale_vide` (⋂_{ι∈∅} X_ι = ∅).
- **ÉCHANGE FAIT** dans `ensembles_abrege.py` (.bak au scratchpad) : `AXIOME_INTER_FAM` est
  désormais la forme de sélection, **`theorie_ensembles()` == 22**, et l'axiome du corpus est
  `==` à celui de la théorie dédiée (donc les lemmes-pont transfèrent tels quels).
- **L'INCOHÉRENCE EST MORTE** : `preuve_incoherence_inter_vide.py` échoue maintenant sur
  `ValueError: modus ponens : mineure ≠ antécédent`. Mécanisme : `(∀i)(i∈∅ ⇒ x∈X_i)` reste
  démontrable (c'est vrai), mais ne suffit plus — l'axiome réclame en plus `x ∈ ⋃_{ι∈∅}`, qui est
  réfutable. On n'a pas interdit la dérivation, on lui a retiré son carburant.
- `@livre` de `inter_famille` corrigé : `Ch.R E.R.19 p.322` → **`Ch.II §4.1 Def.2 | E II.22 | PDF p.73`**.
- **DÉGÂTS MESURÉS** (et non devinés) : zone II.4+II.5+II.6 = 385 verts avant échange →
  **336 verts / 49 échecs** après. **87 % du périmètre a traversé l'échange sans une retouche.**
  Les 49 échecs tiennent en EXACTEMENT 2 motifs, aucun imprévu : 60 × `pas un (∀x)R` (élimination :
  le membre droit est devenu une conjonction, il faut projeter) et 26 × `modus ponens : mineure ≠
  antécédent` (introduction : il faut un témoin d'indice).
### ✅ MIGRATION, VAGUE 1 (workflow `migration-intersection-selection`, 20 agents, 1 h 32)
Classification honnête imposée : **A** re-prouvé à l'identique · **B** hypothèse `(∃i)(i∈I)`
AJOUTÉE à l'énoncé (⇒ le corpus affirmait jusqu'ici quelque chose de FAUX pour I = ∅) · **C**
irréparable. **Résultat : A = 40, B = 7, C = 0.** Zone repassée de **336/49** à **382 verts /
7 échecs** (389 tests : les migrateurs ont AJOUTÉ 4 tests d'ancrage). 8 agents perdus en route
(6 sur plafond de session, 2 sur coupure réseau) — mais 4 d'entre eux avaient fini d'éditer avant
de mourir : il ne restait que **3 fichiers** rouges.

**LES 7 « B » — les endroits où le corpus énonçait une contre-vérité** (chacun est un énoncé
RENFORCÉ, pas un test bricolé) :
1. `inter_incluse_sous_indices` — décroissance ⋂ en l'ensemble d'indices. **L'hypothèse porte sur
   J** (le PETIT ensemble), pas sur I : contre-exemple J=∅ ⊂ I={0}, X_0={a}. Loi générale extraite :
   *le témoin d'indice est exigé du côté où l'on CONCLUT « z ∈ ⋂ », jamais du côté d'où l'on part.*
2. `cible()` du même fichier (l'énoncé-miroir) — recalé, les deux ne peuvent plus diverger en silence.
3. `membre_inter_ensemble` (⋂ d'un ensemble de parties) — hypothèse au compteur.
4. `membre_inter_famille` (`ensembles_familles.py`) — **la charnière** : porte désormais
   `(∃i)(i∈I) ⇒ (…)` en antécédent. C'est littéralement l'énoncé qui rendait la théorie contradictoire.
5. `inter_inf_universelle` — l'hypothèse est mise EN ANTÉCÉDENT (pas au compteur) et un test dédié
   verrouille ce choix pour interdire un retour silencieux à la forme fausse.
6. `_dir_produit_vers_interH` — lemme PRIVÉ ; l'énoncé PUBLIC (`produit_inter_familles`) portait
   déjà `¬(I=∅)` d'après Bourbaki E.R.20 (44) : inchangé.
7. `de_morgan_inter_famille` — **renversement des rôles** : avant la migration c'était *réunion* qui
   était conditionnelle et *inter* l'inconditionnelle ; c'est exactement l'inverse. La docstring qui
   l'expliquait longuement raisonnait sous l'axiome contradictoire.

**LA LOI RÉUTILISABLE (le vrai acquis, transférable hors §II.4)** : quand une preuve tient DÉJÀ un
élément de ⋂, l'hypothèse « I ≠ ∅ » de Bourbaki est **GRATUITE**. Route : `z∈⋂ ⇒ z∈⋃`
(`inter_inclus_reunion`, projection gauche) ; `AXIOME_REUNION_FAM` ; `N.existe_temoin` livre
τi(i∈I ∧ z∈X_i) ; `conjonction_elim_gauche` donne `⊢ T₀∈I`. Corollaire : dans toute preuve par
DOUBLE INCLUSION entre intersections, les deux témoins sont gratuits ⇒ **statut A**. Et tout énoncé
de la forme « (c ∈ U) ⇒ … » est presque toujours un A déguisé. **Ne jamais ajouter `(∃i)(i∈I)` par
réflexe** : une hypothèse inutile est un affaiblissement gratuit, aussi malhonnête qu'un test qui ment.

**TROISIÈME MOTIF DE CASSE, imprévu** (les 2 précédents étaient élimination/introduction) :
`ValueError: pas une conjonction` — un consommateur en aval recevait une ÉQUIVALENCE et reçoit
désormais une IMPLICATION `(∃i)(i∈I) ⇒ (…)`, **parce qu'un producteur amont est devenu un B**. La
migration se propage donc d'un cran : le remède est de décharger l'antécédent, pas de rejouer la preuve.

**AUTRE PIÈGE CONFIRMÉ 4 fois** : le premier traceback MENT sur l'ampleur. Le motif (a) masque
systématiquement un motif (b) quelques lignes plus bas dans la même fonction. Grepper TOUTES les
occurrences du helper d'axiome du fichier, jamais la seule ligne de la trace.

### ✅✅✅ VAGUE 2 — MIGRATION CLOSE (workflow `migration-inter-cloture`, 22 agents, 28 min)
**ZONE : 0 ÉCHEC / 391 VERTS.** Amont II.1+II.2+II.3 : 381 verts, aucune régression hors périmètre.
`theorie_ensembles()` = 22. Incohérence toujours morte, **et morte au bon endroit** : les deux
contrôles préliminaires de `preuve_incoherence_inter_vide.py` passent (le noyau refuse les
non-axiomes, `AXIOME_INTER_FAM` est bien l'un des 22) *puis* `ValueError: modus ponens : mineure ≠
antécédent` — donc l'échec n'est pas un faux négatif d'import, c'est bien le témoin d'indice que
I = ∅ ne peut plus fournir. **Toutes ces mesures re-jouées à la main, indépendamment des agents.**

**Trajectoire complète** : 385 verts → **336/49** (échange d'axiome) → **382/7** (vague 1) →
**391/0**. Le total est monté de 385 à 391 : **+6 tests NETS**, aucun test supprimé, désactivé ou
`xfail`-é pour faire verdir. C'est le seul chiffre qui prouve qu'on n'a pas triché — un total qui
baisse en même temps que les échecs est la signature d'une suite qu'on a fait taire.

**🔍 LE RÉSULTAT QUI COMPTAIT — AUDIT D'HONNÊTETÉ ADVERSARIAL : 18 modules, 18 HONNÊTES,
0 AFFAIBLISSEMENT SILENCIEUX, 0 DOUTE, 0 anomalie BLOQUANTE.** Un auditeur par module, `.bak`
pré-migration chargé comme module indépendant et comparé **bit-à-bit** (conclusion ET hypothèses)
à la version courante — la seule preuve recevable qu'un énoncé n'a pas bougé. Les 12 migrateurs
avaient une incitation forte à faire verdir ; leurs 40 « A » auto-déclarés tiennent.

**12 DETTES trouvées, toutes de gravité DETTE, et le motif est instructif : 10 sur 12 sont des
DOCSTRINGS QUI MENTENT, et 9 de ces 10 sont ANTÉRIEURES à la migration.** L'audit n'a pas
seulement validé la migration, il a mis au jour un sédiment de documentation fausse que personne
ne regardait. Échantillon :
- `reparam_reunion_incluse` : la docstring criait « INCONDITIONNEL » **trois lignes au-dessus** du
  code qui fait `loi_deduction(dom_hyp, incl)` et rend une IMPLICATION. Contradiction *interne au
  même docstring*, jamais lue.
- `image_recip_inter_egal` & 2 voisins : l'en-tête de module annonçait `{Fonctionnelle(f)}` quand la
  conclusion porte **deux** antécédents — le second étant précisément `α∈I`, le « I ≠ ∅ » de la
  Déf. 2. La doc masquait exactement l'hypothèse dont l'absence a rendu la théorie contradictoire.
- `produit_distrib_inter_membre` : docstring à **4 conjoints**, code à **5**. Et la 5ᵉ prémisse était
  présentée comme découlant de `κ₀∈K` — alors que `κ₀∈K` n'est **jamais extrait** du corps : une
  hypothèse MORTE, décorative.
- `@livre Ch.R §4 | E.R.19 item 8` sur `inter_incluse_sous_indices` : citation du Résumé **exacte**
  (vérifiée p.322) mais **trompeuse ici**, puisque le Résumé travaille dans le monde des parties
  d'un E fixe où ⋂_{ι∈∅} = E. C'est la règle « `Ch.R` sur un axiome = défaut par construction »
  qui remonte d'un cran : *une citation peut être exacte et quand même mentir, si son cadre diffère.*
- Références pendantes vers `_inst_inter`, helper disparu du fichier : piste de faux diagnostic
  posée pour le prochain lecteur.

**LA SEULE DETTE QUI TOUCHE UN ÉNONCÉ — et elle valide la loi n°1 par l'absurde** :
`_dir_produit_vers_interH` (lemme exporté, `er20`) est passé de 1 à 2 hypothèses, un migrateur y
ayant ajouté `¬(I=∅)` en le justifiant par « requise DEPUIS la migration Déf. 2 ». L'auditeur a
**RÉFUTÉ la clause EN CODE** (`scratchpad/audit_er20_temoin.py`) : le corps du lemme contient déjà
`p ∈ ⋂_{ι∈I}` comme conjoint, donc le témoin est **gratuit** (1 hypothèse, `¬(I=∅)` absente).
Le migrateur a ajouté par réflexe exactement ce que la loi n°1 interdit. **Une hypothèse inutile
survit à tous les tests verts** : seul un audit qui *tente de la retirer* la détecte.

**LE PIÈGE DU TRACEBACK, MONTÉ D'UN CRAN (leçon confirmée une 5ᵉ fois, en pire)** : sur `prop10`,
diagnostic annoncé = 2 sites, réalité = **4 sites, dont 2 d'un motif inédit**. Le motif neuf :
un helper **PRIVÉ** du fichier (`_membre_inter_terme`) qui instancie l'axiome à la main, invisible
à tout grep du lemme public importé. ⇒ **Grepper aussi le nom des helpers privés du fichier.**
Corollaire mesuré : corriger le seul site du traceback aurait produit 3 échecs successifs.

**PIÈGE DE CAPTURE (moitié du temps d'analyse d'un agent)** : la boîte à outils ii_4 est
**inutilisable telle quelle** quand le fichier client utilise « i » comme indice libre —
`reunion_intro_terme` / `inter_par_membres_si_temoin_terme` codent le liant « i » EN DUR et le
**capturent**. Sonde décisive : instancier l'axiome avec `(P,K,F)` laisse le liant à « i », mais
avec `(row(i),K,F(i))` `subst` le renomme en **« @0 »**. Remède générique : **LIRE le liant sur
l'instance d'axiome, ne jamais le supposer.**

**LA ROUTE « LA MOINS CHÈRE » N'EST PAS TOUJOURS LA BONNE** : `caracterisation_inter_famille_non_vide`
(l'ancienne équivalence sous témoin) est la route par défaut — le corps de preuve se recopie mot
pour mot — **sauf** quand le fichier instancie déjà l'axiome à la main : elle impose alors de
décharger un antécédent aux DEUX directions, alors que l'élimination est inconditionnelle. Tirer
les deux sens directement de l'axiome de sélection est plus court.

**DOUBLE INCLUSION ≠ SYMÉTRIE DE STATUT** (`cor_prop8`) : le sens ⊃ part de `x ∈ ⋂_{p∈I×K}` et
récupère les DEUX témoins gratuitement (⋂⊂⋃ → témoin p₀∈I×K → `AXIOME_PRODUIT` le décompose) ⇒
**statut A**. Le sens ⊂ part d'une DISJONCTION `(⋂X)∪(⋂Y)` qui ne donne jamais qu'un côté ⇒
**statut B irréductible**. Ne pas propager un statut par symétrie apparente.

**📏 RAYON DE SOUFFLE MESURÉ (`scratchpad/portee_migration.py`, fermeture montante des imports)** :
graine = les 21 modules réellement modifiés → **28 modules atteignables, TOUS en §II.4/II.5/II.6,
ZÉRO en chapitre III ou IV.** Conséquence pratique : **la zone de test (391 tests, 14 s) est un
verdict COMPLET pour cette migration** — inutile d'attendre la suite entière (2 h 12) pour être sûr.
Mesurer la portée avant de tester, c'est ce qui transforme une nuit d'attente en trente secondes.

**⚠️ ANGLE MORT TROUVÉ — 3 modules de la zone n'avaient AUCUN test miroir** (donc invisibles au
verdict) : `ensembles_famille_identite_ii4.py` (il consomme `membre_inter_ensemble`, devenu un B —
le risque maximal était précisément là), `ensembles_image_inter_pont_ii4.py` (**module créé pendant
la migration, livré sans test**), `ensembles_quotient_props_graphe.py`. Contrôle manuel fait :
**19 résultats reconstruits, 0 échec**. Mais « ça construit » ≠ « l'énoncé n'a pas bougé ».
Leçon : un verdict de non-régression ne vaut que pour ce que la suite COUVRE ; la première question
n'est pas « est-ce vert ? » mais **« qu'est-ce qui n'est pas regardé ? »**.
### ✅✅✅ VAGUE 3 — DETTES SOLDÉES, INCIDENT DÉFINITIVEMENT CLOS (`solder-dettes-migration-inter`)
**Zone : 391 → 415 verts / 0 échec. Chapitre II entier : 796 verts.** Amont : 381, delta 0.
`theorie_ensembles()` = 22. Incohérence morte. `LIVRE.md` : **0 fichier à caler** (le module de
ponts est ancré sur la Déf. 2 E II.22 — ses trois lemmes SONT les deux directions de cette
définition plus son corollaire, aucune référence inventée). Mesures re-jouées à la main.

**Le +24 est tracé test par test** — 14 (`test_image_inter_pont_ii4`, neuf) + 9
(`test_famille_identite_ii4`, neuf) + 1 (verrou anti-régression `er20`) = 24 exactement, et
`grep` confirme 0 `xfail`, 0 `skip` dans toute la zone. *Un delta de tests qui ne se décompose pas
exactement est un delta qui cache quelque chose.*

**🔬 LES TESTS NEUFS SONT PROUVÉS NON DÉCORATIFS — 21 MUTANTS INJECTÉS, 21 TUÉS, 0 SURVIVANT.**
Deux familles : (a) *pollution* — même conclusion, hypothèse parasite empilée par gestes noyau
purs ; (b) *substitution* — conclusion remplacée. Un test qui survit à (a) ne verrouille pas les
hypothèses ; un test qui survit à (b) ne verrouille pas l'énoncé. Détail qui vaut la méthode :
2 mutants rendaient l'**α-variant** au liant « j » (même force logique, liant renommé) — tués
aussi. **Relire un test ne dit pas s'il protège ; le muter, oui.** À généraliser à tout test
d'ancrage écrit par un agent.

**🎯 LA DÉCOUVERTE MÉTHODOLOGIQUE DE LA VAGUE (elle corrige la vague 2) :
la confrontation au `.bak` détecte la DÉRIVE, pas la DETTE.** `inter_incluse_partie_parties`
sortait *identique* de l'audit différentiel — conclusion identique, hypothèses identiques, 2 = 2 —
et un audit purement différentiel l'aurait classé A. Or son `¬(U=∅)` était **gratuit des deux
côtés**, avant comme après. Une hypothèse inutile *conservée* est invisible au diff. ⇒ **Il faut
DEUX passes : le diff contre le `.bak` (dérive) ET la loi n°1 appliquée à l'énoncé dans l'absolu
(dette).** Retirée : 2 hypothèses → 1, conclusion inchangée à l'octet.

**Bilan des retraits** : `_dir_produit_vers_interH` 2 → 1 hypothèse (exactement celle du `.bak`
pré-migration), `inter_incluse_partie_parties` 2 → 1, les deux à **conclusion identique au sha1**.
Chacun verrouillé par un test qui meurt si l'hypothèse revient. Les 5 résultats d'`er20` ont un
sha1 de conclusion inchangé (garde-fou `scratchpad/garde_fou_er20.py`, exit 0).

**LE MOTIF D'ERREUR GÉNÉRIQUE, à mettre au catalogue** : la docstring fautive disait « `¬(I=∅)` est
requise depuis la migration : conclure z∈⋂H réclame désormais un témoin d'indice ». La 2ᵉ moitié
est VRAIE, la 1ʳᵉ est FAUSSE. **Le migrateur a confondu « il faut un TÉMOIN » et « il faut
l'HYPOTHÈSE de non-vacuité ». Un témoin est un objet à CONSTRUIRE, pas une hypothèse à SUPPOSER.**
Et la loi n°1 **traverse les familles d'une même indexation** : le τ fabriqué depuis X sert tel
quel pour conclure dans H, car ce qui compte est l'ensemble d'INDICES, identique des deux côtés.

**⚠️ PIÈGE DÉSAMORCÉ DANS L'OUTIL D'AUDIT LUI-MÊME** : la docstring de
`preuve_incoherence_inter_vide.py` prescrivait encore « `theorie_ensembles()` passe de 22 à 21
axiomes ». C'était le PLAN, pas ce qui a été fait (remplacement, pas suppression). Un agent pressé
y aurait lu l'ordre de « réparer » 22 en 21 — c'est-à-dire de retirer un axiome dont tout le §II.4
dépend. Corrigé, avec un bandeau disant que **ce script DOIT échouer** (test de non-régression
inversé : s'il réussit un jour, l'incohérence est revenue). *Le fichier qui est le monument d'une
faute est précisément celui où la prose doit être exacte.*

**Charge résiduelle honnête** : `_dir_interH_vers_produit` pourrait AUSSI perdre son `¬(I=∅)` par
la loi n°1 — **renforcement disponible, volontairement non consommé** : cette hypothèse est
antérieure à la migration et c'est celle que Bourbaki écrit noir sur blanc en E.R.20 (44). La
garder est fidèle ; la retirer donnerait un lemme plus fort que le livre. À trancher un jour, pas
en douce. Et `E III p.59` reste la dernière page non ancrée du corpus (pré-existant, hors sujet).

**📏 RAYON DE SOUFFLE MESURÉ (`scratchpad/portee_migration.py`, fermeture montante des imports)** :
graine = les 21 modules réellement modifiés → **28 modules atteignables, TOUS en §II.4/II.5/II.6,
ZÉRO en chapitre III ou IV.** Conséquence pratique : **la zone de test (389 tests, 30 s) est un
verdict COMPLET pour cette migration** — inutile d'attendre la suite entière (2 h 12) pour être sûr.
Mesurer la portée avant de tester, c'est ce qui transforme une nuit d'attente en trente secondes.

**⚠️ ANGLE MORT TROUVÉ — 3 modules de la zone n'ont AUCUN test miroir** (donc invisibles au verdict) :
`ensembles_famille_identite_ii4.py` (il consomme `membre_inter_ensemble`, devenu un B — le risque
maximal était précisément là), `ensembles_image_inter_pont_ii4.py` (**module créé CE MATIN par un
migrateur, livré sans test**), `ensembles_quotient_props_graphe.py`. Contrôle manuel fait :
**19 résultats reconstruits, 0 échec** — rien n'est cassé. Mais « ça construit » ≠ « l'énoncé n'a pas
bougé » : `membre_inter_parties` et `inter_incluse_partie_parties` portent 2 hypothèses, à confronter
au .bak par l'auditeur. **Dette à solder avant de clore : écrire les tests miroirs manquants.**
Leçon : un verdict de non-régression ne vaut que pour ce que la suite COUVRE ; la première question
n'est pas « est-ce vert ? » mais « qu'est-ce qui n'est pas regardé ? ».

## ✅✅ GARDE-FOU A1-A3 : SUITE COMPLÈTE 3606 VERTS, 0 ÉCHEC (2:12:04, 25 juil)
Les chantiers A1 (équations factorielle), A2 (∃!f), A3 (C62 sur ℕ, bon ordre déchargé) sont
SCELLÉS. Les percées A4 (S1/B1/T1a, faites pendant cette suite) seront couvertes par la prochaine.

- **🎉 T1b-1 FAITE (agent build, 2/2 verts 2:27)** : `segment_succ_decomposition` ⊢ **{ n∈ℕ }**
  seg(ℕ, succ n) = seg(ℕ,n) ∪ {n} — 1 SEULE hyp honnête, cible exacte au segment C62 (_seg_NN
  partagé). ensembles_seg_successeur.py (iii_3_6_familles). NB T1c : le lien avec l'hypothèse
  « seg(succ n)=[0,n] » de factorielle_succ_fallback passera par [0,n]=seg(n)∪{n} (fermé↔ouvert).
- **🎉🎉 T1b-2 FAITE — LE CŒUR DU MUR (agent build, P7 ATTEINT, 14/14 verts 2,15 s)** :
  `ensembles_produit_adjonction{,_briques,_bij}.py` (iii_3_6_familles, 3 fichiers ≤300 l) —
  **Eq(∏_{I∪{j}} u, ∏_I u × u_j)** + **Card(∏_{I∪{j}}) = produit_cardinal_binaire(∏_I u, u_j)**
  [terme-à-terme asserté] sous {H1: j∉I ; H2/H3: est_un_graphe des membres des 2 produits —
  AXIOME_PRODUIT_FAM n'expose pas « élément=couple », pont membre-produit⇒graphe inexistant}.
  Φ=graphe_terme(∏_{I∪{j}}, (G|I, G(j,b="c")), "Fq") ; P1-P7 tous verts. Pièges consignés :
  collision lettre « u » de _couple_restriction (exotique+∀+re-instancie), τ-liant valeur « c »
  +alpha_tau, binder z d'est_un_graphe (α par ∀-clôture). Fidélité PDF Prop6 E II.34 p.85 /
  Prop7+Rem1 §5.5 E II.35 p.86 ; LIVRE.md 0 à caler.
- **🎉🎉 T1b-3 FAITE ⇒ T1b TERMINÉE (agent build, 3/3 verts 3:01)** :
  `ensembles_produit_recursion.py` — **Card(∏_{seg(n+1)} u) = Card(∏_{seg(n)} u × u_n)** ;
  H1 déchargée par point_hors_segment [CLOS] ; hyps restantes = {n∈ℕ + gardes-graphes T1b-2}
  (détail au fichier/test). LA RÉCURSION DU PRODUIT FINI INDEXÉ EXISTE.
- **🎉🎉🎉 T1c FAITE (25 juil, 8/8 verts 3:20) ⇒ LA BOUCLE DÉF.2 EST FERMÉE.**
  `ensembles_factorielle_def2_rec.py` : **factorielle_def2(succ n) = produit_cardinal_binaire(
  factorielle_def2(n), successeur(n))** — (n+1)! = n!·(n+1) du livre (E III.41 L.30-32) démontrée
  sur le VRAI terme Déf.2 (hyps honnêtes {n∈ℕ, H2, H3, HW, HN} — détail au fichier/test).
  PIÈGE PERCÉ : la garde _NOMS_RESERVES de T1b-3 réservait « ifs » (liant du graphe_terme de
  famille_successeurs, syntaxiquement LIBRE dans le terme-famille) alors que la machinerie
  traversée ne le lie jamais — retiré avec justification (.bak au scratchpad), T1b-3 re-vert.
  LEÇON : une garde anti-collision doit lister les liants de la machinerie TRAVERSÉE, pas de
  toute la machinerie du dossier. **BILAN FACTORIELLE : Déf.2 fidèle + récursion + C62 (∃!f) +
  équations 0!/succ — le n° 30 de la campagne est INTÉGRALEMENT percé.** Manifestes OK.
- **🎉🎉🎉 S3 FAIT — LA CLEF DE VOÛTE (agent build, P0→P7, 21/21 verts ; ii_4 entière 116/116).**
  ii_4_recollement_somme/ : ensembles_somme_indexee.py (P0 : AXIOME_SOMME_FAM en théorie dédiée
  S8 « theorie_somme_famille » — z∈⊔ ⇔ (∃i∈I) z ∈ X_i×{i}, corps valeur_famille, Déf.8 lue en
  PNG E II.30 p.81 ; + element_marque_dans_somme {i0∈I,u∈X_i0}⊢(u,i0)∈⊔) ; fibres_famille (P1-P2 :
  Xfib=graphe_terme(F, f⁻¹({yb}), "yb") ; x∈f⁻¹({f(x)}) SANS fonctionnalité) ; decomposition_fibres
  {,_bij} (P3-P7 : Φ=x↦(x,f(x)), inj CLOS 0 hyp, **eq_decomposition_fibres ⊢ Eq(E, ⊔_{y∈F} f⁻¹(y))**
  + **card_decomposition_fibres = l'ENTRÉE DES BERGERS**, hyps {Hf1 func f, Hf2 dom=E, Hf3 ∀x∈E
  f(x)∈F, HF pont fam↔valeur}). PIÈGES : τ-liant = lettre SIMPLE (tau_x rejette "cfb") ; ancre
  fibres = Déf.8 + Rem. L.11-14 (PAS une Prop numérotée). Manifestes OK (1952 notions, 0 à caler).
## 📋 A5 — RE-CARTAGE FAIT (agent recon, 25 juil soir) : ~26 items DÉBLOQUÉS sur 76
VERDICTS (preuves grep au transcript) : **A francs (9)** : n°26 multiples ; n°57 relation de
partition (est_partition EXISTE, checklist stale) ; n°60 f(A)≅A/R_A (passage_quotient_Rf fait) ;
n°66-1ʳᵉ moitié bo(ℕ) PÉRIMÉ-prouvé ; n°67 ⋂𝔉∈𝔉 ; n°95=133 Cantor pas-d'ensemble-des-cardinaux.
**A- (17)** : n°100-108 Prop.4 famille (B1 fait, B4=AXIOME_SOMME_FAM, reste B3 fonctorialité) ;
n°112/113/118 (§6.4 via S3) ; n°140 Zorn Cor.2 ; n°52/53/54/56/78/86/88/91/94 (Résumé).
**VRAIS MURS B (durs, brique nommée)** : sup cardinal ABSENT (114, 110-somme) ; comptes
combinatoires OPAQUES (30-42 : bâtir Card{injections}/binomial réel) ; AXIOME_INTER_FAM I≠∅ (89) ;
infra E/R-iso (12/59/61/62) ; Lemme 1 réunion filtrante (134-138) ; CST22 (1). Docstrings STALE à
rafraîchir en perçant : prop4_famille_cardinaux l.20-24, note n°57.
TOP-10 gain/effort (détail transcript agent) : #1 n°26 · #2 n°60 · #3 n°57 · #4 n°67+95+140 (⋃/⋂
d'un ensemble, 3 items d'un coup) · #5 n°101 Prop.4 (débloque 102-108/112/113) · #6 n°66-2e ·
#7 n°56 · #8 n°78 itérées · #9 n°94 choix fonctionnel · #10 n°118.
- **🎉 LOT-1 FAIT (agent build, 12 tests verts)** : **n°26 CLOS 0 hyp** (multiple_de_multiple +
  somme_multiples, ensembles_division_multiples.py, PDF E III.39 L.27-31 vérifié PNG ; reste c−d
  [soustraction absente] + identités quotients ; ⚠️ iii_5_6 à 10 entrées = CAP) ; **n°60 niveau
  valeurs** (b_bijective_valeurs {pont,Hf1} ⊢ inj∧surj, ensembles_decomposition_bijection.py ;
  piège : alpha_tau exige liant lettre SIMPLE (« _vf » rejeté) ⇒ re-dérivation C46 au liant _vf ;
  reste forme graphe est_bijection_de) ; **n°57** (relation_partition symétrique CLOS 0 hyp +
  réflexive {H_rec,H_parties}, casé dans ensembles_egalite_equivalence.py [ii_6 racine PLEIN] ;
  reste transitivité + le pont est_recouvrement⇒H_rec = EXACTEMENT le ⋃/⋂ du LOT-2 #4).
- ⚠️ La suite complète (garde-fou A4) s'est ÉTEINTE à 76% sans bilan (0 process, cause inconnue —
  probablement tuée pendant la fenêtre de limite de session). RELANCÉE pour couvrir A4+LOT-1.
## ⚠️ PASSATION → OPUS 5 (26 juil 1h30) — LIRE outils_ia/corpus/PASSATION_OPUS5.md
Fable épuisé (7%), retour JEUDI 31 juil 22h. Directeur = Opus 5 niveau max. Cron supprimé.
LOT-2 (⋃/⋂) mort en recon → À RELANCER (brief ci-dessous) ; suite full_suite7 (bzcamazs3,
scratchpad/full_suite7.txt) à vérifier. NOUVEAU protocole @source (façon @livre pour toute
source externe, PDF enregistré au projet) + étude Grimm (sources/grimm_gaia/) + veille
« représentation des erreurs » (Talia Ringer proof repair, LeanDojo…) au backlog.

- **📊 PROTOCOLE TRACES (25 juil soir, décision Karl)** : étage 2 de la théorie de la trace EN
  VIGUEUR — outils_ia/traces/{SCHEMA.md, events.jsonl} créés, rétro-remplis (37 événements des
  campagnes 24-25 juil : 12 percées, 6 bloqués-faux, verrous/remèdes avec taux, 4 murs). RÈGLE :
  chaque tick de clôture appende les événements du chantier (PERCEE/VERROU/REMEDE/MUR/
  BLOQUE_FAUX/TENTATIVE) ; les briefs d'agents demandent une section EVENTS. Étages 1 (DAG/M1)
  et 3 (stats) = sessions dédiées, rien d'irréversible. Design : ameliorations/THEORIE_TRACE.md.
- **Tick courant** : suite complète relancée en fond + agent build LOT-2 (#4 ⋃/⋂-d'un-ensemble =
  n°67+95+140 d'un coup ET ferme H_rec de n°57). Ensuite LOT-3 = #5 Prop.4 famille (102-113).

- **🎉🎉🎉 T3b+T2 FAITS, TOUS VERTS DU 1er COUP (agent build) ⇒ CHANTIER A4 TERMINÉ.**
  ii_4_recollement_somme/ : ensembles_somme_constante.py (248 l : famille_constante_valeur {i0∈I} ;
  **somme_constante_egale_produit {HFc} ⊢ ⊔(fam_const,I) = a×I** [double inclusion C48, PAS de
  bijection] ; **card_somme_constante {HFc} ⊢ Σ_{ι∈I} a = Card(a×I)** = « ab » du Cor.2 fidèle
  E III.27 L.27-29 PDF p.130 vérifié PNG ; cœur générique _somme_ponctuelle_produit) +
  ensembles_bergers_plein.py (125 l : **bergers_plein {Hf1,Hf2,Hf3,HF,Hc} ⊢ Card(E) =
  produit_cardinal_binaire(c,F)** — chaîne S3 ∘ congruence ; Hc = « les fibres SONT c », lecture
  fidèle de « a_ι = a »). Tests 5/5 + 4/4 ; recollement_somme 50/50 ; ii_4 125/125 ; theorie==22.
  PIÈGE : element_marque_dans_somme refuse p/q/i libres ⇒ α-renommer pcs/qcs les ∃ d'AXIOME_PRODUIT
  AVANT (congruence_existe). RESTE A4-résiduels (queues documentées, non bloquantes) : Prop.4 B2-B4
  fonctorialité ; T3a Prop5b partition ; 0!=1-def2 ; bergers version fibres ÉQUIPOTENTES (fonctorialité
  de ⊔) ; décision d'encodage valeur_famille:=valeur (migration ~40 fichiers).
- ⚠️ 2e COUPURE limite de session (25 juil, reset 20h30) : le 1er agent T3b+T2 est mort en
  recon sans rien écrire. RELANCÉ à la reprise (même brief + consigne d'écrire tôt) → SUCCÈS ↑.
- **Tick courant (T3b+T2, LA DERNIÈRE LIGNE DROITE)** : famille constante Σ_{ι∈I} a = Card(I)·a
  (Prop6Cor2) sur AXIOME_SOMME_FAM (les familles abstraites n'ont besoin d'AUCUN pont — l'axiome
  parle valeur_famille) puis BERGERS PLEIN : f surjective à fibres de cardinal c ⇒ Card E = Card F·c
  (card_decomposition_fibres + Σ constante). DÉLÉGUÉ à un agent build.
- **RESTE A4 (après)** : T3a Prop5b partition ; Prop.4 B2-B4 fonctorialité ; Prop.10 §4.8 indexée ;
  0!=1-def2 ; décision d'encodage « valeur_famille := valeur » (migration ~40 fichiers, documentée) ;
  Prop.4 B2-B4 (fonctorialité indexée) ; cas de base 0!=1 def2 (briques cartographiées par
  l'agent T1c, voir son fichier — option rapide).
- ⚠️ COUPURE limite de session (24→25 juil, reset 15h30) : le 1er agent T1c est mort en recon
  sans rien écrire. RELANCÉ le 25 juil avec brief enrichi (routes (a) invariance des familles
  sur seg(n) et (b) u_n→succ(n) explicitées ; fichier cible ensembles_factorielle_def2_rec.py).
- **Tick courant (T1c, FERMETURE DE LA BOUCLE DÉF.2)** : instancier u := famille_successeurs(n)
  dans produit_fini_recursion → récursion de factorielle_def2 : (succ n)!_def2 = n!_def2 · succ(n)
  [u_n = succ(n) via famille_successeurs_valeur {n∈seg(succ n)}] + cas de base
  factorielle_def2(ZERO) : seg(ℕ,0)=∅ (à dériver ou hypothèse-position) puis ∏_∅ = {fonction vide}
  → Card=UN (brique produit-vide à chercher/bâtir : produit_famille(u,∅) ≅ {∅} ; grep
  produit_famille vide / fonction vide). Ancien plan (T1b-3) archivé ci-dessous :
  Card(∏_{seg(n+1)} u) = produit_cardinal_binaire(Card... forme : ∏_{seg(n)} u, u_n) en chaînant
  T1b-1 (seg(n+1)=seg(n)∪{n}, {n∈ℕ}) et T1b-2 (adjonction, I:=seg(n), j:=n) par congruence-trou
  sur produit_famille(u, ·) ; H1=n∉seg(n) DÉCHARGEABLE par point_hors_segment [CLOS, c60] ;
  restent {n∈ℕ, H2/H3-graphes}. Puis T1c : instancier u:=famille_successeurs → récursion de
  factorielle_def2 → convergence avec factorielle_zero/succ_fallback (0!=1 déjà : ∏_∅=... vide).

## 🎉 A4 — PREMIÈRES PERCÉES (25 juil, pendant la suite complète en fond)
- **S1 PERCÉ (« bloqué faux » n°6)** : `carte_cardinaux_valeur` DÉBLOQUÉE (3/3 verts) — le
  NotImplementedError « verrou-τ session dédiée » datait d'avant le fix subst. {ι₀∈I} ⊢
  A(ι₀)=Card(E_ι₀), 1 hyp. B1 de Prop.4 close. Piège consigné : graphe_terme_valeur veut des NOMS.
- **T1a FAIT — LA DÉF.2 DU LIVRE POSÉE FIDÈLEMENT** (`ensembles_famille_successeurs.py`,
  iii_3_6_familles, 4/4 verts) : `factorielle_def2(n) := ∏_{i<n}(i+1)` = produit_cardinal de la
  famille graphe_terme(seg(ℕ,n), succ(ι), ι) — même segment que la chaîne C62 (convergence prête) ;
  famille fonctionnelle [CLOS] + valuation [1 hyp]. @livre Def.2 E III.41 L.28-29 posé, manifestes OK.
- **PLAN T1b DÉTAILLÉ (recon 25 juil — la ligne de vie des prochains ticks)** :
  cible : Card(produit_famille(u, seg(succ n))) = produit_cardinal_binaire(Card(∏_{seg(n)}u), Card(u_n)).
  DEUX briques neuves : **(1) seg(ℕ, succ n) = seg(ℕ,n) ∪ {n}** (segment OUVERT ; transposer le cœur
  pointwise _membre_equivalence d'ensembles_prop5_intervalle.py [fermé] ; version GÉNÉRIQUE borne-
  variable pour éviter le résidu τ noté là-bas ; + n∉seg(n) = point_hors_segment déjà CLOS c60) ;
  **(2) LA BIJECTION ∏_{I⊔{j}}(u) ≅ ∏_I(u) × u_j** réalisée par F ↦ (F|I, F(j)), inverse
  (G,x) ↦ G∪{(j,x)} (prolongement-SINGLETON, trivial vs le gros recollement Prop6) — PATRON EXACT :
  proj_est_bijection (ensembles_produit_petits.py:288, schéma fonctionnel∧domaine∧injectif∧image →
  est_bijection_de → S5 → Eq). + (3) lemme produit-singleton ∏_{u,{j}} ≅ u_j (calquer eq_produit_un).
  + (4) assemblage cardinal via _prop1_direct_t [CLOS, 3 copies] + réécritures façon
  factorielle_succ_fallback (_rewrite/composer_egalites). SOCLE PRÊT : AXIOME_PRODUIT_FAM (1 des 22),
  membre_produit_partiel/projection_J=restriction [CLOS], _prop1_direct_t. NE SERVENT PAS :
  extension_produit (=∏ d'applications), Prop7 (conditionnelle), currying. Emplacement :
  iii_3_6_familles/ (2 fichiers : ensembles_seg_successeur.py + ensembles_produit_adjonction.py).
  ENSUITE : T1c convergence Def.2↔C62 ; S3 recollement indexé (bergers T2, Prop5b/6Cor2 T3) ; Prop4 B2-B4.

## 📋 CHANTIER A4 (familles indexées) — CARTE FAITE, ATTAQUE EN COURS
Recon complète (agent, 25 juil). CHEMIN CRITIQUE : S1 (valuation cardinal-valuée — annotation
« verrou-τ session dédiée » de carte_cardinaux_valeur DATE D'AVANT le fix subst ⇒ PROBE en cours,
bloqué-faux n°6 potentiel) ; S3 recollement indexé = clef de voûte (bergers plein T2 + Prop5b T3a
+ Prop6Cor2 T3b convergent dessus) ; point d'attaque le moins risqué = T1a (famille i↦i+1 par
graphe_terme + graphe_terme_valeur, τ-léger) → T1b (produit fini indexé, récursion C61-style)
→ T1c (raccord Def.2-produit ↔ caractérisation C62 close). Défs-termes ∑/∏ de familles EXISTENT
(ensembles_cardinaux.py:125-137, opaques) ; binaire clos partout ; iii_3_6_familles = dossier-trou
officiel. Suite complète en fond (garde-fou A1-A3) — ticks légers jusqu'à son verdict.

## 🎉🎉🎉 CHANTIER A3 TERMINÉ (25 juil) — C62 SUR LE VRAI ℕ, BON ORDRE DÉCHARGÉ
`ensembles_ordre_NN_graphe.py` (iii_6_1), 5/5 verts (3:17) : G_≤ (S8 pleine forme, théorie dédiée) ;
`couple_dans_G_ordre` [CLOS, construit exotique s0g/t0g puis instancié — 2 collisions de briques
percées : trou « w » de couple_egal_implique_composantes (_wrap4) + liants d'épine sous ≤] ;
**`bo_graphe_NN` ⊢ est_bien_ordonne(R_G≤, ℕ) [CLOS]** (marcheur congruence-par-feuilles à épine
IDENTIQUE — binders xo/yo/zo/X/a/w de n_bien_ordonne — + alpha_bridge final vers la forme-défaut) ;
**`c62_recursion_sur_NN` et `fonction_recursion_NN` : 2 RÉSIDUS {ebf, rc}** — le « ℕ étant bien
ordonné » du livre est un THÉORÈME déchargé. Stratégies : 1 échec (épine défaut), 2 échec (renommage
∃ dans le marcheur), 3 SUCCÈS (épine identique + bridge final + lemme-feuille exotique-instancié).
LEÇONS : (a) épine identique >> renommage dans le marcheur ; (b) toute brique nom-basée appelée sur
des liants d'épine ⇒ _inst_gen systématique ; (c) le vrai RHS d'un lemme instancié s'EXTRAIT
(equivalence_avant(...).conclusion.sous[1]), jamais reconstruit. Manifestes régénérés.

## 🔁 BASCULE 25 juil : boucle CRON 60s (job a94b1943) avec prompt corrigé V2 — POLITIQUE
## MUR-PERÇAGE (jamais contourner : construire les briques/théories manquantes, récursif,
## trans-chantiers ; anti-meulage 3-stratégies⇒rapport de mur⇒prérequis ; journal fait foi).
- **🎉🎉 CHANTIER A1 TERMINÉ (25 juil)** : `factorielle_succ_fallback` VERT (2:44, seul sans plafond —
  leçon : background long ⇒ JAMAIS de paramètre timeout). BILAN A1 : f(0)=1 [6 hyps honnêtes] +
  f(succ n)=succ(succ n)·valeur(u,[0,n]) [9 hyps, forme-fallback, T_Z=regle(zcard="Z")] + briques
  CLOS t_fac_en_vide/restriction_vide_est_vide/seg_inclus_e + u_non_vide/dom_restriction_seg.
  Manifestes régénérés. Écarts documentés : fallback prev (attend B1 sup_borne), indexation
  f(n)=(n+1)!, données d'ordre en hypothèses (attendent A3 sur ensemble_NN()).
- **🎉🎉 CHANTIER A2 TERMINÉ (25 juil)** : `ensembles_c62_fonction_unicite.py`, 4/4 verts en 0,86 s,
  1er coup. `⋃𝔇_tot⊂E×V` [CLOS] + `est_un_graphe(⋃𝔇_tot)` [CLOS] + **`unicite_fonction_c62` ⊢
  {bo,ebf,rc} (∀g)((func∧graphe∧dom=E∧équation)⇒g=f)** — joint à fonction_recursion_c62 = (∃!f)
  parmi les graphes. Manifestes régénérés. Dossier c62 à 10 entrées = CAP.
- **🎉🎉 A3 PHASE 1 : BLOCAGE ensemble_NN() TOMBÉ (25 juil)** — probe VERTE : c62_recursion_sur_N
  ET fonction_recursion_c62 s'instancient au TERME ℕ (3 hyps, theorie==22). Le « binder interne du
  gluing » était le renommage gratuit pré-fix. ⇒ mettre à jour la docstring c62 l.60-65 (périmée) +
  exposer des wrappers e=ensemble_NN() quand le bon ordre sera dérivé.
- **🎉 A3 PHASE 2 : est_bien_ordonne(≤,ℕ) EST DÉJÀ CLOS** (« bloqué » faux une 5e fois !) —
  `n_bien_ordonne()` (iii_6_1/ensembles_n_bien_ordonne.py:419) ⊢ est_bien_ordonne(ordre_induit_NN, ℕ),
  CLOS 0 hyp, testé. Nuances : conclusion == cible à α près (liant τ de est_cardinal — test :39) ;
  appartenance_NN déclenche N_existe ~5 min (1×/session).
- **A3 PHASE 3 (le VRAI reste) : LA JONCTION graphe↔callable.** La chaîne C62 est paramétrée par un
  ordre-GRAPHE (R=_graphe_R(Gle) : (a,b)∈Gle) ; n_bien_ordonne parle du CALLABLE ordre_induit_NN
  (et(et(a≤b, a∈ℕ), b∈ℕ)) — formules ≠ structurellement, MP impossible direct. Options tick suivant :
  (i) AUDITER la plomberie : la chaîne c60/c62 passe-t-elle partout par un R CALLABLE (auquel cas une
  variante c62_recursion_sur_R(ordre_induit_NN) marche telle quelle — seg_ext(e,x) n'embarque pas R !)
  → AUDIT FAIT : _graphe_R construit DANS les 8 fichiers de la chaîne (option (i) = replomberie de
  toute la machinerie déposée, REJETÉE). ROUTE RETENUE (ii-raffinée), plan tick suivant :
  (1) vérifier _graphe_R accepte un TERME pour G (comme e=NN a marché) ; (2) fichier
  `ensembles_ordre_NN_graphe.py` (iii_6_1, entrées<10 à vérifier) : terme G_le=app("G_ordre_NN"),
  axiome S8 dédié (∀a∀b)((a,b)∈G_le ⇔ ordre_induit_NN(a,b)), théorie dédiée motif Dtot ;
  (3) marcheur `congruence_selon_feuilles(f_graphe, f_callable, table_equiv)` — motif bridge_equiv
  (equiv_neg/ou_congruence/congruence_existe) mais aux FEUILLES atomiques via l'axiome S8 (au lieu
  d'α) → ⊢ est_bien_ordonne(R_Gle, ℕ) ⇔ est_bien_ordonne(ordre_induit_NN, ℕ) ; (4) MP avec
  n_bien_ordonne ⇒ **bo(R_G≤, ℕ) CLOS** ; (5) wrappers C62/assemblage e=ℕ, G=G_le : les 3 résidus
  tombent à 2 {ebf, rc} — LES DONNÉES DE LA RÈGLE SEULES. Piège PERF : N_existe ~5 min au 1er appel.
- **PLAN A2 (recon faite, prêt à builder dès 3B clos)** : `graphe_egal_par_valeurs(f,g)` EXISTE CLOS
  (ii_3_4_fonctions/ensembles_extensionnalite.py:171 — ⚠️ exige AUSSI est_un_graphe(F/G), 6 prémisses).
  À construire : (i) `est_un_graphe(⋃𝔇_tot)` [chaînon neuf : p∈𝔓(E×V) (1er conjoint du corps Dtot,
  _inst_Dtot avant) → p⊂E×V (membre_parties_t, powerset_deux.py:67) → w∈p→w∈E×V→couple
  (_inclus_produit_est_graphe, application_valeur.py:163 ; membre_union_famille pour w∈⋃𝔇) —
  motif chi_est_graphe prop12_powerset.py:221] ; (ii) `unicite_fonction_c62` : pour tout g avec
  (func g ∧ graphe g ∧ dom g=E ∧ (∀z∈E)val(g,z)=T(z)) ⊢ g=f — les 6 prémisses de graphe_egal_par_
  valeurs fournies par fonction_globale_fonctionnelle [CLOS] + dom_fonction_globale + equation_
  fonction_globale + (i) + les hyps de g ; egalite_valeurs via T(x) commun (transport dom f=E).
  Fichier : ensembles_c62_fonction_unicite.py (dossier c62 à 9 → 10 entrées = CAP après ça).

## 🔄 CAMPAGNE MURS (Fable niveau max) — lancée 25 juil, boucle auto-cadencée
Ordre : (1) factorielle équations séparées f(0)=1 / f(n+1)=(n+1)·f(n) ; (2) unicité-graphe (∃!f) ;
(3) bo(≤,ℕ) [re-tester ensemble_NN() post-fix subst] ; (4) familles indexées (Def.2-produit, bergers) ;
(5) re-carter les ⏸ débloqués. Un focus/tick, garde-fous habituels.
- **Tick 1 (25 juil)** : recon chantier (1) — verdict : briques f(0)=1 TOUTES présentes ; VRAI trou
  = Card([0,n[)=n (segment OUVERT ; seul Card([0,b])=b+1 fermé existe, prop5_intervalle_zero CLOS) ;
  sur la variable (Enat,Gle) « rien avant 0 » N'EST PAS dérivable ⇒ données de position en hypothèses.
- **🎉 Tick 2 (25 juil)** : **f(0)=1 DÉMONTRÉ** (`ensembles_factorielle_zero.py`, 3 tests verts 4,1 s,
  1er coup) : `t_fac_en_vide` ⊢ T_fac(∅)=1 [CLOS — garde-disjonction + S7 + S5/existe_temoin ; ¬¬ par
  a_implique_a+S3] ; `restriction_vide_est_vide` ⊢ F|∅=∅ [CLOS] ; **`factorielle_zero` ⊢ {bo, ebf, rc,
  essais_restriction, ZERO∈E, seg(≤,E,ZERO)=∅} valeur(f,ZERO)=UN** [6 hyps honnêtes]. theorie==22.
- **✅ Tick 3A (25 juil)** : briques cas-successeur VERTES (`ensembles_factorielle_succ.py`, 4 tests,
  0,5 s, 1er coup) : `t_fac_en_non_vide(T,u,⊢u≠∅)` ⊢ T(u)=(card(dom u)+1)·u(dom u) [garde-disjonction
  ordre inverse + _ou_commute_gd + S7 + S5/existe_temoin ; ⊢¬(u=∅) sert 2×] ; `seg_inclus_e` [CLOS] ;
  `dom_restriction_seg` ⊢ {bo,ebf,rc} dom(f|seg(x))=seg(x). DÉCISION D'ARCHI : le liant cardinal
  « Zfac62 » de la règle (anti-verrou pré-fix) est α-incompatible avec prop5 (binder « Z » défaut) et
  renommer un liant τ EXTERNE est hors noyau ⇒ tick 3B utilisera regle_factorielle(zcard="Z") (variante
  canonique, légitime post-fix subst) via les fonctions GÉNÉRIQUES c62 (pas les wrappers factorielle_*).
- **Tick 3B (prochain, dans ensembles_factorielle_succ.py — dossier à 10 entrées, CAP)** :
  (i) `u_non_vide` {ZERO∈E, ZERO∈seg(succ n), bo/ebf/rc} ⊢ f|seg(succ n)≠∅ [témoin (0,y)∈f via
  ZERO∈dom f (e_inclus_dom/dom=E) + rebuild couple_restriction ; non_vide_ssi_element ⇐] ;
  (ii) chaîne finale `factorielle_succ_fallback` avec T_Z=regle_factorielle(zcard="Z") :
  equation_restriction_fonction(T_Z,T_Z) instancié à successeur(vn) [succ n∈E hyp] → t_fac_en_non_vide
  → réécrire dom u→seg [dom_restriction_seg + congruence-trou sur produit(succ(card(·,Z)),val(u,·))]
  → seg(succ n)=[0,n] [HYP donnée d'ordre] → cardinal([0,n],Z)=succ n [prop5_intervalle_zero CLOS,
  hyp est_entier(n)] → conclusion f(succ n) = produit(succ(succ n), valeur(u, seg(succ n))),
  forme-FALLBACK (prev=u(seg) faute de sup_borne — écart documenté). NB indexation : la règle déposée
  encode f(n)=(n+1)! (docstring factorielle_existence) — cohérent, à documenter dans le livrable.

## ✅✅ VERDICT FINAL 25 juil — SUITE COMPLÈTE 100 % VERTE, DEUX FOIS
- Passe post-fix-subst : **3566 passed, 0 failed (2:43:57)** — le verrou-τ est clos sans régression.
- Passe finale avec TOUS les nouveaux fichiers C62/factorielle : **3588 passed, 0 failed (2:20:22)**.
theorie==22 partout. Les chantiers « verrou-τ » et « fonction factorielle + forme du livre » sont FERMÉS.

## 🎉🎉🎉 SESSION 25 juil (suite 2) — LE PONT RESTRICTION : LA FORME DU LIVRE f(n)=T{f⁽ⁿ⁾}
**L'équation FIDÈLE de C62 (E III.46) est DÉRIVÉE** — la règle lit la RESTRICTION, plus le point :
- `ensembles_c62_fonction_restriction.py` (258 l) — **LE CŒUR** : `restriction_egale_essai_seg`
  ⊢ {p∈𝔇_tot, est_essai(p,x)} f|seg(x) = p|seg(x) (ÉGALITÉ DE GRAPHES, double inclusion + A1).
  Sens dur : (a,b)∈f vient d'un AUTRE essai q, mais b=val(q,a)=T(a)=val(p,a) (valeurs épinglées)
  ⇒ (a,b)∈p. + p⊂f, p|A⊂f|A. [5 tests, 0,35 s, PREMIER COUP]
- `ensembles_c62_equation_restriction.py` (140 l) — hypothèse honnête `essais_restriction(T,vh)`
  (lecture-restriction au point-extrémité, style regle_locale) + **🎯 equation_restriction_fonction :
  {bo, ebf, rc, essais_restriction} ⊢ (∀n∈E) valeur(f,n) = T(restriction(f, seg(n)))**. [2 tests, 3,6 s]
- `factorielle_equation_restriction` (ensembles_factorielle_fonction.py) — **LA FORME DU LIVRE pour la
  factorielle : (∀n∈ℕ) f(n) = T_fac( f|[0,n[ )**, 4 hyps honnêtes. [3 tests, 41,7 s]
Motifs réutilisés : décomposition/rebuild AXIOME_RESTRICTION (témoins p/q), couple_donne_valeur,
_congruence_T par trou wct (motif _inst_gen). theorie==22 partout, rien postulé.
RESTE §5.8 : équations séparées f(0)=1 / f(n+1)=(n+1)·f(n) (cas du τ + Card(dom u)=n) ; Def.2-produit
(familles) ; bo(≤,ℕ) irréductible.

## 🎉🎉 SESSION 24-25 juil (suite) — LA FONCTION FACTORIELLE EXISTE (assemblage C62 COMPLET)
**L'assemblage essais→fonction (le trou O1) est CONSTRUIT, générique, puis instancié à T_fac.**
4 nouveaux fichiers (tous ≤300 l, tests fichier-seul VERTS, theorie==22, rien postulé) :
- `iii_6_2_recursion_c62/ensembles_c62_fonction_globale.py` — 𝔇_tot := {p∈𝔓(E×V) | (∃n∈E) est_essai(p,n)}
  (motif S8/théorie dédiée de Dfam_real, sélecteur « n∈E ») ; f := ⋃𝔇_tot ; coincidence/compatibilité de famille
  CLOS (valeurs épinglées sur la règle) ; **est_fonctionnel(f) CLOS 0 hyp**. [4 tests, 0,3 s]
- `…/ensembles_c62_fonction_domaine.py` — essai_dans_Dtot (pont bien-formes→ambiant + S8⇐) ;
  **dom(f)⊂E CLOS** ; E⊂dom(f) et **dom(f)=E sous les 3 résidus C62**. [4 tests, 3,3 s]
- `…/ensembles_c62_fonction_existence.py` — valeur(f,z)=T(z) (valeur_union_famille + équation d'essai,
  α-pont alpha_bridge pour le liant pess) ; équation universelle ; **🎯 (∃f)(func ∧ dom=E ∧ (∀z∈E)f(z)=T(z))
  sous {bo, essais_bien_formes, rule_codomain}** = LA conclusion C62 niveau valeur-règle. [4 tests, 6,9 s]
- `iii_5_8_factorielle/ensembles_factorielle_fonction.py` — **factorielle_fonction_existe : la fonction
  factorielle par récurrence C62 EXISTE** (3 résidus honnêtes). [2 tests, 15,8 s]
LEÇON (piège collision de nom, prévenu) : liants EXOTIQUES zfgl/fglb/nDt pour l'équation et l'∃ — la règle
factorielle lie u/v/y/z en interne ⇒ quantifier sur un nom lié par T capturerait à la construction.
Piège rencontré : valeur_union_famille(p="pess") rend famille_compatible au liant pess (α-variant) ⇒ alpha_bridge.
**Écarts de fidélité documentés (prochains chantiers)** : (i) équation au POINT (pas encore T{f|seg}) ;
(ii) Def.2-produit-de-famille (∏_{i<n}(i+1), E III.41 L.28-29 lu au PDF p.144) = mur familles indexées ;
(iii) équations séparées f(0)=1 / f(n+1)=(n+1)·f(n) = élimination des cas du τ + pont Card(dom u)=n ;
(iv) résidu bo(≤,ℕ) irréductible (bon ordre clos = intervalles bornés seulement).

## 🔓 SESSION JOUR 24 juil — VERROU-τ RÉSOLU À LA RACINE (fix subst) + MUR C62/FACTORIELLE PERCÉ
**Le verrou-τ n'existe plus.** Racine trouvée : `subst_t`/`subst_f` (outil_formule.py) renommaient un liant homonyme
même quand la variable substituée n'était PAS libre dessous (renommage GRATUIT, sans risque de capture réel) ⇒ deux
chemins de construction α-divergeaient ⇒ « modus ponens : mineure ≠ antécédent ». FIX = court-circuit CS textbook
`(T|x)t = t si x ∉ libres(t)` (2×3 lignes). Noyau INTOUCHÉ, theorie==22, gain de perf en prime.
- **Repro AVANT/APRÈS** : `somme_cardinale_commutative(diff, b)` (τ Card-valué) rouge→VERT CLOS 0 hyp, les 2 sens.
- **Suite complète** : 3558 verts / 8 « rouges » — TOUS traités : 7 = tests-DOCUMENTATION du mur (assertaient « ça lève »),
  retournés en tests de déverrouillage ; 1 = `division_successeur`, qui était rouge AUSSI avant le fix (vérifié A/B sur
  l'ancienne subst) — réparé par `_wrap4` sur `distributivite_cardinale` (l'arg NOMMÉ « q » collisionnait le témoin
  interne « q » de la machinerie produit). Suite complète re-lancée pour verdict 100 % (en cours à la rédaction).
- **🎉 MUR C62/FACTORIELLE PERCÉ (O3 levée)** : `factorielle_essais_existe()` CONSTRUIT désormais
  ⊢ (∀n)(n∈ℕ ⇒ (∃p) est_essai(p, T_fac, ≤, ℕ, n)) sous 3 résidus C62 honnêtes {bo(≤,ℕ), essais_bien_formes,
  rule_codomain}. Le wrapper hygiénique clôt aussi la classe-VALEUR. Pont maximalité (trichotomie §III.2) construit
  au témoin τ. Tests retournés VERTS : factorielle 23/23 (12:07), maximalité 7/7 (5:38), hygienic 5/5.
- Adaptation douce : `_A_inclus_interv_raw` (principe récurrence) reconnaît la forme déjà propre (pont s7 sans objet
  quand `ZERO@0` n'existe plus) — 11/11 verts. `gate_onto_top` 13/13, commute 9/9, prop10 3/3 inchangés.
- **CONSÉQUENCE FRONTIÈRE : re-carter les murs.** Le mur « C62 récursion-fonction » (n°30-42 factorielle/binomial…)
  est OUVERT (les essais existent ; reste unicité/recollement → fonction factorielle). Les items jadis « verrou-τ »
  (usages directs de commutativité sur τ) sont TRACTABLES sans `_inst_gen`. À re-vérifier : graphe_terme≠22 ?
  Prochaine session recommandée : **factorielle Def.2 n°30+ via C62 déverrouillé**.

## ☀️ BILAN NUIT 23→24 juil (à lire au réveil, Karl)
**🎉🎉 THÉORÈME 1 §III.5.6 (DIVISION EUCLIDIENNE) COMPLET — EXISTENCE *ET* UNICITÉ démontrées cette nuit.**
- EXISTENCE : ensembles_division_existence_final.py (division_existence, (∀n)(Fini n⇒(∃q,r)(b·q+r=n et r<b))).
- UNICITÉ : ensembles_division_unicite.py (_unicite, (b·q+r=a et r<b et b·q'+r'=a et r'<b)⇒(q=q' et r=r')) — sous-lemmes
  _gap, _lt_chain (cœur commute-free). + n°24 Déf.1 (reste/quotient/multiple/diviseur/divisible) FAIT.
Tout « CLOS modulo C61 » (résidus honnêtes = ceux de l'existence de ℕ), theorie==22, SANS toucher noyau/commute (verrou-τ
contourné par _inst_gen + routes sans commutativité). C'était le PLUS GROS chantier ouvert du §III.5 ; il est fermé.
**Tests fichier seul VERTS confirmés : existence 3 passed (20:54) ; unicité 4 passed (15:20) ; défs n°24 4 passed (0,22s).**
**FRONTIÈRE POST-DIVISION (tick final) : le front TRACTABLE-sans-infra-dédiée est ÉPUISÉ.** La division était le dernier gros
item tractable ; il est fait. Re-vérif nuit (n°86/78/89/94/121/110/41/20/37 + n°23/24) = tout le reste est derrière les murs
documentés : C62 récursion-fonction (factorielle/binomial n°30-42), familles indexées (R/§3.3/§6.4), Zorn (Hessenberg/limites),
arith cardinale infinie (§6.4), graphe_terme≠22 (produits d'applis), + n°26 illisible au PDF (scan sans texte). ⇒ boucle en
HEARTBEAT ; reprise = sessions dédiées (chaque mur = un chantier infra). Le verrou-τ, lui, est LEVÉ (contournement _inst_gen).
--- détail existence ci-dessous ---
**🎉 DIVISION EUCLIDIENNE, EXISTENCE (Th.1 §III.5.6, n°23) DÉMONTRÉE** « CLOS modulo C61 »
(résidus honnêtes {b≠0, Fini b, pred_univ, principe_recurrence, cardinal_pas_entre} = les MÊMES que l'existence de ℕ).
`ensembles_division_existence_final.py` : `division_existence` ⊢ (∀n)(Fini n ⇒ (∃q)(∃r)(b·q+r=n et r<b)), concl==énoncé,
5 hyps, theorie==22. Construit ENTIÈREMENT à partir de théorèmes clos, SANS toucher noyau/commute (route commute-free).
Chaîne : `_diff_inf_egal` (a−b≤a) → `_diff_strict` (a−b<a, route SANS commutativité via somme_strict_monotone+strict_irreflexif,
verrou-τ contourné par `_inst_gen`) → `_strong_step` (récurrence forte + `trichotomie_finis` : n<b→_pas_petit, b≤n→_pas_grand
avec R{n−b} tiré de S{n}) → `recurrence_forte`. n°23 marqué `[~]` CLOS modulo C61 (PAS `[x]` FINI sec, honnêteté). RESTE pour
le Th.1 COMPLET : UNICITÉ (q,r uniques) = ⏸ CHANTIER (tick 69, prérequis non-fidèlement dispo à §5.6) :
il faut (i) q<q'⇒succ(q)≤q' (gap successeur, = cardinal_pas_entre, résidu C61) ; (ii) monotonie NON-STRICTE du produit
à GAUCHE (q+1≤q'⇒b·(q+1)≤b·q') — seul produit_strict_monotone (a·c<b·c, mult À DROITE) existe ; (iii) commutativité produit
b·q=q·b via _inst_gen. Assemblage ~150 l + tests 20 min ⇒ session dédiée. L'EXISTENCE (le dur) est faite ; l'unicité est
« mécanique mais lourde ». Déféré. NB simplification_multiplicative (§6.3) INTERDIT ici (postérieur, infidèle). **Def.1 n°24 FAIT** (ensembles_division_definitions.py, défs fidèles sur produit
cardinal réel : divise_cardinal/est_multiple/est_diviseur/reste_cardinal/quotient_cardinal ; test 4 passed ; n°24 coché [x]). **Briques VERTES (tests fichier seul) :** _diff_inf_egal, _diff_est_fini,
_diff_strict, _strong_step, division_existence. **pytest test_division_existence_final.py = 3 passed (20:54, lourd mais slow-marké).**
**Percée réutilisable :** `_inst_gen` (symbolique puis `instancie` le τ Card-valué) contourne le verrou-τ ; le fix infra du
verrou reste utile ailleurs mais N'EST PLUS bloquant. Mémoire bourbaki-commute-ordre-dependant à jour.
**Cases fermées cette nuit : n°23 (existence, [~] CLOS modulo C61) + n°24 (Déf.1, [x]).** Unicité déférée ⏸ (prérequis
successeur-gap + monotonie produit non-stricte). ⚠️ CORRECTION (tick 71, garde-fou honnêteté) : l'UNICITÉ n'est PAS bloquée — mes prérequis « manquants » EXISTENT :
produit_cardinale_monotone_droite(q,q',b) ⊢ (q≤q')⇒b·q≤b·q' [SANS commutativité, facteur gauche b fixe, §3.3 position-OK],
produit_succ_distribue(b,q) ⊢ b·(q+1)=b·q+b, cardinal_pas_entre/successeur_ordre_strict (gap q<q'⇒q+1≤q', résidu C61),
somme_strict_monotone + somme commutative via _inst_gen (b·q+r<b·q+b), simplification_additive_finie (r=r'). ⇒ UNICITÉ =
build ~180 l « CLOS modulo C61 », TRACTABLE. PLAN (ensembles_division_unicite.py, INCRÉMENTAL — sous-lemmes testables) :
  · _gap(q,q') : {card q,card q',entiers} q<q' ⇒ succ(q)≤q'. Via successeur_ordre_strict(q',q) [(q'<q+1)⟺(q'≤q)] +
    antisymetrique_card : q<q' ⇒ ¬(q'≤q) [sinon antisym q=q', contra q≠q'] ⇒ ¬(q'<q+1) ⇒ (comparabilité) succ(q)≤q'.
  · _lt_chain(b,q,q',r) : {b≠0,entiers, q<q', r<b} b·q+r < b·q'+r'. b·q+r < b·q+b [somme_strict_monotone(r,b,b·q)
    + somme commut via _inst_gen] = b·(q+1) [produit_succ_distribue] ≤ b·q' [produit_cardinale_monotone_droite(succ q,q',b)
    via _gap] ≤ b·q'+r' [inf_egal_somme_droite]. Transitivité < / ≤.
  · unicite : trichotomie_finis(q,q') ; q<q' ⇒ _lt_chain ⇒ b·q+r<b·q'+r'=b·q+r contra strict_irreflexif ⇒ ¬(q<q') ;
    symétrique ¬(q'<q) ; donc q=q' ; puis b·q+r=b·q+r' ⇒ r=r' [simplification_additive_finie, a=b·q entier (produit entiers)].
  Résidus : b≠0, entiers, + C61 (via successeur_ordre_strict/cardinal_pas_entre) ⇒ « CLOS modulo C61 ».
  LEÇON HONNÊTETÉ : « bloqué » faux 3× (division, ℕ, unicité) ⇒ TOUJOURS grep les bricks avant de déférer.
  BRICKS EXACTS confirmés : successeur_ordre_strict(x,b)⊢(card x,fini b)⇒((x<b+1)⟺(x≤b)) [iii_5_2/ensembles_successeur_ordre] ;
  inf_egal_antisymetrique_card()⊢(∀a∀b)((a≤b,b≤a,card a,card b)⇒a=b) ; trichotomie_finis(a,b) accepte des TERMES ;
  strict_implique_inf_egal(a,b) accepte termes ; inf_egal_reflexif_general()⊢(∀X)(X≤X) [instancier au TERME succ q ;
  inf_egal_reflexif SIMPLE veut un NOM] ; _ex_falso(thmP,thm¬P,cible) [ensembles_cardinaux_consequences:73] pour la branche
  impossible q'<succ q ; produit_cardinale_monotone_droite(q,q',b)⊢(q≤q')⇒Card(b×q)≤Card(b×q')=b·q≤b·q' [iii_3 ordre_cardinaux].
  BUILD INCRÉMENTAL sous-lemme/tick (petits tests) : _gap d'abord (~40 l, testable seul sur q,q' entiers), puis _lt_chain, puis unicite.
  ✅ _gap VERT (tick 72) + ✅ _lt_chain VERT (tick 75, 6 hyps {Fini b,q,q',r ; q<q' ; r<b}, theorie==22) — le CŒUR
  (b·q+r<b·q'+r' sous q<q', SANS commute via prop4_translation_stricte). Pièges corrigés : produit_binaire_entier via
  _inst_gen (pas d'appel défaut) ; inf_egal_transitive_general est DÉJÀ ∀-clos ⇒ instancie direct (pas _inst_gen).
  RESTE : unicite (trichotomie + 2×_lt_chain + strict_irreflexif + prop4_translation_injective pour r=r').
  _lt_chain BRICKS EXACTS confirmés (tick 73) : somme_strict_monotone(r,b,X)⊢(ent r,ent b,ent X,r<b)⇒r+X<b+X ;
  produit_binaire_entier(a,b,n,k) [iii_5_1/ensembles_prop3_produit_entier:217] ⊢ ent(a·b) [vérifier antécédent exact] ;
  produit_succ_distribue(b,q)⊢(card b,card q)⇒b·(q+1)=b·q+b ; produit_cardinale_monotone_droite(succ q,q',b)⊢(succ q≤q')⇒
  Card(b×succ q)≤Card(b×q') [=b·(q+1)≤b·q'] ; inf_egal_somme_gauche_binaire(a,b)⊢Card(a)≤a+b [rewrite Card(b·q')→b·q' via
  cardinal_de_cardinal + est_cardinal(produit)] ; inf_egal_transitive_general (∀)(X≤Y,Y≤Z⇒X≤Z) ; strict_inf_egal_compose(a,b,c)
  ⊢(a<b,b≤c,cards)⇒a<c ; somme_cardinale_commutative via _inst_gen pour r+X↦X+r, b+X↦X+b. CHAÎNE : b·q+r <[S1] b·q+b =[succ] b·(q+1)
  ≤[mono+_gap] b·q' ≤[somme_gauche] b·q'+r' ⇒ strict_inf_egal_compose(b·q+r, b·(q+1), b·q'+r') avec inf_egal_transitive_general
  (b·(q+1),b·q',b·q'+r'). Build INCRÉMENTAL prochain tick (vérifier sig produit_binaire_entier + Card-rewrite d'abord).
  Suite = ce build (ensembles_division_unicite.py).
Suite = n°26 stabilité multiples ⏸ (tick 70 : (a) énoncé EXACT illisible cette session — PDF scan SANS couche texte
[get_text vide], pdftoppm absent, V7 grep vide ⇒ fidélité impossible ; (b) besoin d'un pont distributivité set-level
[distributivite_cardinale = Card(A×(B⊔C))] → binary-op [b·(q+q')=b·q+b·q'], ~60-80 l). base-b n°27/28 ⏸ (base b).
BILAN DIVISION : EXISTENCE + Déf.1 FAITES ; unicité/n°26/base-b = session dédiée (pont distributivité, gap successeur,
monotonie produit ; + rendu PDF pour la fidélité). Le VERROU historique (verrou-τ) est LEVÉ pour la division.

**Découverte majeure de la nuit — RACINE du blocage division ENFIN trouvée :** l'étape `a=(a−b)+b`
passe par `somme_cardinale_commutative` → `graphe_terme_fonctionnel`, qui bute sur le **VERROU-τ** : le
terme-valeur lie en interne `u`/`t`, EXACTEMENT les noms de liants codés en dur par la preuve
(`ensembles_fonction_terme.py:184`), et comme le noyau compare en égalité STRUCTURELLE (pas α), les deux
chemins de construction divergent (`wit=exists/u` vs `ante=exists/@0`). **Soundness JAMAIS en cause**
(c'est le MP défensif qui bloque). Diagnostic écarté au passage : subst-cache, cache_clear, idempotence,
déterminisme de s5 — TOUS innocentés par mesure. Détail complet : mémoire `bourbaki-commute-ordre-dependant`
+ tâche dédiée (chip). **Ce n'est PAS un bug à corriger vite** : le fix (α dans MP, ou est_fonctionnel à
liants frais, ou lemme α-conversion) est un chantier infra SUPERVISÉ (un prior α-rename ici a déjà régressé).

**Honnête sur le reste :** le front des « purs assemblages » est SATURÉ (re-vérifié en code n°86=écart
graphe_terme, n°78/factorielle=mur C62 « essais≠fonction », n°77=déjà clos). Les ~70 items restants sont
TOUS de vrais chantiers derrière un petit nombre de murs infra documentés : (1) verrou-τ/commute ci-dessus ;
(2) théorie graphe_terme ≠22 (produits d'applications, identité famille Groupe A) ; (3) récursion C62
« essais≠fonction assemblée » (factorielle, fⁿ, arith. index-aware) ; (4) Zorn (Hessenberg a²=a, limites
Th.1) ; (5) familles indexées (§3.3, chap. R) ; (6) arithmétique cardinale infinie / ℵ₀≤a (§6.4). Chacun =
une session dédiée. Je n'ai RIEN coché de faux ni postulé.

**🔑 PERCÉE (tick 64, retour cadence 60s) — ROUTE COMMUTE-FREE pour débloquer la division, sans toucher au noyau :**
la division était bloquée car `_diff_strict` ((a−b)<a) passait par `somme_cardinale_commutative` (verrou-τ). NOUVELLE route
qui l'ÉVITE : prouver `a−b≠a` par l'absurde via `somme_strict_monotone(0,b,a)` [⊢0+a<b+a] au lieu de la commutativité.
CLEF anti-verrou-τ VALIDÉE (test) : appeler ces lemmes graphe_terme-dépendants DIRECTEMENT sur un τ Card-valué (ZERO,diff)
rebute sur le verrou ; MAIS `_inst_gen` = construire le lemme sur variables SYMBOLIQUES ('A','B'...) puis `generalisation`+
`instancie [ZERO,vb,va]` (substitution PURE, ne reconstruit AUCUNE bijection) le CONTOURNE — `somme_strict_monotone` instancié
ZERO donne bien 0+a<b+a (symbolic_clos=True inst_ok=True). ✅✅ **_diff_strict VERT (tick 65) — ((a−b)<a) DÉBLOQUÉ, SANS résidu C61 !** 6 hyps propres {card a, card b, b≤a,
Fini a, Fini b, b≠0}, theorie==22, test fichier seul. La route commute-free ÉLIMINE même _diff_est_fini (donc les
résidus C61 qu'il portait) — _diff_strict est PLUS propre que le plan d'origine. Verrou-τ CONTOURNÉ par _inst_gen sur
somme_strict_monotone(ZERO,...). EXISTENCE n°23 : ensembles_division_existence_final.py ÉCRIT (tick 66) — _strong_step (trichotomie_finis : n<b→_pas_petit,
n=b/b<n→_pas_grand avec R{n−b} depuis S{n}, cuts pour décharger card/b≤n) + division_existence (recurrence_forte + décharge H).
comparabilité CLOS (pas de Zorn) ; résidus attendus {b≠0, pred_univ, C61 via _diff_est_fini} ⇒ « CLOS modulo C61 ».
✅ _strong_step VERT (tick 67) — 4 hyps {Fini b, b≠0, principe_recurrence, cardinal_pas_entre}, theorie==22. Le b<n branch
(build_grand + cuts + _diff_strict/_diff_est_fini/_pas_grand) et la trichotomie PASSENT. (Bug trivial corrigé : inf_egal_reflexif
veut un NOM string pas un terme.) division_existence() SOUS TEST (recurrence_forte + décharge H).
Recon contrats (tick 65) :
  RECON contrats (tick 65) : recurrence_forte(R,p="pfor") ⊢ {H, predecesseur_fini_universel} ⊢ (∀n)(n entier⇒R{n}),
  EXACTEMENT 2 hyps ; H=hypothese_recurrence_forte(R,"nfor","pfor")=(∀n)(S{n}⇒R{n}) ; S{n}=s_recurrence_forte(R,n,p)=
  (∀p)((n fini ∧ p fini ∧ p<n)⇒R{p}). _R_rel(vb,cible)=∃q∃r(b·q+r=cible ∧ r<b) [binders _Q,_R]. _pas_petit ⊢{a fini}(a<b)⇒R{a} ;
  _pas_grand ⊢{a fini,b fini,b≤a,R{a−b}} R{a} (4 hyps, conclusion R{a}). inf_egal_total_general(x,y) [ensembles_cardinaux_props_restantes_ordre:83].
  ⇒ _strong_step = prouver H : (∀n)(S{n}⇒(est_fini n⇒_R_rel(vb,n))) : assume S{n},est_fini n ; trichotomie n<b/_pas_petit,
  b≤n/_pas_grand avec R{n−b}=S{n} instancié p=n−b (n−b<n par _diff_strict, n−b fini par _diff_est_fini) ; puis recurrence_forte+discharge H.
  Détail brique commute-free :
Brick set COMPLET repéré : fini_zero() [Fini 0], cardinal_vide_egale_vide()
[Card∅=∅ pour ZERO↔∅], cardinal_de_cardinal [Card a=a si cardinal], card_somme_zero_neutre [scb(∅,B)=Card B ⇒ 0+a=a],
cardinal_zero_inf_egal [Card∅≤Card A ⇒ 0≤b], somme_strict_monotone via _inst_gen. Reste = ASSEMBLER _diff_strict Part-2 (chaîne
absurde + réécritures ∅/ZERO/Card + contraposition finale) sur plusieurs ticks. Route SÛRE (n'utilise que des théorèmes clos,
via _inst_gen si τ Card-valué ; ne modifie PAS noyau/commute). Cf. mémoire bourbaki-commute-ordre-dependant (contournement _inst_gen).

**Re-vérification faux-négatifs (tick 58) — TERMINÉE, aucun trouvé :** n°86=écart graphe_terme, n°78=mur
C62, n°77=déjà clos, n°89=écart AXIOME_INTER_FAM (I≠∅), n°92=déjà coché, converses-de-facteur=déjà bâties
(dans n°77/79/86). La liste « candidats à re-vérifier » des prompts précédents était STALE (déjà fermés).
Heartbeat tick 59 : n°94 (choix fonctionnel) re-vérifié = mur infra famille/quotient (bloc E.R.20-25).
Heartbeat tick 60 : n°121 (max⇔suites stationnaires) = défs présentes mais théorème = mur récursion/choix sur suites.
Heartbeat tick 61 : n°110 (ℵ₀≤a) = énoncé posé (aleph0_inf_egal_cardinal_infini_enonce), ℕ dispo, mais preuve = mur récursion/choix (injection ℕ↪a).
Heartbeat tick 62 : n°41 (Σi=n(n+1)/2) = Cor. de n°40, mur combinatoire (comptage couples i≤j). Régions échantillonnées : produit, récursion, famille, infinis, combinatoire, ordre — TOUTES saturées.
Heartbeat tick 63 : n°20 (relèvement fini lim→ §7.5) = mur infra limites/familles filtrantes. Région LIMITES aussi saturée ⇒ les 7 régions du livre confirmées saturées.
CONCLUSION : le front autonome sûr est ÉPUISÉ — tout progrès réel demande maintenant TOI (travail infra
supervisé : verrou-τ, ou un des 6 murs). ⇒ boucle passée en HEARTBEAT LENT (1 h), sans toucher au noyau.
Réveille-moi sur le verrou-τ (racine précise prête) ou choisis un mur à attaquer ensemble.

---


Boucle /loop : dériver TOUTES les démos du livre, **dans l'ordre du livre**
(chapitre → page E imprimée → ligne), la démo du LIVRE (page rendue pymupdf,
marqueur @livre) comme guide.

## ⚠️ RÈGLE D'ORDRE (décision Karl, 23 juil) — NE PLUS trier par difficulté
Prendre la PREMIÈRE case non cochée **en ordre livre**, PAS la plus facile.
RAISON (fidélité) : le noyau interdit déjà toute circularité logique (on ne peut
invoquer qu'un `Theoreme` déjà clos), MAIS en ordre de difficulté on risque de
démontrer la démo d'un résultat X en s'appuyant sur un objet/lemme qui, DANS LE
LIVRE, n'apparaît qu'APRÈS X — sound mais INFIDÈLE (la démo de Bourbaki pour X
n'a droit qu'à ce qui précède X). « Démontré dans le livre == vérifié par la
machine » exige donc l'ordre du livre. La colonne [T1..T4] reste indiquée à titre
d'estimation d'effort, elle ne pilote PLUS l'ordre.

Règles inchangées : noyau seul, `theorie==22`, tests verts (fichier seul, JAMAIS
le dossier C61 entier = 13-18 min), @livre `Demo.-` seulement si réellement dérivé.
Métathéorème (critère C/CS/CF, résultat SUR le formalisme) = prose + preuve en
COMMENTAIRE ou fonction Python vérifiable, JAMAIS un `Theoreme` du noyau.
Numéros n°X = tag de CAMPAGNE_TROUS.md « Campagne tout le livre » (cross-réf).

**CLAUSE CHANTIERS (23 juil).** Certains items en ordre livre sont de VRAIS chantiers
(leur démo fidèle exige de bâtir d'abord une infrastructure NON encore formalisée —
p.ex. le théorème général E II.47 §6.9, l'ordre quotient, le préordre-graphe). On ne
les BÂCLE PAS et on ne les POSTULE PAS : ils sont marqués `⏸ CHANTIER` avec leur
prérequis et DÉFÉRÉS en session dédiée (comme division euclidienne §5.6 et Th.1 limites
E III.59). La boucle prend alors le prochain item TRACTABLE et AUTONOME en ordre livre.
FIDÉLITÉ PRÉSERVÉE : déférer ≠ prouver un résultat antérieur avec un postérieur ; quand
on reviendra sur un chantier, on n'utilisera QUE des résultats ≤ sa position livre.

## 🔨 EN COURS (24 juil, tick 57) — _diff_strict RACINE TROUVÉE = VERROU-τ (collision de liants u/t). Instrumentation de
##   membre_graphe_terme (⇐, l.87) : au point fautif `wit=exists/u` vs `ante=(v|y)body_uy=exists/@0` — le terme-valeur lie
##   u/t = noms fixes codés en dur par _gtf_preuve (ensembles_fonction_terme.py:184) ; les 2 chemins renomment différemment ;
##   noyau compare structurellement (pas α) ⇒ MP défensif rejette (soundness OK). ÉCARTÉS par mesure : subst renvoie l'objet
##   IDENTIQUE après poison (cache_clear inutile), somme_cardinale_commutative idempotent 4×, s5 déterministe. « Ordre-dépendant »
##   = timing de mémoïsation par-dessus la collision (secondaire). FIX = chantier infra SUPERVISÉ (α dans MP / est_fonctionnel
##   liants frais / lemme α-conversion ; un prior α-rename a régressé). _diff_strict = NotImplementedError, assemblage préservé,
##   racine en docstring. Tâche dédiée + mémoire bourbaki-commute-ordre-dependant à jour. _diff_inf_egal + _diff_est_fini VERTS.
##
## 🔨 (24 juil, tick 56) — _diff_strict ((a−b)<a) BLOQUÉ sur un BUG INFRA ordre-dépendant. Assemblage LOGIQUE correct
##   écrit (prop2_strict_backward(diff,a) + témoin c=b + a=(a−b)+b), mais l'étape a=(a−b)+b exige somme_cardinale_commutative,
##   dont l'appel LÈVE « MP : mineure ≠ antécédent » DANS commute_graphe_fonctionnel → membre_graphe_terme (⇐, ex_y=mp(wit,
##   s5(body_uy,vv,y))) — UNIQUEMENT quand il est appelé APRÈS avoir construit somme_cardinale_binaire sur le τ Card-valué diff
##   (dépendance à l'ordre : somme_cardinale_commutative('A','B') est VERT en process frais). Le MP DÉFENSIF du noyau bloque ⇒
##   AUCUN faux théorème (soundness intacte). subst_t/subst_f.cache_clear() NE corrige PAS ⇒ l'état partagé fautif n'est pas (que)
##   ces lru_cache (seuls caches de la machinerie). ⇒ _diff_strict lève NotImplementedError (assemblage préservé en commentaire/code).
##   TOUTE route strict-increase (a<b+a, x<y+x…) repasse par la commutativité ⇒ pas de contournement local : le vrai fix = réparer
##   la machinerie commute/membre_graphe_terme (α-collision / état partagé) — CHANTIER INFRA d'une session dédiée (touche toute
##   l'arithmétique cardinale). Signalé Karl. Voir mémoire bourbaki-commute-ordre-dependant.
##
## 🔨 (24 juil, tick 55) — DIVISION : nouveau fichier ensembles_division_recurrence.py, 2 briques VERTES (test fichier seul).
##   ✅ _diff_inf_egal : {est_cardinal a, est_cardinal b, b≤a} ⊢ (a−b) ≤ a  (3 hyps, theorie==22). VOIE ANTI-CIRCULARITÉ réussie :
##      inf_egal_somme_droite (injection droite a−b ↪ b⊔(a−b)) TRANSPORTÉE le long de Eq(b⊔(a−b), a) [equipotent_son_cardinal +
##      Card(b⊔(a−b))=a par soustraction_caracterisation(vb,va) + réécriture s6] via inf_egal_invariant_equipotence. JAMAIS supposé
##      est_cardinal(a−b). ⚠️ PIÈGE RÉSOLU : diff_somme(a,b,BINDER) — soustraction_caracterisation utilise le binder DÉFAUT 'c' ;
##      j'avais 'cfr' ⇒ Card(S) syntaxiquement ≠ ⇒ modus ponens KO. Fix = aligner le binder sur 'c'. (somme_cardinale_binaire(x,y) ==
##      cardinal(somme_disjointe(x,y)), vérifié.) rôles échangés confirmés : soustraction_caracterisation(vb,va) ⊢ b+(a−b)=a.
##   ✅ _diff_est_fini : {card a, card b, b≤a, Fini a, + résidus C61} ⊢ Fini(a−b)  (6 hyps, theorie==22). fini_downward_thm() instancié
##      (a−b, a) + _diff_inf_egal. RÉSIDUS HÉRITÉS = principe_recurrence(P) + (∀c∀b)cardinal_pas_entre — LES MÊMES qui conditionnent
##      l'existence de ℕ (N_collectivise_final). ⇒ HONNÊTETÉ : la division euclidienne, bâtie ainsi, portera {b≠0, pred_univ,
##      principe_recurrence, cardinal_pas_entre}. Les 2 derniers = bon ordre des cardinaux / C61 (écart documenté standard du niveau
##      fini-cardinal, PAS un faux axiome). ⇒ n°23 sera « CLOS modulo résidus C61 », pas fully closed — décision de coche à Karl.
##   🎯 RESTE : _diff_strict (prop2_strict_backward(diff,a), témoin c=b, sous b≠0+entier) → _strong_step → recurrence_forte(R_rec)
##      → EXISTENCE. Tests tests/…/test_division_recurrence.py (fichier seul, slow).
##
## 🔨 (24 juil, tick 52) — DIVISION DÉBLOQUÉE ! Le « verrou-τ bloquant la division » était un PHANTÔME = simple collision
##   de NOMS d'arguments. VÉRIFIÉ : distributivite_cardinale('Aa','Bb','Cc') CLOS ; produit_succ_distribue('Aps','Nps') CLOS 0-hyp ;
##   division_successeur('Bd','Qd') [NOMS FRAIS] CLOS ==cible. C'est UNIQUEMENT division_successeur('b','q') [noms par DÉFAUT] qui
##   casse ('b'/'q' collisionnent les liants internes de distributivite_cardinale). FIX trivial : appeler avec noms frais + gen/inst.
##   ✅ _pas_grand DÉ-GARDÉ et VERT : {a fini, b fini, b≤a, R{a−b}} ⊢ R{a}, 4 hyps, theorie==22 (succ_eq via
##   division_successeur('Bdiv','Qdiv') gen+inst → vb,Q0). BRICKS DIVISION VERTES : _pas_petit, _assoc_binaire, _pas_grand.
##   ⚠️ LEÇON : le verrou-τ RÉEL existe (graphe_terme_fonctionnel sensible aux collisions) MAIS il se contourne par des NOMS FRAIS
##   d'arguments (gen/inst) — PAS besoin de réparer le noyau. Les ticks 46-51 ont sur-diagnostiqué un cas de collision évitable.
##   🎯 RESTE division : BRIQUE 3 _strong_step (S{a}⇒R_rec{a}, R_rec{n}=impl(est_fini n,_R_rel(b,n)) pour gérer le n non-fini vacuous ;
##   case-split n<b [_pas_petit] / b≤n [_pas_grand via S{a} en p=n−b] ; besoin trichotomie cardinaux + n−b<n sous b≠0) ; BRIQUE 4
##   recurrence_forte(R_rec) décharge H ⇒ (∀n)(n fini⇒_R_rel(b,n)) = EXISTENCE division ⇒ cocher n°23-28.
##   📍 LEMMES REPÉRÉS (reconnaissance tick 52) : inf_egal_total_general(X,Y) [X≤Y ou Y≤X, dans cardinaux_ordre_total] ;
##   somme_strict_monotone(a,b,c) ⊢ (a,b,c entiers et a<b)⇒a+c<b+c [iii_5_2/ensembles_prop3_strict_mono_iii5] ;
##   soustraction_caracterisation(a,b) ⊢ (card a,card b,a≤b)⇒a+(b−a)=b [rôles échangés : b+(a−b)=a] ; fini_downward_thm [C61, p<n∧fini n⇒fini p] ;
##   somme_cardinale_zero_neutre ; diff_somme(a,b)=a−b=τc(a=b+c). PLAN a−b<a : 0<b [b≠0,entier] + somme_strict_monotone(0,b,a−b)
##   ⇒ 0+(a−b)<b+(a−b) ; 0+(a−b)=(a−b) [zero neutre] ; b+(a−b)=a [soustraction] ⇒ (a−b)<a. ⚠️ NOMS FRAIS partout (leçon collision).
##   ⚠️ tests brique 3/4 LOURDS (recurrence_forte+fini_downward+N) ⇒ background+monitor, jamais le dossier C61 entier.
##   📍 tick 53 : SUBTILITÉ à résoudre AVANT _diff_strict/_strong_step = est_cardinal(a−b) et est_fini(a−b). AUCUN lemme direct
##   (grep vide). existe_complement_somme(a,b) ⊢ (card a,card b,b≤a)⇒(∃c)a=b+c MAIS ne dit pas que le témoin diff_somme(a,b) est
##   un CARDINAL. inf_egal_somme_droite_binaire renvoie inf_egal_card(cardinal(a−b), b+(a−b)) [∃injection]. Pour (a−b)<a il faut
##   réécrire cardinal(a−b)→(a−b) [est_cardinal(a−b)] + (b+(a−b))→a [soustraction]. ⇒ PROUVER est_cardinal(a−b) : soit un lemme
##   soustraction-est-cardinal (à bâtir : depuis ∃c(a=b+c), le témoin τc EST le c ; montrer que ce c est cardinal via… ou reformuler
##   a−b = cardinal(diff) partout), soit REDESIGN _R_rel avec est_cardinal(q) porté (préserve la cardinalité des témoins par récurrence,
##   utile aussi pour produit_succ_distribue). DÉCISION prochaine tick : bâtir `_diff_est_cardinal` (est_cardinal(a−b)) d'abord.
##   ⚠️ HONNÊTE : la division = preuve intriquée (ponts Card/ensemble/cardinal à chaque pas) = vrai chantier soutenu, pas fil-de-l'eau rapide.
##   📍 tick 54 : CHAÎNE COMPLÈTE de est_cardinal/est_fini(a−b) MAPPÉE. (1) est_fini(a−b) : a−b≤a [inf_egal_somme_droite_binaire(b,a−b)
##   donne inf_egal_card(cardinal(a−b),b+(a−b)) ; b+(a−b)=a soustraction ; PONT cardinal(a−b)→(a−b) ⇐ est_cardinal(a−b)…] PUIS
##   fini_downward(a−b,a) [ÉNONCÉ ii_6_1/ensembles_N_collectivise:86 : (b≤c ∧ Fini c)⇒Fini b ; PREUVE = fini_downward_thm C61
##   iii_4_recurrence_c61/ensembles_recurrence_C61:430, PORTE le résidu predecesseur_fini_universel — OK, la division porte déjà pred_univ].
##   (2) est_cardinal(a−b) : Fini(a−b)⇒est_cardinal(a−b) [fini_implique_cardinal]. (3) a−b<a : prop2_strict_backward(a−b,a,c)
##   [iii_5_2/ensembles_prop2_strict_iii5:256, ⊢(entier(a−b),entier a)⇒(∃c(entier c,c≠0,a=(a−b)+c)⇒(a−b)<a)] avec témoin c=b
##   (b entier, b≠0, a=(a−b)+b via soustraction+commut). ⇒ _diff_strict CLOSEABLE sous {est_fini a, est_fini b, b≤a, b≠0, pred_univ}.
##   ⚠️ CIRCULARITÉ à éviter : est_fini(a−b) via a−b≤a qui via bridging via est_cardinal(a−b)… → prouver est_cardinal(a−b) D'ABORD par
##   une AUTRE voie (existe_complement_somme + le témoin diff EST le c, montrer c cardinal) OU reformuler a−b=Card(diff). PROCHAIN tick :
##   isoler est_cardinal(a−b) proprement (probablement le vrai point dur), puis dérouler _diff_strict→_strong_step→recurrence_forte.
##
## (archive) ⏹️ tick 51 — le verrou-τ pour est_fonctionnel(graphe_terme(A,Card)) reste irréductible (cas DIFFÉRENT, non requis par division).
##   PREUVE IRRÉDUCTIBILITÉ (diff récursif tick 51) : prouver est_fonctionnel(graphe_terme(A,t)) quand t lie u/v/z (Card) exige
##   ces MÊMES liants canoniques (F=graphe_terme(A,t) les lie aussi) ; la preuve à liants FRAIS marche mais l'α-renommage vers
##   u/v/z RENOMME le z de F (capture-évitement z→@0) ⇒ F' ≠ F cible ⇒ α-variants ≠ noyau ⇒ AUCUNE preuve substitutive. Contournement
##   = α-égalité au NOYAU (franchit la frontière de confiance) OU redéf globale d'est_fonctionnel (change tout). = HORS fil-de-l'eau.
##   ACQUIS non-régressifs GARDÉS : membre_graphe_terme ⇒ (congruence directe, plus propre) ; graphe_terme_fonctionnel refactoré
##   (_gtf_preuve) = comportement IDENTIQUE à l'historique ; 17 tests verts. Bricks division _pas_petit/_assoc_binaire verts, _pas_grand gardé.
##   BILAN COMPLÉTION (ticks 43-51) : 0 nouveau th. fermé (division bloquée verrou-τ ; arith-infinie bloquée 2 résidus Zorn ;
##   Group D family-layer ; n°66 C61). TOUS les 71 restants = bloqués-documentés sur un socle foundational profond. La campagne
##   fil-de-l'eau NE PEUT PAS les fermer — reste = sessions dédiées OU changements noyau. VICTOIRES SESSION : n°111 + n°63 (pur-assemblage).
##
## (archive) 🔨 tick 50→51 — RETOUR au VERROU-τ (keystone à FINITION CLAIRE, plus haut levier : débloque division + Groupe D).
##   Constat tick 50 : ARITH INFINIE via Hessenberg AUSSI bloquée — hessenberg_a_carre_egal_a_REEL ⊢ est_infini(Card E)⇒Card E²=Card E
##   avec 2 RÉSIDUS ZORN (∃x∈𝔉(E) [base] ; ∀C (⋃₁C,⋃₂C)∈𝔉(E) [inductivité]) NON déchargés (frame jamais prouvé inductif). Donc
##   ℵ₀·ℵ₀=ℵ₀ hérite des 2 résidus ⇒ pas 0-hyp. PATTERN CONFIRMÉ (ticks 43-50) : tout item restant bute sur un résidu foundational
##   profond (verrou-τ / Zorn-frame / family-layer / C61-lourd / infra absente). Les pur-assemblages (n°111,n°63) sont FAITS.
##   🎯 DÉCISION : concentrer le loop sur le VERROU-τ (seul keystone à chemin de finition CLAIR + diagnostiqué). PLAN tick 51 :
##   graphe_terme_fonctionnel chemin-collision → utiliser liants-VALEURS FRAIS u9,v9,z9,y9 TOUS absents de t (pas seulement u9) dans
##   _gtf_preuve (membre_graphe_terme marche alors car témoin v9 ne collisionne plus le 'v' de t) ⇒ prf9=(∀u9)(∀v9)(∀z9)M ; puis
##   α-RENOMMAGE IMBRIQUÉ u9→u,v9→v,z9→z. Pour le nested-α : chercher/utiliser un `congruence_pourtout` (∀u(A⇔B)⇒(∀uA⇔∀uB)) OU
##   renommer de l'INTÉRIEUR (z9 d'abord) via alpha_pour_tout sous les ∀ extérieurs (instancie témoin frais → rename → re-generalise).
##   VALIDER : gtf(Card) == est_fonctionnel + 17 tests + division_successeur() [background] ⇒ déguarder _pas_grand.
##   (membre_graphe_terme ⇐, diagnostic exact consigné plus bas ; fix connu = liants-valeurs frais + α-imbriqué, session dédiée).
##   FIXES CORE GARDÉS (non-régressifs, 17 tests verts) : membre_graphe_terme ⇒ (congruence directe) + graphe_terme_fonctionnel
##   (chemin liants-frais conditionnel). Bricks division VERTES conservées : _pas_petit, _assoc_binaire. _pas_grand reste gardé.
##   🎯 TICK 50 : ARITH CARDINALE INFINIE via Hessenberg (§6.4/H/n°114). (1) GREP+vérifier Hessenberg a²=a clos
##   (hessenberg_a_carre_egal_a_0hyp ou équivalent) : est_infini(a)⇒a·a=a ? sous quelles hyps ? (2) viser ℵ₀·ℵ₀=ℵ₀
##   (NN infini via NN_est_infini_ensemble ⇒ Hessenberg) et/ou n°114 (ab=a+b=sup(a,b) infinis — mais sup indéfini, vérifier).
##   (3) chercher les énoncés posés (aleph0_*, §6.4) qui deviennent closeables une fois a·a=a dispo. Pur-assemblage si possible,
##   sinon consigner le vrai blocage. ⚠️ éviter la machinerie graphe_terme (verrou-τ) : préférer les lemmes cardinaux déjà clos.
##
## (archive) 🔨 BOUCLE COMPLÉTION RELANCÉE par Karl (24 juil, tick 43) — objectif : DÉMONTRER TOUS LES TH. RESTANTS (71).
##   Mode COMPLÉTION : on bâtit l'infra manquante brique par brique + on accepte les TESTS LOURDS ISOLÉS (background+monitor,
##   jamais toute la suite C61 d'un coup). Ordre = levier (infra d'abord). Quelques items resteront de vrais écarts d'axiome
##   (ex. famille-layer, hypothèse du continu métamath.) — les consigner honnêtement, ne pas postuler.
##   ⚠️ tick 43 : GROUPE A RE-CONFIRMÉ ÉCART (family-layer). valeur_famille(f,i)=app("fam") est un objet du LAYER FAMILLE
##   axiomatisé séparément (AXIOME_REUNION_FAM), SANS pont vers le layer fonction (graphe_terme/valeur=app("valeur")). La famille
##   identité (est_famille_identite : valeur_famille(f,X)=X) est INDÉCHARGEABLE car aucun constructeur de famille concrète +
##   aucun pont valeur_famille↔valeur. ⇒ A (n°95/140/67) reste écart. Idem D-fonctorialité. **1ère CIBLE loop = DIVISION
##   EUCLIDIENNE (E, n°23-28)** : self-contained, plan en mémoire [bourbaki-chantier-division-euclidienne], existence par
##   récurrence forte C61 (a<b→(0,a) ; a≥b→HR sur a−b), remplacer plus_ent/prod_ent par somme/produit_cardinal_binaire (existent).
##   Puis F (combinatoire), puis arith cardinale infinie via Hessenberg (§6.4/H), puis quotients/limites. Écarts A/famille en dernier.
##   ÉTAT DIVISION (vérifié tick 43, dossier iii_5_6_divisibilite_division_euclidienne, DÉJÀ ENTAMÉ) : division_cas_petit ⊢
##   (Card a<b)⇒(∃q,r)(b·q+r=Card a et r<b) [BASE CLOS] ; division_pas_recomposition {card b,card a,b≤a,a−b=b·q+r}⊢b+(b·q+r)=a ;
##   division_successeur (b·(q+1)=b+b·q, CLOS). 🎯 PROCHAINE BRIQUE (tick 44) : assembler l'EXISTENCE via recurrence_forte(R),
##   R{a}=(∃q,r)(b·q+r=a et r<b) : base=division_cas_petit ; pas a≥b via division_pas + HR sur a−b (a−b<a) ⇒ (∀a entier)(R{a})
##   sous {b≠0}. Test possiblement lourd (recurrence_forte+arith) → background+monitor. Ensuite : UNICITÉ (q,r), puis diviseur/multiple.
##   ✅ tick 44 : BRIQUE 1 division existence VERTE — `_pas_petit` {a fini}⊢(a<b)⇒R{a} [R{a}=(∃q,r)(b·q+r=a et r<b)], fichier
##   iii_5_6.../ensembles_division_existence.py. division_cas_petit (→ « =Card a ») transporté vers « =a » par pont Card a=a
##   (fini_implique_cardinal+cardinal_de_cardinal) + réécriture sous ∃∃ (congruence_existe ×2). theorie=22, probe OK.
##   🎯 BRIQUE 2 (tick 45) : `_pas_grand` — {a fini, b fini, b≤a, R{a−b}} ⊢ R{a} : soustraction_caracterisation (b+(a−b)=a) +
##   division_pas_recomposition + division_successeur (b·(q'+1)=b+b·q') ⇒ témoins q=q'+1, r=r'. Puis BRIQUE 3 strong-step (cas
##   a<b / a≥b via trichotomie c58) et BRIQUE 4 recurrence_forte(_R_rel) [décharge H=hypothese_recurrence_forte, résidu pred_univ].
##   ✅ tick 45 : helper `_assoc_binaire` ⊢ (x+y)+z=x+(y+z) [somme cardinale binaire, forme Card-wrappée] CLOS 0-hyp theorie=22,
##   via somme_cardinale_associative (brute) + 2 bien-def (somme_cardinale_bien_definie + equipotent_son_cardinal). Débloque la
##   recomposition. RESTE brique 2 `_pas_grand` (tick 46) : extraire Q0,R0 de R{a−b} (existe_temoin×2), division_pas_recomposition
##   (b+(b·Q0+R0)=a) + division_successeur (b·succ(Q0)=b+b·Q0) + _assoc_binaire ⇒ b·succ(Q0)+R0=a, puis ∃-intro (q=succ Q0, r=R0).
##   ⚠️⚠️ tick 46 : _pas_grand ÉCRIT (assemblage correct) mais BLOQUÉ — **RÉGRESSION DÉCOUVERTE : division_successeur ET
##   distributivite_cardinale sont CASSÉS** (echec « modus ponens : mineure ≠ antécédent » dans graphe_terme_fonctionnel).
##   RACINE = VERROU-τ : graphe_terme_fonctionnel hardcode ses liants canoniques {u,v,z} (est_fonctionnel) qui collisionnent le
##   terme-valeur binder-riche de la distributivité ⇒ capture-renommage incohérent de T[u] (test_division_successeur marqué `slow`
##   ⇒ régression silencieuse). _pas_grand gardé (NotImplementedError, code correct préservé). 🎯 KEYSTONE tick 47 = **RÉPARER
##   graphe_terme_fonctionnel** (ii_3_6_fonction_terme/ensembles_fonction_terme.py) : prouver la fonctionnalité à LIANTS FRAIS
##   (u9,v9,z9 disjoints du terme-valeur) puis alpha_pour_tout ×3 vers les liants canoniques {u,v,z}. Débloque division_successeur
##   + distributivite_cardinale + _pas_grand + potentiellement GROUPE D (même verrou-τ !). GAIN LEVIER ÉNORME. Vérifier non-régression
##   des usages existants de graphe_terme_fonctionnel (nombreux). Si irréparable proprement ⇒ rebâtir distributivite sans graphe_terme_fonctionnel.
##   ✅/⚠️ tick 47 : graphe_terme_fonctionnel PATCHÉ (chemin liants-frais u9/y9 + alpha_pour_tout, CONDITIONNEL sur collision « u »/« y »
##   liés dans t ; non-régression OK sur terme simple : conclusion == est_fonctionnel(F), chemin historique intact). MAIS le verrou-τ
##   est PLUS PROFOND : `membre_graphe_terme` LUI-MÊME échoue sur t binder-riche (Card) — ses directions ⇒ et ⇐ construisent T[u]
##   par DEUX chemins de substitution DIFFÉRENTS (subst directe `Tu=subst_t(vu,x,t)` L.51 vs congruence par trou `Thole` L.68-73)
##   qui DIVERGENT (α-renommage @k différent) ⇒ « modus ponens : mineure ≠ antécédent » à L.87. 🎯 KEYSTONE VRAI (tick 48) =
##   RÉPARER membre_graphe_terme : faire coïncider T[u] entre ⇒ et ⇐ (utiliser le MÊME subst_t(vu,x,t) partout, supprimer le
##   détour Thole/hole, OU forcer les 2 à la même forme canonique). Fichier ii_3_6_fonction_terme/ensembles_fonction_terme.py L.41-92.
##   ⚠️ membre_graphe_terme a ~50+ appelants → non-régression cruciale. C'est le vrai débloqueur de division_successeur + Groupe D.
##   ✅/⚠️ tick 48 : membre_graphe_terme direction ⇒ RÉPARÉE (remplacé le détour trou `Thole`/`hole`+congruence par
##   `congruence_terme(vx,vu,t,x)` direct ⇒ T[u]=subst_t(vu,x,t)=Tu canonique, IDENTIQUE au sens ⇐). NON-RÉGRESSION OK (17 tests
##   verts). MAIS il RESTE la direction ⇐ (L.78-89) : le témoin `wit` (conjonction_intro(refl, hc…) L.82) ne matche PAS
##   subst_f(vv,y,subst_f(vu,x,body)) attendu par s5 L.87 sur t binder-riche ⇒ « modus ponens : mineure ≠ antécédent ». 🎯 tick 49
##   = 1 SEULE tentative ciblée ⇐ : DIFFER le vrai `wit.conclusion` vs `cible=subst_f(vv,y,subst_f(vu,x,body))` (récupérés du VRAI
##   chemin, pas reconstruits main ; attention désucrage et=ou/non) pour trouver le conjoint qui diffère, puis construire wit pour
##   matcher cible EXACTEMENT (p.ex. bâtir la preuve de `cible` par sa structure au lieu du conjonction_intro manuel). SI non résolu
##   ⇒ PIVOT FERME : marquer division a≥b « écart verrou-τ résiduel (membre ⇐) » + garder les 2 fixes non-régressifs, et passer à
##   la cible suivante (F combinatoire OU arith cardinale infinie via Hessenberg). Les fixes ⇒/gtf RESTENT (progrès réel, non-régressif).
##   🔬 tick 49 : RACINE ⇐ PINPOINTÉE (diff récursif) = « LIEUR 'v' vs '@1' » dans le sous-terme T[u]. Le témoin ∃ de la direction ⇐
##   est var('v') ; il COLLISIONNE le liant 'v' de t (Card lie v) ⇒ subst_f(vv,y,body_uy) RENOMME le v-liant de T[u] en @1, alors
##   que `wit` (bâti depuis hc=assume(egal(vv,Tu))) garde 'v' ⇒ wit ≠ antécédent de s5 (α-variants ≠ dans le noyau). FIX COMPLET
##   (multi-tick, reporté) = liants-VALEURS frais u9,v9,z9 ABSENTS de t dans graphe_terme_fonctionnel (chemin collision) + α-renommage
##   IMBRIQUÉ des 3 ∀ (u9→u,v9→v,z9→z) via alpha_pour_tout sous quantificateur ; OU rendre membre_graphe_terme robuste (fresh internes
##   + α-conv de la conclusion). **PIVOT FERME appliqué tick 49** : division a≥b = ÉCART VERROU-τ RÉSIDUEL (membre⇐), consigné ; les
##   2 fixes ⇒/gtf gardés (non-régressifs, 17 tests verts) ; _pas_grand reste gardé. Reprise verrou-τ = session dédiée (le fix est
##   CLAIR maintenant : liants-valeurs frais + α-imbriqué). CIBLE SUIVANTE (tick 50) = ARITH CARDINALE INFINIE via Hessenberg.
##
## (archive) ⏹️ BOUCLE ARRÊTÉE (24 juil, tick 42, fin normale — condition stop atteinte : tous items cochés ou bloqués-documentés).
##   BILAN SESSION CHANTIERS (ticks 22-42) : **2 THÉORÈMES FERMÉS — n°111 (aⁿ=a, conditionnel, ensembles_a_puissance_n_er.py)
##   et n°63 (ℕ ordonné par ≤, ensembles_ordre_NN.py)**, tous deux CLOS theorie==22, tests verts, cases cochées, manifestes OK.
##   + méthode réutilisable (FORME RELATION GARDÉE) + carte fine des blocages vérifiés en code + énoncés Prop.4 (D) posés.
##   AUDIT cheap-win tick 42 (pattern « déjà clos non crédité ») : RIEN — les basiques §6 clos (aleph0_est_cardinal, NN_denombrable,
##   dedekind_aleph0, NN_est_infini_ensemble) sont des lemmes de support, PAS des items Bourbaki numérotés à cocher.
##   FRONTIÈRE FIL-DE-L'EAU ÉPUISÉE (vérifié ticks 35-42, avec 2 corrections docs-stale gagnantes n°111/n°63). RESTANT = sessions
##   dédiées sur keystones : verrou-τ (D,J,K) · arith cardinale infinie/récursion (H,§6.4,I) · C61-lourd (E,F,66) · quotient (L) ·
##   ⋃/⋂-d'un-ensemble (A,67) · segments/limites (N,O) · sup indéfini (114). REPRISE = /loop ciblant UN keystone en session dédiée.
##
## (archive) 🔨 tick 41→42 — §6.4 dénombrables SURVEYÉ → tous dédiés (arith cardinale infinie/récursion REPORTÉ).
##   BILAN session : n°111 ✅, n°63 ✅ fermés ; frontière fil-de-l'eau VÉRIFIÉE épuisée (ticks 35-41, blocages foundational
##   spécifiques par groupe : verrou-τ D/J/K, arith-inf H/§6.4/I, C61 E/F/66, quotient L, ⋃/⋂-set A/67, segments/limites N/O).
##   🎯 TICK 42 — DERNIER angle cheap-win : AUDIT « déjà clos, docs stale » (pattern n°100 Def.3 / n°65 déjà faits mais découverts
##   tard). GREP les théorèmes CLOS 0-hyp de §6.1-6.4 (aleph0_est_cardinal, NN_denombrable, dedekind_aleph0, NN_est_infini_ensemble,
##   aleph0_est_infini, zero_dans_NN, NN_clos_successeur…) et croiser avec les items NON cochés de la campagne : y a-t-il un item
##   Bourbaki numéroté dont le théorème est DÉJÀ prouvé mais la case non cochée ? Si OUI ⇒ cocher (livrable gratuit). Si rien de
##   crédible ⇒ CONCLURE honnêtement à Karl : frontière fil-de-l'eau épuisée, 2 wins bankés, recommander session dédiée sur un
##   keystone (séparation/verrou-τ/arith-cardinale-infinie) — et proposer d'arrêter la boucle (condition stop du loop atteinte).
##   ── CONSTAT tick 35 (grep+livre, CORRIGE l'écart présumé) : (1) n°100 Def.3 (∑/∏ de FAMILLE de cardinaux) DÉJÀ FORMALISÉ
##   [somme_cardinale(f,i)=Card(somme_famille), produit_cardinal(f,i)=Card(produit_famille), ensembles_cardinaux.py:125-137,
##   @livre §3.3 Def.3 E III.25]. (2) D N'EST PAS le mur Groupe A : toute l'infra de CONSTRUCTION+caractérisation de familles
##   EXISTE et est close — graphe_terme (C54, abrege:123), graphe_terme_valeur {u∈A}⊢F(u)=T[u], membre_graphe_terme,
##   graphe_terme_fonctionnel [ii_3_6_fonction_terme], famille_constante [ii_5_1_extension_canonique:156], membre_produit_famille
##   ⊢(F∈∏)⇔corps + produit_fonctionnel/produit_domaine/projection_dans_facteur/extensionnalite_produit [ii_5_definitions],
##   produit_props_fonctoriel (image d'un produit par une famille d'applications) [ii_5_1]. ⇒ Prop.4/5 sont des THÉORÈMES
##   tractables (assemblage sur cette infra), sous-campagne MULTI-TICK comme n°111. Le mur Groupe A/n°86 était SUR-généralisé :
##   il ne concerne QUE les familles données ABSTRAITEMENT (f opaque) ou l'IDENTITÉ-sur-un-ensemble-de-parties, pas les familles
##   CONSTRUITES par graphe_terme. LIVRE §III.3.3 (V7) : Def.3 + Prop.4 (bij. II p.30 prop.10 & p.38 cor.prop.11) + Cor +
##   Prop.5 a[réindex bij]/b[assoc. via partition]/c[distrib. ∏/∑] + Cor binaire (a+b=b+a, ab=ba, assoc, distrib).
##   n°111 clos via récurrence recurrence_depuis (base_111 + heredite_111 + assemblage), fichier ensembles_a_puissance_n_er.py.

## ✅ (annulé) BOUCLE CHANTIERS « TERMINÉE » tick 20 — Karl a relancé ; frontière rouverte sur n°111.
##   BILAN : **3 CASES COCHÉES** — n°79 (perm composées), n°77 (bijective⇔identités), n°92 (⋂×⋂ mêmes indices).
##   + audit : n°100 Def.3 déjà formalisé. + 2 écarts documentés (Groupe A famille-identité, n°86 produit-de-fonctions).
##   + ~15 briques réutilisables (composee_valeur_app, image_incluse_arrivee, converses inj/surj de facteur, ⋃/⋂-d'ensemble
##   sous hyp, hyp_applicative, inj_dans↔fonctionnel(f⁻¹), _cpp_ssi, direction_bijective_vers_identites, converses X/Y…).
##   ARRÊT (raison structurelle, tick 20) : les items restants exigent TOUS une SESSION DÉDIÉE :
##     · n°111 (G) = closeable mais sa clôture 0-hyp IMPORTE le test Hessenberg (10-18 min) — INTERDIT par la règle boucle
##       (« tests fichier seul, jamais 13-18 min ») ; la version conditionnelle (a²=a en hyp) n'est pas « FINIE ». → session dédiée.
##     · D (lois cardinales de famille), E (division binaire), F (combinatoire, dépend D), H-O (collectivisation N, familles
##       double-indice, produit-famille, quotient E/R, graphe-ordre N, segments bon-ordre, limites) = construction d'infra.
##   Reprise = SESSION DÉDIÉE par brique/théorème. LEÇON transversale : mettre les propriétés-de-construction en ANTÉCÉDENT
##   garde le 0-hyp (n°79/92) ; le mur récurrent = objets terme-définis opaques en th.22 (valeur_famille, produit_applications).

## 🔨 (archive) GROUPE G : n°111 (a^n=a, a infini, n≥1). Assemblage sur bricks TOUS clos.
##   ✅ 3 CASES COCHÉES : n°79, n°77 (Groupe B), n°92 (Groupe C). Écarts : Groupe A, n°86.
##   GROUPES D/E/F DÉFÉRÉS (tick 19, vrais chantiers d'infra, PAS tractables au fil de l'eau) :
##     · D (n°101-108) = LOIS d'arith. cardinale de FAMILLE (bijections assoc/distrib/reindex) — n°100 Def.3 DÉJÀ FORMALISÉ,
##       mais 1 seule case pour 8 props ⇒ construction lourde, session dédiée.
##     · E (division euclidienne §5.6) = bâtir l'arithmétique binaire entière — session FRAÎCHE dédiée (mémoire bourbaki-chantier-division).
##     · F (combinatoire §5.8) = dépend de D (bergers plein) + binomial opaque ⇒ bloqué tant que D non fait.
##   ⇒ Prochain TRACTABLE = n°111 (Groupe G) : SEUL théorème unique restant en PUR ASSEMBLAGE (rien de neuf à bâtir).
##   PLAN n°111 (voir ligne « [ ] 111 ») : a^{n+1}=a via Cantor-Bernstein (borne sup a^{n⊔1}≤a^n·a¹=a·a=a [Th.2] ;
##   borne inf a^n≤a^{n+1} [support_extension_domaine] =a). STRATÉGIE : CONDITIONNEL d'abord (a²=a=Th.2 en HYPOTHÈSE,
##   debug rapide SANS test Hessenberg), puis décharge Hessenberg en 1 test lourd séparé. Bricks clos : inf_egal_phi,
##   support_extension_domaine, B_preuve, exposant_un_egale, eq_exposant_invariant, hessenberg_0hyp, recurrence_depuis.

## 🔨 (archive) GROUPE D : arithmétique de FAMILLE indexée §3.3 → n°100-108, n°112, n°113 (déféré, cf. ci-dessus).

## 🔨 (archive) GROUPE C : n°92 ((⋂X_ι)×(⋂Y_ι)=⋂(X_ι×Y_ι), mêmes indices).
##   ✅ GROUPE B TERMINÉ : n°79 CLOS (perm composées), n°77 CLOS (bijective⇔identités), n°86 ÉCART (produit binaire de fonctions).
##   9 briques réutilisables livrées (composee_valeur_app, image_incluse_arrivee, injective_facteur_droit,
##   surjective_facteur_gauche, hyp_applicative_de_application, inj_dans_implique_reciproque_fonctionnel, _valeur_de_couple,
##   direction_bijective_vers_identites, converse_X/Y). PLAN n°92 : voir ligne « [ ] 92 » (⊢ {¬(I=∅), H=famille ι↦f_ι×g_ι en hyp}
##   ⇒ produit(⋂f,⋂g)=⋂H) ; extensionnalité z générique, membre_inter_famille + couple_dans_produit_ssi + décomposition couple n°84.
##   ⚠️ RISQUE n°92 : H=famille-terme prise en HYP (comme famille_identite Groupe A) ⇒ POSSIBLE écart 0-hyp à ré-évaluer.

## 🔨 (archive) GROUPE B : converses-de-facteur + composée-valeur + produit-binaire → n°79, n°86, n°77.
##   (Groupe A = BRIQUE POSÉE mais boxes ÉCART, cf. bloc ci-dessous. Pivot vers B où le 0-hyp est atteignable.)
##   PLAN B (RAFFINÉ tick 5 après investigation) :
##   · ÉTAPE 1 (DÉJÀ ACQUISE) : composée-valeur (g∘f)(x)=g(f(x)) = composition_valeur_t (ii_3_8_retractions_sections/
##     ensembles_composee_valeurs.py). MAIS porte 3 hyps de POINT : (a) (∃y)(u,y)∈F [u∈domF], (b) (∃y)(f(u),y)∈G
##     [f(u)∈domG], (c) est_fonctionnel(G∘F). Ces hyps de point BLOQUENT la généralisation sur u ⇒ inutilisables telles quelles.
##   · ÉTAPE 2 (FAITE tick 6) : keystone composee_valeur_app — {est_application(F,E,Fp), est_application(G,Fp,Gp)} ⊢
##     (u∈E)⇒((g∘f)(u)=g(f(u))). AJOUTÉ à ensembles_composee_valeurs.py (ii_3_8). Décharge des 3 hyps de point via
##     _cut (composee_fonctionnelle + Leibniz S6 domF/domG + valeur_dans_graphe + couple_dans_produit_ssi). Exactement
##     2 hyps restantes (est_application×2), théorie=22, 2 tests verts (+3 frères). GÉNÉRALISABLE sur u ✓.
##   · ÉTAPE 3 (FAITE tick 7) : converse injective_facteur_droit — {est_application ×2} ⊢ injective_dans(G∘F,E) ⇒
##     injective_dans(F,E). Dans ensembles_composee_valeurs.py, congruence_terme(g) + composee_valeur_app ×2 + inj(G∘F).
##     Vérifié 2 hyps (est_application×2), théorie=22, 3 tests verts. Généralisation OK.
##   · ÉTAPE 4a (FAIT tick 8) : sous-brick image_incluse_arrivee {est_application(F,E,B)} ⊢ f⟨E⟩⊂B (membre_image +
##     couple_dans_produit_ssi + existe_elimination). Pièces converse-surj TOUTES prêtes : image_composee [(f∘g)⟨F⟩=f⟨g⟨F⟩⟩ CLOS],
##     image_croissante [CLOS], image_incluse_arrivee, extensionnalite_appliquee.
##   · ÉTAPE 4b (FAIT tick 9) : surjective_facteur_gauche {est_app(f,E,Fs), est_app(g,Fs,E)} ⊢ est_surjective(f∘g,Fs,Fs)⇒
##     est_surjective(f,E,Fs). Double inclusion f⟨E⟩/Fs (image_composee + image_croissante + image_incluse_arrivee×2 +
##     extensionnalite_appliquee + S6). 2 hyps, théorie=22, 5 tests verts. LES 2 CONVERSES SONT PRÊTES.
##   · ÉTAPE 5 (FAITE tick 10) : ✅ n°79 CLOS 0-hyp — ensembles_perm_composees_er10.py, assemblage des 4 converses,
##     theorie=22, 2 tests verts. **PREMIÈRE CASE COCHÉE de la campagne CHANTIERS.**
##   · ÉTAPE 6 (tick 11) : ⏸ n°86 ÉCART — vérifié produit_applications=app("produit_app",g,h) OPAQUE ; le produit binaire
##     de fonctions (x,y)↦(f(x),g(y)) exige graphe_terme (théorie dédiée ≠22) OU hyp-valeur honnête (pas 0-hyp) = MÊME
##     mur que la famille identité du Groupe A (objets terme-définis opaques en th.22). Case n°86 NON cochée + note écart.
##   · ÉTAPE 7 (EN COURS) : n°77 (E.R.10 item 10d) — ⊢ est_application(f,E,F) ⇒ ((∀X⊂E)(f⁻¹⟨f⟨X⟩⟩=X) et (∀Y⊂F)(f⟨f⁻¹⟨Y⟩⟩=Y))
##     ⇔ est_bijective(f,E,F). Fichier ii_3_2_reciproque/ensembles_bijective_identites_er10.py. 0-hyp ATTEIGNABLE.
##     BRICKS EXISTANTS : image_reciproque_image_egal_si_injective {H_app(X,f),est_fonctionnel(f⁻¹)} ⊢ f⁻¹⟨f⟨X⟩⟩=X ;
##     image_image_reciproque_egal_si_surjective {est_fonctionnel(f),Y⊂f⟨E⟩} ⊢ f⟨f⁻¹⟨Y⟩⟩=Y ; injectif_implique_reciproque_
##     fonctionnel (_graphe_injectif(f)⇒est_fonctionnel(f⁻¹)) ; reciproque_fonctionnel_ssi_injectif ; image_incluse_arrivee ; extensionnalite.
##     PONTS À BÂTIR : (1✅ tick 12) H_app←est_application [hyp_applicative_de_application] ; (2✅ tick 13) injective_dans(f,E)
##     ⇒est_fonctionnel(f⁻¹) sous est_application [inj_dans_implique_graphe_injectif + injectif_implique_reciproque_fonctionnel,
##     via helper _valeur_de_couple] ; (3) surj⇒(Y⊂F⇒Y⊂f⟨E⟩) [f⟨E⟩=F, immédiat depuis est_surjective=egal(img,F)] ; CONVERSES :
##     (4) (∀X)⇒injective_dans [X={a} singletons] ; (5) (∀Y)⇒surjective [Y=F : f⟨f⁻¹⟨F⟩⟩=F=f⟨E⟩⊂F]. Puis assembler l'⇔. ~350 l, multi-tick.
##     ✅ tick 14 : SENS ⇐ ASSEMBLÉ (direction_bijective_vers_identites) — bijective ⇒ (∀X…)∧(∀Y…), 1 hyp (est_application),
##     théorie=22, 4 tests. Reste : SENS ⇒ (converses 4+5) puis l'⇔ final + décharge est_application (CLOS 0-hyp).
##   · ÉTAPE 5 : n°79 (g∘f perm E ∧ f∘g perm F ⇒ f,g bij) — assemble converses ; perm=bijective(·,E,E) décharge est_application.
##   Bricks : est_permutation, injective_dans, retraction_implique_injective, section_implique_surjective_valeur, composition ∘.

## ⏸ GROUPE A — ÉCART DE CLÔTURE documenté (23 juil, tick 4). BRIQUE ⋃/⋂-d'un-ensemble POSÉE & testée (4 lemmes,
##   ensembles_reunion_ensemble_parties_ii4.py) mais les boxes n°95/140/67 NE PEUVENT PAS être CLOSES 0-hyp :
##   ÉCART RÉEL (investigation tick 4) : valeur_famille(f,i)=app("fam",f,i) est OPAQUE, sans pont vers valeur(f,x)/
##   diagonale (un pont = 23ᵉ axiome, interdit) ⇒ AUCUNE famille identité concrète en th.22 ⇒ famille_identite(f,U)
##   est un résidu indéchargeable. C'est le MÊME mur que l'existence-collectivisée reportée partout dans V9
##   (ensemble_cardinaux_inf_egal, borne_sup : existence REPORTÉE sur Th.1). Donc n°95/140/67 = « formalisables modulo
##   existence reportée » (comme a_dans_cardinaux_inf_egal), PAS 0-hyp ⇒ cases laissées NON cochées + note écart.
##   DÉCISION KARL possible (au repos) : soit relâcher la barre à « résidu honnête » (comme C61) pour cocher n°95/140/67
##   via leur cœur-contradiction, soit les laisser écart. La brique 4-lemmes reste acquise et réutilisable (D/K).

## 🔨 (archive tick1-3) GROUPE A : brique ⋃/⋂-d'un-ensemble-de-parties → débloque n°95, n°140, n°67.
##   DESIGN (theorie==22, fidèle) : Bourbaki définit ⋃_{X∈𝔊}X = réunion de la FAMILLE IDENTITÉ sur 𝔊. On réutilise
##   reunion_famille/inter_famille (déjà axiomatisés dans les 22) SANS ajouter d'axiome ni passer par graphe_terme
##   (théorie dédiée ≠22) : on prend la propriété identité « valeur_famille(f,X)=X ∀X∈U » en HYPOTHÈSE honnête
##   (pattern n°92/H). reunion_ensemble(f,U):=reunion_famille(f,U), inter_ensemble(f,U):=inter_famille(f,U).
##   ÉTAPE 1 (FAITE) : brique membre_reunion_ensemble — {famille_identite(f,U)} ⊢ (z∈⋃U)⇔(∃i)(i∈U ∧ z∈i), via
##     membre_reunion_famille + réécriture Leibniz S6 (valeur_famille(f,i)=i) sous l'existentiel (monotonie_existe ×2).
##   ÉTAPE 2 (FAITE) : membre_inter_ensemble — {famille_identite(f,U)} ⊢ (z∈⋂U)⇔(∀i)(i∈U ⇒ z∈i), dual (monotonie_pour_tout).
##   ÉTAPE 3 (FAITE) : partie_incluse_reunion {famille_identite} ⊢ (c∈U)⇒(c⊂⋃U) + inter_incluse_partie ⊢ (c∈U)⇒(⋂U⊂c).
##   ⚠️ ÉTAPE 4 = DÉCISION-CLÉ (investigation prioritaire) : l'hyp famille_identite(f,U) est-elle DÉCHARGEABLE en
##   théorie 22 ? Il faut une VRAIE famille identité sur U (valeur_famille=identité). Obstacle connu : valeur_famille(f,i)
##   =app("fam",f,i) est OPAQUE, distinct de valeur(G,i) des graphes ; le pont valeur_famille↔diagonale/valeur n'existe
##   peut-être qu'en théorie dédiée (graphe_terme_valeur ≠22). SI déchargeable → n°95/140/67 CLOS 0-hyp ; SINON ils
##   portent famille_identite = résidu honnête (comme C61) ⇒ NON « FINI » au sens boucle (case non cochée + note écart).
##   Prochain tick : investiguer le pont (grep valeur_famille def + diagonale + tout lemme reliant les deux).
##   (5) n°95 Cantor (S=⋃U, tout c∈U ⇒ c⊂S ⇒ 2^Card(S)≤Card(S) absurde) ; puis Γ⊂, n°140, n°67.
##   NB usabilité : famille_identite(f,U) devra à terme être DÉCHARGEABLE (identité concrète sur U via pont
##   valeur_famille↔diagonale) pour que n°95 soit CLOS 0-hyp — sinon n°95 reste sous cette hypothèse. À évaluer étape 4.

## ✅ BOUCLE /loop TERMINÉE (23 juil) — front closeable-au-fil-de-l'eau ÉPUISÉ.
##   Vérifié : 0 item tractable restant — les 76 cases [ ] sont TOUTES ⏸ CHANTIER ; 26 closes. La boucle 60s ne peut plus
##   rien fermer (chaque item restant = session dédiée). Pour reprendre : lancer une SESSION DÉDIÉE sur une brique à levier
##   (ordre de valeur : ⋃/⋂-d'un-ensemble → débloque n°67/95/140/familles ; converses-de-facteur+produit binaire → n°79/86 ;
##   n°92 plan prêt ; division euclidienne §5.6 ; a^n=a n°111). Chaque chantier porte son PLAN/prérequis dans ce tableau.
##   (Si Karl relance /loop : il n'y a plus d'item tractable → re-vérifier ce constat plutôt que de re-trier.)
##   BILAN 23 juil : fermés cette session — THÉORÈMES n°76/n°84/n°87, DÉFINITIONS n°80/n°85. n°92 reclassé dédié (~300 l, plan complet).
##   Bloc E.R.20-25 restant (n°93/94 ∏-famille+choix, n°52-56 produits-famille, n°57-62 quotients) = chantier (infra famille/quotient).
##   DERNIERS items moyens = n°63/67 (ordre sur N, E.R.26-27), loin derrière. La boucle 60s va surtout trier ce bloc.
##   n°87 CLOS (helper _existe_ou). ⏸ chantier : n°88/n°91 (double-famille J×K), n°89 (⋂_∅=E).
##   ⚠️ n°92 A GROSSI (assessment 23 juil) — plan RAFFINÉ, ~300 l (patterns n°84 couple + n°87 famille) :
##   ÉNONCÉ : ⊢ { ¬(I=∅), (∀i)(i∈I ⇒ valeur_famille(H,i)=produit(f_i,g_i)) } ⇒ produit(inter_famille(f,I),inter_famille(g,I)) = inter_famille(H,I).
##     · H = famille ι↦f_ι×g_ι prise EN HYPOTHÈSE (graphe_terme_valeur vit en théorie dédiée ≠22 → ne PAS construire H) ;
##     · ¬(I=∅) REQUISE : (44) FAUX pour I=∅ en ⋂ non-borné (⋂_∅=univers ⇒ (⋂f)×(⋂g)=univers×univers ≠ univers=⋂H).
##   PREUVE (extensionnalité, z générique) : ⇒ z∈(⋂f)×(⋂g), c'est un produit ⇒ z couple (u,v) [z∈A×B⇒est_couple, via témoin],
##   u∈⋂f,v∈⋂g [couple_dans_produit_ssi] ⇒ ∀i∈I: u∈f_i,v∈g_i [membre_inter_famille] ⇒ (u,v)∈f_i×g_i=H_i [couple_dans_produit_ssi
##   + hyp H] ⇒ z∈⋂H. ⇐ z∈⋂H ⇒ z∈H_{i0} pour un i0∈I [témoin de ¬(I=∅)] ⇒ z couple, puis ∀i (u,v)∈H_i=f_i×g_i ⇒ u∈f_i,v∈g_i
##   ⇒ u∈⋂f,v∈⋂g ⇒ z∈(⋂f)×(⋂g). BRICKS : membre_inter_famille, couple_dans_produit_ssi, couple_egal_projections+est_un_couple
##   (décomp n°84), non_vide_ssi_element (témoin i0), _pourtout_et_distrib, extensionnalite_appliquee. Réutiliser idiomes n°84.
##   CLOS théorèmes taille-n°76 : n°76, n°84. CLOS prose/déf : n°80. Dédiées : n°77/78/79 (glue), n°82/83 (bijections 𝔓↔appl).
##   n°85 = E.R.16 item 13 : SURTOUT des DÉFINITIONS (fonction de 3 args f(x,y,z) sur E×F×G, applications partielles f(a,·,·))
##   → formaliser la/les définition(s), pas de théorème (comme représentation_parametrique n°80). n°86 (item 14 : f×g×h préserve
##   inj/surj/bij) = THÉORÈME modéré/dédié. Ensuite familles/produits/quotients (chantier) puis n°63/67 (ordre N, derniers moyens).
##   FRONTIÈRE SATURÉE ATTEINTE (confirme mémoire bourbaki-frontiere-2026-06). §6.3 corollaires Th.2 : n°110/112/113/114
##   = chantiers (reporté/famille/sup) ; n°111 (a^n=a) = ⏸ CHANTIER-DÉRIVATION (tous bricks clos mais ~centaines de lignes
##   + Hessenberg + mismatch entier↔ensemble ; Prop.9 égalité PAS close, contournement Cantor-Bernstein — plan complet au n°111).
##   ⇒ les tours suivants fast-trient §6.4/6.5 (dénombrable/famille/nœthérien, majoritairement lourds), §7 (Zorn-limites),
##   IV (CST22) — pour ATTEINDRE les items LÉGERS du Résumé (E.R. T2 : n°76/77/79/80/84/63/67/57, applications/ordre-sur-N,
##   indépendants de §6). Note fidélité : Résumé = synthèse de Chap I-IV antérieurs, donc le dériver ne viole PAS l'ordre.
##   🔑 INFRA PARTAGÉE à bâtir (session dédiée) : ⋃-d'un-ensemble-de-parties → débloque n°95, n°140, familles §3.3

────────────────────────────────────────────────────────────────────────────────
# À FAIRE — en ordre livre

## Chapitre I — Logique (E I)
- [x] 46 C45 sens réciproque ✅ CLOS 23 juil (c45_arriere, i_5_3_relations_fonctionnelles_c45.py :
      schéma métathéorique — d'un thm CLOS ⊢ R⇒(x=T) [x∉T] produit ⊢ relation_univoque_x(R),
      CLOS 0 hyp ; route livre gén.x + instancie y,z + symétrie/transitivité ; 8 tests §I.5.3 verts) | E I.41 L.14-19 | T2
- [x] 48 C46 R fonctionnelle ⇔ (x=τx(R)) ✅ CLOS 23 juil (i_5_3_relations_fonctionnelles_c46_c47.py :
      c46_avant [de ⊢«R fonctionnelle» produit ⊢R⇔(x=τx(R)) : C45 direct + S6/témoin] et
      c46_arriere [de ⊢R⇔(x=T) produit ⊢«R fonctionnelle» : c45_arriere + T=T/S5] ; schémas
      métathéoriques, clos 0 hyp ; 4 tests + 22 verts §I.5, theorie=22) | E I.41 L.24-36 | T2
- [x] 50 C47 S{τx(R)} ⇔ (∃x)(R{x} et S{x}) ✅ CLOS 23 juil (c47_equivalence dans
      i_5_3_relations_fonctionnelles_c46_c47.py : de ⊢«R fonctionnelle» produit
      ⊢ S{τx(R)} ⇔ (∃x)(R et S), CLOS ; route noyau équivalente aux C46+C43+C33 du livre
      [2 sens directs : témoin+S5 ; C46+Leibniz+existe_elimination] ; 24 tests §I.5 verts) | E I.42 L.5-13 | T3

## Chapitre II — Ensembles (E II)
- [ ] ⏸ CHANTIER 12 f=(t↦A{t}) bijection Θ ≅ F/R (R équiv. dans F) | E II.48 L.3-6 | T4
      PRÉREQUIS non formalisés (déféré session dédiée) : théorème général §6.9 E II.47
      « f:t↦A{t} bijection Θ→E_R sous condition (1) » (Θ ensemble-index + graphe de f
      NON formalisés ; seule la NOTION ensemble_classes_objets/E_R existe, host
      ensembles_quotient_complements.py l.361-368) ; injectivité θ{x}=θ{x'}⇒R{x,x'}
      (réciproque de classe_objets_unicite, déjà close) ; identification E_R = F/R.

## Chapitre III — Ordre, cardinaux, entiers (E III)
### §1-2 Ordre / bon ordre
- [ ] ⏸ CHANTIER 7 ordre quotient sur E/S (R' ordre sur E/S) | E III.4 L.1-3 | T4
      (prérequis : ordre quotient non formalisé — même famille infra §II.6/quotient que n°12 ;
      à évaluer en session dédiée avant de dériver)
- [ ] ⏸ CHANTIER 8 préordre version graphe (Δ⊂G, G∘G=G, S=G∩G⁻¹) | E III.4 L.4-12 | T4
      (prérequis : préordre-comme-correspondance Γ=(G,E,E) non formalisé ; compo de graphes
      existe en ii_3 mais le préordre-graphe est à bâtir — session dédiée)
- [x] 10 C58 partie 2 ✅ CLOS 23 juil (ensembles_c58_ordre_strict.py : c58_trans_gauche
      {card(y),card(z)}⊢(x≤y et y<z)⇒x<z et c58_trans_droite {card(x),card(y)}⊢(x<y et y≤z)⇒x<z ;
      route livre exacte [transitivité pour x≤z ; x=z⇒égalité via antisym cardinale, contredit la
      partie stricte, contraposée] ; 5 tests §III.1.4 verts, theorie=22) | E III.5 L.8-15 | T2
- [ ] ⏸ CHANTIER 134/135/136/137/138 **cluster bon-ordre segments/réunion §2.1-2.3** | E III.16-21 | T3-T4
      Prop.3 (n°134 : famille de bien-ordonnés 2-à-2 segments ⇒ ordre unique sur ⋃X_ι, bien
      ordonné + 3 propriétés de segments) + sa démo (135) reposent sur le **Lemme 1** (136,
      réunion filtrante) dont le host `ensembles_lemme1_reunion_filtrante.py` déclare LUI-MÊME
      « DÉRIVATION NON FAITE (PARTIEL ; chantier) » ; Lemme 2 (137) et Prop.4/Zorn-route (138)
      idem. Prérequis à bâtir en session dédiée : dérivation Lemme 1 (graphe ⋃G_α, cohérence),
      Lemme 2 (segments clos), puis Prop.3/Prop.4. Déféré (page E III.16 relue 23 juil).
- [x] 139 Cor.1 Th.2 (élément maximal m≥a) ✅ CLOS 23 juil (ensembles_zorn_corollaires.py :
      zorn_cor1_maximal_superieur, {est_inductif(G,E), a∈E} ⊢ ∃m(element_maximal(G,E,m) et (a,m)∈G) ;
      Zorn appliqué au MÊME graphe G sur F={x≥a} [est_ordre indépendant du support, réflexivité
      transférée], F inductif [chaîne de F = chaîne de E, majorant m≥c≥a ou a si vide], transfert
      maximal ; ~200 lignes, F opaque + axiome dédié, theorie=22 ; 2 tests verts) | E III.21 L.11-14 | T3
- [ ] ⏸ CHANTIER 140 Cor.2 Th.2 (famille close réunion/inter chaînes ⇒ max/min) | E III.21 L.15-17 | T3
      DÉRIVABLE mais NOUVELLE infra (contrairement à Cor.1 qui réutilisait G sur un sous-ensemble) :
      exige de CONSTRUIRE (a) le graphe-ordre-inclusion Γ_⊂ sur une famille 𝔉 [(X,Y)∈Γ ⇔ X⊂Y ;
      les briques inclusion_reflexive/transitive/antisym existent mais donnent la RELATION ⊂, pas
      le GRAPHE] et (b) l'union ⋃𝔊 d'un ENSEMBLE de parties [seuls binaire/famille/Zermelo existent],
      + est_ordre(Γ_⊂,𝔉) + inductivité (majorant=⋃𝔊∈𝔉 par hyp) + Zorn, ×2 pour le DUAL
      intersection/minimal. ~300 lignes, 2 constructions réutilisables → session dédiée.
- [ ] ⏸ CHANTIER 141 Cor.2 Lemme 4 (isos croisés ⇒ S=E,T=F, f,g réciproques) | E III.22 L.18-24 | T3
      (cluster §2 segments/Lemme 4 — pas de host, CAMPAGNE_TROUS ; même famille que 134-138, déféré)
- [ ] ⏸ CHANTIER 142 Cor.3 (tout A⊂bon ordre E ≅ segment de E) | E III.22 L.25-30 | T3
      (segment-isomorphisme via Lemme 4 — cluster §2 déféré)
### §3.3-3.6 Arithmétique cardinale — formes FAMILLE
- [ ] ⏸ CHANTIER 100-108 (+Cor.1 §3.6) **cluster arithmétique cardinale FAMILLE** | E III.25-30 | T3-T4
      ✅ CORRECTION AUDIT (boucle CHANTIERS tick 19) : **n°100 Def.3 est DÉJÀ FORMALISÉ** — produit_cardinal(f,i)=Card(∏X_ι)
      ET somme_cardinale(f,i)=Card(⨆X_ι) EXISTENT (definitions_cardinaux/ensembles_cardinaux.py:125-137, @livre Def.3).
      Le note « dossiers iii_3_6/iii_3_7 VIDES » ne vaut QUE pour les LOIS (props). Cluster reste [ ] car UNE SEULE case
      pour 100-108 : les props 101-108 (Prop.4/5/6/7/10/14) = LOIS d'arith. cardinale famille = constructions de
      BIJECTIONS (associativité/distributivité/reindexation ∏,Σ) — vrai chantier d'infra, session dédiée. Déféré.
      · 100 Def.3 (E III.25 L.32-34) · 101 Prop.4 (E III.26 L.3-8) · 102 Cor Prop.4 (E III.26 L.9-12)
      · 103 Prop.5 a/b/c (E III.26-27) · 104 Prop.6 (E III.27 L.15-23) · 105 Cor.2 §3.4 (E III.27 L.25-30)
      · 106 Prop.7 (E III.28 L.1-4) · 107 Prop.10 (E III.28 L.25-28) · 108 Prop.14 (E III.30 L.4-6)
      · Cor.1 §3.6 J⊂I (E III.30 L.12-15)
- [ ] ⏸ CHANTIER 95=133 Cor. Th.2 Cantor (pas d'ensemble de tous les cardinaux) | E III.30 L.27-33 | T3
      DÉRIVABLE mais exige la brique **⋃U (union d'un ENSEMBLE de parties)** — la MÊME que n°140 et
      l'arithmétique famille : la démo pose S=⋃_{X∈U}X, tout cardinal c∈U vérifie c⊂S donc c≤Card(S),
      puis 2^Card(S)≤Card(S), absurde (aucun_plus_grand_cardinal CLOS). Reste tractable (~150 l) une
      fois ⋃U bâti. 🔑 INFRA PARTAGÉE ⋃-d'un-ensemble : la bâtir UNE fois débloque n°95 + n°140 +
      familles §3.3 — candidat prioritaire de session infra dédiée.
### §4.3 Variantes du principe de récurrence
- [x] 96 Variante 1 récurrence FORTE ✅ CLOS 23 juil (ensembles_recurrence_forte_preuve.py :
      recurrence_forte ⊢ (∀n)(n entier ⇒ R{n}) sous {H=(∀n)(S{n}⇒R{n}),
      predecesseur_fini_universel} — 3 maillons : S{0} vacuité, S{n}⇒S{n+1}
      [successeur_ordre_strict + C58 + cas()], C61 [principe_recurrence_preuve] + retour R.
      3 tests verts, theorie=22, 2 résidus honnêtes hérités de C61) | E III.33 L.4-15 | T2
- [x] 97 Variante 2 « récurrence à partir de k » ✅ CLOS 23 juil (ensembles_recurrence_depuis_preuve.py :
      recurrence_depuis, S{n}:=(k≤n)⇒R{n} ; S{0} [k≤0 ⇒ k=0 par antisym ⇒ R{k}], hérédité [disjonction
      sur k≤n : si oui prémisse-depuis, sinon ¬(k≤n)⇒¬(k<n+1) [successeur_ordre_strict] + C58 sur k≤n+1
      ⇒ k=n+1 ⇒ R{k}], C61 + décurryfiage ; ⊢ (∀n)((n entier et n≥k)⇒R{n}) sous 3 hyps {hyp, card k,
      predecesseur_fini_universel} ; 3 tests, theorie=22) | E III.33 L.16-26 | T2
- [x] 98 Variante 3 « récurrence limitée à [a,b] » ✅ CLOS 23 juil (ensembles_recurrence_intervalle_preuve.py :
      recurrence_intervalle, S{n}:=(a≤n et n≤b)⇒R{n} ; miroir variante 2 + borne b (de n+1≤b :
      n≤b par successeur_ordre+transitivité, n<b par succ_pas_inf_egal) ; C61 + décurryfiage ;
      ⊢ (∀n)((n entier et a≤n≤b)⇒R{n}) sous 3 hyps {hyp, card a, predecesseur_fini_universel} ;
      3 tests, theorie=22 ; dérivée du premier coup) | E III.33 L.27-33 | T2
- [x] 99 Variante 4 « récurrence descendante » ✅ CLOS 23 juil (ensembles_recurrence_descendante_preuve.py :
      recurrence_descendante, RÉDUITE à la variante 3 comme dans le livre. pas_ascendant_non_R = contraposée
      du pas descendant (R{m+1}⇒R{m} ⊢ ¬R{m}⇒¬R{m+1}) ; pour n∈[a,b] par l'absurde, ¬R{n} + pas ascendant
      + recurrence_intervalle(¬R) sur [n,b] donnent ¬R{b} en m=b, contredisant R{b}, d'où R{n} par tiers
      exclu ; ⊢ (∀n)((n entier et a≤n≤b)⇒R{n}) sous 3 hyps {hyp descendante, est_fini b, pred universel} ;
      2 tests verts (201s), theorie=22. PIÈGE : generalise+instancie sur recurrence_intervalle α-renomme les
      liants internes ⇒ MP échoue ; FIX = appliquer recurrence_intervalle DIRECTEMENT à la base voulue
      (a="nfin", b) puis décharger H_int/card par _cut) | E III.33 L.34 - E III.34 L.7 | T2
### §5.6-5.7 Division euclidienne / base b  ⏸ CHANTIER (session dédiée, cf. mémoire bourbaki-chantier-division-euclidienne)
###   Prérequis : remplacer plus_ent/prod_ent opaques par somme/produit_cardinal_binaire ; existence par
###   récurrence forte C61 sur a (a<b→(0,a) ; a≥b→HR sur a−b). Tests lourds ⇒ session FRAÎCHE. n°23-28 déférés.
- [~] 23 ✅✅ CLOS modulo C61 (24 juil nuit) Th.1 division euclidienne EXISTENCE **+ UNICITÉ** (Th.1 COMPLET) | E III.39 L.10-19 | T3
      UNICITÉ : ensembles_division_unicite.py : _unicite ⊢ {Fini b,q,q',r,r', +C61} ⊢ (b·q+r=a et r<b et b·q'+r'=a et r'<b)⇒
      (q=q' et r=r'), concl==énoncé, 7 hyps, theorie==22. Route SANS commutativité (prop4_translation_stricte/injective, verrou-τ
      évité par _inst_gen). Sous-lemmes VERTS : _gap (succ q≤q'), _lt_chain (b·q+r<b·q'+r', le cœur), _unicite. Test fichier seul.
      Le THÉORÈME 1 §5.6 (existence ET unicité du quotient/reste) est DÉMONTRÉ (« CLOS modulo C61 »).
      ensembles_division_existence_final.py : division_existence ⊢ {b≠0, Fini b, pred_univ, principe_recurrence,
      cardinal_pas_entre} ⊢ (∀n)(Fini n ⇒ (∃q)(∃r)(b·q+r=n et r<b)). concl==énoncé, 5 hyps, theorie==22. Route
      commute-free (_diff_strict), récurrence forte + trichotomie_finis. Résidus = C61 (mêmes que l'existence de ℕ)
      ⇒ « CLOS modulo C61 », PAS coché [x] FINI sec (décision honnêteté). RESTE : UNICITÉ (quotient/reste uniques) pour
      l'énoncé COMPLET du Th.1, + Def.1 n°24 (reste/multiple/diviseur) au-dessus.
- [x] 24 ✅ CLOS (24 juil nuit) Def.1 (reste, multiple, divisible, diviseur, quotient) | E III.39 L.20-23 | T2
      ensembles_division_definitions.py : divise_cardinal(b,a):=(∃q)(Fini q et a=b·q) [produit cardinal RÉEL], est_multiple_cardinal /
      est_diviseur_cardinal synonymes, reste_cardinal(a,b):=τr((∃q)(b·q+r=a et r<b)), quotient_cardinal(a,b):=τq(...) — alignés sur
      _R_rel (division_existence). DÉFINITIONS (constructeurs, pas de théorème ⇒ pas de résidu). Supplantent les placeholders OPAQUES
      (app prod_ent/reste/quot_ent) de ensembles_entiers, pour la FIDÉLITÉ. Test fichier 4 passed 0,22s, theorie==22.
- [ ] 26 ⏸ CHANTIER stabilité des multiples (prose formalisable) | E III.39 L.27-31 | T3  (arith. multiples, après n°23/24)
- [ ] 27 ⏸ CHANTIER Prop.8 base b (E_k lexico ≅ intervalle (0,b^k−1)) + démo | E III.40 L.1-21 | T3  (base b, après division euclid.)
- [ ] 28 ⏸ CHANTIER a<b^a + existence/unicité dév. base b | E III.40 L.22-29 | T2  (base b, après division euclid.)
### §5.8 Combinatoire  ⏸ CHANTIER (démos n°30-42 déférées ; ÉNONCÉS déjà formalisés, forme multiplicative)
###   Prérequis PARTAGÉ : principe des bergers PLEIN (seul le cœur binaire est clos, ensembles_prop9_bergers_iii5.py)
###   = arithmétique de famille INDEXÉE §3.3 (Prop 5b partition + Prop 6 Cor 2 famille constante) ⇒ bloqué sur
###   ⋃-d'un-ensemble ; ET coefficient binomial DÉFINI comme Card{X⊂E:Card X=p} (opaque ici). Session infra dédiée.
- [ ] 30 ⏸ CHANTIER Prop.10 n!/(n−m)! = # injections + démo | E III.41 L.33 - E III.42 L.4 | T3 (bergers d'abord)
- [ ] 31 ⏸ CHANTIER Cor. # permutations = n! (cas m=n de Prop.10) | E III.42 L.5-7 | T2
- [ ] 32 ⏸ CHANTIER Prop.11 recouvrements disjoints n!/∏p_i! + démo | E III.42 L.8-21 | T3
- [ ] 33 ⏸ CHANTIER Cor.1 # parties à p éléments = n!/(p!(n−p)!) | E III.42 L.22-24 | T3
- [ ] 34 ⏸ CHANTIER symétrie binomiale (n p)=(n n−p) [exige (n p)=Card{X⊂E:Card X=p}] | E III.42 L.25-28 | T2
- [x] 35 convention (n p)=0 si p>n ✅ CLOS 17 juil (enonce_convention_binomiale_nulle,
      garde inf_strict_card, 9 tests §5.8) | E III.43 L.1-6 | T2
- [ ] 36 ⏸ CHANTIER Cor.2 # applications strict. croissantes E→F = (n p) + démo | E III.43 L.7-13 | T3
- [ ] 37 ⏸ CHANTIER Prop.12 Σ_p (n p) = 2^n + démo | E III.43 L.14-16 | T3
- [ ] 38 ⏸ CHANTIER Prop.13 Pascal (n+1 p+1)=(n p+1)+(n p) + démo | E III.43 L.17-25 | T3
- [ ] 40 ⏸ CHANTIER Prop.14 # couples i≤j (resp. i<j) = n(n+1)/2 (resp. n(n−1)/2) + démo | E III.43 L.28 - E III.44 L.5 | T3
- [ ] 41 ⏸ CHANTIER Cor. Σ_{i=1..n} i = n(n+1)/2 | E III.44 L.6-10 | T3
- [ ] 42 ⏸ CHANTIER Prop.15 # applications u:E→(0,n), Σu(x)≤n (resp.=n) + démo | E III.44 L.11-26 | T4
### §6 Ensembles infinis
- [ ] 110 ⏸ CHANTIER Lemme 1 (tout infini ⊇ un équipotent à N ; ℵ₀≤a) + démo | E III.47 L.33 - E III.48 L.2 | T3
###   REPORTÉ (cf. aleph0_inf_egal_cardinal_infini_enonce, code explicite) : exige collectivisation de N (Th.1)
###   + « tout entier n ≤ a » (entier_inf_egal_a, sous fini_downward/C61) + arithmétique cardinale infinie (sup/limite).
- [x] 111 ✅ CONDITIONNEL Cor.1 Th.2 (a^n=a, a infini, n≥1) | E III.49 L.5-6 | T2  → a_puissance_n_egale_a
###   ✅ 24 juil (ticks 22-34) : `a_puissance_n_egale_a` ⊢ {Eq(A×A,A), a₀∈A, predecesseur_fini_universel}
###   (∀n)((n entier et n≥1) ⇒ Eq(𝓕(n;A),A))  [= aⁿ=a, n≥1]. theorie=22, 14 tests verts. Fichier
###   iii_6_2_proprietes_infinis/ensembles_a_puissance_n_er.py (13 ponts + base + hérédité + assemblage).
###   RÉCURRENCE « à partir de 1 » (variante 2 recurrence_depuis) sur R{n}=Eq(𝓕(n;A),A) : base_111 (R{1}, clos,
###   pont eq_un_singleton Eq(1,{∅})) + heredite_111 (R{n}⇒R{n+1}, {a²=a,a₀∈A}, via Cantor-Bernstein sur SUP
###   [inf_egal_phi Dir.A + a²=a] et INF [support_extension_domaine + a₀∈A]). Assemblage : décharge des 2 gardes
###   k-dépendantes dans la conclusion → ∀kdep → instancie 1 → décharge conjonction_intro(base,hérédité) +
###   un_est_un_cardinal. LIVRABLE ACCEPTÉ (consigne). Les 3 hyps sont des RÉSIDUS déchargeables en test lent isolé :
###   a²=a par Hessenberg (hessenberg_a_carre_egal_a_0hyp, 10-18 min) ; a₀∈A par « A infini ⇒ non vide » ;
###   predecesseur_fini_universel par predecesseur_fini_universel_preuve (schéma C61). ⇒ version 0-hyp = test lent final reporté.
###   ⚠️ test file lourd (92s seul ; 426s sous contention) — après cette clôture, candidat au marqueur `slow`.
- [ ] 112 ⏸ CHANTIER Cor.2 Th.2 (∏ famille finie, plus grand infini) | E III.49 L.7-11 | T2  (arith. famille indexée §3.3)
- [ ] 113 ⏸ CHANTIER Cor.3 Th.2 (Σ famille de cardinaux ≤a, indices ≤a) | E III.49 L.12-16 | T2  (arith. famille indexée §3.3)
- [ ] 114 ⏸ CHANTIER Cor.4 Th.2 (ab=a+b=sup(a,b)) | E III.49 L.17-19 | T2
###   Partie PRODUIT (ab=b sous a≤b, 1≤a, b infini) tractable en binaire (Th.2 + monotonie produit close) ; mais
###   énoncé FIDÈLE exige (a) sup(a,b) cardinal DÉFINI (absent) et (b) partie SOMME a+b=b exige « 2≤b » pour b infini
###   = tranche du « entier≤infini » REPORTÉ (cf. n°110). Déféré tant que sup + 2≤b(infini) non clos.
- [ ] 115 ⏸ CHANTIER Prop.1 §6.4 2e/3e assertions (∏ fini / ⋃ suite dénombrables) | E III.49 L.23-27 | T3  (∏ famille + ⋃ suite)
- [ ] 116 ⏸ CHANTIER Prop.2 §6.4 (tout infini dénombrable ≅ N) | E III.49 L.30-32 | T3  (exige ℵ₀≤a = n°110 reporté)
- [ ] 117 ⏸ CHANTIER Prop.3 §6.4 (partition infini en dénombrables infinis) | E III.50 L.1-3 | T3  (partition/famille)
- [ ] 118 ⏸ CHANTIER Prop.4 §6.4 (fibres dénombrables ⇒ équipotence) | E III.50 L.4-8 | T3  (famille de fibres)
- [ ] 119 ⏸ CHANTIER Prop.5 §6.4 (F(E) parties finies ≅ E) + démo | E III.50 L.9-17 | T4  (parties finies, lourd)
- [ ] 120 ⏸ CHANTIER Cor Prop.5 (suites finies ≅ E) | E III.50 L.18-23 | T4  (suites finies, lourd)
### §6.5 ⏸ CHANTIER (n°121-124 : Prop.6 et suite — récursion/choix sur les suites ; est_stationnaire/est_noetherien
###   DÉFINIS mais l'équivalence max⇔stationnaire n'est pas prouvée ; n°122/123 en dépendent). Session dédiée.
- [ ] 121 ⏸ CHANTIER Prop.6 §6.5 (max ⇔ suites croissantes stationnaires) + démo | E III.51 L.1-12 | T3
- [ ] 122 ⏸ CHANTIER Cor.1 Prop.6 (bien ordonné ⇔ décroissantes stationnaires) | E III.51 L.13-17 | T3
- [ ] 123 ⏸ CHANTIER Cor.2 Prop.6 (suite croissante d'un ordonné fini stationnaire) | E III.51 L.18-21 | T2 (dépend n°121)
- [ ] 124 ⏸ CHANTIER Prop.7 récurrence nœthérienne | E III.51 L.24-28 | T3
### §7 Limites projectives / inductives  ⏸ CHANTIER (tout le §7 : infra limites proj/ind + Zorn non bâtie ; T3/T4)
- [ ] 14 ⏸ CHANTIER Prop.5 §7.4 (f_α surjective si I filtrant cofinal dénombrable) + démo | E III.58 L.1-14 | T3
- [ ] 15 ⏸ CHANTIER conditions (i)/(ii)/(ii') sur S_α (2e critère non-vacuité) | E III.58 L.15-25 | T3
- [ ] 16+17+18 ⏸ CHANTIER Th.1 limites projectives (i)-(iv)⇒a),b) + démo (E III.59 entière, Zorn) | E III.58 L.26 - E III.60 L.17 | T4
- [ ] 20 ⏸ CHANTIER Lem.1 §7.5 (relèvement fini dans lim→) + démo | E III.62 L.8-20 | T3
- [ ] 21 ⏸ CHANTIER Prop.6 §7.6 (propriété universelle lim→, ∃!u) + démo | E III.62 L.21 - E III.63 L.4 | T3
- [ ] 22 ⏸ CHANTIER identités (26)(27) lim→ + démo | E III.65 L.9-21 | T3

## Chapitre IV — Structures (E IV)
- [ ] 1 ⏸ CHANTIER Démo CST22 (F_E comme produit des X_λ) | E IV.24 L.7-38 | T4 (produit-famille + structures, lourd)

## Résumé des résultats (E.R.)
### E.R.8-11 Applications
- [x] 76 « f appl. de E SUR F » ⇔ « X≠∅ ⇒ f⁻¹(X)≠∅ » ✅ CLOS 23 juil (ensembles_surjective_preimage_er8.py :
      surjective_ssi_preimage_non_vide ⊢ est_application(f,E,F) ⇒ (est_surjective(f,E,F) ⇔ (∀X)(X⊂F ⇒ (¬(X=∅) ⇒
      ¬(f⁻¹⟨X⟩=∅)))), CLOS 0 hyp, theorie=22, 2 tests verts 0,55s. Dir A (surj⇒prop) sans est_application : témoin
      z∈X→z∈image[S6]→membre_image→couple_reciproque→membre_image_reciproque→≠∅. Dir B (app∧prop⇒surj) extensionnalité :
      (a) image⊂F via f⊂E×F+couple_dans_produit_ssi ; (b) F⊂image via X={y}, prop, singleton_membre, couple_reciproque,
      image_reciproque_inclus_domaine. PIÈGE liants résolu : élément « y » en Dir B (pas « z », collision avec liant
      interne de appartient_singleton_inclus/non_vide_ssi_element) puis α-conversion y→z via instancie+generalisation
      pour extensionnalite_appliquee ; _temoin_non_vide = generalize+instancie capture-safe de non_vide_ssi_element) | E.R.8 item 7 (p.311) | T2
- [x] 77 « f⁻¹(f(X))=X et f(f⁻¹(Y))=Y ∀X,Y » ⇔ « f bijective » ✅ CLOS 23 juil (boucle CHANTIERS Groupe B) —
      ii_3_2_reciproque/ensembles_bijective_identites_er10.py : bijective_ssi_identites ⊢ est_application(f,E,F) ⇒
      ((∀X⊂E)(f⁻¹⟨f⟨X⟩⟩=X) et (∀Y⊂F)(f⟨f⁻¹⟨Y⟩⟩=Y) ⇔ est_bijective(f,E,F)), CLOS 0 hyp, theorie=22, 7 tests verts.
      Assemblage 5 ponts/converses NEUFS : hyp_applicative_de_application, inj_dans_implique_reciproque_fonctionnel
      (via _valeur_de_couple + Prop.7), direction_bijective_vers_identites (⇐, bricks (18)/(19)-égalité existants),
      converse_Y_vers_surjective (Y=F), converse_X_vers_injective (singletons X={u} + couple_reciproque). | E.R.10 item 10d (p.313) | T2
###   Énoncé : (∀X⊂E)(f⁻¹⟨f⟨X⟩⟩=X) ∧ (∀Y⊂F)(f⟨f⁻¹⟨Y⟩⟩=Y) ⇔ est_bijective(f,E,F)=injective_dans(f,E)∧est_surjective(f,E,F).
###   NON un chantier d'infra (bricks atomiques présents) mais ~350 l, 4 parties + ponts de REPRÉSENTATION → session dédiée :
###     ⇐ inj⇒(∀X…) : image_reciproque_image_egal_si_injective EXISTE mais sous {H_app(X,f), est_fonctionnel(f⁻¹)} —
###        fournir H_app(X,f) ∀X⊂E depuis est_application (pont ~20 l) + pont injective_dans(f,E)⇒est_fonctionnel(f⁻¹) (~30 l) ;
###     ⇐ surj⇒(∀Y…) : image_image_reciproque_egal_si_surjective EXISTE sous {est_fonctionnel(f), Y⊂f⟨E⟩} (surj⇒Y⊂F=f⟨E⟩) ;
###     ⇒ (∀X…)⇒injective : converse À BÂTIR (X={a} : f(a)=f(b)⇒b∈f⁻¹⟨f⟨{a}⟩⟩={a}⇒b=a ; singletons, ~60 l) ;
###     ⇒ (∀Y…)⇒surjective : converse À BÂTIR (Y=F : f⟨f⁻¹⟨F⟩⟩=F et f⟨f⁻¹⟨F⟩⟩⊂f⟨E⟩⊂F ⇒ f⟨E⟩=F, ~40 l).
###   Réutiliser les idiomes de n°76 (singletons, α-liants y→z, _temoin_non_vide). Test léger (pas de Hessenberg).
- [ ] 78 ⏸ CHANTIER-DÉRIVATION itérées fⁿ (f¹=f, fⁿ=fⁿ⁻¹∘f, f^{m+n}=f^m∘f^n) | E.R.10 item 11 (p.313) | T3 (C63)
###   fⁿ N'EST PAS défini dans le dépôt (juste prose d'exemples E III.47 §6.2). Exige : (a) DÉFINIR la suite n↦fⁿ par
###   récursion (C62/C63) avec f¹=f, f^{n+1}=fⁿ∘f ; (b) prouver f^{m+n}=f^m∘f^n par récurrence sur n (associativité ∘).
###   Session dédiée (construction récursion + induction). Prérequis : composition ∘ (existe ii_3), C62/C63 (existe).
- [x] 79 g∘f perm E et f∘g perm F ⇒ f,g bijectives ✅ CLOS 23 juil (boucle CHANTIERS Groupe B) — ensembles_perm_composees_er10.py :
      perm_composees_bijectives ⊢ (est_application(F,E,Ff) et est_application(G,Ff,E) et est_permutation(g∘f,E) et
      est_permutation(f∘g,Ff)) ⇒ (est_bijective(F,E,Ff) et est_bijective(G,Ff,E)), CLOS 0 hyp, theorie=22, 2 tests verts.
      Assemblage des 4 converses de facteur bâties dans ensembles_composee_valeurs.py : injective_facteur_droit (×2, facteur
      intérieur d'une composée inj) + surjective_facteur_gauche (×2, facteur extérieur d'une composée surj), sur les briques
      neuves composee_valeur_app + image_incluse_arrivee. est_permutation→conjonction_elim donne inj/surj des composées. | E.R.10-11 item 12 (p.313) | T2
###   PLAN (route directe, ~250 l) : f injective ← g∘f injective [(g∘f)(u)=g(f(u)) composée-valeur + Leibniz f(u)=f(u')⇒
###   g(f(u))=g(f(u')) + injective_dans(g∘f,E)] ; f surjective ← f∘g surjective [(f∘g)⟨F⟩=f⟨g⟨F⟩⟩⊂f⟨E⟩⊂F, =F] ; f
###   bijective. Symétrique pour g. BRICKS : est_permutation=est_bijective(·,a,a), injective_dans, retraction_implique_injective
###   /section_implique_surjective_valeur (existent) MAIS converses de facteur (composée inj⇒facteur inj) À BÂTIR +
###   composée-valeur générale (g∘f)(x)=g(f(x)) + image-de-composée f⟨g⟨·⟩⟩ pas garanties closes ⇒ session dédiée.
- [x] 80 représentation paramétrique (ensemble des paramètres) ✅ CLOS 23 juil (DÉFINITION, pas de théorème :
      representation_parametrique(f,E,F):=est_surjective(f,E,F) dans ensembles_fonctions_complements.py, @livre Def
      E.R.11 item 14. Terminologie pure — « application de E SUR F = représentation paramétrique de F, E=paramètres » ;
      synonyme de la surjection, aucune propriété nouvelle donc aucun Theoreme) | E.R.11 item 14 (p.314) | T2
### E.R.13-17 Correspondances / coupes / produits
- [ ] 82 ⏸ CHANTIER-DÉRIVATION parties fonctionnelles 𝔓(E×F) ↔ applications d'une partie de E dans F | E.R.13 item 5 (p.316) | T3
###   BIJECTION entre ensembles : {C⊂E×F fonctionnel} ↔ {applications d'une partie de E dans F}. Exige de CONSTRUIRE les
###   deux ensembles (partie de 𝔓(E×F) + ensemble des applications d'une sous-partie) + la bijection C↦(pr₁C→F) + inj/surj.
###   ~300 l, objets ensemblistes à bâtir → session dédiée.
- [ ] 83 ⏸ CHANTIER-DÉRIVATION 𝔓(E×F) ↔ applications de E dans 𝔓(F) | E.R.14 item 7 (p.317) | T3
###   BIJECTION 𝔓(E×F) ↔ {applications E→𝔓(F)} (C ↦ (x↦C(x)=coupe)). ~300 l, même famille que n°82 → session dédiée.
- [x] 84 « K⊂K' » ⇔ « K(x)⊂K'(x) ∀x » ✅ CLOS 23 juil (ensembles_inclusion_coupes_er14.py : inclusion_ssi_coupes
      ⊢ est_un_graphe(K) ⇒ (K⊂K' ⇔ (∀a)(K{a}⊂K'{a})), CLOS 0 hyp, theorie=22, 2 tests 0,21s. ⇒ via coupe_caracterisation
      [(y∈K{a})⇔((a,y)∈K)] + inclus(K,K') instancié à (a,y) ; ⇐ sous est_un_graphe(K) : z∈K couple → z=(pr₁z,pr₂z)
      [couple_egal_projections] → pr₂z∈K{pr₁z} → hyp x=pr₁z → (pr₁z,pr₂z)∈K' → z∈K'. PIÈGES résolus : coupe_membre a le
      liant interne « x » ⇒ point de coupe nommé « a » (pas « x ») ; coupe_caracterisation n'accepte que des NOMS ⇒
      generalize a,y puis instancie pour les termes pr₁z/pr₂z ; pont α est_un_couple[x,y]→est_couple[a,b]) | E.R.14 item 8 (p.317) | T2
- [x] 85 fonctions de 3 arguments et plus ✅ CLOS 23 juil (DÉFINITIONS, pas de théorème : 4 défs dans
      ensembles_fonctions_complements.py — est_fonction_trois_arguments(f,E,F,G) [fonctionnel + dom⊂(E×F)×G],
      valeur_trois_arguments(f,x,y,z):=f(((x,y),z)), application_partielle_trois_premiere_terme (f(a,·,·)),
      application_partielle_trois_deux_terme (f(a,b,·)) ; @livre Def E.R.16 item 13, produit associé à gauche ;
      calque des fonctions à 2 args. Terminologie du livre, aucune propriété nouvelle) | E.R.16 item 13 (p.319) | T2
- [ ] 86 ⏸ ÉCART (boucle CHANTIERS tick 11) préservation inj/surj/bij par f×g×h | E.R.16 item 14 (p.319) | T2
###   ÉCART CONFIRMÉ : produit_applications=app("produit_app",g,h) OPAQUE ; produit binaire de fonctions (x,y)↦(f(x),g(y))
###   exige graphe_terme (théorie dédiée ≠22) ou hyp-valeur honnête (pas 0-hyp) = MÊME mur que la famille identité Groupe A.
###   Case non cochée. Déblocable seulement avec l'infra terme-défini (décision Karl : relâcher barre 0-hyp, ou construire).
###   f×g×h : E×F×G→E'×F'×G' préserve inj/surj/bij. PAS de préservation BINAIRE (f×g) close ; seule la version FAMILLE
###   (§5.7, extension_produit via théorie dédiée axiome_extension_produit) existe = chantier. Exige soit bâtir le produit
###   binaire de 2 fonctions (x,y)↦(f(x),g(y)) + préservation coordonnée [couple_dans_produit_ssi] puis (f×g)×h (~250 l),
###   soit l'infra famille. → session dédiée.
### E.R.18-20 Familles réunion/intersection/produit
- [x] 87 (36) ⋃_{J₁∪J₂}X_ι = (⋃_{J₁})∪(⋃_{J₂}) ✅ CLOS 23 juil (ensembles_reunion_indices_union_er18.py :
      reunion_indices_union, CLOS 0 hyp, theorie=22, 2 tests 0,10s, DU PREMIER COUP. Extensionnalité + chaîne membership
      via membre_reunion_famille (generalize I + instancie J₁∪J₂), _instance_reunion binaire, et_ou_distrib+commute, et
      un helper local **_existe_ou** [(∃x)(P∨Q)⇔(∃x)P∨(∃x)Q, fwd cas+s5 / bwd monotonie_existe]. 🔧 RÉUTILISABLE :
      _existe_ou + _commute_et + _equiv_sym + le pattern « chaîne membership sous congruence_existe » resserviront à
      n°88/91/92 (identités binaires de familles)) | E.R.18 item 3 (p.321) | T2
- [ ] 88 ⏸ CHANTIER-DÉRIVATION (38) (⋃X_ι)×(⋃Y_κ)=⋃(X_ι×Y_κ) famille | E.R.18 item 3 (p.321) | T3
###   RHS = famille indexée par le PRODUIT J×K (ι,κ)↦X_ι×Y_κ — famille DOUBLE-INDEXÉE non formalisée (à construire :
###   graphe_terme sur J×K + membership). Dédiée. (n°92 « mêmes indices » est SIMPLE et closeable, cf. plus bas.)
- [ ] 89 ⏸ CHANTIER (40) ⋂ sur J=∅ vaut E | E.R.19 item 6 (p.322) | T2 (écart AXIOME_INTER_FAM connu)
###   NON DÉRIVABLE en l'état : AXIOME_INTER_FAM est explicitement restreint à I≠∅ (commentaire abrege.py:1061) et donne
###   z∈⋂_∅ ⇔ (∀i)(i∈∅⇒…) = VRAI ∀z = l'UNIVERS, pas E. (40) est la CONVENTION de Bourbaki (⋂ d'une famille de PARTIES de E
###   bornée à E). Prérequis (session dédiée) : ⋂ bornée à 𝔓(E) OU poser (40) comme convention/définition pour le cas vide.
- [ ] 91 ⏸ CHANTIER-DÉRIVATION (43) (⋂X_ι)×(⋂Y_κ)=⋂(X_ι×Y_κ) famille | E.R.19 item 8 (p.322) | T3
###   Comme n°88 : famille DOUBLE-INDEXÉE J×K (ι,κ)↦X_ι×Y_κ non formalisée → dédiée.
- [x] 92 (44) (⋂X_ι)×(⋂Y_ι)=⋂(X_ι×Y_ι) même indices ✅ CLOS 23 juil (boucle CHANTIERS Groupe C) —
      ii_4_2_proprietes/ensembles_produit_inter_familles_er20.py : produit_inter_familles ⊢ (¬(I=∅) et (∀i)(i∈I⇒H_i=X_i×Y_i))
      ⇒ (⋂X)×(⋂Y)=⋂H, CLOS 0 hyp, theorie=22, 2 tests verts. H-propriété + non-vacuité en ANTÉCÉDENT (0-hyp, PAS écart).
      Extensionnalité + témoins existentiels p,q du produit (pas pr₁/pr₂) : ⇒ membre_inter_famille×2 + _cpp_ssi + Leibniz H_i ;
      ⇐ témoin i0 (non_vide_ssi_element + alpha_existe z→i0), même route inverse. helper _cpp_ssi (couple_dans_produit_ssi
      generalize+instancie, anti-collision liants p,q). | E.R.20 item 8 (p.323) | T3
###   CLOSEABLE mais ~300 l (assessment 23 juil a révélé la vraie taille) : combine pont couple n°84 (est_un_couple↔est_couple
###   + couple_egal_projections + décomposition z=(pr₁z,pr₂z)), membership-famille n°87 (membre_inter_famille), distribution
###   ∀-sur-∧ (_pourtout_et_distrib), témoin I≠∅ (non_vide_ssi_element), ET membership produit générique dans les 2 sens
###   (_instance_produit ∃p∃q OU couple_dans_produit_ssi après décomposition). Subtilités : hyp ¬(I=∅) [(44) faux pour ∅],
###   H=ι↦f_ι×g_ι en hyp [graphe_terme_valeur en théorie dédiée]. Haut risque mismatch liants ⇒ session dédiée. PLAN complet
###   ci-dessus (pointeur) : ⊢ {¬(I=∅), (∀i)(i∈I⇒valeur_famille(H,i)=produit(f_i,g_i))} ⇒ produit(⋂f,⋂g)=inter_famille(H,I).
- [ ] 93 ⏸ CHANTIER ∏ sur famille vide = singleton ; ∏X_ι=E^J si X_ι=E | E.R.20 item 9 (p.323) | T4
###   produit_famille + membership EXISTENT, mais : (a) ∏_∅=singleton{∅} = subtilité empty-index (comme n°89 AXIOME_INTER_FAM) ;
###   (b) ∏_J E=E^J = lien produit-famille ↔ exponentiation (exposant_cardinal). 2 sous-résultats à assesser en dédié (T4).
- [ ] 94 ⏸ CHANTIER-DÉRIVATION (∀x)(∃y)R ⇔ ∃f (∀x)R{x,f(x)} (choix fonctionnel) | E.R.20 item 10 (p.323) | T3
###   Sens ⇒ construit la fonction-choix f = x↦τ_y R{x,y} (graphe_terme, théorie dédiée ≠22) + le graphe ∃f ; C-schéma τ
###   (R{x,y}⇒R{x,τ_yR}). Sens ⇐ trivial. Construction de fonction via τ = session dédiée (graphe_terme + ∃f).
### E.R.21-22 Produits de familles  ⏸ CHANTIER (n°52-56 : produit ∏ d'une famille + projections pr_ι + recollement — infra
###   produit-famille §5.4-5.7 lourde/non close ; à attaquer en session dédiée « produits de familles »)
- [ ] 52 ⏸ CHANTIER (47) ∏Xι = ⋂_ι pr_ι⁻¹(Xι) famille | E.R.21 item 12b (p.324) | T3  (∏ + pr_ι⁻¹ + ⋂-famille)
- [ ] 53 ⏸ CHANTIER (48) pr_κ(∏Xι)=X_κ si ∏_{ι≠κ}≠∅ famille | E.R.21 item 12c (p.324) | T3  (projection surjective, ∏≠∅)
- [ ] 54 ⏸ CHANTIER ∏Yι ≅ ∏_{J2}Xι (Yι={aι} sur J1) | E.R.22 item 12e (p.325) | T3  (bijection produits, singletons)
- [ ] 55 ⏸ CHANTIER (∏Aι)^E ≅ ∏(Aι^E) | E.R.22 item 13 (p.325) | T3  (exponentiation d'un ∏-famille)
- [ ] 56 ⏸ CHANTIER recollement d'une FAMILLE (fι coïncidant sur Aι∩Aκ) + F^A≅∏F^{Aι} | E.R.22 item 15 (p.325) | T2  (recollement famille)
### E.R.22-25 Équivalence / quotients  ⏸ CHANTIER (bloc équivalence/quotient — infra partition/E-R iso non close, cf. n°12)
- [ ] 57 ⏸ CHANTIER relation d'une partition (réflexive, symétrique) | E.R.22-23 §5 item 1 (p.325-326) | T2
###   (relation « même bloc » d'une partition ; infra partition/recouvrement absente [pas de est_partition] ; réflexivité
###   exige le recouvrement, item 2 §5.4 partition↔équivalence. Session dédiée équivalence.)
- [ ] 59 ⏸ CHANTIER (E×F)/R ≅ E (R : pr₁(z)=pr₁(z')) | E.R.23 item 3 (p.326) | T3  (iso quotient, infra E/R)
- [ ] 60 ⏸ CHANTIER f(A) ≅ A/R_A canonique | E.R.24 item 5 (p.327) | T3  (décomposition canonique, iso E/R)
- [ ] 61 ⏸ CHANTIER (E/R)/(T/R) ≅ E/T | E.R.25 item 9 (p.328) | T3  (quotient de quotient, iso E/R)
- [ ] 62 ⏸ CHANTIER (E/R)×(F/S) ≅ (E×F)/(R×S) | E.R.25 item 10 (p.328) | T3  (produit de quotients, iso E/R)
### E.R.26-27 Ordre sur N
- [x] 63 ✅ ℕ ORDONNÉ PAR ≤ | E.R.26 item 2 (p.329) | T2  → ordre_NN (est_relation_ordre_dans(R_N,ℕ), CLOS 0-hyp, theorie==22, test 197s)
###   ✅ 24 juil tick 39 : FORME RELATION (pas graphe) — est_relation_ordre_dans(R_N,ℕ), R_N(x,y)=(x∈ℕ et y∈ℕ et x≤y). Pur
###   assemblage : inf_egal_reflexif/transitive_general/antisymetrique_card + appartenance_NN_instanciee + fini_implique_cardinal.
###   Fichier iii_6_1_n_objet_existence/ensembles_ordre_NN.py. Le graphe G_N aurait exigé un axiome S8 dédié (casse 22) ⇒ évité.
### (ANCIEN, périmé) est_ordre(G,E) prend un GRAPHE G (ensemble de couples), pas la relation inf_egal_card ⇒ gap relation→graphe (comme n°140) :
###   construire le graphe-ordre ≤ sur N (graphe_terme/collectivisation {(x,y)∈N×N : x≤y}) + est_ordre(G_N,N) [réflexif/antisym/
###   transitif hérités des lemmes cardinaux : inf_egal_reflexif, inf_egal_antisymetrique_card, inf_egal_transitive, sous n∈N⇒cardinal].
###   Session dédiée « graphe-ordre » (partagée avec n°140). NB : les 3 propriétés SÉPARÉES sont déjà des théorèmes clos.
- [x] 65 trichotomie exclusive (x<y, x=y, x>y) ✅ CLOS 23 juil (ensembles_trichotomie_total_er27.py :
      trichotomie_totale ⊢ totalement_ordonne(G,E) ⇒ (∀u,v∈E)((u<v ou u=v ou v<u) et ¬(u<v et u=v) et ¬(u<v et v<u) et
      ¬(u=v et v<u)), CLOS 0 hyp, theorie=22, 2 tests 0,08s, DU PREMIER COUP. x<y:=(x,y)∈G et x≠y. EXHAUSTIVE : tiers_exclu(u=v)
      + comparabilité [conjonction_elim de totalement_ordonne] ; EXCLUSIVE : antisymétrie [de est_ordre] + symétrie égalité +
      _ex_falso. Bricks : totalement_ordonne, antisymetrie, tiers_exclu, cas, symetrie. NB : « partie vide totalement ordonnée »
      = sous-résultat vacuité NON inclus ici, trivial séparé) | E.R.27 item 4 (p.330) | T2
- [ ] 66 ⏸ CHANTIER-DÉDIÉ N bien ordonné ; partie de N a un plus grand élément ⇔ finie non vide | E.R.27 item 5 (p.330) | T3
###   MàJ tick 40 : la FORME RELATION (ordre_NN) donne l'ORDRE, mais le BON-ORDRE de ℕ = « (∀X)((X⊂ℕ et X≠∅)⇒∃ plus petit
###   élément) » = principe du plus petit élément de l'INFINI ℕ = récurrence forte/descente C61. Vérifié : prop6_bien_ordonne
###   (fini_total_est_bien_ordonne) ne couvre QUE les ENSEMBLES FINIS (ℕ est infini) ; la machinerie descente (fini_downward_thm,
###   recurrence_forte) est DANS le dossier C61 (iii_4_recurrence_c61) ⇒ test 13-18 min INTERDIT en boucle. ⇒ SESSION DÉDIÉE
###   (construction well-ordering ℕ + partie-plus-grand-⇔-finie). Sous-lemme « toute partie non vide de ℕ a un plus petit » ABSENT.
- [ ] 67 ⏸ CHANTIER 𝔉⊂𝔓(E) : plus petit (grand) élément ⇔ ⋂𝔉∈𝔉 (⋃𝔉∈𝔉) | E.R.27 item 5 fin (p.330) | T2
###   Exige ⋂𝔉 / ⋃𝔉 d'un ENSEMBLE de parties (infra ⋃/⋂-d'un-ensemble partagée avec n°95/140) + ordre-inclusion. Session dédiée.
### E.R.30-31 Limites (Résumé)  ⏸ CHANTIER (tout : infra limites projectives/inductives lim→/lim← non bâtie — cf. §7 chantier)
- [ ] 68 ⏸ CHANTIER E' ≅ lim→ E'α (fβα injectives, réunion croissante) | E.R.30 item 13 (p.333) | T3
- [ ] 69 ⏸ CHANTIER produit de deux lim inductives D=lim→(Aα×Bα)≅A×B | E.R.30 item 13 (p.333) | T4
- [ ] 70 ⏸ CHANTIER critères complets inj/surj de g=lim→ gα | E.R.30 item 13 (p.333) | T3
- [ ] 72 ⏸ CHANTIER critère d'injectivité g:E'→lim← Eα | E.R.31 item 14 (p.334) | T3

────────────────────────────────────────────────────────────────────────────────
# ARCHIVE — FAITS (closes) et PROSE (rien à dériver)

## Déjà CLOS (hors ordre — faits avant la bascule ordre-livre, tous en ordre livre valides)
- [x] 44 CS6 (E I.29 L.14-16) · 45 CS7 (E I.30 L.38-40) · 47 Def rel. fonctionnelle (E I.41 L.20-23)
- [x] 90 règle de dualité — Meta prose+preuve (E.R.19 item 7, p.322)
- [x] 58 x=y est une équivalence (E.R.23 item 2, p.326)
- [x] 73 injection canonique + Card(A)≤Card(E) (E.R.7 item 3, p.310)
- [x] 74 partie stable par f (E.R.7 item 4, p.310)
- [x] 75 X≠∅ ⇔ f⟨X⟩≠∅ (E.R.8 item 5b, p.311)
- [x] 81 bijection diagonale est_bijective(D_X,X,Δ_X) (E.R.13 item 4, p.316)
- [x] 35 convention (n p)=0 (E III.43 L.1-6)
- [x] 96 Variante 1 récurrence forte (E III.33 L.4-15) — voir section §4.3 ci-dessus
- [x] 10+11+64 C58 partie 1 (x≤y ⇔ x<y ou x=y) (E III.5 L.7-9 ; E.R.26 item 3)

## T0 — PROSE / hors théorie E / contre-exemples (RIEN à dériver, marqueurs Rem/Ex posés)
2-6 (chap IV Ex.IV-IX, E IV.26-27 : renvois TG/A), 9 (divisibilité anneau E III.4 L.13-16),
13 (« partie pleine » E II.2 L.32), 25 (partie entière quotient E III.39 L.24-26),
29 (chiffres/systèmes E III.40 L.30 - E III.41 L.21), 39 (preuve calculatoire Pascal E III.43 L.26-27),
43 (monômes E III.44 L.27-30), 49 (symbole Σ prose E I.41 L.37 - E I.42 L.4),
51 (intro chap I E I.7-13), 71 (Rem E vide même si Eα≠∅ E.R.31 item 14),
109 (Rem pas de différence a−b E III.30 L.1-3).

────────────────────────────────────────────────────────────────────────────────
## Journal d'avancement
- 23 juil : **BOUCLE CHANTIERS lancée** (Karl) — attaque les 76 chantiers un par un en ordre de levier
  A→O (chaque groupe bâtit une brique partagée). GROUPE A = ⋃/⋂-d'un-ensemble-de-parties.
- 23 juil : **[A] brique ⋃𝔊 étape 1** — nouveau `ensembles_reunion_ensemble_parties_ii4.py` :
  défs est_famille_identite/reunion_ensemble/inter_ensemble + `membre_reunion_ensemble`
  {famille_identite(f,U)} ⊢ (z∈⋃U)⇔(∃i)(i∈U et z∈i), dérivé de membre_reunion_famille +
  Leibniz S6 sous existentiel (monotonie_existe ×2) ; 2 tests verts 0,09s, theorie=22. NON clos
  (porte l'hyp famille_identite = pattern n°92/H). Prochain pas : membre_inter_ensemble (dual ∀).
- 23 juil : **[A] brique ⋃𝔊 étape 2** — membre_inter_ensemble {famille_identite(f,U)} ⊢ (z∈⋂U)⇔(∀i)(i∈U⇒z∈i),
  dual via membre_inter_famille + Leibniz S6 sous monotonie_pour_tout ; 3 tests verts 0,35s, theorie=22.
  Prochain pas : lemmes d'inclusion c⊂⋃U et ⋂U⊂c (intro/elim) pour préparer n°95.
- 23 juil : **[A] brique ⋃𝔊 étape 3** — partie_incluse_reunion {H} ⊢ (c∈U)⇒(c⊂⋃U) [témoin i=c, s5] +
  inter_incluse_partie {H} ⊢ (c∈U)⇒(⋂U⊂c) [instancie ∀ à c] ; 5 tests verts 0,07s, theorie=22.
- 23 juil : **[A] tick 4 — investigation clôture = ÉCART**. Vérifié en code : valeur_famille=app("fam",…) OPAQUE, nul
  pont vers valeur/diagonale sans 23ᵉ axiome ; existence-collectivisée reportée partout (cardinaux_inf_egal, borne_sup).
  ⇒ famille_identite INDÉCHARGEABLE en th.22 ⇒ n°95/140/67 pas CLOS 0-hyp (écart, cases non cochées + note). Brique
  4-lemmes acquise/réutilisable. **PIVOT vers GROUPE B** (converses-de-facteur + produit binaire, 0-hyp atteignable).
- 23 juil : **[B] tick 5 — investigation/mapping**. Trouvé : composée-valeur (g∘f)(x)=g(f(x)) EXISTE (composition_valeur_t)
  mais porte 3 hyps de point ⇒ à re-empaqueter en version « application » composee_valeur_app (domaines universels,
  généralisable). Toutes les briques de décharge CONFIRMÉES présentes (composee_fonctionnelle, est_application,
  valeur_dans_graphe, AXIOME_DOM/PRODUIT) ; est_un_graphe_fonctionnel==est_fonctionnel. Plan B raffiné en 5 étapes
  (marqueur). Prochain tick : bâtir composee_valeur_app + test.
- 23 juil : **[B] tick 6 — keystone composee_valeur_app CONSTRUIT** (ii_3_8/ensembles_composee_valeurs.py) :
  {est_application(F,E,Fp), est_application(G,Fp,Gp)} ⊢ (u∈E)⇒((g∘f)(u)=g(f(u))). Les 3 hyps de point de
  composition_valeur_t déchargées via helper _cut (composee_fonctionnelle pour G∘F func ; Leibniz S6 sur domF=E /
  domG=Fp ; valeur_dans_graphe + couple_dans_produit_ssi pour f(u)∈Fp). Vérifié : exactement 2 hyps (est_application×2),
  théorie=22, 2 tests + 3 frères verts 0,21s. Généralisable sur u ✓. Prochain : injective_facteur_droit (converse).
- 23 juil : **[B] tick 7 — converse injective_facteur_droit CONSTRUITE** : {est_application×2} ⊢ injective_dans(G∘F,E)⇒
  injective_dans(F,E). congruence_terme sous g + composee_valeur_app aux 2 points + injective_dans(G∘F). 2 hyps, théorie=22,
  3 tests verts 0,20s. Prochain : converse de SURJECTIVITÉ (image-de-composée f⟨g⟨·⟩⟩⊂f⟨E⟩ + f∘g surj ⇒ f surj) pour n°79.
- 23 juil : **[B] tick 8 — sous-brick image_incluse_arrivee CONSTRUIT** {est_application(F,E,B)} ⊢ f⟨E⟩⊂B (membre_image +
  couple_dans_produit_ssi + existe_elimination) ; 1 hyp, théorie=22, 4 tests verts 0,36s. Investigation converse-surj :
  toutes pièces prêtes (image_composee CLOS, image_croissante CLOS, image_incluse_arrivee, extensionnalite_appliquee).
  Prochain : surjective_facteur_gauche (f∘g surj ⇒ f surj) puis assemblage n°79.
- 23 juil : **[B] tick 9 — surjective_facteur_gauche CONSTRUITE** {est_app(f,E,Fs), est_app(g,Fs,E)} ⊢
  est_surjective(f∘g,Fs,Fs)⇒est_surjective(f,E,Fs). Double inclusion (image_composee CLOS + image_croissante +
  image_incluse_arrivee×2 + extensionnalite_appliquee + réécriture S6). 2 hyps, théorie=22, 5 tests verts 0,48s.
  LES 2 CONVERSES SONT PRÊTES (inj facteur droit + surj facteur gauche). Prochain : ASSEMBLER n°79 (CLOS 0-hyp attendu).
- 23 juil : **[B] tick 10 — ✅ n°79 CLOS → 1ʳᵉ CASE COCHÉE de la campagne CHANTIERS.** ensembles_perm_composees_er10.py :
  perm_composees_bijectives ⊢ (est_app(F,E,Ff) et est_app(G,Ff,E) et perm(g∘f,E) et perm(f∘g,Ff)) ⇒ (bij(F) et bij(G)),
  CLOS 0 hyp, theorie=22, 2 tests (7 avec briques) verts 1,05s. Assemblage 4 converses (inj_facteur_droit×2 +
  surj_facteur_gauche×2). Manifestes régénérés. **n°79 clos → passe à n°86** (f×g×h préserve inj/surj/bij ; besoin produit binaire de fonctions).
- 23 juil : **[B] tick 11 — n°86 ÉCART, pivot n°77**. produit_applications OPAQUE, produit binaire de fonctions exige
  graphe_terme≠22 (même mur famille Groupe A) ⇒ n°86 pas 0-hyp, case non cochée + note. Passe à n°77 (f⁻¹(f(X))=X ∀ et
  f(f⁻¹(Y))=Y ∀ ⇔ f bij) : 0-hyp atteignable (images/préimages, bricks image_reciproque_image_egal_si_injective +
  image_image_reciproque_egal_si_surjective existent ; converses ⇒inj/⇒surj à bâtir via singletons, idiomes n°76). ~350 l multi-tick.
- 23 juil : **[B] tick 12 — n°77 démarré, étape 1**. Nouveau ii_3_2_reciproque/ensembles_bijective_identites_er10.py :
  pont hyp_applicative_de_application {est_application(f,E,F), X⊂E} ⊢ (∀x)(x∈X⇒(x,f(x))∈f). Conclusion COÏNCIDE avec le
  _hyp_applicative privé attendu par image_reciproque_image_egal_si_injective (branchement direct). 2 hyps, théorie=22,
  2 tests verts. Trouvé : injectif_implique_reciproque_fonctionnel + reciproque_fonctionnel_ssi_injectif EXISTENT
  (niveau _graphe_injectif). Plan 5 ponts/converses dans le marqueur. Prochain : pont injective_dans↔_graphe_injectif.
- 23 juil : **[B] tick 13 — n°77 étape 2** : ponts value↔graphe injectivité. inj_dans_implique_graphe_injectif
  {est_application} ⊢ injective_dans(f,E)⇒_graphe_injectif(f) [(v,u),(z,u)∈f⇒v,z∈E + f(v)=u=f(z) via helper
  _valeur_de_couple, puis injective_dans] ; composé avec injectif_implique_reciproque_fonctionnel ⇒
  inj_dans_implique_reciproque_fonctionnel : injective_dans(f,E)⇒est_fonctionnel(f⁻¹). 1 hyp, théorie=22, 3 tests verts.
  Prochain : pont surj⇒(Y⊂F⇒Y⊂f⟨E⟩) puis assembler le sens ⇐ (bijective⇒2 identités).
- 23 juil : **[B] tick 14 — n°77 SENS ⇐ ASSEMBLÉ**. direction_bijective_vers_identites {est_application} ⊢ bijective ⇒
  ((∀X⊂E)f⁻¹⟨f⟨X⟩⟩=X et (∀Y⊂F)f⟨f⁻¹⟨Y⟩⟩=Y). ⇐-inj : inj→est_fonct(f⁻¹) [tick13] + H_app [tick12] + brick (18)-égalité ;
  ⇐-surj : surj (f⟨E⟩=F) → Y⊂f⟨E⟩ [S6] + f fonct + brick (19)-égalité. 1 hyp, théorie=22, 4 tests verts 0,47s.
  Prochain : SENS ⇒ (converse (∀X)⇒injective_dans via singletons X={a} ; (∀Y)⇒surjective via Y=F) puis l'⇔ final.
- 23 juil : **[B] tick 15 — n°77 converse SURJECTIVITÉ**. converse_Y_vers_surjective {est_application} ⊢ (∀Y⊂F)(f⟨f⁻¹⟨Y⟩⟩=Y)
  ⇒ est_surjective(f,E,F). Y=F : f⟨f⁻¹⟨F⟩⟩=F [instance + inclusion_reflexive] ; f⁻¹⟨F⟩⊂E [image_reciproque_inclus_domaine
  + domf=E] ⇒ f⟨f⁻¹⟨F⟩⟩⊂f⟨E⟩ [image_croissante] ⇒ F⊂f⟨E⟩ [S6] ; f⟨E⟩⊂F [image_incluse_arrivee] ⇒ f⟨E⟩=F [extensionnalite].
  1 hyp, théorie=22, 5 tests verts. Prochain : converse INJECTIVITÉ (singletons X={u}) puis l'⇔ final (CLOS 0-hyp).
- 23 juil : **[B] tick 16 — ✅ n°77 CLOS → 2ᵉ CASE COCHÉE.** converse_X_vers_injective (singletons {u} + couple_reciproque +
  membre_image/reciproque, DU PREMIER COUP) puis assemblage ⇔ : bijective_ssi_identites ⊢ est_application ⇒ (both⇔bijective),
  CLOS 0 hyp, theorie=22, 7 tests verts 1,02s. **GROUPE B TERMINÉ** (n°79✓ n°77✓ ; n°86 écart). Manifestes régénérés.
  **n°77 clos → GROUPE C n°92** (⋂×⋂ mêmes indices). ⚠️ risque : H=famille-terme en hyp ⇒ possible écart 0-hyp (à ré-évaluer).
- 23 juil : **[C] tick 17 — n°92 démarré, SENS ⇒**. Nouveau ii_4_2_proprietes/ensembles_produit_inter_familles_er20.py.
  DÉCISION : H-propriété (∀i)(H_i=X_i×Y_i) + ¬(I=∅) mises en ANTÉCÉDENT ⇒ 0-hyp closeable (comme est_application n°79),
  PAS écart. _dir_produit_vers_interH {hyp_produit_famille} ⊢ z∈(⋂X)×(⋂Y)⇒z∈⋂H : témoins existentiels p,q du produit
  (pas de pr₁/pr₂), membre_inter_famille ×2, _cpp_ssi (couple_dans_produit_ssi via generalize+instancie pour éviter
  collision liants p,q), Leibniz H_i=X_i×Y_i, existe_elimination ×2. 1 hyp, théorie=22. Prochain : SENS ⇐ (témoin i0 de ¬I=∅).
- 23 juil : **[C] tick 18 — ✅ n°92 CLOS → 3ᵉ CASE COCHÉE.** Sens ⇐ (_dir_interH_vers_produit, témoin i0 via alpha_existe
  z→i0) puis extensionnalité : produit_inter_familles ⊢ (¬(I=∅) et ∀i H_i=X_i×Y_i) ⇒ (⋂X)×(⋂Y)=⋂H, CLOS 0 hyp, theorie=22,
  2 tests verts. **GROUPE C TERMINÉ.** Manifestes régénérés. **n°92 clos → GROUPE D** (arith. famille §3.3). Bilan : 3 cases
  (n°79/n°77/n°92), 2 écarts (Groupe A, n°86). LEÇON réutilisable : propriétés-de-construction en ANTÉCÉDENT ⇒ 0-hyp.
- 23 juil : **[D] tick 19 — évaluation → GROUPES D/E/F déférés (chantiers d'infra), pivot n°111 (G)**. AUDIT : n°100 Def.3
  DÉJÀ FORMALISÉ (produit_cardinal/somme_cardinale existent, docs stale). Mais cluster 100-108 = 1 case pour 8 props =
  LOIS cardinales de famille (bijections) = infra lourde ; E (division) = arith. binaire dédiée ; F dépend de D. Tous NON
  tractables au fil de l'eau. Prochain tractable en PUR ASSEMBLAGE = n°111 (a^n=a, bricks tous clos). STRATÉGIE conditionnel
  d'abord (a²=a en hyp, sans Hessenberg) puis décharge Hessenberg. Marqueur → GROUPE G.
- 23 juil : **[G] tick 20 — n°111 confirmé DÉDIÉ → BOUCLE CHANTIERS ARRÊTÉE (fin normale).** Vérifié : bricks au cœur profond
  (a^b=Card(𝓕(b;a)), B_preuve n+1=n⊔{∅}, support_extension_domaine, inf_egal_phi Dir.A, eq_exposant_invariant). Sa clôture
  0-hyp IMPORTE Hessenberg (10-18 min) = test INTERDIT par la règle boucle ; version conditionnelle (a²=a en hyp) pas « FINIE ».
  ⇒ session dédiée. Tous les items restants (D/E/F/H-O + n°111) = sessions dédiées (infra/test-lourd). Frontière fil-de-l'eau
  ÉPUISÉE. **BILAN CAMPAGNE CHANTIERS : 3 cases (n°79/77/92) + audit n°100 + 2 écarts + ~15 briques.** Boucle stoppée.
- 23 juil : **Karl RELANCE (« reprends toutes les 60s ») → boucle ROUVERTE sur n°111**. Tick 21 = orientation : lu
  support_extension_domaine ({S⊆D,a₀∈A}⊢𝓕(S;A)≤𝓕(D;A)) + inf_egal_phi (⊢𝓕(B⊔C;A)≤𝓕(B;A)×𝓕(C;A), Dir.A). Bricks ENSEMBLISTES
  (inf_egal_card entre 𝓕(X;A)=applications(X,A)) ; pont a^n=Card(𝓕(n;A)) via eq_exposant_invariant = piège (ii). PLAN affiné :
  (1) borne INF a^n≤a^{n+1} [support_extension_domaine, S=n D=succ(n), n⊆succ(n), a₀∈A depuis A infini] ; (2) borne SUP a^{n+1}≤a
  [B_preuve a^{n+1}=𝓕(n⊔{∅};A) ; inf_egal_phi(A,n,{∅}) ; HR + a^1=a ; a²=a EN HYP conditionnel] ; (3) antisymétrie ⇒ a^{n+1}=a ;
  (4) recurrence_depuis(k=1). Prochain tick : borne INF.
- 23 juil : **[G] tick 22 — n°111 PONT 1 posé** (pivot : 1 pont-lemme/tick). Nouveau fichier iii_6_2_proprietes_infinis/
  ensembles_a_puissance_n_er.py. copie_gauche_inclus_somme ⊢ (n×{∅})⊆(n⊔{∅}) [inclusion_reunion_gauche via generalize+
  instancie], CLOS, theorie=22, 2 tests verts. BUG résolu : somme_disjointe utilise MARQUEURS ensemblistes ZERO=∅, UN={∅}
  (importer depuis ensembles_somme_disjointe), PAS les cardinaux Card(∅) (termes énormes). Confirmé : n°111 = ~20 ponts
  d'équipotence/inclusion (chaque étape du plan se déploie en 4-5 sous-ponts car A⊔B=(A×{0})∪(B×{1}) marqué).
  Prochain pont : support_extension_domaine(n×{∅}, n⊔{∅}, a0, A) ⇒ 𝓕(n×{∅};A)≤𝓕(n⊔{∅};A) [via pont 1 + témoin a0∈A].
- 23 juil : **[G] tick 23 — n°111 PONT 2** support_copie_gauche {a₀∈A} ⊢ 𝓕(n×{∅};A)≤𝓕(n⊔{∅};A) [support_extension_domaine
  + _cut du pont 1]. 3 tests verts, theorie=22.
- 23 juil : **[G] tick 24 — n°111 PONT 3** eq_exposant_copie_gauche ⊢ Eq(𝓕(n;A),𝓕(n×{∅};A)) [eq_copie_gauche : Eq(n,n×{∅})
  + eq_exposant_invariant appelé en NOMS puis generalize+instancie (casse sur termes complexes X,Y)]. CLOS, 4 tests verts
  6,1s, theorie=22. Prochain pont 4 : combiner ponts 2+3 (inf_egal transporté par équipotence) ⇒ 𝓕(n;A)≤𝓕(n⊔{∅};A), puis
  B_preuve (𝓕(n⊔{∅};A)=a^{n+1}) ⇒ BORNE INF a^n≤a^{n+1}. Ponts 1-3 FAITS.
- 23 juil : **[G] tick 25 — n°111 PONT 4** inf_Fn_Fsucc {a₀∈A} ⊢ 𝓕(n;A)≤𝓕(n⊔{∅};A) (BORNE INF niveau 𝓕) : Eq→≤
  [equipotence_implique_inf_egal en NOMS+generalize/instancie] du pont 3 + transitivité [inf_egal_transitive_general ∀-clos,
  instancié ×3] avec pont 2. 5 tests verts 16s, theorie=22. 𝓕(S;A)=E.applications(S,A). Prochain : ponts vers les FORMES
  CARDINALES — B_preuve donne a^{n+1}=Card(𝓕(n⊔{∅};A)) ; reste a^n=Card(𝓕(n;A)) [def exposant_cardinal via Card] ⇒ a^n≤a^{n+1}.
- 23 juil : **[G] tick 26 — n°111 PONT 5** sup_Fsucc_produit ⊢ 𝓕(n⊔{∅};A)≤𝓕(n;A)×𝓕({∅};A) = inf_egal_phi(A,n,{∅}) (Dir.A
  Prop.9, CLOS ; domaine_phi=applications(somme_disjointe(B,C),A) matche mon n⊔{∅}). 6 tests verts 20s, theorie=22.
  RECADRAGE cible : viser Card(𝓕(n⊔{∅};A))=Card(A) par récurrence (B_preuve donne Card(𝓕(succ n;A))=Card(𝓕(n⊔{∅};A)) à la
  fin). Prochain pont 6 : exposant_un_egale (Card(𝓕({∅};A))=Card(A)=a) ⇒ Card(𝓕(n;A)×𝓕({∅};A))=a^n·a, vers borne SUP a^{n+1}≤a·a=a².
- 23 juil : **[G] tick 27 — n°111 PONT 7** (approche niveau-Eq, ~12 ponts au lieu de 20). eq_produit_Fn_F1 {Eq(𝓕(n;A),A)}
  ⊢ Eq(𝓕(n;A)×𝓕({∅};A), A×A) [eq_produit_invariant en DÉFAUTS + generalize/instancie X,Y,X1,Y1 ; casse si on change les
  noms témoins F,G] + eq_applications_A (=base R{1}=Eq(𝓕({∅};A),A)). HR=hyp_recurrence=Eq(𝓕(n;A),A). 7 tests 23s, theorie=22.
  Bricks-clés : eq_applications_A, equipotent_si_cardinal_egal (Card=⇒Eq). RESTE ~6 ponts : (8) A×A≅A [Hessenberg a²=a] ;
  (9) SUP chain 𝓕(n⊔{∅};A)≤A [5+7+8] ; (10) INF chain A≤𝓕(n⊔{∅};A) [HR+4] ; (11) Cantor-Bernstein ⇒ Eq(𝓕(n⊔{∅};A),A) ;
  (12) B_preuve ⇒ R{n+1}=Eq(𝓕(succ n;A),A) ; (13) recurrence_depuis(k=1) + décharge a²=a via hessenberg_0hyp (test lent final).
- 23 juil : **[G] tick 28 — n°111 PONT 9 = BORNE SUP COMPLÈTE** sup_Fsucc_le_A {Eq(𝓕(n;A),A), Eq(A×A,A)} ⊢ 𝓕(n⊔{∅};A)≤A
  [chaîne pont 5 (≤ 𝓕(n;A)×𝓕({∅};A)) → pont 7 (≅A×A, Eq→≤) → a²=a hyp (≅A, Eq→≤), via _trans3 = inf_egal_transitive_general
  ×2]. a²=a pris comme hyp Eq(A×A,A)=hyp_carre (déchargé fin via Hessenberg). 8 tests 32s, theorie=22. NOTE : hessenberg_a_
  carre_egal_a_0hyp donne « est_infini(Card E)⇒Card E·Card E=Card E » + 2 RÉSIDUS Zorn ⇒ n°111 final portera {est_infini(A),
  H1, H2} + pont Card·Card↔Eq(A×A,A). RESTE : (10) INF A≤𝓕(n⊔{∅};A) [HR Eq→≤ + pont 4] ; (11) Cantor-Bernstein antisym ⇒
  Eq(𝓕(n⊔{∅};A),A)=cœur récurrence ; (12) B_preuve → R{n+1} ; (13) recurrence_depuis. SUP (le plus dur) FAIT.
- 23 juil : **[G] tick 29 — n°111 PONT 10 = BORNE INF COMPLÈTE** inf_A_Fsucc {Eq(𝓕(n;A),A), a₀∈A} ⊢ A≤𝓕(n⊔{∅};A)
  [HR→Eq(A,𝓕(n;A)) via equipotence_symetrique (DÉFAUTS+gen/inst) → A≤𝓕(n;A) ; _trans3 avec pont 4]. 9 tests 30s, theorie=22.
  **LES 2 BORNES SUP+INF FAITES** (sup_Fsucc_le_A {HR,a²=a} 𝓕(n⊔{∅};A)≤A ; inf_A_Fsucc {HR,a₀∈A} A≤𝓕(n⊔{∅};A)).
  Helpers ajoutés : _eq_sym_impl(t1,t2)=Eq(t1,t2)⇒Eq(t2,t1). RESTE 3 ponts : (11) inf_egal_antisymetrique_card sur SUP+INF ⇒
  Card(𝓕(n⊔{∅};A))=Card(A) ; equipotent_si_cardinal_egal ⇒ Eq(𝓕(n⊔{∅};A),A) = pas de récurrence {HR,a²=a,a₀∈A} ;
  (12) B_preuve rewrite succ n→n⊔{∅} ⇒ R{n+1}=Eq(𝓕(succ n;A),A) ; (13) recurrence_depuis(k=1) base=eq_applications_A.
- 23 juil : **[G] tick 30 — n°111 PONT 11 = CŒUR RÉCURRENCE** eq_Fsucc_A {Eq(𝓕(n;A),A), Eq(A×A,A), a₀∈A} ⊢
  Eq(𝓕(n⊔{∅};A),A) via cantor_bernstein("A","B","f","g") [DÉFAUTS+generalize/instancie dom,cod] sur SUP+INF. 10 tests 41s,
  theorie=22. RESTE 2 ponts : (12) eq_Fsuccessor_A : B_preuve(A,n)=Card(𝓕(succ n;A))=Card(𝓕(n⊔{∅};A)) [PROBE conclusion
  exposant_invariance_enonce] + pont 11 (Card=(A) via _prop1_direct_t sur Eq) + transitivité Card + equipotent_si_cardinal_egal
  ⇒ Eq(𝓕(succ n;A),A)=R{n+1} ; (13) recurrence_depuis(R,k=1) R{m}=Eq(𝓕(m;A),A), base eq_applications_A ⇒ théorème CONDITIONNEL
  {a²=a,a₀∈A,résidus C61} (∀m≥1)Eq(𝓕(m;A),A). NB test 41s (chaque pont re-run cantor_bernstein/cardinaux) — sous limite.
- 23 juil : **[G] tick 31 — n°111 PONT 12 = PAS DE RÉCURRENCE COMPLET** eq_R_np1 {Eq(𝓕(n;A),A),Eq(A×A,A),a₀∈A} ⊢
  Eq(𝓕(succ n;A),A)=R{n+1} [B_preuve(A,n)=Card(𝓕(succ n;A))=Card(𝓕(n⊔{∅};A)) clos ; pont 11 Eq→Card= via cardinal_egal_si_
  equipotent ; composer_egalites ; equipotent_si_cardinal_egal Card=⇒Eq]. Helpers _eq_impl_card/_card_impl_eq. 11 tests 61s,
  theorie=22. NB test 61s (B_preuve lourd) — sous limite mais surveiller. RESTE 1 PONT : (13) recurrence_depuis(R,k=1),
  R{m}=equipotent(applications(m,A),A) ; base eq_applications_A, pas=eq_R_np1 décurryfié (loi_deduction HR) ⇒ théorème
  CONDITIONNEL (∀m≥1)Eq(𝓕(m;A),A) sous {a²=a, a₀∈A, résidus C61}. Puis décharge Hessenberg finale (test lent isolé).
- 23 juil : **[G] tick 32 — n°111 HÉRÉDITÉ posée** heredite_111 {Eq(A×A,A), a₀∈A} ⊢ (∀n)((n entier et n≥1 et R{n})⇒R{n+1})
  [R{m}=_R111(m)=Eq(𝓕(m;A),A) ; extraire R{n} de l'antécédent, appliquer eq_R_np1 en "ndep", _cut, loi_deduction, generalisation ;
  hypothese_recurrence_depuis(R,k)=et(R{k}, hérédité gardée n entier/n≥k)]. 12 tests 75s, theorie=22. ⚠️ PIÈGE RÉSOLU :
  importer UN d'ensembles_entiers (cardinal 1=successeur(ZERO)) ÉCRASE UN de somme_disjointe (tag {∅}) ⇒ alias UN_CARD pour
  la garde n≥1, garder UN (=tag {∅}) pour somme_disjointe. RESTE : base R{1}=Eq(𝓕(UN_CARD;A),A) [pont UN_CARD↔{∅} via
  eq_exposant_invariant(Eq(UN_CARD,{∅})) + eq_applications_A] puis recurrence_depuis(R,k) : décharger hypothese_recurrence_depuis
  =conjonction_intro(base, heredite_111) + est_cardinal(UN_CARD) [successeur_est_un_cardinal] + predecesseur_fini_universel (résidu C61).
- 23 juil : **[G] tick 33 — n°111 BASE R{1} posée** base_111 ⊢ Eq(𝓕(1;A),A) CLOS [eq_un_singleton : Eq(1,{∅}) →
  eq_exposant_invariant ⇒ Eq(𝓕(1;A),𝓕({∅};A)) ; eq_applications_A : Eq(𝓕({∅};A),A) ; chaînés par Card via _eq_impl_card/
  composer_egalites/_card_impl_eq]. 13 tests 92s, theorie=22. BASE+HÉRÉDITÉ PRÊTES. RESTE 1 : assemblage final
  recurrence_depuis(_R111, kdep) [renvoie {hypothese_recurrence_depuis(_R111,kdep), est_cardinal(kdep), pred_univ} ⊢
  (∀n)((n entier et n≥kdep)⇒R{n})] : généraliser kdep + instancie UN_CARD, décharger hyp_rec_depuis via conjonction_intro(
  base_111, heredite_111), est_cardinal(UN_CARD) via successeur_est_un_cardinal(ZERO) ⇒ théorème CONDITIONNEL {a²=a,a₀∈A,pred_univ}.
  ⚠️ test file 92s (13 lemmes cardinaux lourds re-run) — sous limite mais après clôture TRIMMER (marquer slow ou réduire).
- 24 juil : **[G] tick 34 — n°111 FERMÉ ✅ (théorème conditionnel, case cochée)**. `a_puissance_n_egale_a` ⊢
  {Eq(A×A,A), a₀∈A, predecesseur_fini_universel} (∀n)((n entier et n≥1)⇒Eq(𝓕(n;A),A)). ASSEMBLAGE FINAL :
  recurrence_depuis(_R111, k="kdep") [3 hyps {hyp_rec_depuis(kdep), est_cardinal(kdep), pfu}] ; décharge des 2
  gardes k-dépendantes DANS la conclusion (loi_deduction ×2) → generalisation("kdep") [pfu kdep-free] → instancie(UN_CARD)
  → modus_ponens(conjonction_intro(base_111, heredite_111)) [décharge hyp_rec_depuis(1), hyps {a²=a,a₀∈A}] →
  modus_ponens(un_est_un_cardinal()) [décharge est_cardinal(1), clos]. CONCL == conclusion_recurrence_depuis(_R111,UN_CARD).
  14 tests VERTS (exit 0 ; 426s sous contention CPU concurrente, ~92s isolé), theorie=22. Manifestes régénérés, box cochée.
  LIVRABLE ACCEPTÉ par la consigne (« conditionnel = livrable, version 0-hyp = test lent isolé reporté »). Les 3 résidus
  se déchargent hors-boucle : a²=a→hessenberg_a_carre_egal_a_0hyp (10-18 min), a₀∈A→A infini non vide, pfu→pred_fini_univ_preuve.
  PIÈGE RÉSOLU tick 34 : base R{1} sur l'exposant ENTIER 1 (=successeur(0)) ≠ exposant {∅} (tag somme_disjointe) ⇒ pont
  eq_un_singleton Eq(1,{∅}) OBLIGATOIRE ; un_est_un_cardinal().conclusion == est_cardinal(UN_CARD) (vérifié).
- 24 juil : **[D] tick 35 — RECLASSEMENT MAJEUR : Groupe D n'est PAS un écart d'axiome, c'est une sous-campagne TRACTABLE.**
  AUDIT grep+livre (§III.3.3 V7) : (1) **n°100 Def.3 DÉJÀ FORMALISÉ** — somme_cardinale/produit_cardinal de FAMILLE
  (Card(somme_famille)/Card(produit_famille)) existent [ensembles_cardinaux.py:125-137, @livre Def.3 E III.25]. (2) Toute
  l'infra CONSTRUCTION+caractérisation de familles est CLOSE : graphe_terme (C54), graphe_terme_valeur {u∈A}⊢F(u)=T[u],
  membre_graphe_terme, membre_produit_famille ⊢(F∈∏)⇔corps, produit_fonctionnel/domaine/projection/extensionnalite_produit,
  produit_props_fonctoriel, famille_constante. ⇒ le « mur valeur_famille » du Groupe A/n°86 était SUR-généralisé : il ne
  bloque QUE les familles ABSTRAITES ou l'identité-sur-parties, PAS les familles construites par graphe_terme. CONSÉQUENCE :
  Prop.4/5 (n°101-108) sont des THÉORÈMES tractables (assemblage sur infra existante), sous-campagne multi-tick façon n°111.
  PROCHAINE BRIQUE = Prop.4 : Card(produit_famille(E))=∏Card(E_ι) & Card(somme_famille(E))=∑Card(E_ι) via fonctorialité
  produit/somme sous famille de bijections E_ι≅Card(E_ι). Fichier iii_3_6_familles/ensembles_prop4_famille_cardinaux.py (à créer).
  ⚠️ CORRIGE le verdict « frontière définitivement épuisée » du tick 34 : D est un vrai chantier ACTIONNABLE au fil de l'eau.
- 24 juil : **[D] tick 36 — Prop.4 briques posées + VERROU-τ identifié sur la famille des cardinaux.** Créé
  iii_3_6_familles/ensembles_prop4_famille_cardinaux.py : ÉNONCÉS FIDÈLES posés (enonce_prop4_produit
  Card(∏E)=∏Card E, enonce_prop4_somme Card(∑E)=∑Card E, _famille_cardinaux A=graphe_terme(I,Card(E_ι),ι)), 3 tests
  verts, theorie=22. ⚠️ BRIQUE 1 (carte_cardinaux_valeur : {ι₀∈I}⊢A(ι₀)=Card E_{ι₀}) BLOQUÉE par le VERROU-τ (vérifié) :
  le terme-valeur Card(E_ι)=τ_Z(∃F…) unfold en liants {F,Z,u,up,v,y,z} qui COLLISIONNENT les liants internes de
  graphe_terme_valeur (valeur_caracterisation u/up/v ; graphe_terme_couple_dans x/y) ⇒ « modus ponens : mineure ≠
  antécédent », ÉCHOUE MÊME AVEC y frais (collision profonde sur u/up/v/F non paramétrables). Fonction lève NotImplementedError
  (documenté). ⇒ Prop.4 (produit ET somme) hérite du verrou ; la fonctorialité (famille de bijections τ-valuées) le rencontre
  A FORTIORI. CONTOURNEMENT possible (technique verrou-τ mémoire) = prouver A(ι)=Card E_ι via membre_graphe_terme(a,t,u,v,x,y)
  [liants u,v,x,y PARAMÉTRABLES → choisir frais disjoints de {F,Z,u,up,v,y,z}] + extraction valeur manuelle à liants frais,
  PAS graphe_terme_valeur (liants hardcodés). = travail DÉLICAT multi-tick (session dédiée). **BILAN D : pas un écart d'axiome,
  mais bloqué au fil de l'eau par verrou-τ sur les familles Card-valuées / bij-valuées ⇒ CHANTIER DÉDIÉ (comme E/division).**
- 24 juil : **[D] tick 37 — contournement verrou-τ TENTÉ, CONFIRMÉ irréductible au fil de l'eau ⇒ D = SESSION DÉDIÉE, PIVOT.**
  Probes : membre_graphe_terme(I, Card(E_ι), u,v,x,y FRAIS) FONCTIONNE (clos) ✓ ; MAIS graphe_terme_fonctionnel ÉCHOUE
  (« modus ponens : mineure ≠ antécédent ») car il hardcode ses liants u,v,vp="u","v","z" qui collisionnent {u,v,z}⊂Card.
  RACINE IRRÉDUCTIBLE : est_fonctionnel(F) est DÉFINI avec les liants canoniques FIXES (∀u)(∀v)(∀z)(…) [abrege.py:139] ;
  or Card(E_ι) contient exactement les liants bound {u,v,z}. Prouver la fonctionnalité d'un graphe_terme Card-valué SUBSTITUE
  l'indice dans Card ⇒ capture-renommage qui casse la machine ; et rebâtir à liants frais BUTE sur les liants REQUIS {u,v,z}
  de est_fonctionnel (α-variants ≠ dans le noyau). ⇒ verrou-τ profond, kernel-level = session dédiée (même classe que II.5
  Prop.2, cf. mémoire bourbaki-verrou-tau-contournement). **D CONFIRMÉ DÉDIÉ.** PIVOT (pré-engagé) : survey L/M pour un
  pur-assemblage façon n°111 (voir tick 38).
- 24 juil : **[survey L/M] tick 37 (suite) — L ET M CONFIRMÉS BLOQUÉS ⇒ frontière pur-assemblage ÉPUISÉE ; keystone = Th.1.**
  L (quotient E/R n°57/59-62) : infra partition/recouvrement + iso-quotient ABSENTE (pas de est_partition prouvé) = session
  dédiée équivalence. M (n°63 « N ordonné ») : exige le SET N (collectivisation des cardinaux finis = Th.1 §III.6.1) —
  GREP CONFIRME N-comme-ensemble ABSENT ; est_ordre(G,E) existe mais G_N (graphe-ordre sur N) inconstructible sans N. Idem
  n°66/8. **CONSTAT VÉRIFIÉ (pas pessimisme tick-20) : après n°111, TOUT le restant est dédié — D(verrou-τ), E/F(C61 lourd),
  H/I/M(Th.1 absent), J/K(famille=verrou-τ), L(quotient infra), N/O(segments/limites infra).** KEYSTONE le + haut levier =
  **Th.1 (collectivisation de N, §III.6.1)** : débloque H(110,115-120)+M(63,66,8)+I(nœthérien) ≈ 13 items.
  ⚠️⚠️ **CORRECTION tick 37 (leçon n°111 : docs/mon grep STALE) — Th.1 EST FAIT, N EXISTE À theorie==22 !** Mon grep
  « N-as-set absent » utilisait de MAUVAIS noms. RÉALITÉ (iii_6_1_n_objet_existence/) : `N_existe` prouve coll(x,Fini x)
  INCONDITIONNELLEMENT 0-hyp (Th.1) ; `ensemble_NN()` = τy((∀x)(x∈y⇔Fini x)) = ℕ (terme CLOS) ; `appartenance_NN()` ⊢
  (∀z)(z∈NN⇔Fini z) [CLOS 0-hyp theorie==22] ; `zero_dans_NN` ⊢ 0∈NN ; `NN_clos_successeur` ⊢ (∀n)(n∈NN⇒succ n∈NN).
  AUCUN axiome neuf (docstring ensembles_ensemble_NN.py L.40-42). ⚠️ COÛT : N_existe ~5 min (τ-cardinaux imbriqués, lru_cached).
  ⇒ **H(110,115-120)/M(63,66,8)/I NE SONT PAS bloqués sur l'existence de N.** Reste à vérifier par item la construction
  graphe-ordre (relation→graphe, risque verrou-τ sur inf_egal_card) + le coût test. PIVOT loop tick 38 : reassess n°63 (N ordonné)
  avec NN dispo — cible la + simple d'abord (p.ex. une propriété de NN, ou est_ordre(G_N,NN) si le graphe se construit sans verrou).
- 24 juil : **[survey M/H avec N dispo] tick 38 — M(n°63) ET H(n°110) confirmés DÉDIÉS (gaps foundational distincts). KEYSTONE = séparation bornée.**
  n°63 (« N ordonné ») exige est_ordre(G_N,NN) avec G_N={(x,y)∈NN×NN:x≤y} un GRAPHE concret. GREP : (1) AUCUN outil de
  SÉPARATION/compréhension bornée {x∈E:P} avec caractérisation d'appartenance ; (2) est_ordre n'a JAMAIS été prouvé sur un
  graphe CONCRET (toutes les preuves sont sur G abstrait via N.assume). ⇒ n°63/66/8 butent sur le « gap relation→graphe »
  (même mur que n°140, Groupe A). n°110 (« ℵ₀≤a ») : ENONCE posé [aleph0_inf_egal_cardinal_infini_enonce], N dispo, mais le
  passage « ∀n n≤a ⇒ Card(N)≤a » exige l'ARITHMÉTIQUE CARDINALE INFINIE (injection N↪a par récursion/limite) = ABSENTE. ⇒ H dédié.
  **BILAN VÉRIFIÉ (ticks 35-38, 4 pivots, 4 gaps distincts) : la frontière PUR-ASSEMBLAGE est ÉPUISÉE après n°111.** Chaque item
  restant bute sur UNE brique foundational-keystone : (1) **SÉPARATION BORNÉE** (R⟹x∈A ensemble ⟹ {x∈A:R} existe+caractérisé) →
  débloque M(63/66/8), n°140, tout sous-ensemble concret ; (2) VERROU-τ contournement → D/J/K ; (3) ARITH CARDINALE INFINIE
  (N↪a) → H ; (4) QUOTIENT/PARTITION infra → L ; (5) ARITH BINAIRE C61 lourde → E/F. **Toutes = chantiers dédiés multi-session.**
  ⇒ La boucle 60s « chasse pur-assemblage » n'a plus de cible. PIVOT : viser le KEYSTONE le + haut levier = SÉPARATION BORNÉE
  (Bourbaki schéma S8 sélection-réunion) ; tick 39 = assess si dérivable en theorie==22 (axiome sous-jacent présent ?) puis construire.
- 24 juil : **[S8/séparation] tick 38 (suite) — la compréhension bornée MARCHE à theorie==22 (témoin explicite). n°63 TRACTABLE mais DÉDIÉ.**
  `appartenance_collectivisante` ⊢ Coll_x(x∈y) CLOS 0-hyp SANS schéma S8 (témoin Y:=y, via S5) ; `N_existe` a bâti NN en
  bornant Fini(x) par l'intervalle [0,a] (`intervalle_entiers`, « légitimé S8+A1 »), le tout à theorie==22. ⇒ la compréhension
  {x∈E:R} se fait en EXHIBANT le témoin (pas de schéma S8 axiomatique dans les 22). **CONSÉQUENCE : n°63 EST tractable** — G_N=
  {(x,y)∈NN×NN:x≤y} se construit comme une compréhension S8 sur le pattern intervalle_entiers/N_existe (NN×NN est un ensemble),
  puis est_ordre(G_N,NN). MAIS c'est une construction ~200 lignes + test ~5 min (N_existe) = **CHANTIER DÉDIÉ multi-tick, PAS
  pur-assemblage**. DÉCISION : la boucle passe en mode GRIND DÉDIÉ sur n°63 (brique par brique, comme n°111 mais + lourd).
  Tick 39 = brique 1 : définir le terme G_N (app + pattern) et sa caractérisation d'appartenance z∈G_N⇔(z∈NN×NN et pr₁z≤pr₂z),
  en calquant EXACTEMENT ensembles_N_collectivise (le modèle de compréhension bornée le + proche). ⚠️ tests FICHIER SEUL, ~5min.
- 24 juil : **[M] tick 39 — n°63 (ℕ ordonné par ≤) CONSTRUIT via la FORME RELATION (pas graphe !) — encore la leçon docs-stale.**
  DÉCOUVERTE : le graphe concret G_N n'est PAS nécessaire. `diagonale_membre` (le seul est_ordre sur graphe concret) s'appuie sur
  AXIOME_DIAGONALE (compté dans les 22) ⇒ un graphe-ordre G_N exigerait un axiome neuf (casse 22) OU une preuve coll ~200l.
  MAIS Bourbaki définit l'ordre AUSSI comme une RELATION (E.III.1.1) : `est_relation_ordre_dans(R,E)` prend un PRÉDICAT R, pas un
  graphe. ⇒ n°63 = est_relation_ordre_dans(R_N, ℕ) avec R_N(x,y)=(x∈ℕ et y∈ℕ et x≤y) [garde REQUISE pour la fidélité :
  est_reflexive_dans_ordre exige R{x,x}⇔x∈ℕ]. PUR ASSEMBLAGE sur lemmes clos : inf_egal_reflexif (X≤X inconditionnel),
  inf_egal_transitive_general (∀-clos), inf_egal_antisymetrique_card (sur cardinaux), appartenance_NN_instanciee (x∈ℕ⇒Fini x) +
  fini_implique_cardinal (Fini⇒cardinal). Fichier iii_6_1_n_objet_existence/ensembles_ordre_NN.py : 4 composantes (transitif,
  antisym, reflexif_implicite, reflexive_dans) + assemblage ordre_NN(). 3 composantes rapides PROBÉES clos/0-hyp/slot-match/
  theorie==22 ✓ ; test complet (antisym touche N_existe ~5min) EN COURS. ⚠️ OVERTURN du verdict tick 38 « M bloqué gap-graphe » :
  la forme relation contourne le graphe. Si test vert ⇒ COCHER n°63, puis viser n°66/8 (même forme relation + bon-ordre).
- 24 juil : **[M] tick 39 (fin) — n°63 ✅ FERMÉ.** test VERT 197s (1 passed), ordre_NN ⊢ est_relation_ordre_dans(R_N,ℕ) CLOS
  0-hyp theorie==22. Case cochée, @livre Demo posé, manifestes régénérés. **2e théorème fermé de la session (après n°111).**
  LEÇON CONFIRMÉE (3e fois : n°111, N-existe, n°63) : re-vérifier EN CODE tout « bloqué » présumé — la forme relation d'ordre
  (est_relation_ordre_dans, prédicat gardé) débloque l'ordre sur ℕ SANS graphe ni axiome neuf. Marqueur → n°66 (ℕ bien ordonné :
  toute partie non vide a un plus petit élément ; partie majorée a un plus grand élément ⇔ finie non vide) — MAIS n°66 exige
  est_bien_ordonne(R,E) = ordre + (∀X⊂E non vide ∃ plus petit) : le « bon ordre » sur ℕ = récurrence/descente C61 ⇒ PLUS lourd,
  possiblement dossier C61 interdit. À ÉVALUER tick 40 : n°66 tractable en forme relation ? sinon n°8, sinon retour survey.
- 24 juil : **[§6.4] tick 41 — SURVEY dénombrables n°115-120 → tous BLOQUÉS (arith cardinale infinie / récursion-énumération, REPORTÉ).**
  est_denombrable(E)=(∃Y)(Y⊂ℕ et Eq(E,Y)) [Déf.3, clos]. n°116 (tout infini dénombrable ≅ ℕ) exige « sous-ensemble infini de ℕ ≅ ℕ »
  = énumération par récursion (REPORTÉ). n°115/117/118/120 = arithmétique cardinale infinie (ℵ₀·ℵ₀=ℵ₀, ⋃ suite, ∏ fini) toutes
  marquées REPORTÉ dans ensembles_infinis*.py. CLOS déjà présents (aleph0_est_cardinal/infini, NN_denombrable, dedekind_aleph0,
  NN_est_infini_ensemble) = socle, mais les Prop.1-5 §6.4 butent sur l'arith cardinale infinie absente. ⇒ §6.4 = chantier dédié.
  **BILAN ticks 35-41 : 2 théorèmes FERMÉS (n°111, n°63) ; frontière fil-de-l'eau VÉRIFIÉE épuisée** — restant bloqué sur un
  petit socle foundational : verrou-τ (D,J,K), arith cardinale infinie/récursion (H,§6.4,I), C61-lourd (E,F,66), quotient (L),
  ⋃/⋂-set (A,67), segments/limites (N,O). PROCHAIN (tick 42) : DERNIER angle cheap-win = AUDIT des théorèmes DÉJÀ CLOS non crédités
  (pattern n°100/n°65 « déjà fait, docs stale ») dans §6.1-6.4 vs items non cochés ; si rien ⇒ recommander session dédiée à Karl.
- 24 juil : **[M] tick 40 — n°66 ÉVALUÉ → DÉDIÉ (bon-ordre ℕ infini = C61).** Vérifié : ordre_NN donne l'ordre (forme relation),
  mais le bon-ordre = « toute partie non vide de ℕ a un plus petit élément » sur l'INFINI ℕ = récurrence forte/descente ;
  prop6_bien_ordonne (fini_total_est_bien_ordonne) ne couvre QUE le FINI ; la machinerie (fini_downward_thm, recurrence_forte)
  est DANS le dossier C61 (test interdit). Sous-lemme least-element-ℕ ABSENT. ⇒ n°66 consigné dédié. n°8 = pas un item ouvert ;
  n°67 déjà dédié (⋃/⋂-d'un-ensemble). **Zone ordre-sur-ℕ (E.R.26-27) MINÉE : n°63✅ n°65✅ ; 66/67 dédiés.** Prochain (tick 41) :
  survey §6.4 dénombrables (n°115-120) avec le lens « N existe », chercher un pur-assemblage sur lemmes clos.
- 17 juil : classification 142 entrées + T1 TERMINÉ 9/9 (C58 p.1, CS6, CS7, Def rel.
  fonctionnelle, x=y équiv, injection canonique, partie stable, image non vide, dualité Meta).
- 17 juil : n°81 bijection diagonale CLOS (leçon α-@1 graphe_terme). n°35 convention binomiale CLOS.
- 23 juil : **n°96 variante 1 récurrence FORTE CLOS** (recurrence_forte : S{0} vacuité +
  hérédité [successeur_ordre_strict+C58+cas()] + C61 [principe_recurrence_preuve] + retour R ;
  ⊢ (∀n)(n entier⇒R{n}) sous 2 résidus honnêtes {H, predecesseur_fini_universel} ; 3 tests verts).
- 23 juil : **BASCULE ORDRE LIVRE** (décision Karl) — le tableau est re-trié chapitre→page E→ligne ;
  la boucle prend désormais la 1ʳᵉ case non cochée en ordre livre, plus par difficulté (fidélité :
  ne jamais utiliser un objet postérieur à la démo dans le livre).
- 23 juil : **n°46 C45 réciproque CLOS** (1ʳᵉ démo en ordre livre) — c45_arriere, miroir du sens
  direct c45_avant, schéma métathéorique (critère chap. I = fonction Python vérifiable, pas un
  Theoreme schématique) ; d'un thm CLOS ⊢R⇒(x=T) produit ⊢relation_univoque_x(R) clos ; 8 tests verts.
- 23 juil : **n°48 C46 CLOS** (2 sens) — nouveau fichier i_5_3_relations_fonctionnelles_c46_c47.py :
  c46_avant (⊢«R fonctionnelle» → ⊢R⇔(x=τx(R)), via C45 direct + S6 sur le témoin) et c46_arriere
  (⊢R⇔(x=T) → ⊢«R fonctionnelle», via c45_arriere pour l'univocité + T=T/S5 pour (∃x)R) ;
  schémas métathéoriques clos ; ⇔ = conjonction_intro(fwd,back) ; 22 tests §I.5 verts, theorie=22.
- 23 juil : **n°50 C47 CLOS** (c47_equivalence, même fichier) — ⊢ S{τx(R)} ⇔ (∃x)(R et S) sous
  «R fonctionnelle» ; route noyau équivalente aux C46+C43+C33 du livre (2 sens directs : témoin+S5 ;
  C46+Leibniz+existe_elimination), notée comme écart de route ; 24 tests §I.5 verts, theorie=22.
  **CHAPITRE I terminé côté critères fonctionnels (C45↔, C46, C47).**
- 23 juil : **CLAUSE CHANTIERS ajoutée.** n°12 (Θ≅F/R) inspecté → VRAI CHANTIER : la bijection
  Θ→F/R et le théorème général §6.9 E II.47 ne sont PAS formalisés (host quotient_complements.py
  l.361-368 le dit) ; le dériver exige de bâtir Θ + graphe de f + injectivité + E_R=F/R. Déféré
  (session dédiée), comme n°7 (ordre quotient) et n°8 (préordre-graphe) — même famille infra.
  La boucle avance au 1er item TRACTABLE en ordre livre. PROCHAINE : n°10 C58 partie 2 (E III.5,
  miroir de la partie 1 déjà close).
- 23 juil : **n°10 C58 partie 2 CLOS** — c58_trans_gauche/droite dans le fichier C58 existant ;
  route livre exacte (transitivité ⇒ x≤z ; antisymétrie cardinale ⇒ x≠z par contraposée) ; clos
  modulo gardes est_cardinal (résidus honnêtes) ; 5 tests §III.1.4, theorie=22.
  PROCHAINE : n°134 (Prop.3 §2.1, E III.16) — à évaluer (probable infra bon-ordre/segments →
  possiblement ⏸ chantier ; le tick lira la page et tranchera).
- 23 juil : **cluster §2.1-2.3 (134/135/136/137/138) DÉFÉRÉ chantier** — page E III.16 relue :
  Prop.3 est une proposition majeure (ordre unique sur ⋃ de bien-ordonnés 2-à-2 segments) dont
  la démo passe par le Lemme 1, et le host lemme1_reunion_filtrante.py déclare lui-même sa
  dérivation « NON FAITE (chantier) ». Cluster segment/filtrante à bâtir en session dédiée.
  PROCHAINE : n°139 (Cor.1 Th.2 Zorn m≥a, E III.21) — à évaluer, Zorn Th.2 étant CLOS.
- 23 juil : **n°139 Cor.1 Th.2 Zorn CLOS** — belle démo T3 (~200 lignes, ensembles_zorn_corollaires.py) :
  découverte-clé `est_ordre(G,E)` = réflexivité SUR E + antisym/trans INDÉPENDANTES du support ⇒ on
  applique Zorn (clos) au MÊME graphe G sur F={x∈E|(a,x)∈G}, sans construire d'ordre induit. F inductif
  (chaîne de F = chaîne de E ; majorant m∈E est ≥a via un élément ou a si vide ⇒ m∈F), transfert de
  maximalité. Clos sous les 2 seules hyps honnêtes {est_inductif(G,E), a∈E}, theorie=22, 2 tests.
  Pièges levés : inclusion_transitive renomme le binder (⇒ C⊂E construit à la main au binder 'z') ;
  s5 sur un témoin figé produit un ∃ vide (⇒ R générique `majorant(G,C,m,F)` + témoin a).
  PROCHAINE : n°140 (Cor.2 Th.2, famille close par réunion/inter de chaînes ⇒ max/min, E III.21).
- 23 juil : **n°140 (Zorn Cor.2) + clusters §2-fin (141/142) et §3.3-famille (100-108) DÉFÉRÉS.**
  n°140 DÉRIVABLE mais nouvelle infra (graphe-ordre-inclusion sur une famille + union ⋃𝔊 d'un
  ensemble de parties + dual) ~300 lignes — distinct de Cor.1 qui réutilisait G ; les briques
  inclusion_* donnent la RELATION ⊂, pas le GRAPHE. 141/142 = cluster §2 segments/Lemme 4 (pas de
  host). 100-108 = formes FAMILLE, « dossiers familles/inégalités VIDES » (CAMPAGNE_TROUS). Tous
  déférés session dédiée (nouvelle infra à bâtir, pas des démos-de-tick). La boucle saute au
  prochain tractable. PROCHAINE : n°95 (Cor. Th.2 Cantor, E III.30) — Cantor Th.2 étant CLOS.
- 23 juil : **n°95 (Cor Cantor) DÉFÉRÉ** — page E III.30 relue : la démo pose S=⋃_{X∈U}X, donc exige
  la MÊME brique ⋃-d'un-ensemble que n°140/familles. 🔑 CONSTAT : ⋃-d'un-ensemble est un prérequis
  PARTAGÉ (n°95 + n°140 + arithmétique famille §3.3) → forte valeur à le bâtir une fois en session
  infra dédiée. La boucle continue sur les items SANS ce prérequis. PROCHAINE : n°97 (variante 2
  récurrence « à partir de k », E III.33 — tractable, miroir de la variante 1 n°96 déjà close).
- 23 juil : **n°97 variante 2 « à partir de k » CLOS** (~180 l, ensembles_recurrence_depuis_preuve.py) :
  S{n}=(k≤n)⇒R{n}, S{0} par antisymétrie (k≤0⇒k=0), hérédité par disjonction (k≤n ⇒ prémisse-depuis ;
  ¬(k≤n)+k≤n+1 ⇒ k=n+1 via ¬(k<n+1)[successeur_ordre_strict]+C58), C61+décurryfiage ; 3 hyps honnêtes.
  Piège : c58_ordre_strict ne prend que des NOMS ⇒ generalise+instancie pour l'appliquer à k≤n+1 (terme
  composé). PROCHAINE : n°98 (variante 3 « limitée à [a,b] », E III.33, même patron).
- 23 juil : **n°98 variante 3 « limitée à [a,b] » CLOS** (~230 l, ensembles_recurrence_intervalle_preuve.py) —
  miroir de la variante 2 + borne supérieure b : S{n}=(a≤n et n≤b)⇒R{n}, hérédité tire n≤b et n<b de
  n+1≤b (successeur_ordre + transitivité ; succ_pas_inf_egal pour n≠b), reste identique. Dérivée du
  PREMIER COUP (le patron variante 2 se transpose). PROCHAINE : n°99 (variante 4 « descendante »,
  E III.33-34 — descend de b, démo différente).
- 23 juil : **n°99 variante 4 « récurrence descendante » CLOS** (~150 l, ensembles_recurrence_descendante_preuve.py) —
  RÉDUITE à la variante 3 EXACTEMENT comme le livre (E III.33 L.34 - E III.34 L.7). pas_ascendant_non_R =
  contraposée du pas descendant : de R{m+1}⇒R{m} on tire ¬R{m}⇒¬R{m+1} (contraposition sous les gardes).
  Pour n∈[a,b] fixé, par l'absurde : ¬R{n} + ce pas ascendant + recurrence_intervalle(¬R) sur [n,b] donnent
  ¬R{b} en m=b, contredisant R{b} ⇒ R{n} (tiers exclu). ⊢ (∀n)((n entier et a≤n≤b)⇒R{n}) sous 3 hyps
  {hyp descendante, est_fini b, pred universel}. 2 tests verts (201s), theorie=22. **PIÈGE (résolu) :**
  generalise+instancie sur recurrence_intervalle α-renomme les liants internes ⇒ le MP de décharge échoue
  (antécédent α-équivalent mais ≠ structurel). FIX propre = appeler recurrence_intervalle DIRECTEMENT à la
  base voulue (a="nfin", b), puis décharger H_int et card(n) par _cut = MP∘loi_deduction. **§4.3 variantes
  de récurrence (96/97/98/99) TOUTES CLOSES.** PROCHAINE : §5.6-5.7 division euclidienne = ⏸ CHANTIER (déféré
  session dédiée, cf. mémoire) → le prochain tractable en ordre livre est §5.8 combinatoire (n°30+), à
  assesser au réveil (infra injections/factorielle/binomial requise pour certains).
- 23 juil : **§5.8 combinatoire (n°30-42) marqué ⏸ CHANTIER en bloc** après relecture code : les ÉNONCÉS sont
  déjà formalisés (ensembles_combinatoire_enonces.py, forme multiplicative, décomptes opaques) mais leurs
  DÉMOS exigent (a) le principe des bergers PLEIN — seul le cœur binaire est clos (ensembles_prop9_bergers_iii5.py),
  la forme pleine demande l'arith. de famille indexée §3.3 (Prop 5b + Prop 6 Cor 2), bloquée sur ⋃-d'un-ensemble ;
  (b) le coefficient binomial DÉFINI comme Card{X⊂E:Card X=p} (opaque ici) pour n°34/38. Cluster déféré.
  **CONSTAT-CLÉ pour §6 :** Th.2 Hessenberg (a·a=a, a infini) EST DÉJÀ CLOS (hessenberg_a_carre_egal_a_0hyp,
  conclusion E-seule, 2 résidus Zorn) ⇒ ses corollaires BINAIRES sont tractables sans infra famille : cibles
  n°114 (ab=a+b=sup(a,b)) et n°111 (a^n=a, exposant fini≥1, par récurrence sur n depuis a·a=a). PROCHAINE :
  §6 n°110+ — assesser d'abord si n°110 (Lemme 1 ⊇≅N) est déjà interne à Hessenberg, sinon viser n°114/n°111.
- 23 juil : **triage §6.3 corollaires de Th.2 (recherche d'infra exhaustive, 0 démo close ce tour — frontière saturée
  ATTEINTE comme prévu)**. Constats : n°110 (Lemme 1, ℵ₀≤a) = ⏸ CHANTIER, le code (aleph0_inf_egal_cardinal_infini_enonce)
  dit explicitement REPORTÉ (collectivisation N + entier≤a + arith. cardinale infinie). n°112/113 = ⏸ CHANTIER (∏/Σ
  FAMILLE, arith. famille indexée §3.3). n°114 (ab=a+b=sup) = ⏸ CHANTIER : partie produit tractable binaire mais énoncé
  fidèle exige sup(a,b) DÉFINI (absent) + « 2≤b » infini (reporté, cf. n°110) pour la partie somme. **SEUL n°111 (a^n=a)
  est tractable** : recherche a CONFIRMÉ que TOUS ses bricks sont clos — a^1=a (exposant_un_egale), a^{n+1}=a^{n⊔1}
  (B_preuve, pont exposant-successeur via keystone eq_exposant_invariant), Prop.9 a^{X⊔Y}=a^X·a^Y (prop9_close), a²=a
  (hessenberg_0hyp), récurrence-depuis (variante 2). Rien à bâtir. C'est une VRAIE dérivation lourde (Hessenberg ⇒ test
  10-18 min ; plombage exposant/produit/cardinal délicat, risque de spirale de debug à chaque test lourd). D'où la
  stratégie CONDITIONNEL-D'ABORD : prouver (a²=a)⇒(a^n=a) sans importer Hessenberg (test rapide, valide tout le
  plombage), PUIS décharger a²=a via hessenberg_0hyp (un seul test lourd final). PROCHAINE : dériver n°111 (contexte frais).
- 23 juil : **n°111 reclassé ⏸ CHANTIER-DÉRIVATION après lecture fine des signatures.** CORRECTION IMPORTANTE : ma
  supposition « Prop.9 close » était FAUSSE — ensembles_prop9_close n'a que la Direction A (inf_egal_phi : a^{b+c} ≤
  a^b·a^c) ; l'égalité (Direction B, ψ-injectivité) est REPORTÉE (direction_B_REPORTE lève NotImplementedError). [Leçon
  bourbaki-audit-verifier-en-code confirmée : lire le CODE, pas le header/docstring qui décrit les PARTIES closes.] La
  récurrence par égalité a^{n+1}=a^n·a est donc impossible ; contournement Cantor-Bernstein (borne sup via Dir.A + borne
  inf via support_extension_domaine + antisymétrie) — bricks tous clos mais dérivation de plusieurs centaines de lignes
  avec ponts entier↔ensemble multiples (récurrence sur entiers UN/DEUX vs exposant {∅}) + témoin a0∈A + Hessenberg
  (test 10-18 min). Même profil que division euclidienne ⇒ session dédiée. Plan corrigé COMPLET consigné à l'entrée n°111.
  **FRONTIÈRE SATURÉE confirmée** (3 tours de triage §5.6→§6.3 : tout est chantier ou dérivation-lourde-dédiée). Stratégie
  boucle : fast-trier §6.4→§7→IV pour atteindre les items LÉGERS du Résumé (E.R. T2, indépendants de §6). PROCHAINE : §6.4 n°115.
- 23 juil : **§6.5 + §7 + IV batch-triés ⏸ CHANTIER** (n°121-124 récursion/choix sur suites ; §7 limites proj/ind
  + Zorn non bâtie ; IV CST22 produit-famille) → premier item LÉGER en ordre livre = **Résumé n°76** (surjection ⇔
  préimage non vide, E.R.8). Infra CONFIRMÉE présente (est_application, est_surjective=image=F, membre_image,
  membre_image_reciproque, couple_reciproque, non_vide_ssi_element, singleton, image_reciproque_inclus_domaine,
  extensionnalite_appliquee). CONCEPTION COMPLÈTE des 2 directions consignée à l'entrée n°76 (transcription pure au
  prochain tour, ~250 l, gabarit image_image_reciproque_contient_si_surjective). PROCHAINE : ÉCRIRE n°76.
- 23 juil : **n°76 (surjection ⇔ préimage non vide, E.R.8 item 7) CLOS** (~230 l, ensembles_surjective_preimage_er8.py) —
  PREMIÈRE clôture depuis la bascule Résumé. ⊢ est_application(f,E,F) ⇒ (surj ⇔ (∀X)(X⊂F⇒(¬(X=∅)⇒¬(f⁻¹⟨X⟩=∅)))), 0 hyp,
  theorie=22, 2 tests 0,55s. Dir A propre ; Dir B extensionnalité (image⊂F + F⊂image via singletons). **LEÇON liants :**
  ne JAMAIS prendre « z » comme élément dans une inclusion qui appelle appartient_singleton_inclus / non_vide_ssi_element
  (liant interne « z » ⇒ collision) → bâtir avec « y » puis α-convertir y→z (instancie+generalisation) pour matcher
  extensionnalite_appliquee/A1 ; _temoin_non_vide = generalize+instancie capture-safe de non_vide_ssi_element. Bugs corrigés :
  import est_application (fondations_notions, pas abrege) ; equivalence_avant manquant sur le S6 de Leibniz. PROCHAINE : n°77.
- 23 juil : **n°77 (⇔ bijective) classé ⏸ CHANTIER-DÉRIVATION** — pas d'infra manquante mais ~350 l, 4 parties (2 sens
  × inj/surj) + converses à bâtir (singletons) + ponts de représentation (injective_dans↔est_fonctionnel(f⁻¹), H_app par X
  depuis est_application). Marathon incompatible avec la contrainte contexte de Karl ⇒ session dédiée, plan complet à l'entrée
  n°77 (réutilise idiomes n°76). PROCHAINE : n°78 (itérées fⁿ, probable dérivation récursion/C63 dédiée aussi → sinon n°79).
- 23 juil : **n°79 (g∘f/f∘g perm ⇒ bijectives) classé ⏸ CHANTIER-DÉRIVATION** (plan direct consigné, ~250 l : converses
  de facteur composée-inj⇒facteur-inj À BÂTIR + composée-valeur/image-de-composée pas garanties closes). **CONSTAT
  MAJEUR : le front closeable-en-1-tour est ÉPUISÉ.** n°76 était l'exception auto-contenue ; n°77/78/79 et le reste du
  cluster applications (n°80/85/86) sont tous des dérivations dédiées (~250-350 l, glue composition/bijection/représentation).
  La boucle 60s ne peut plus que trier. DÉCISION à prendre : dédier des tours ENTIERS à une dérivation (n°77 ou les
  converses-de-facteur réutilisables), OU scanner les rares items encore moyens (n°84 K⊂K', n°63/67 ordre-sur-N). PROCHAINE : n°80.
- 23 juil : **n°84 (K⊂K' ⇔ K(x)⊂K'(x) ∀x, E.R.14 item 8) CLOS** (~130 l, ensembles_inclusion_coupes_er14.py) — 2e
  clôture (option B : dernier fruit bas trouvé). ⊢ est_un_graphe(K) ⇒ (K⊂K' ⇔ (∀a)K{a}⊂K'{a}), 0 hyp, theorie=22, 2
  tests 0,21s. Bricks : coupe_caracterisation, couple_egal_projections, est_un_graphe. LEÇONS liants : coupe_membre a le
  liant interne « x » → ne jamais nommer le point de coupe « x » (pris « a ») ; coupe_caracterisation n'accepte que des
  NOMS → pour un point-terme (pr₁z) : generalize a,y puis instancie ; pont α est_un_couple[x,y]→est_couple[a,b] (~12 l).
  PROCHAINE : n°80 (scan) puis n°63/67 (derniers moyens). Le gros du Résumé applications (n°77/78/79/80/85/86) = dédiées.
- 23 juil : **n°80 (représentation paramétrique, E.R.11 item 14) CLOS comme DÉFINITION** — pas un théorème :
  representation_parametrique(f,E,F):=est_surjective(f,E,F) (ensembles_fonctions_complements.py, @livre Def). Terminologie
  pure (synonyme surjection), aucune propriété nouvelle. PROCHAINE : n°82 (𝔓(E×F)↔applications, probable dédiée).
- 23 juil : **n°82 et n°83 marqués ⏸ CHANTIER-DÉRIVATION** (bijections entre ensembles 𝔓(E×F)↔{applications}, ~300 l
  chacune, objets ensemblistes à construire). E.R.16 relu : **n°85 = surtout définitions** (fonction de 3 arguments
  f(x,y,z) sur E×F×G, applications partielles) → à fermer comme DÉFINITION (cf. n°80), pas de théorème ; **n°86 = théorème**
  (f×g×h préserve inj/surj/bij, modéré/dédié). PROCHAINE : n°85 (définitions 3-arg).
- 23 juil : **n°85 (fonctions de 3 arguments, E.R.16 item 13) CLOS comme DÉFINITIONS** — 4 défs (est_fonction_trois_arguments,
  valeur_trois_arguments f(((x,y),z)), applications partielles f(a,·,·) et f(a,b,·)) dans ensembles_fonctions_complements.py,
  @livre Def, calque des fonctions à 2 args, produit associé à gauche. Aucun théorème (terminologie). PROCHAINE : n°86
  (f×g×h préserve inj/surj/bij, THÉORÈME — scan modéré/dédié).
- 23 juil : **n°86 (f×g×h préserve inj/surj/bij) classé ⏸ CHANTIER-DÉRIVATION** — pas de préservation binaire (f×g) close,
  seule la version FAMILLE (§5.7 axiome_extension_produit) existe = chantier. Dérivation dédiée (~250 l : produit binaire de
  fonctions + préservation coordonnée, puis (f×g)×h). PROCHAINE : bloc familles E.R.18+ (n°87), majoritairement chantier.
- 23 juil : **n°87 (⋃_{J₁∪J₂}=⋃_{J₁}∪⋃_{J₂}) évalué CLOSEABLE** (modéré ~250 l, membership + extensionnalité). Bricks TOUS
  clos (membre_reunion_famille, congruence_existe, monotonie_existe, et_ou_distrib, _instance_reunion bin+fam) sauf un helper
  ∃-sur-∨ trivial à bâtir (~25 l). Fiddly (réécritures du corps ∃ sous congruence_existe) → build en contexte frais plutôt
  que cramer un tour marathon (contrainte contexte Karl). Plan COMPLET consigné à l'entrée n°87. PROCHAINE : BÂTIR n°87.
- 23 juil : **n°87 (⋃_{J₁∪J₂}=⋃_{J₁}∪⋃_{J₂}, E.R.18 (36)) CLOS DU PREMIER COUP** (~180 l, ensembles_reunion_indices_union_er18.py) —
  le bloc familles n'était PAS entièrement bloqué. Membership + extensionnalité ; helper local **_existe_ou** ((∃x)(P∨Q)⇔(∃x)P∨(∃x)Q)
  RÉUTILISABLE. 0 hyp, theorie=22, 2 tests 0,10s. PROCHAINE : n°88 (produit×d'unions = union de produits, double famille — scan
  infra produit-famille) ; n°91/92 (⋂ analogues, membre_inter_famille avec ∀) probablement closeables via le même pattern.
- 23 juil : **n°88 et n°91 marqués ⏸ CHANTIER-DÉRIVATION** (produit×d'unions/inters = union/inter de produits sur famille
  DOUBLE-indexée J×K (ι,κ)↦X_ι×Y_κ, non formalisée). n°92 (MÊMES indices I, famille simple ι↦X_ι×Y_ι) reste CLOSEABLE via
  pattern n°87. PROCHAINE : n°89 (⋂ famille vide=E, écart AXIOME_INTER_FAM à lire) puis n°92 (build).
- 23 juil : **n°89 (⋂_∅=E) marqué ⏸ CHANTIER** — non dérivable : AXIOME_INTER_FAM restreint à I≠∅ (donne l'univers pour ∅,
  pas E) ; (40) = convention Bourbaki (⋂ bornée à 𝔓(E)). Prérequis : ⋂ bornée OU convention (40) posée. PROCHAINE : BÂTIR
  n°92 (mêmes indices, famille simple) via pattern n°87 + membre_inter_famille + couple_dans_produit_ssi. ⚠️ BUILD n°92 :
  vérifier/construire d'abord la famille ι↦X_ι×Y_ι (produit terme-à-terme, graphe_terme) + son valeur_famille ; helper à
  bâtir = distribution ∀ sur ∧ ((∀i)(P_i∧Q_i)⇔(∀i)P_i∧(∀i)Q_i, ou la version implicative i∈I⇒(P∧Q)) — miroir de _existe_ou.
- 23 juil : **n°92 assessment approfondi — plan RAFFINÉ (a grossi à ~300 l)**. Découvertes : (1) même écart empty-I → (44)
  FAUX pour I=∅ en ⋂ non-borné ⇒ hypothèse ¬(I=∅) requise ; (2) famille H=ι↦f_ι×g_ι NON constructible en theorie=22
  (graphe_terme_valeur en théorie dédiée) ⇒ H pris en hypothèse (∀i)(i∈I⇒valeur_famille(H,i)=produit(f_i,g_i)) ; (3)
  membership produit z générique = décomposition couple (idiomes n°84). Plan complet + bricks consignés à l'entrée n°92.
  Tous bricks clos (membre_inter_famille, couple_dans_produit_ssi, couple_egal_projections, non_vide_ssi_element,
  _pourtout_et_distrib, extensionnalite). Build en contexte frais (pattern plan→build, comme n°76/n°87). PROCHAINE : BÂTIR n°92.
- 23 juil : **n°92 reclassé ⏸ CHANTIER-DÉRIVATION** — assessment a révélé ~300 l (pont couple n°84 + famille n°87 + ∀-dist +
  ¬(I=∅) + membership produit 2 sens, haut risque mismatch liants). Plan complet consigné. Le bloc E.R.20-25 (n°93/94/52-62)
  est majoritairement chantier (produit-famille/quotient). Derniers moyens = n°63/67 (ordre N). PROCHAINE : n°93 (à trier).
- 23 juil : **n°65 (trichotomie exclusive d'un ordre total, E.R.27 item 4) CLOS DU PREMIER COUP** (~150 l,
  ensembles_trichotomie_total_er27.py) — 4e théorème de la session. ⊢ totalement_ordonne(G,E) ⇒ (∀u,v∈E)(exactement un de
  u<v/u=v/v<u), 0 hyp, theorie=22, 2 tests 0,08s. Exhaustive : tiers_exclu(u=v)+comparabilité ; exclusive : antisymétrie
  (de est_ordre) + symétrie égalité + _ex_falso. Bricks tous clos. PROCHAINE : n°66 (N bien ordonné, probable chantier bon-ordre).
  **Le front closeable au fil de la boucle est ÉPUISÉ** — n°65 était le dernier item moyen ; reste = backlog dédié documenté.
- 23 juil : **BOUCLE /loop TERMINÉE (fin normale).** Segment final trié (n°66/67 bon-ordre-N/⋂𝔉, limites n°68-72, division
  euclidienne n°24/26/27/28) = tous ⏸ CHANTIER. VÉRIFIÉ par grep : 0 case [ ] sans marqueur CHANTIER. 26 items clos, 76
  chantiers documentés avec plan. Le front closeable au fil de la boucle 60s est ÉPUISÉ ⇒ arrêt du loop (step 6). Reprise =
  sessions dédiées (voir pointeur : ⋃/⋂-d'un-ensemble, converses-de-facteur, n°92, division euclidienne, a^n=a).
