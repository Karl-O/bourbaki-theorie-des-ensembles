# RECHERCHE.md — journal d'hypothèses et d'idées nées des résultats

Principe (décidé avec Karl le 2026-08-22) : le formaliseur (Claude) vit dans le
bac à sable ; chaque résultat — vert, rouge, ou surprenant — peut suggérer une
idée de recherche. On les consigne ICI au fil de l'eau, avec un verdict qui
évolue. Le « mode découverte » actif (des ticks dédiés à explorer ces questions)
s'enclenche après Hessenberg ; d'ici là ce journal accumule.

Statuts : `OUVERTE` (à explorer) · `EN COURS` · `CLOSE` (résolue/utilisée) ·
`ABANDONNÉE` (avec la raison).

---

## R-1 (2026-08-19, CLOSE) — L'astuce du clamp : borner une règle τ sans toucher aux évaluations
**Née de** : le verrou de la borne V (l'itération de Dedekind exigeait
`regle_dans_V(T,E)`, impossible pour une règle u arbitraire).
**Idée** : composer la règle avec un garde `clamp_E(t) = τ_z((t∈E∧z=t)∨(t∉E∧z=x0))` ;
la borne devient dérivable sous la seule hypothèse `x0∈E` (double tiers exclu),
et le clamp est *invisible* sur le domaine utile (déclampage sous `g(n)∈E`).
**Portée générale** : technique réutilisable pour TOUTE construction par
récursion dans le calcul du τ où la règle n'est pas nativement bornée. Candidat
à un lemme générique et à une section d'article (ingénierie de preuve du τ).

## R-2 (2026-08-21, CLOSE — leçon majeure) — Soundness ≠ fidélité : la « récursion » qui était une tabulation
**Née de** : l'audit du C60 déposé — il prouvait une équation affaiblie
(tabulation), pas `f(x) = T(f|seg x)`.
**Observation de recherche** : un noyau LCF garantit zéro faux théorème mais ne
protège PAS d'un énoncé silencieusement affaibli. La reconstruction complète
(C60-vrai → C63-vrai, ~30 ticks) a montré que l'écart était réparable *dans le
système*. Matériau d'article : taxonomie des « affaiblissements silencieux »
et méthode de détection (relecture PDF + assertions de forme).

## R-3 (2026-08-22, OUVERTE) — Mesurer le « 1 » de Bourbaki (vérifier Mathias)
**Née de** : la question de Karl « peut-on faire de la recherche ? ».
**Idée** : écrire un déplieur-compteur qui expanse intégralement un terme
(τ, ⊃, définitions) et MESURE sa taille — confronter l'estimation de Mathias
(~10^54 symboles pour le chiffre 1) à une mesure machine exacte, première
mondiale. Ne demande pas de prouveur ; quelques jours. Après Hessenberg.

## R-4 (2026-08-22, OUVERTE) — La machine, 3 étages
**Née de** : discussion avec Karl (plan détaillé dans DECISIONS du 2026-08-22).
Étage 1 automate (tautologies S1-S4, chaînes d'égalités, ∀ évidents) — accélère
le chantier lui-même ; étage 2 chaînage arrière sur la bibliothèque ; étage 3
LLM suggéreur + noyau juge (« LLM + calcul du τ », sujet vierge).

## R-5 (2026-08-22, OUVERTE) — Taxonomie des captures : 14+ leçons = un résultat en soi
**Née de** : l'accumulation des leçons de capture (liants ∀-clos aux noms frais,
paramètres-lieurs réutilisés (leçon 13), et()-encodé, témoins ∃ à α-renommer…).
**Idée** : ces pièges sont *spécifiques au τ de Bourbaki* et nulle part
documentés mécaniquement. Les systématiser (catalogue + contre-exemples
machine-vérifiés) = contribution originale sur l'ingénierie de preuve du τ.

## R-6 (2026-08-22, OUVERTE) — Le patron « familles S8 dédiées » comme principe général
**Née de** : Dfam_rec/Dglob_rec (le terme PORTE son graphe — leçon seg_ext) et
des théories S8 jamais auto-référentes.
**Idée** : formuler le principe (« toute construction paramétrique passe par une
théorie dédiée conservative ») et prouver sa conservativité au-dessus des 22
axiomes — un mini-théorème métathéorique sur NOTRE architecture, publiable dans
le rapport et l'article A1.
