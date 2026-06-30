# STATUT RÉEL — 30 juin 2026 (corrige tous les docs périmés)

**Constat : le projet est QUASI-COMPLET sur Ch I–IV.** Tous les docs de couverture
(`COUVERTURE*.md` du 24 juin, la liste « gros chantiers ouverts » de `CLAUDE.md`)
SOUS-ESTIMENT massivement la réalité. À chaque vérification ce mois-ci, ce qui était
listé « manquant / chantier ouvert » s'avère **déjà fait et clos**.

## Métriques brutes (30 juin)
- **616** modules `bourbaki/.py` ; **939** marqueurs `@livre` ; **450+** fichiers de test.
- **326** modules rien que pour `cardinaux/` + `entiers/` (Ch III).

## Spot-checks « gros chantiers » de CLAUDE.md → TOUS faits
- **Cantor `a < 2^a`** : CLOS (`ensembles_cantor.cantor_strict`).
- **Zermelo (Th.1), Zorn (Th.2), Trichotomie (Th.3)** : CLOS (bundle `iii_2_trichotomie_ordinaux`, 60+ fichiers).
- **Récurrence transfinie C59** : CLOS. **Ordinaux ↔ cardinaux** (`iii_4_ordinal_cardinal`) : massivement développé.
- **Entiers / calcul sur les entiers (III.4–5)** : développés (`entiers/`, parité, prop9, etc.).
- **Audits fan-out 30 juin** : II.6 saturé (0 gap), II.5 17/18, III.2 lourd/fait, II.3.4-3.8 saturé.

## Frontière RÉELLE restante = résidus DURS (peu nombreux, pas de gain rapide)
1. **Cœur σ/Σ des structures (IV)** : récurrence sur le schéma d'échelon, transportabilité
   effective ; déf. de « l'ensemble des structures d'espèce Σ sur E » (E IV.4). HARD.
2. **Verrou-τ de la conjugaison** `f↦v∘f∘u` (II.5 Prop.2) : construction du graphe-terme. HARD.
3. **Sens ⊃ bloqués par le choix** (Prop.8 générale, etc.) : résidus HONNÊTES fidèles au livre,
   NON comblables sans poser le choix (hors périmètre).
4. Variantes pleines de quelques critères CST (IV) reportées (squelette logique présent).

## Conséquence stratégique
La phase **« formalisation tractable »** est essentiellement **terminée**. Les ticks de boucle
« cherche un trou tractable » atteignent un **rendement décroissant** (on retombe sur du saturé,
des tautologies, ou des résidus durs). Deux suites sensées :
- **(a)** attaquer délibérément UN résidu dur (lent/gros, ex. un bout du cœur σ/Σ) — vrai contenu
  mais cadence lente ;
- **(b)** PIVOTER sur le méta-algo (cf. [[but-final]] / mémoire `meta-algo-diffusion-marche`) :
  le **substrat est mûr** (616 modules + 939 traces `@livre` + le « pourquoi »/erreurs documentés),
  c'est exactement le carburant d'un générateur generate-and-verify (GFlowNet sur DAG / diffusion
  discrète + noyau-vérificateur). Le substrat ne demande plus qu'à être EXPLOITÉ.

> Recommandation : (b) est probablement le meilleur usage du temps maintenant ; (a) en complément
> ponctuel. La chasse au gain-rapide section-par-section, elle, est officiellement close.
