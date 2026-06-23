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
