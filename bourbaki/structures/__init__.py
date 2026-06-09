"""Sous-package `bourbaki.structures` — chapitre IV (Structures).

Représentations FIDÈLES, au niveau objet, des notions de :
  • IV.1 — espèces de structure, échelons, typification (modules ensembles_especes*) ;
  • IV.2 — morphismes et structures dérivées (σ-morphisme, plus fine/moins fine,
    structures initiale/finale, induite/image réciproque, produit, quotient/image
    directe) ;
  • IV.3 — applications universelles (données (Σ,σ,α), α-application, Σ-ensemble /
    α-application universels, ensemble libre engendré).

Le chapitre IV est ABSTRAIT au plus haut degré : Σ est une espèce de structure
(paramètre quantifié sur les espèces, MÉTA), σ une notion générique de morphisme
(terme σ{x,y,s,t} postulé MO_I–III) et α un terme générique (postulé QM_I–II).
Aucune de ces données n'est exprimable par une seule formule du fragment objet
{var, τ, =, ∈, ¬, ∨, ∃}.  On suit donc la convention déjà retenue dans
`ensembles_morphismes` / `ensembles_isomorphismes` / `ensembles_applications_universelles` :
on PARAMÈTRE chaque notion par des PRÉDICATS ABSTRAITS (callables Python renvoyant
des Formule du fragment objet) — « morph(f) », « alpha(phi) », « structure(s,E) »…
Le lecteur passe ses prédicats concrets (p.ex. ceux de `ensembles_morphismes` pour
une espèce relationnelle) ; les DÉFINITIONS et les THÉORÈMES PUREMENT LOGIQUES
prouvés ici valent QUEL QUE SOIT leur contenu, car ils ne reposent que sur la
structure ∀/∃/⇔ des propriétés universelles (IN)/(FI)/(AU).

theorie_ensembles() reste à 22 axiomes : aucun module de ce package ne l'enrichit.
"""
