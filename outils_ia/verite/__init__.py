# -*- coding: utf-8 -*-
"""`outils_ia/verite/` — outils de MESURE de ce qu'une dérivation doit vraiment.

Ce paquet contient des outils **sur** le corpus, pas des notions du livre :
aucun marqueur `@livre`, aucun passage par `gen_livre_manifestes`.

Règle absolue de ce dossier : **rien ici ne touche au noyau**
(`bourbaki/i_description_mathematique_formelle/i_2_theoremes/noyau/`) ni à
`subst`, et **aucun monkeypatch** — l'observation se fait par `sys.setprofile`,
qui ne substitue aucune fonction.

Modules (voir `README.md` pour les six définitions et leurs angles morts) :
  * `axiomes_consommes` — Ax(D), Dette(th), invariant_reel (M1).
  * `classer_residu`    — déchargeable / réfutable / indépendante / **inconnu**
    pour une hypothèse résiduelle. « inconnu » est une DETTE DE MESURE, à
    re-passer après chaque fix d'infrastructure — pas un mur.
  * `echec`             — `Echec` (E1..E7), `Mur`, `verifier` : un échec n'est
    admis qu'avec un certificat que la machine REFAIT.

⚠️ COLLISION DE NOM, VOULUE MAIS DANGEREUSE : `echec.CLASSES` (dict "E1".."E7")
et `classer_residu.CLASSES` (tuple des 4 verdicts) portent le MÊME nom. Importer
les deux par `from … import *` en écraserait un EN SILENCE. Toujours importer les
modules, jamais leur contenu en vrac.

⚠️ UN SEUL CHEMIN D'IMPORT : `outils_ia.verite.<module>`. Un `sys.path.insert` qui
rendrait `echec` importable en top-level crée une SECONDE copie du module ; un
`Echec` bâti par l'une est alors rejeté par le `verifier` de l'autre (mesuré le
2026-07-26 : `VE.Echec is TOP.Echec` → False). Les tests vivent dans
`tests/outils_ia/verite/` et importent par le paquet.
"""
