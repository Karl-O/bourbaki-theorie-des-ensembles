"""Test V9 — §II.3.1 : image du domaine = ensemble des valeurs (E II.10).

  ⊢ G⟨pr₁G⟩ = pr₂G        (= image(G, dom G) = img G).

Vérifie (en APPELANT le théorème) : la conclusion reconstruite indépendamment,
la CLÔTURE INCONDITIONNELLE (0 hypothèse, est_clos True), et l'invariant
theorie_ensembles() == 22.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_3_correspondances.ensembles_image_domaine import (
    image_domaine_egale_img, image_domaine_egale_img_cible)


def test_image_domaine_conclusion():
    vG = var("G")
    t = image_domaine_egale_img("G")
    # conclusion reconstruite : G⟨pr₁G⟩ = pr₂G = egal(image(G, dom G), img G).
    cible = egal(E.image(vG, E.dom(vG)), E.img(vG))
    assert t.conclusion == cible
    assert t.conclusion == image_domaine_egale_img_cible("G")


def test_image_domaine_clos():
    t = image_domaine_egale_img("G")
    # résultat CLOS : 0 hypothèse non déchargée (inconditionnel).
    assert t.hypotheses == frozenset()
    assert t.est_clos


def test_theorie_invariant_22():
    assert len(E.theorie_ensembles().axiomes) == 22
