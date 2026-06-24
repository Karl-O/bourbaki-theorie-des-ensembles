"""Tests §II.3.2 — fidélité image directe / réciproque (E.R.9, §2 item 10).

  (18)  X ⊂ f⁻¹⟨f⟨X⟩⟩   sous H_app(X,f)
  (19)  f⟨f⁻¹⟨Y⟩⟩ ⊂ Y    sous est_fonctionnel(f)

Pour chaque énoncé : APPEL du théorème (pas seulement import), conclusion == cible
Bourbaki, hypothèses honnêtes attendues, clôture (0 hyp), theorie_ensembles()==22.
"""
from bourbaki.logique.i_1_termes_relations.formule import (
    var, et, impl, pourtout, appartient)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_image_reciproque_props import (
    inclus_image_reciproque_image, cible_inclus_image_reciproque_image,
    image_image_reciproque_inclus, cible_image_image_reciproque_inclus)


def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inclus_image_reciproque_image_18():
    th = inclus_image_reciproque_image()
    cible = cible_inclus_image_reciproque_image()
    # hypothèse honnête load-bearing : H_app(X,f) = (∀x)(x∈X ⇒ (x,f(x))∈f)
    vf, vx, vu = var("f"), var("X"), var("x")
    hyp_app = pourtout("x", impl(appartient(vu, vx),
                                 appartient(E.couple(vu, E.valeur(vf, vu)), vf)))
    # ⊢ H_app ⇒ (X ⊂ f⁻¹⟨f⟨X⟩⟩)
    assert th.conclusion == impl(hyp_app, cible)
    assert th.hypotheses == frozenset()            # clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_image_image_reciproque_inclus_19():
    th = image_image_reciproque_inclus()
    cible = cible_image_image_reciproque_inclus()
    vf = var("f")
    # ⊢ est_fonctionnel(f) ⇒ (f⟨f⁻¹⟨Y⟩⟩ ⊂ Y)
    assert th.conclusion == impl(E.est_fonctionnel(vf), cible)
    assert th.hypotheses == frozenset()            # clos
    assert len(E.theorie_ensembles().axiomes) == 22
