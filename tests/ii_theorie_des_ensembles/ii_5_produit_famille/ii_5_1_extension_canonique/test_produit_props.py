"""Tests §II.5 — PROPOSITIONS du produit / extension canonique (preuves).

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
Aucun fichier existant n'est modifié ; theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, non, appartient, existe,
                                       inclus, pourtout, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_1_extension_canonique import ensembles_produit_props as P


# ── §5.1 — (Γ'∘Γ)^ = Γ̂'∘Γ̂ (valeur) ──────────────────────────────────────────
def test_ext_compose_valeur():
    thm = P.ext_compose_valeur("Gp", "G", "X")
    vGp, vG, vX = var("Gp"), var("G"), var("X")
    cible = egal(E.image(E.composee(vGp, vG), vX),
                 E.image(vGp, E.image(vG, vX)))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── §5.1 — Prop. 1.2° : f̂ injective (conditionnel rétraction) ────────────────
def test_ext_canonique_injective():
    thm = P.ext_canonique_injective("R", "G", "A", "X", "Xp")
    vR, vG, vX, vXp = var("R"), var("G"), var("X"), var("Xp")
    GX, GXp = E.image(vG, vX), E.image(vG, vXp)
    RGX, RGXp = E.image(vR, GX), E.image(vR, GXp)
    hyp = et(et(et(et(appartient(vX, E.parties(var("A"))),
                      appartient(vXp, E.parties(var("A")))),
                   egal(RGX, vX)), egal(RGXp, vXp)), egal(GX, GXp))
    cible = impl(hyp, egal(vX, vXp))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── §5.1 — Prop. 1.1° : f̂ surjective (conditionnel section) ──────────────────
def test_ext_canonique_surjective():
    thm = P.ext_canonique_surjective("G", "S", "A", "B", "Y")
    vG, vS, vY = var("G"), var("S"), var("Y")
    SY = E.image(vS, vY)
    GSY = E.image(vG, SY)
    hyp = et(et(appartient(vY, E.parties(var("B"))),
                appartient(SY, E.parties(var("A")))),
             egal(GSY, vY))
    body = et(appartient(var("X"), E.parties(var("A"))),
              egal(E.image(vG, var("X")), vY))
    cible = impl(hyp, existe("X", body))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
