"""Tests §II.5.4 — PROJECTION partielle pr_J : Prop. 5-6 et corollaires (preuves).

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
Aucun fichier existant n'est modifié ; theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.logique.i_1_termes_relations.formule import (var, tau, egal, et, impl, non, appartient, existe,
                                       inclus, pourtout, equiv)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_4_projection_partielle import ensembles_produit_props_projection as P
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_1_extension_canonique import ensembles_extension_canonique as X
from bourbaki.cardinaux.ensembles_cardinaux_un_borne import temoin_dans


# ── §5.4 — Prop. 6 : choix-τ dans un facteur non vide ────────────────────────
def test_facteur_temoin():
    thm = P.facteur_temoin("f", "iota")
    vf, vi = var("f"), var("iota")
    X_iota = E.valeur_famille(vf, vi)
    # même conclusion que temoin_dans instancié au facteur X_ι
    cible = temoin_dans(X_iota).conclusion
    assert thm.conclusion == cible
    assert thm.est_clos
    # forme attendue : ¬(X_ι=∅) ⇒ (τ_w(w∈X_ι) ∈ X_ι)
    e = tau("w", appartient(var("w"), X_iota))
    assert thm.conclusion == impl(non(egal(X_iota, E.VIDE)), appartient(e, X_iota))


# ── §5.4 — Cor. 2 (sens facile) : ∏≠∅ ⇒ chaque facteur ≠∅ ─────────────────────
def test_facteur_non_vide_si_membre():
    thm = P.facteur_non_vide_si_membre("f", "I", "F", "iota")
    vf, vI, vF, vi = var("f"), var("I"), var("F"), var("iota")
    X_i = E.valeur_famille(vf, vi)
    hyp = et(appartient(vF, E.produit_famille(vf, vI)), appartient(vi, vI))
    cible = impl(hyp, non(egal(X_i, E.VIDE)))
    assert thm.conclusion == cible
    assert thm.est_clos


# ── §5.4 — Prop. 5 : pr_J surjective (réduction au prolongement) ─────────────
def test_pr_J_surjective_via_prolongement():
    thm = P.pr_J_surjective_via_prolongement("f", "I", "J", "G", "F")
    vf, vI, vJ, vG, vF = var("f"), var("I"), var("J"), var("G"), var("F")
    hyp = et(et(appartient(vG, X.produit_partiel(vf, vJ)),
                appartient(vF, E.produit_famille(vf, vI))),
             egal(X.projection_J(vF, vJ), vG))
    body = et(appartient(var("P"), E.produit_famille(vf, vI)),
              egal(X.projection_J(var("P"), vJ), vG))
    cible = impl(hyp, existe("P", body))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
