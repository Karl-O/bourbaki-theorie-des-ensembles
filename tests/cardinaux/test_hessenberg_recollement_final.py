"""Tests — §III.6.3 Théorème 2 (HESSENBERG) assemblage final ¬(𝔟<a) + a²=a.

Vérifie : theorie_ensembles()==22 ; conclusions == cibles miroir ; conclusion ∉ hyps ;
liste les hypothèses honnêtes exactes de chaque lemme."""
from bourbaki.logique.i_1_termes_relations.formule import egal, inclus, et, non, var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.cardinaux import ensembles_hessenberg_recollement_final as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_b_le_complement():
    thm = M._b_le_complement("E", "S0")
    cible = M._b_le_complement_cible("E", "S0")
    assert thm.conclusion == cible
    assert thm.conclusion not in thm.hypotheses
    # hypothèses honnêtes attendues
    vE, vS = var("E"), var("S0")
    b = cardinal(vS)
    bb = M.produit_b(b)
    bpb = M.somme_b(b)
    expected = {
        inclus(vS, vE),
        est_cardinal(b),
        est_infini(b),
        egal(bb, b),
        inf_strict_card(b, cardinal(vE)),
    }
    assert thm.hypotheses == expected, f"hyps inattendues:\n{thm.hypotheses}\nvs\n{expected}"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_negation_b_inf_strict_a():
    thm = M.negation_b_inf_strict_a("E", "S0", "phi0", "psi", "Ucadre", "uwit")
    cible = M.negation_b_inf_strict_a_cible("E", "S0")
    assert thm.conclusion == cible
    assert thm.conclusion not in thm.hypotheses
    vS, vE = var("S0"), var("E")
    b = cardinal(vS)
    # 𝔟<a doit être DÉCHARGÉE (jamais postulée vraie)
    assert inf_strict_card(b, cardinal(vE)) not in thm.hypotheses, \
        "𝔟<a non déchargée — théorème vacueux/faux"
    # quelques hyps honnêtes attendues (arithmétiques + géométriques)
    assert inclus(vS, vE) in thm.hypotheses          # S₀⊂E
    assert est_cardinal(b) in thm.hypotheses          # est_cardinal(𝔟)
    assert est_infini(b) in thm.hypotheses            # est_infini(𝔟)
    # Z=S₀ (verrou de maximalité, résidu structurel)
    Z = E.reunion(vS, var("Ucadre"))
    assert egal(Z, vS) in thm.hypotheses
    # témoin u∈U (U≠∅)
    from bourbaki.logique.i_1_termes_relations.formule import appartient
    assert appartient(var("uwit"), var("Ucadre")) in thm.hypotheses
    # documenter la liste exacte
    print("\nHYPS HONNÊTES negation_b_inf_strict_a:")
    for hh in sorted(thm.hypotheses, key=str):
        print("  ", hh)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hessenberg_a_carre_egal_a_inconditionnel():
    thm = M.hessenberg_a_carre_egal_a_inconditionnel("E", "S0", "phi0", "psi",
                                                     "Ucadre", "uwit")
    cible = M.hessenberg_a_carre_egal_a_inconditionnel_cible("E")
    assert thm.conclusion == cible
    assert thm.conclusion not in thm.hypotheses
    vS, vE = var("S0"), var("E")
    b = cardinal(vS)
    # ¬(𝔟<a) DOIT être déchargée (dérivée par negation_b_inf_strict_a)
    assert non(inf_strict_card(b, cardinal(vE))) not in thm.hypotheses, \
        "¬(𝔟<a) non déchargée"
    # Card(S₀×S₀)=Card S₀ honnête présente
    SxS = E.produit(vS, vS)
    assert egal(cardinal(SxS), b) in thm.hypotheses
    print("\nHYPS HONNÊTES hessenberg_a_carre_egal_a_inconditionnel:")
    for hh in sorted(thm.hypotheses, key=str):
        print("  ", hh)
    assert len(E.theorie_ensembles().axiomes) == 22
