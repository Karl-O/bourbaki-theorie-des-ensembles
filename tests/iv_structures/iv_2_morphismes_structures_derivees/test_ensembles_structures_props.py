"""Tests ISOLÉS du module NEUF `bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_structures_props`
(§IV.1.5 / IV.2.2 / IV.3.1 — propositions « logiquement directes » du chap. IV).

Vérifie, pour chacun des cinq groupes de la mission IV-structures-props :
  • la CLÔTURE conditionnelle (hypothèses EXPLICITES = axiomes-schémas (MO_II)/
    (MO_III)/CST1/(AU_II′) instanciés, jamais des axiomes de la théorie) ;
  • l'ANTI-TAUTOLOGIE (la conclusion n'est PAS l'une des hypothèses) ;
  • l'IDENTITÉ LITTÉRALE de la conclusion à la cible fidèle (plus_fine / est_morphisme
    / est_isomorphisme du chap. IV) ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    plus_fine, est_morphisme, _morph_defaut)
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes import Espece, est_isomorphisme
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import Schema
import bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_structures_props as P


# ── espèce minimale (1 base principale, 0 auxiliaire, schéma identité) ──────────
def _espece():
    return Espece(nom="Sig", n=1, auxiliaires=(),
                  schema=Schema(((0, 1),)),
                  axiome=lambda bases, s: var("R"))


def _m():
    return _morph_defaut()


# ════════════════════════════════════════════════════════════════════════════
#  theorie = 22 (invariant intangible)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    th = E.theorie_ensembles()
    assert len(th.axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  1. COMPOSITION DE MORPHISMES EST UN MORPHISME  (MO_II)
# ════════════════════════════════════════════════════════════════════════════
def test_composee_morphismes_est_morphisme():
    t = P.composee_morphismes_est_morphisme()
    m = _m()
    ve = var("E")
    cible = est_morphisme(ve, var("S"), var("Epp"), var("Spp"),
                          E.composee(var("g"), var("f")), m)
    assert t.conclusion == cible
    # 3 hypothèses EXPLICITES : (MO_II) + morph(f) + morph(g)
    assert len(t.hypotheses) == 3
    # anti-tautologie : la conclusion n'est pas une hypothèse
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  2. « PLUS FINE / MOINS FINE » EST UN PRÉORDRE  (IV.2.2)
# ════════════════════════════════════════════════════════════════════════════
def test_plus_fine_reflexive():
    t = P.plus_fine_reflexive()
    m = _m()
    ve = var("E")
    cible = est_morphisme(ve, var("S"), ve, var("S"), E.diagonale(ve), m)
    # plus_fine(E,S,S) == « id_E morphisme » : réflexivité (MO_III)
    assert t.conclusion == cible
    assert len(t.hypotheses) == 1                      # l'instance (MO_III)


def test_plus_fine_transitive_normalisee():
    t = P.plus_fine_transitive_normalisee()
    m = _m()
    ve = var("E")
    cible = plus_fine(ve, var("S1"), var("S3"), m)     # plus_fine(E,S1,S3)
    assert t.conclusion == cible
    # 4 hypothèses : (MO_II) + plus_fine(S1,S2) + plus_fine(S2,S3) + (Δ∘Δ=Δ)
    assert len(t.hypotheses) == 4
    # ANTI-TAUTOLOGIE : la transitivité n'est pas une de ses prémisses
    assert cible not in t.hypotheses
    # les prémisses plus_fine(S1,S2) et plus_fine(S2,S3) SONT bien présentes
    pf12 = plus_fine(ve, var("S1"), var("S2"), m)
    pf23 = plus_fine(ve, var("S2"), var("S3"), m)
    assert pf12 in t.hypotheses and pf23 in t.hypotheses


def test_plus_fine_transitive_brute():
    # forme brute (avec Δ_E∘Δ_E) — fidèle à (MO_II), 3 hyps
    t = P.plus_fine_transitive()
    assert len(t.hypotheses) == 3


def test_moins_fine_preordre_marqueur():
    d = P.moins_fine_preordre()
    assert d["est_preordre"] is True
    # réflexivité et transitivité sont des THÉORÈMES (objets Theoreme)
    assert hasattr(d["reflexivite"], "conclusion")
    assert hasattr(d["transitivite"], "conclusion")
    assert len(d["reflexivite"].hypotheses) == 1
    assert len(d["transitivite"].hypotheses) == 4


# ════════════════════════════════════════════════════════════════════════════
#  3. IDENTITÉ EST UN ISOMORPHISME  (niveau ESPÈCE Σ, IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
def test_identite_est_isomorphisme_espece():
    sig = _espece()
    t = P.identite_est_isomorphisme_espece(sig)
    ve, vu = var("E"), var("U")
    cible = est_isomorphisme(sig, [E.diagonale(ve)], [ve], [ve], vu, vu)
    assert t.conclusion == cible
    # UNIQUE hypothèse = clause (4) à l'identité (CST1) ; bijection inconditionnelle
    assert len(t.hypotheses) == 1


def test_identite_iso_bijection_inconditionnelle():
    # la partie « bijection » Δ_E est bien un théorème CLOS (absorbé sans hypothèse)
    bij = P._diagonale_bijection("E")
    assert bij.est_clos
    assert bij.conclusion == est_bijection_de(E.diagonale(var("E")),
                                              var("E"), var("E"))


# ════════════════════════════════════════════════════════════════════════════
#  4. TRANSPORT COMPOSÉ / COMPOSITION D'ISOMORPHISMES  (CST4, IV.1.5)
# ════════════════════════════════════════════════════════════════════════════
def test_composee_isomorphismes_est_isomorphisme():
    sig = _espece()
    t = P.composee_isomorphismes_est_isomorphisme(sig)
    ve, vepp = var("E"), var("Epp")
    vu, vupp = var("U"), var("Upp")
    gof = E.composee(var("g"), var("f"))
    cible = est_isomorphisme(sig, [gof], [ve], [vepp], vu, vupp)
    assert t.conclusion == cible
    # 5 hypothèses EXPLICITES : bij(f) + bij(g) + (4)_f + (4)_g + CST1
    assert len(t.hypotheses) == 5
    # les deux bijections données sont bien des prémisses (pas postulées vraies)
    assert est_bijection_de(var("f"), ve, var("Ep")) in t.hypotheses
    assert est_bijection_de(var("g"), var("Ep"), vepp) in t.hypotheses
    # anti-tautologie
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  5. UNICITÉ (À ISO UNIQUE PRÈS) DE LA SOLUTION UNIVERSELLE  (CST8, IV.3.1)
# ════════════════════════════════════════════════════════════════════════════
def test_solution_universelle_iso_unique():
    t = P.solution_universelle_iso_unique()
    m = _m()
    fe, fep = var("FE"), var("FEp")
    f1, f2 = var("f1"), var("f2")
    inv1 = egal(E.composee(f2, f1), E.diagonale(fe))    # f₂∘f₁ = Id_{F_E}
    inv2 = egal(E.composee(f1, f2), E.diagonale(fep))   # f₁∘f₂ = Id_{F_E'}
    assert t.conclusion == et(inv1, inv2)
    # 3 hypothèses : H1 (AU_I′), H2 (AU_I′), INV (AU_II′)
    assert len(t.hypotheses) == 3
    # anti-tautologie : la conclusion d'inversibilité n'est pas une prémisse
    assert et(inv1, inv2) not in t.hypotheses
