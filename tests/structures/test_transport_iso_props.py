"""Tests ISOLÉS du module NEUF `bourbaki.structures.ensembles_transport_iso_props`
(§IV.1.5 / IV.1.2 — transport de structure & isomorphismes, niveau ESPÈCE Σ).

Vérifie, pour chacun des six théorèmes :
  • la CLÔTURE conditionnelle (hypothèses EXPLICITES = axiomes-schémas CST1/CST2/CST3
    de Bourbaki instanciés + faits ensemblistes, JAMAIS des axiomes de la théorie) ;
  • l'ANTI-TAUTOLOGIE / NON-VACUITÉ (la conclusion n'est PAS l'une des hypothèses) ;
  • l'IDENTITÉ LITTÉRALE de la conclusion à la cible fidèle (est_isomorphisme /
    sont_isomorphes / est_automorphisme / est_bijection_de / égalité de transport) ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé).
"""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures.ensembles_especes import (
    Espece, structure_transportee, est_isomorphisme, sont_isomorphes,
    est_automorphisme)
from bourbaki.structures.ensembles_especes_echelon import (
    Schema, echelon, extension_canonique, schema_parties)
import bourbaki.structures.ensembles_transport_iso_props as P


# ── espèces de test ──────────────────────────────────────────────────────────
def _espece():
    """Espèce minimale : 1 base, 0 auxiliaire, schéma identité S(E)=E."""
    return Espece(nom="Sig", n=1, auxiliaires=(),
                  schema=Schema(((0, 1),)),
                  axiome=lambda bases, s: var("R"))


def _espece_parties():
    """Espèce à schéma NON trivial S(E)=𝔓(E) (pour la non-vacuité de l'échelon)."""
    return Espece(nom="SigP", n=1, auxiliaires=(),
                  schema=schema_parties(),
                  axiome=lambda bases, s: var("R"))


# ════════════════════════════════════════════════════════════════════════════
#  theorie = 22 (invariant intangible)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    th = E.theorie_ensembles()
    assert len(th.axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  1. RÉCIPROQUE D'UN ISOMORPHISME D'ESPÈCE EST UN ISOMORPHISME
# ════════════════════════════════════════════════════════════════════════════
def test_reciproque_isomorphisme_espece():
    sig = _espece()
    t = P.reciproque_isomorphisme_espece(sig)
    ve, vep, vu, vup = var("E"), var("Ep"), var("U"), var("Up")
    finv = E.reciproque(var("f"))
    cible = est_isomorphisme(sig, [finv], [vep], [ve], vup, vu)
    assert t.conclusion == cible
    # 3 hypothèses EXPLICITES : iso(f) donné + bij(f⁻¹) + CST3
    assert len(t.hypotheses) == 3
    # iso de départ est bien une prémisse (pas postulé vrai)
    iso_f = est_isomorphisme(sig, [var("f")], [ve], [vep], vu, vup)
    assert iso_f in t.hypotheses
    # bijection de f⁻¹ est bien une prémisse
    assert est_bijection_de(finv, vep, ve) in t.hypotheses
    # anti-tautologie : la conclusion n'est pas une hypothèse
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  2. « SONT ISOMORPHES » EST RÉFLEXIVE
# ════════════════════════════════════════════════════════════════════════════
def test_sont_isomorphes_reflexive_espece():
    sig = _espece()
    t = P.sont_isomorphes_reflexive_espece(sig)
    ve, vu = var("E"), var("U")
    cible = sont_isomorphes(sig, [ve], [ve], vu, vu)
    assert t.conclusion == cible
    assert cible.tag == "exists"                # c'est bien une relation existentielle
    # UNIQUE hypothèse = clause (4) à l'identité (CST1) ; bijection inconditionnelle
    assert len(t.hypotheses) == 1
    eq4_id = egal(structure_transportee(sig, [E.diagonale(ve)], vu), vu)
    assert eq4_id in t.hypotheses
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  3. L'IDENTITÉ EST UN AUTOMORPHISME
# ════════════════════════════════════════════════════════════════════════════
def test_automorphisme_identite_espece():
    sig = _espece()
    t = P.automorphisme_identite_espece(sig)
    ve, vu = var("E"), var("U")
    cible = est_automorphisme(sig, [E.diagonale(ve)], [ve], vu)
    assert t.conclusion == cible
    # UNIQUE hypothèse = clause (4) à l'identité ; bijection inconditionnelle
    assert len(t.hypotheses) == 1
    eq4_id = egal(structure_transportee(sig, [E.diagonale(ve)], vu), vu)
    assert eq4_id in t.hypotheses
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  4. UNICITÉ DE LA STRUCTURE TRANSPORTÉE
# ════════════════════════════════════════════════════════════════════════════
def test_transporte_unique_espece():
    sig = _espece()
    t = P.transporte_unique_espece(sig)
    vv, vv2 = var("V"), var("V2")
    cible = egal(vv, vv2)                       # V = V'
    assert t.conclusion == cible
    # 2 hypothèses : les deux isomorphismes (mêmes f, U ; cibles V, V')
    assert len(t.hypotheses) == 2
    ve, vep, vu = var("E"), var("Ep"), var("U")
    isoV = est_isomorphisme(sig, [var("f")], [ve], [vep], vu, vv)
    isoV2 = est_isomorphisme(sig, [var("f")], [ve], [vep], vu, vv2)
    assert isoV in t.hypotheses and isoV2 in t.hypotheses
    # anti-tautologie : V=V' n'est pas une prémisse
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  5. ÉCHELON D'IDENTITÉS DONNE UNE BIJECTION  (schéma NON trivial S(E)=𝔓(E))
# ════════════════════════════════════════════════════════════════════════════
def test_echelon_identite_bijection():
    sig = _espece_parties()
    t = P.echelon_identite_bijection(sig)
    ve = var("E")
    DE = E.diagonale(ve)
    SE = echelon(sig.schema, [ve])
    extDE = extension_canonique(sig.schema, [DE])          # ⟨Δ_E⟩^S = ext_parties(Δ_E)
    cible = est_bijection_de(extDE, SE, SE)
    assert t.conclusion == cible
    # 2 hypothèses : bij(Δ_{S(E)}) (CST2-id) + ⟨Δ_E⟩^S = Δ_{S(E)} (CST1-id)
    assert len(t.hypotheses) == 2
    DSE = E.diagonale(SE)
    assert est_bijection_de(DSE, SE, SE) in t.hypotheses
    assert egal(extDE, DSE) in t.hypotheses
    # NON-VACUITÉ FORTE : ⟨Δ_E⟩^S DIFFÈRE LITTÉRALEMENT de Δ_{S(E)} (schéma non trivial)
    assert extDE != DSE
    # la conclusion (bij de ⟨Δ_E⟩^S) n'est pas l'hypothèse (bij de Δ_{S(E)})
    assert cible not in t.hypotheses


def test_echelon_identite_schema_trivial_degenere():
    # avec le schéma identité S(E)=E, ⟨Δ_E⟩^S = Δ_E = Δ_{S(E)} : le théorème reste vrai
    # (les hypothèses se confondent) mais l'intérêt est le cas non trivial ci-dessus.
    sig = _espece()
    t = P.echelon_identite_bijection(sig)
    ve = var("E")
    SE = echelon(sig.schema, [ve])
    extDE = extension_canonique(sig.schema, [E.diagonale(ve)])
    assert t.conclusion == est_bijection_de(extDE, SE, SE)


# ════════════════════════════════════════════════════════════════════════════
#  6. UN ISOMORPHISME DONNE L'ÉGALITÉ DE TRANSPORT  (relation (4))
# ════════════════════════════════════════════════════════════════════════════
def test_isomorphisme_donne_transport_eq():
    sig = _espece()
    t = P.isomorphisme_donne_transport_eq(sig)
    ve, vep, vu, vup = var("E"), var("Ep"), var("U"), var("Up")
    cible = egal(structure_transportee(sig, [var("f")], vu), vup)   # ⟨f⟩^S(U) = U'
    assert t.conclusion == cible
    # UNIQUE hypothèse = l'isomorphisme (la CONJONCTION bijection ∧ égalité)
    assert len(t.hypotheses) == 1
    iso = est_isomorphisme(sig, [var("f")], [ve], [vep], vu, vup)
    assert iso in t.hypotheses
    # NON-VACUITÉ : la conclusion (une ÉGALITÉ) n'est PAS l'hypothèse (la CONJONCTION)
    assert cible not in t.hypotheses
    assert cible != iso
