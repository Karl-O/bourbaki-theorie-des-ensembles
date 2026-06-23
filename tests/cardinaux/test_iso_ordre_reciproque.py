"""Test §III.1.3 / §III.2 — l'isomorphisme RÉCIPROQUE d'un iso d'ordre est un iso.

KEYSTONE de la trichotomie (Th3 §III.2).

  { est_isomorphisme_ordre(φ,S,T,R,R'),  est_fonctionnel(φ),  dom φ = S }
      ⊢  est_isomorphisme_ordre(φ⁻¹, T, S, R', R).

Binders SAINS x,w (le second binder « y » empoisonnerait fy=valeur(φ,var y) par
auto-capture τ_y) — forme fidèle non poisonnée de la définition E.III.1.3.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    est_isomorphisme_ordre, compatible_ordre)
from bourbaki.cardinaux.ensembles_iso_ordre_reciproque import (
    section_reciproque, compatible_ordre_reciproque,
    reciproque_isomorphisme_ordre, cible_reciproque_isomorphisme_ordre,
    _R_defaut)


def _R():
    return _R_defaut("G")


def _Rp():
    return _R_defaut("Gp")


def test_theorie_intacte_22():
    """theorie_ensembles() reste à 22 axiomes (INTANGIBLE) après import du module."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_section_reciproque():
    """{ φ func, dom(φ⁻¹)=T, x∈T } ⊢ φ(φ⁻¹(x)) = x   (φ∘φ⁻¹ = Id_T, point x∈T)."""
    vphi, vT = var("phi"), var("T")
    t = section_reciproque("phi", "x", "T")
    finv_x = E.valeur(E.reciproque(vphi), var("x"))
    phi_finv_x = E.valeur(vphi, finv_x)
    assert t.conclusion == egal(phi_finv_x, var("x"))
    assert t.hypotheses == {
        E.est_fonctionnel(vphi),
        egal(E.dom(E.reciproque(vphi)), vT),
        appartient(var("x"), vT),
    }


def test_compatible_ordre_reciproque():
    """compatible_ordre(φ⁻¹,T,R',R) [binders x,w], hyps = func, dom φ=S,
    compatible_ordre(φ,S,R,R')[x,w], dom φ⁻¹=T."""
    vphi, vS, vT = var("phi"), var("S"), var("T")
    R, Rp = _R(), _Rp()
    t = compatible_ordre_reciproque("phi", "S", "T", R, Rp)
    cible = compatible_ordre(E.reciproque(vphi), vT, Rp, R, x="x", y="w")
    assert t.conclusion == cible
    assert t.hypotheses == {
        E.est_fonctionnel(vphi),
        egal(E.dom(vphi), vS),
        compatible_ordre(vphi, vS, R, Rp, x="x", y="w"),
        egal(E.dom(E.reciproque(vphi)), vT),
    }


def test_reciproque_isomorphisme_ordre_conclusion():
    """La conclusion est EXACTEMENT est_isomorphisme_ordre(φ⁻¹, T, S, R', R)."""
    t = reciproque_isomorphisme_ordre("phi", "S", "T")
    assert t.conclusion == cible_reciproque_isomorphisme_ordre("phi", "S", "T")


def test_reciproque_isomorphisme_ordre_hypotheses():
    """Hypothèses du séquent = EXACTEMENT { iso(φ,S,T,R,R'), φ func, dom φ=S }.

    Théorème CONDITIONNEL fidèle : le pont 2→4 conjoints (est_isomorphisme_ordre
    ne porte que est_bijective) est bouclé par func + dom=S, hypothèses VRAIES pour
    tout iso d'ordre représenté par un graphe d'application."""
    vphi, vS, vT = var("phi"), var("S"), var("T")
    R, Rp = _R(), _Rp()
    t = reciproque_isomorphisme_ordre("phi", "S", "T")
    attendu = {
        est_isomorphisme_ordre(vphi, vS, vT, R, Rp, x="x", y="w"),
        E.est_fonctionnel(vphi),
        egal(E.dom(vphi), vS),
    }
    assert t.hypotheses == attendu


def test_reciproque_isomorphisme_ordre_non_trivial():
    """Anti-tautologie : la conclusion N'EST PAS une des hypothèses (et n'est pas
    triviale).  L'iso de φ⁻¹ porte sur φ⁻¹, T, S, R', R — distinct de l'hyp iso(φ,…)."""
    t = reciproque_isomorphisme_ordre("phi", "S", "T")
    assert t.conclusion not in t.hypotheses
