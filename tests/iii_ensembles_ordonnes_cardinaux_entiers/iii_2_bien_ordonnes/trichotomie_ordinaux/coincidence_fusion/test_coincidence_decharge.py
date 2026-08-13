"""Tests §III.2 — Lemme 1 (témoins communs) : DÉCHARGE de la géométrie de
`coincidence_sur_chevauchement` via le KEYSTONE (composée / réciproque d'iso d'ordre).

Certifie que `ensembles_coincidence_decharge` livre :

  ✅ auto_de_deux_isos       : { iso(φ,S,T,R,R'), iso(ψ,T,S,R',R), func/dom φ,ψ }
                                  ⊢ est_isomorphisme_ordre(ψ∘φ, S, S, R, R)
     — CONSTRUIT (keystone), c=ψ∘φ est un AUTOMORPHISME d'ordre de (S,R).
  ✅ psi_est_reciproque_de   : { iso(φ',S,T,R,R'), func/dom φ' } ⊢ iso(φ'⁻¹, T, S, R', R)
     — PONT ψ:=φ'⁻¹ (réciproque, keystone) : l'hyp « ψ:T≅S » d'auto_de_deux_isos est livrée.
  ⚠️ coincidence_depuis_isos : consomme les isos pour ATTESTER iso(c,S,S,R,R) +
                                iso(k,S,S,R,R), chaîne coincidence ⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))
     — CONDITIONNEL (résidu b="yv" + rétractions REPORTÉ).

Aucune conclusion n'est tautologie / postulée ; theorie=22 ; aucun fichier modifié.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (
    est_isomorphisme_ordre, compatible_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.coincidence_fusion import ensembles_coincidence_decharge as D
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences.ensembles_trichotomie_restriction import (
    coincidence_sur_chevauchement,
)


def _R(nom):
    return lambda a, b: appartient(E.couple(a, b), var(nom))


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR — c = ψ∘φ est un AUTOMORPHISME d'ordre de (S,R)  (CONSTRUIT via keystone)
# ════════════════════════════════════════════════════════════════════════════
def test_auto_de_deux_isos_conclusion():
    """⊢ est_isomorphisme_ordre(ψ∘φ, S, S, R, R)  (conclusion == cible)."""
    a = D.auto_de_deux_isos()
    assert not a.est_clos
    assert a.conclusion == D.auto_de_deux_isos_cible()
    assert a.conclusion not in a.hypotheses           # non tautologique


def test_auto_de_deux_isos_est_conjonction_substantielle():
    """La conclusion est RÉELLEMENT « bijective ET compatible_ordre » (pas affaiblie)."""
    a = D.auto_de_deux_isos()
    R = _R("G")
    c = E.composee(var("psi"), var("phi"))
    co = compatible_ordre(c, var("S"), R, R, "x", "x2")
    assert a.conclusion == et(E.est_bijective(c, var("S"), var("S")), co)


def test_auto_de_deux_isos_hypotheses_exactes():
    """Les 6 hyps sont EXACTEMENT les deux isos + fonctionnel/dom de φ et ψ."""
    a = D.auto_de_deux_isos()
    R, Rp = _R("G"), _R("Gp")
    expected = {
        est_isomorphisme_ordre(var("psi"), var("T"), var("S"), Rp, R, "x", "x2"),
        est_isomorphisme_ordre(var("phi"), var("S"), var("T"), R, Rp, "x", "x2"),
        E.est_fonctionnel(var("phi")),
        egal(E.dom(var("phi")), var("S")),
        E.est_fonctionnel(var("psi")),
        egal(E.dom(var("psi")), var("T")),
    }
    assert set(a.hypotheses) == expected
    assert len(a.hypotheses) == 6
    # les DEUX isos sont réellement consommés (cœur du témoin commun)
    assert est_isomorphisme_ordre(var("phi"), var("S"), var("T"), R, Rp, "x", "x2") in a.hypotheses
    assert est_isomorphisme_ordre(var("psi"), var("T"), var("S"), Rp, R, "x", "x2") in a.hypotheses


def test_auto_de_deux_isos_parametrable():
    a = D.auto_de_deux_isos("f", "g", "A", "B", "Ga", "Gb")
    assert len(a.hypotheses) == 6
    assert a.conclusion == D.auto_de_deux_isos_cible("f", "g", "A", "B", "Ga", "Gb")


# ════════════════════════════════════════════════════════════════════════════
#  PONT  ψ = φ'⁻¹  (l'hyp « ψ:T≅S » est livrée par la réciproque de φ')
# ════════════════════════════════════════════════════════════════════════════
def test_psi_est_reciproque_de_conclusion():
    """⊢ est_isomorphisme_ordre(φ'⁻¹, T, S, R', R)  (réciproque, keystone)."""
    p = D.psi_est_reciproque_de()
    assert not p.est_clos
    assert p.conclusion == D.psi_est_reciproque_de_cible()
    assert p.conclusion not in p.hypotheses


def test_psi_est_reciproque_de_livre_iso_reciproque():
    """La conclusion est l'iso de φ'⁻¹ : T≅S (= ce qu'auto_de_deux_isos attend pour ψ)."""
    p = D.psi_est_reciproque_de()
    R, Rp = _R("G"), _R("Gp")
    assert p.conclusion == est_isomorphisme_ordre(
        E.reciproque(var("phip")), var("T"), var("S"), Rp, R, x="x", y="w")


def test_psi_est_reciproque_de_trois_hyps():
    """Exactement { iso(φ',S,T,R,R'), φ' fonctionnel, dom φ'=S }."""
    p = D.psi_est_reciproque_de()
    assert len(p.hypotheses) == 3
    assert egal(E.dom(var("phip")), var("S")) in p.hypotheses
    assert E.est_fonctionnel(var("phip")) in p.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE CONDITIONNEL — coïncidence depuis les deux isos.
# ════════════════════════════════════════════════════════════════════════════
def test_coincidence_depuis_isos_conclusion():
    """⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))  (conclusion == cible de coincidence)."""
    ci = D.coincidence_depuis_isos()
    assert not ci.est_clos
    assert ci.conclusion == D.coincidence_depuis_isos_cible()
    assert ci.conclusion not in ci.hypotheses         # non tautologique : φ=φ' n'est pas une hyp


def test_coincidence_depuis_isos_consomme_les_temoins():
    """Le séquent porte BIEN les deux isos (témoins c,k automorphismes) ET la
    géométrie de coincidence — la chaîne fidèle est réelle (rien postulé)."""
    ci = D.coincidence_depuis_isos()
    H = set(ci.hypotheses)
    R, Rp = _R("G"), _R("Gp")
    # témoin c = ψ∘φ : les deux isos qui le construisent sont dans le séquent
    assert est_isomorphisme_ordre(var("phi"), var("S"), var("T"), R, Rp, "x", "x2") in H
    assert est_isomorphisme_ordre(var("psi"), var("T"), var("S"), Rp, R, "x", "x2") in H
    # témoin k = χ∘φ' : idem
    assert est_isomorphisme_ordre(var("phip"), var("S"), var("T"), R, Rp, "x", "x2") in H
    assert est_isomorphisme_ordre(var("chi"), var("T"), var("S"), Rp, R, "x", "x2") in H


def test_coincidence_depuis_isos_porte_la_geometrie_coincidence():
    """Le séquent contient EXACTEMENT l'union { hyps iso(c), hyps iso(k), hyps coincidence }."""
    ci = D.coincidence_depuis_isos()
    H = set(ci.hypotheses)
    iso_c = D.auto_de_deux_isos("phi", "psi", "S", "T", "G", "Gp")
    iso_k = D.auto_de_deux_isos("phip", "chi", "S", "T", "G", "Gp")
    coinc = coincidence_sur_chevauchement("R", "S", "phi", "phip", "c", "k", "u")
    union = set(iso_c.hypotheses) | set(iso_k.hypotheses) | set(coinc.hypotheses)
    assert H == union
    # la géométrie b="yv" de coincidence est réellement portée (chaînage non vacueux)
    assert set(coinc.hypotheses).issubset(H)


def test_coincidence_depuis_isos_parametrable():
    ci = D.coincidence_depuis_isos("f", "fp", "g", "h", "A", "B", "cc", "kk", "v",
                                   "Ga", "Gb")
    assert ci.conclusion == D.coincidence_depuis_isos_cible(
        "f", "fp", "g", "h", "A", "B", "cc", "kk", "v", "Ga", "Gb")
    assert ci.conclusion not in ci.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT — theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_inchangee_22():
    """theorie_ensembles reste à 22 axiomes (aucun axiome postulé)."""
    D.auto_de_deux_isos()
    D.psi_est_reciproque_de()
    D.coincidence_depuis_isos()
    assert len(E.theorie_ensembles().axiomes) == 22
