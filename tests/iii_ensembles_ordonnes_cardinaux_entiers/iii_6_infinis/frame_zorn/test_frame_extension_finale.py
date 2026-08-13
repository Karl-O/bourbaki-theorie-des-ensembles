"""Tests — §III.6.3 Hessenberg, EXTENSION FINALE du maximal (E.III.48-49).

Vérifie les pièces de l'argument « CLAIM : Card(S₀)=Card(E) ⇒ a²=a » :
  • cadre_bijection            (CLOS, 0 hyp)
  • cadre_card_trois_b         (hyps honnêtes : Card S₀=Card U, 𝔟²=𝔟, card/inf)
  • phi_etendue_bijection      (recollement bij. ; func+inj dérivés, dom/img honnêtes)
  • extension_dans_frame       (frame-membership (Z,φ₁)∈𝔉 ; hyps honnêtes)
  • extension_ordre            ((p,q)∈Γ𝔉 ; hyps honnêtes)
  • extension_force_egalite    (maximalité ⇒ Z=S₀ ; hyps honnêtes)
  • extension_absurde          (Z=S₀ + U≠∅ + U∩S₀=∅ ⇒ ⊥ ; hyps honnêtes)

INVARIANT : theorie_ensembles() == 22 ; conclusion ∉ hyps (non vacuous).
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_extension_finale import (
    cadre_bijection, cadre_bijection_cible,
    cadre_card_trois_b, cadre_card_trois_b_cible,
    phi_etendue_bijection, extension_dans_frame, extension_ordre,
    extension_force_egalite, extension_absurde,
    card_S0_egal_card_E, card_S0_egal_card_E_cible,
    hessenberg_a_carre_egal_a,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cadre_bijection_clos():
    r = cadre_bijection()
    assert r.est_clos
    assert r.conclusion == cadre_bijection_cible()
    assert r.conclusion not in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cadre_card_trois_b():
    r = cadre_card_trois_b()
    assert r.conclusion == cadre_card_trois_b_cible()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1     # hyps honnêtes
    assert len(E.theorie_ensembles().axiomes) == 22


def test_phi_etendue_bijection():
    r = phi_etendue_bijection()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extension_dans_frame():
    r = extension_dans_frame()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extension_ordre():
    r = extension_ordre()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extension_force_egalite():
    r = extension_force_egalite()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extension_absurde():
    r = extension_absurde()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_card_S0_egal_card_E():
    r = card_S0_egal_card_E()
    assert r.conclusion == card_S0_egal_card_E_cible()
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hessenberg_a_carre_egal_a():
    r = hessenberg_a_carre_egal_a()
    assert r.conclusion == enonce_hessenberg("E")     # est_infini(Card E)⇒CardE·CardE=CardE
    assert r.conclusion not in r.hypotheses
    assert len(r.hypotheses) >= 1                      # résidus honnêtes
    assert len(E.theorie_ensembles().axiomes) == 22
