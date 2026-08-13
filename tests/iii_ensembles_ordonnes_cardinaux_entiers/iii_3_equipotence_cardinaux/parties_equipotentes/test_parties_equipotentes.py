"""Tests Résumé §7.1 — Eq(E,F)⇒Eq(𝔓E,𝔓F) : fondation (témoin H = A↦f⟨A⟩)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal, var
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.parties_equipotentes.ensembles_parties_equipotentes as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pilier1_H_fonctionnel():
    th = M.H_fonctionnel()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == E.est_fonctionnel(M.graphe_H())


def test_pilier2_H_domaine():
    th = M.H_domaine()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == egal(E.dom(M.graphe_H()), E.parties(var("E")))


def test_H_valeur():
    """{Y0∈𝔓E} ⊢ H(Y0) = f⟨Y0⟩."""
    th = M.H_valeur()
    assert len(th.hypotheses) == 1           # Y0 ∈ 𝔓(E)
    assert th.conclusion == M.cible_H_valeur()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pilier3_H_injective():
    """⊢ H_app(E,f) ⇒ est_fonctionnel(f⁻¹) ⇒ injective_dans(H, 𝔓E)."""
    th = M.H_injective()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_H_injective()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pilier4_H_image():
    """⊢ est_fonctionnel(f) ⇒ dom f=E ⇒ f⟨E⟩=F ⇒ image(H, 𝔓E) = 𝔓F  (surjectivité de H)."""
    th = M.H_image()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_H_image()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equipotent_parties():
    """THÉORÈME (Résumé §7.1) : ⊢ Eq(E,G) ⇒ Eq(𝔓E, 𝔓G)  (assemblage des 4 piliers)."""
    th = M.equipotent_parties()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == M.cible_equipotent_parties()
    assert len(E.theorie_ensembles().axiomes) == 22
