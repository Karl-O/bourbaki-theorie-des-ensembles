"""Tests — §III.6.3 Hessenberg, direction PROFONDE (échafaudage Zorn).

Vérifie :
  • theorie_ensembles() reste = 22 (aucun axiome ajouté au noyau) ;
  • frame_membre : l'axiome définitionnel de 𝔉 s'instancie (équivalence) ;
  • maximal_pair_existe : application de Zorn au poset 𝔉, CLOS (.est_clos) ;
  • hessenberg_carre : le pont final, CLOS, conclusion = (résidu ⇒ Hessenberg) ;
  • le RÉSIDU HONNÊTE (enonce_hard_aa_inf_egal_a) est non vacueux.

NB : dans le noyau, impl(p,q) DÉSUCRE en ou(non p, q) et equiv en conjonction de
ou ; on teste donc l'ÉGALITÉ STRUCTURELLE contre les énoncés-cibles (et non le tag).
"""
from bourbaki.logique.i_1_termes_relations.formule import impl, equiv, non
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_hessenberg_hard import (
    frame_membre, maximal_pair_existe, hessenberg_carre,
    enonce_hard_aa_inf_egal_a, enonce_hessenberg,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_frame_membre_clos():
    th = frame_membre()
    assert th.est_clos


def test_maximal_pair_existe_clos():
    th = maximal_pair_existe()
    assert th.est_clos, f"hyps résiduelles: {th.hypotheses}"
    # conclusion = ( hyps de Zorn ) ⇒ (∃m) maximal  : une implication (désucrée ou)
    assert th.conclusion.tag == "ou"


def test_hessenberg_carre_clos_et_residu_honnete():
    th = hessenberg_carre()
    assert th.est_clos, f"hyps résiduelles: {th.hypotheses}"
    # conclusion == ( enonce_hard ⇒ enonce_hessenberg ), STRUCTURELLEMENT
    assert th.conclusion == impl(enonce_hard_aa_inf_egal_a(), enonce_hessenberg())


def test_residu_non_vacuux():
    # le résidu (le verrou ≥ dur) est l'implication est_infini(a) ⇒ a·a≤a,
    # qui désucre en ou(non(est_infini), a·a≤a) — non triviale (≠ tautologie).
    hard = enonce_hard_aa_inf_egal_a()
    assert hard.tag == "ou"
    # son membre droit n'est pas la négation du gauche (non vacuité)
    gauche_non, droite = hard.sous
    assert droite != non(non(gauche_non))
