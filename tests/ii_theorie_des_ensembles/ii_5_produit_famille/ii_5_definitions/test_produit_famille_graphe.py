"""Tests §II.5.3 Déf.1 — témoins sur {∅} pour le conjoint « graphe » du produit.

Chaque énoncé est RECONSTRUIT À LA MAIN ici (hors du module testé) et comparé par
égalité EXACTE ; les hypothèses sont assertées par égalité de frozenset ;
theorie_ensembles() vaut 22 avant ET après.  Un test qui vérifierait seulement
« ça construit » ne verrouillerait rien.

⚠️ HISTORIQUE.  Ce fichier testait, jusqu'au 2026-07-26, le CONTRE-THÉORÈME
`produit_vide_n_est_pas_singleton` (⊢ ¬(∏(u,∅)={∅})) et la RÉFUTATION de H-graphe.
Ces deux résultats étaient des théorèmes du DÉFAUT de `AXIOME_PRODUIT_FAM` (conjoint
« F ⊂ I × ⋃X_ι » perdu à la transcription).  L'axiome ayant été RÉPARÉ, ils ne sont
plus démontrables — et devaient disparaître : H-graphe est désormais un THÉORÈME
(`produit_graphe`), sa réfutation aurait rendu la théorie incohérente.  Ils sont
remplacés ici par leur MIROIR positif `test_singleton_vide_hors_produit_vide`.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, non, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille_graphe import (
    singleton_vide, singleton_gauche_dans_couple, singleton_vide_est_fonctionnel,
    dom_singleton_vide_est_vide, singleton_vide_different_du_vide,
    singleton_vide_hors_produit_vide,
)

U = var("upfg")                                   # famille QUELCONQUE
S_MAIN = E.paire(E.VIDE, E.VIDE)                  # {∅} reconstruit à la main
PROD = E.produit_famille(U, E.VIDE)


def test_invariant_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_singleton_vide_est_bien_le_singleton_du_vide():
    """Le témoin est {∅} = paire(∅,∅) — reconstruit à la main."""
    assert singleton_vide() == S_MAIN == E.singleton(E.VIDE)
    assert singleton_vide() != E.VIDE


def test_singleton_gauche_dans_couple():
    """⊢ {a} ∈ (a,b)  — c'est ce qui rend un couple non vide."""
    thm = singleton_gauche_dans_couple("a", "b")
    va, vb = var("a"), var("b")
    assert thm.conclusion == appartient(E.paire(va, va), E.couple(va, vb))
    assert thm.est_clos and thm.hypotheses == frozenset()


def test_singleton_vide_est_fonctionnel():
    """⊢ est_fonctionnel({∅})  — vacuement : {∅} ne contient aucun couple.

    C'est LA mesure qui montre que `est_fonctionnel` seule ne code PAS la Déf. 1 :
    elle laisse passer un ensemble qui n'est pas un graphe."""
    thm = singleton_vide_est_fonctionnel()
    vu, vv, vz = var("u"), var("v"), var("z")
    attendu = pourtout("u", pourtout("v", pourtout("z", impl(
        et(appartient(E.couple(vu, vv), S_MAIN), appartient(E.couple(vu, vz), S_MAIN)),
        egal(vv, vz)))))
    assert thm.conclusion == attendu
    assert thm.conclusion == E.est_fonctionnel(S_MAIN)
    assert thm.est_clos and thm.hypotheses == frozenset()


def test_dom_singleton_vide_est_vide():
    """⊢ dom({∅}) = ∅  — reconstruit à la main."""
    thm = dom_singleton_vide_est_vide()
    assert thm.conclusion == egal(E.dom(S_MAIN), E.VIDE)
    assert thm.est_clos and thm.hypotheses == frozenset()


def test_singleton_vide_different_du_vide():
    thm = singleton_vide_different_du_vide()
    assert thm.conclusion == non(egal(S_MAIN, E.VIDE))
    assert thm.est_clos and thm.hypotheses == frozenset()


def test_le_bruit_satisfait_les_trois_anciens_conjoints():
    """MESURE de ce que la réparation était NÉCESSAIRE, sans rien postuler.

    {∅} vérifie est_fonctionnel ET dom = ∅ (deux théorèmes CLOS ci-dessus) ; la
    3ᵉ condition de l'ancien encodage est vide pour I = ∅.  Les trois conjoints
    conservés ne suffisaient donc PAS à l'exclure : seul le conjoint de tête
    « F ⊂ I × ⋃X_ι » le fait (cf. `test_singleton_vide_hors_produit_vide`)."""
    assert singleton_vide_est_fonctionnel().est_clos
    assert dom_singleton_vide_est_vide().est_clos
    n_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)
    assert n_vide.est_clos                     # (∀z)¬(z∈∅) : la 3ᵉ clause est vacuous


def test_singleton_vide_hors_produit_vide():
    """🎯 ⊢ ¬( {∅} ∈ ∏(u,∅) ) SOUS LES 22 AXIOMES SEULS — le bruit est EXCLU.

    C'est la mesure, dans le formalisme, que le conjoint de tête rétabli fait son
    travail : {∅} vérifie toujours les trois autres conjoints (cf. le test
    ci-dessus), et n'est plus élément du produit vide.  Le corpus cesse ainsi de
    contredire E II.32.  Cible RECONSTRUITE À LA MAIN."""
    thm = singleton_vide_hors_produit_vide(U)
    assert thm.conclusion == non(appartient(S_MAIN, PROD))
    assert thm.est_clos, "le théorème DOIT être clos, sinon il ne mesure rien"
    assert thm.hypotheses == frozenset()


def test_invariant_22_axiomes_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
