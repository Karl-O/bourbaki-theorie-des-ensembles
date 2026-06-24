"""§II.5 — PROPOSITION 8, formule (1), PREMIÈRE INCLUSION (sens ⊂, E II.35–36) :
    ⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) ⊂ ⋂_{f∈I}(⋃_{λ∈L}X_{λ,f(λ)}),  I=∏_{λ∈L}J_λ.

Inclusion DIRECTE ponctuelle seule ; réciproque (choix) hors cible.  Le test APPELLE
le théorème et vérifie : conclusion == cible construite indépendamment avec les
constructeurs E.*, clôture (0 hyp), et theorie_ensembles() == 22 axiomes."""
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit import (
    ensembles_prop8_distrib_directe_ii5 as M)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, et, impl, appartient, pourtout, inclus


def _cible_independante():
    """⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) ⊂ ⋂_{f∈I}(⋃_{λ∈L}X_{λ,f(λ)}) reconstruite à la main
    avec les MÊMES constructeurs E.* que la fonction (GL, GR familles externes)."""
    vXX, vJ, vL = var("XX"), var("J"), var("L")
    vGL, vGR = var("GL"), var("GR")
    gauche = E.reunion_famille(vGL, vL)
    droite = E.inter_famille(vGR, E.produit_famille(vJ, vL))
    return inclus(gauche, droite)


def test_distributivite_inclusion_directe_close():
    th = M.distributivite_reunion_inter_inclusion_directe()
    # clôture : 0 hypothèse pendante
    assert th.est_clos is True
    assert th.hypotheses == frozenset()
    # conclusion == cible (construction indépendante avec E.*)
    assert th.conclusion == _cible_independante()
    assert th.conclusion == M._cible()
    # invariant : théorie des ensembles inchangée (22 axiomes)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cible_est_une_inclusion_pointwise():
    """La cible est bien (∀z)(z∈gauche ⇒ z∈droite) — forme close inclusion."""
    th = M.distributivite_reunion_inter_inclusion_directe()
    c = th.conclusion
    # inclus(A,B) = pourtout("z", impl(z∈A, z∈B)) = non(existe("z", non(...)))
    # on vérifie la structure via la cible reconstruite
    vXX, vJ, vL = var("XX"), var("J"), var("L")
    vGL, vGR = var("GL"), var("GR")
    gauche = E.reunion_famille(vGL, vL)
    droite = E.inter_famille(vGR, E.produit_famille(vJ, vL))
    attendu = pourtout("z", impl(appartient(var("z"), gauche),
                                 appartient(var("z"), droite)))
    assert c == attendu
