"""§II.5 — PROPOSITION 8, formule (1), PREMIÈRE INCLUSION (sens ⊂, E II.35–36) :
    (∃i)(i∈I) ⇒ ⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) ⊂ ⋂_{f∈I}(⋃_{λ∈L}X_{λ,f(λ)}),  I=∏_{λ∈L}J_λ.

Inclusion DIRECTE ponctuelle seule ; réciproque (choix) hors cible.  Le test APPELLE
le théorème et vérifie : conclusion == cible construite indépendamment avec les
constructeurs E.*, clôture (0 hyp), et theorie_ensembles() == 22 axiomes.

MISE À JOUR (2026-07-26) — MIGRATION « ⋂ = sélection dans ⋃ ».  Ces tests encodaient
l'énoncé SANS hypothèse : `attendu = pourtout("z", impl(z∈gauche, z∈droite))`.  Cet
énoncé n'était démontrable que via l'ANCIEN AXIOME_INTER_FAM, qui était CONTRADICTOIRE
(il peuplait ⋂ sur un ensemble d'indices vide de tout objet, contredisant
`pas_ensemble_universel`).  Avec l'axiome réparé, ⋂_{f∈∅}(…) = ∅ et l'inclusion est
FAUSSE pour I = ∅ : le membre gauche ⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) n'a aucune raison
d'être vide.  L'énoncé porte donc désormais l'antécédent « I ≠ ∅ », sous la forme
(∃i)(i∈I) — hypothèse que la Proposition 8 écrit noir sur blanc (E II.35 : « Soit
I = ∏_{λ∈L} J_λ ≠ ∅ »).  C'est un RENFORCEMENT D'ÉNONCÉ, donc un GAIN de fidélité au
livre : le test suit l'énoncé, pas l'inverse.
"""
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_6_7_algebre_produit import (
    ensembles_prop8_distrib_directe_ii5 as M)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl, appartient, pourtout, inclus


def _membres_independants():
    """(gauche, droite, I) reconstruits à la main avec les MÊMES constructeurs E.*
    que le module (GL, GR = familles externes définies par `theorie_distrib`)."""
    vJ, vL = var("J"), var("L")
    vGL, vGR = var("GL"), var("GR")
    vI = E.produit_famille(vJ, vL)                 # I = ∏_{λ∈L} J_λ
    return E.reunion_famille(vGL, vL), E.inter_famille(vGR, vI), vI


def _cible_independante():
    """(∃i)(i∈I) ⇒ ⋃_{λ∈L}(⋂_{ι∈J_λ}X_{λ,ι}) ⊂ ⋂_{f∈I}(⋃_{λ∈L}X_{λ,f(λ)}).

    L'antécédent est l'hypothèse « I ≠ ∅ » de la Proposition 8 (cf. docstring du
    module) : sans lui l'inclusion est fausse pour I = ∅."""
    gauche, droite, vI = _membres_independants()
    return impl(indices_non_vides(vI), inclus(gauche, droite))


def test_distributivite_inclusion_directe_close():
    th = M.distributivite_reunion_inter_inclusion_directe()
    # clôture : 0 hypothèse pendante — l'hypothèse « I ≠ ∅ » est DÉCHARGÉE en
    # antécédent (loi de déduction), elle ne reste donc pas au compteur.
    assert th.est_clos is True
    assert th.hypotheses == frozenset()
    # conclusion == cible (construction indépendante avec E.*)
    assert th.conclusion == _cible_independante()
    assert th.conclusion == M._cible()
    # invariant : théorie des ensembles inchangée (22 axiomes)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cible_est_une_inclusion_pointwise():
    """La cible est bien (∃i)(i∈I) ⇒ (∀z)(z∈gauche ⇒ z∈droite) — forme close."""
    th = M.distributivite_reunion_inter_inclusion_directe()
    c = th.conclusion
    # inclus(A,B) = pourtout("z", impl(z∈A, z∈B)) = non(existe("z", non(...)))
    # on vérifie la structure via la cible reconstruite
    gauche, droite, vI = _membres_independants()
    attendu = impl(indices_non_vides(vI),
                   pourtout("z", impl(appartient(var("z"), gauche),
                                      appartient(var("z"), droite))))
    assert c == attendu


def test_hypothese_I_non_vide_est_bien_l_antecedent():
    """L'hypothèse ajoutée par la migration est EXACTEMENT (∃i)(i ∈ ∏_{λ∈L}J_λ).

    Test neuf : il rend visible, et donc auditable, le RENFORCEMENT d'énoncé — le
    conséquent, lui, est verbatim l'ancienne cible (inclusion ponctuelle)."""
    gauche, droite, vI = _membres_independants()
    assert M._hyp_I_non_vide() == indices_non_vides(vI)
    ancienne_cible = inclus(gauche, droite)
    th = M.distributivite_reunion_inter_inclusion_directe()
    # impl(P,Q) = ou(non P, Q) : le conséquent est le 2e sous-terme du « ou »
    assert th.conclusion.sous[1] == ancienne_cible
