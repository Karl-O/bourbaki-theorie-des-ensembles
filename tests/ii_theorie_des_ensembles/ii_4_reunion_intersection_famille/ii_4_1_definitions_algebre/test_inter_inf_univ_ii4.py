# -*- coding: utf-8 -*-
"""Test §II.4 — propriété universelle (inf) de l'intersection d'une famille.

MISE À JOUR (migration Déf. 2 : ⋂ défini par SÉLECTION dans ⋃, 2026-07).
Ce test assertait auparavant que l'équivalence

        ( A ⊂ ⋂_{ι∈I} X_ι ) ⟺ ( (∀k)(k∈I ⇒ A ⊂ X_k) )

était démontrable SANS hypothèse.  Ce n'était pas une propriété du livre mais un
artefact de l'ancien AXIOME_INTER_FAM, posé sans la restriction « I ≠ ∅ » de la
Déf. 2 (E II.22) et donc CONTRADICTOIRE.  Avec la Déf. 2 réparée, ⋂_{ι∈∅} X_ι = ∅
et le sens « ⇐ » est FAUX pour I = ∅ et A ≠ ∅.  L'énoncé a donc légitimement
CHANGÉ (renforcement) et c'est le test qui suit l'énoncé :
  • `inter_inf_minorante`   : sens « ⇒ », INCONDITIONNEL, énoncé INCHANGÉ ;
  • `inter_inf_universelle` : équivalence sous l'hypothèse (∃i)(i∈I) du livre.
Les deux restent CLOS (0 hypothèse non déchargée) et la théorie reste à 22 axiomes.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, impl, equiv)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_inter_inf_univ_ii4 import (
    _membres, inter_inf_minorante, cible_inter_inf_minorante,
    inter_inf_universelle, cible_inter_inf_universelle)


def test_inter_inf_minorante_close():
    """Sens « ⇒ » : ⋂ est un minorant de la famille — SANS hypothèse (inchangé)."""
    thm = inter_inf_minorante()
    assert thm.est_clos
    assert thm.hypotheses == frozenset()
    assert thm.conclusion == cible_inter_inf_minorante()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inter_inf_universelle_close():
    """Équivalence complète, désormais sous l'hypothèse « I n'est pas vide »."""
    thm = inter_inf_universelle()
    assert thm.est_clos
    assert thm.hypotheses == frozenset()
    assert thm.conclusion == cible_inter_inf_universelle()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hypothese_ajoutee_est_en_antecedent_et_non_au_compteur():
    """Garde-fou d'HONNÊTETÉ du renforcement d'énoncé (issue B).

    La conclusion doit être exactement  impl( (∃i)(i∈I), equiv(gauche, droite) ) :
    l'hypothèse de la Déf. 2 est PORTÉE PAR L'ÉNONCÉ (antécédent), et non passée
    sous silence ni laissée en hypothèse non déchargée.  Ce test échouerait si
    quelqu'un « simplifiait » l'énoncé pour retrouver la forme (fausse) d'avant."""
    gauche, droite = _membres(var("X"), var("I"), var("A"))
    attendu = impl(indices_non_vides(var("I")), equiv(gauche, droite))
    assert cible_inter_inf_universelle() == attendu
    assert inter_inf_universelle().conclusion == attendu
    # L'ancienne cible (équivalence NUE, sans antécédent) n'est plus l'énoncé.
    assert cible_inter_inf_universelle() != equiv(gauche, droite)
