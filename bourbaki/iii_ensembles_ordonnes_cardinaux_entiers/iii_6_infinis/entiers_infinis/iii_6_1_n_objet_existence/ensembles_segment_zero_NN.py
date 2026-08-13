"""§III.6.1 — « RIEN AVANT 0 » DANS ℕ :  seg(≤_G, ℕ, 0) = ∅.       [CLOS, 0 hyp]

  🎯 segment_zero_NN_est_vide() : ⊢ seg( ≤_G , ℕ , 0 ) = ∅
  🎯 plus_petit_element_zero_NN() : ⊢ est_plus_petit_element( ≤_G , ℕ , 0 )

Le segment initial OUVERT de 0 dans ℕ — l'ensemble des entiers STRICTEMENT
inférieurs à 0 — est vide.  C'est la « donnée de position » de la récursion C62 :
c'est elle qui fait démarrer toute définition par récurrence sur ℕ (le cas de base
n'a aucun prédécesseur à consulter), et c'est le terme d'indice de la famille
(i+1)_{i<n} de la Déf. 2 de la factorielle prise en n = 0.

────────────────────────────────────────────────────────────────────────────────
ROUTE (uniquement des briques CLOSES déjà au dépôt — rien postulé) :
  (1) 0 minore ℕ :  pour x ∈ ℕ,  x est fini (appartenance_NN_instanciee)
      ⇒ x est un cardinal (fini_implique_cardinal) ⇒ 0 ≤ x (_zero_le_terme) ;
      avec 0 ∈ ℕ (zero_dans_NN [CLOS]) et x ∈ ℕ, on reconstruit LITTÉRALEMENT
      ordre_induit_NN(0, x), donc (0,x) ∈ G_ordre_NN (couple_dans_G_ordre) ;
      ∀-clôture sur le liant « x » — celui de est_plus_petit_element.
  (2) 0 est donc le plus petit élément de ℕ  (conjonction avec 0 ∈ ℕ).
  (3) segment_du_plus_petit_est_vide (§III.2.1) conclut, ses DEUX hypothèses étant
      déchargées : « ℕ bien ordonné » par bo_graphe_NN [CLOS], « 0 plus petit »
      par (2).

⚠️ CORRECTION D'UNE ANNOTATION PÉRIMÉE.  Le journal de campagne notait « sur
(E,G) la donnée "rien avant 0" N'EST PAS dérivable ⇒ la mettre en hypothèse ».
C'est vrai sur des VARIABLES (E, G) quelconques, et FAUX sur les TERMES ℕ et
G_ordre_NN : ici la donnée est dérivable ET close.  Toute annotation « pas
dérivable » écrite avant bo_graphe_NN est à re-tester sur les termes concrets.

⚠️ PERF : le premier contact avec ensemble_NN() déclenche N_existe (~3 min,
mémoïsé par session) — le test miroir est marqué `slow`.

INVARIANT : theorie_ensembles() = 22.  Noyau et subst intouchés.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments.ensembles_segment_minimum import (
    segment_du_plus_petit_est_vide,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, zero_dans_NN, appartenance_NN_instanciee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN, couple_dans_G_ordre, bo_graphe_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_n_bien_ordonne import (
    ordre_induit_NN, _zero_le_terme,
)

#: Liant de est_plus_petit_element / du minorant universel (imposé par l'abrégé).
_LIANT = "x"


def graphe_ordre_NN():
    """R := ≤_G, l'ordre de ℕ sous la forme attendue par les segments.

    ⚠️ `_graphe_R` rend un CONSTRUCTEUR de relation (lambda), pas un Terme : il
    n'est pas comparable par == ; seuls les TERMES qu'il produit le sont."""
    return _graphe_R(G_ordre_NN())


def segment_zero_NN():
    """Le terme  seg( ≤_G , ℕ , 0 )  = [0,0[  — l'indice de la Déf. 2 en n = 0."""
    return E.segment_extremite(G_ordre_NN(), ensemble_NN(), ZERO)


# @livre Ch.III §6.1 Rem.- | E III.45 L.23-24 | PDF p.148  (« Quand on considère N comme ensemble ordonné, il s'agit toujours de l'ordre (dit usuel) » : 0 est le plus petit élément de ℕ pour CET ordre, sur le ℕ concret ensemble_NN)
def plus_petit_element_zero_NN():
    """⊢ est_plus_petit_element( ≤_G , ℕ , 0 ).                     [CLOS, 0 hyp]

    0 ∈ ℕ (zero_dans_NN) et 0 minore ℕ : tout x ∈ ℕ est fini, donc cardinal, donc
    0 ≤ x ; le triplet (0≤x, 0∈ℕ, x∈ℕ) EST littéralement ordre_induit_NN(0,x),
    que couple_dans_G_ordre transporte en (0,x) ∈ G_ordre_NN."""
    NN = ensemble_NN()
    vx = var(_LIANT)
    z0 = zero_dans_NN()                                       # 0 ∈ ℕ            [CLOS]
    h_x = N.assume(appartient(vx, NN))
    fini_x = N.modus_ponens(h_x, equivalence_avant(appartenance_NN_instanciee(vx)))
    card_x = N.modus_ponens(fini_x, fini_implique_cardinal(vx))
    le_0x = N.modus_ponens(card_x, _zero_le_terme(vx))         # 0 ≤ x
    corps = conjonction_intro(conjonction_intro(le_0x, z0), h_x)
    assert corps.conclusion == ordre_induit_NN(ZERO, vx), \
        "plus_petit_element_zero_NN : corps ≠ ordre_induit_NN(0, x)"
    in_G = N.modus_ponens(corps, equivalence_arriere(couple_dans_G_ordre(ZERO, vx)))
    minore = N.generalisation(_LIANT, N.loi_deduction(appartient(vx, NN), in_G))
    res = conjonction_intro(z0, minore)
    assert res.conclusion == E.est_plus_petit_element(graphe_ordre_NN(), NN, ZERO), \
        "plus_petit_element_zero_NN : conclusion ≠ est_plus_petit_element(≤_G, ℕ, 0)"
    assert res.est_clos, "plus_petit_element_zero_NN : non clos"
    return res


def segment_zero_NN_est_vide_enonce():
    """Formule cible :  seg( ≤_G , ℕ , 0 ) = ∅."""
    return egal(segment_zero_NN(), E.VIDE)


# @livre Ch.III §2.1 Rem.- | E III.16 L.21-22 | PDF p.119  (« si E bien ordonné non vide, S_x = (α, x( » — cas limite x = α : le segment du plus petit élément est vide ; ICI l'instance au ℕ concret et à son ordre usuel)
# @livre Ch.III §6.1 Rem.- | E III.45 L.23-24 | PDF p.148  (ℕ muni de l'ordre usuel — la « donnée de position » qui fait démarrer la récursion C62 sur le VRAI ℕ)
def segment_zero_NN_est_vide():
    """🎯 ⊢ seg( ≤_G , ℕ , 0 ) = ∅.                                 [CLOS, 0 hyp]

    Instance au VRAI ℕ de segment_du_plus_petit_est_vide (§III.2.1), dont les DEUX
    hypothèses sont déchargées ici : « ℕ bien ordonné » par bo_graphe_NN [CLOS] et
    « 0 plus petit élément » par plus_petit_element_zero_NN [CLOS].
    NON vacueux : la conclusion n'est aucune hypothèse (il n'y en a aucune)."""
    NN, R = ensemble_NN(), graphe_ordre_NN()
    sp = segment_du_plus_petit_est_vide(G_ordre_NN(), NN, ZERO)
    assert sp.conclusion == segment_zero_NN_est_vide_enonce(), \
        "segment_zero_NN_est_vide : §III.2.1 ne conclut pas seg(ℕ,0)=∅"
    sans_bo = N.modus_ponens(bo_graphe_NN(),
                             N.loi_deduction(E.est_bien_ordonne(R, NN), sp))
    res = N.modus_ponens(plus_petit_element_zero_NN(),
                         N.loi_deduction(E.est_plus_petit_element(R, NN, ZERO), sans_bo))
    assert res.conclusion == segment_zero_NN_est_vide_enonce(), \
        "segment_zero_NN_est_vide : conclusion ≠ seg(≤_G, ℕ, 0) = ∅"
    assert res.est_clos and res.hypotheses == frozenset(), \
        "segment_zero_NN_est_vide : hypothèses résiduelles"
    return res


__all__ = ["graphe_ordre_NN", "segment_zero_NN", "plus_petit_element_zero_NN",
           "segment_zero_NN_est_vide_enonce", "segment_zero_NN_est_vide"]
