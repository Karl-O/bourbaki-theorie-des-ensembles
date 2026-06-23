"""§III.3.5 — EXPONENTIATION CARDINALE  a^1 = a   (Proposition 11, E.III.3.5).

THÉORÈME (CLOS, rien postulé) :

    ⊢ exposant_cardinal_un(A) = Card(A)      (= a^1 = a, où 1 = {∅})
    ⊢ exposant_cardinal_binaire(Card A, {∅}) = Card(A)

  a^1 = Card(𝓕({∅}; A)) = Card(A) car l'évaluation f ↦ f(∅) est une bijection de
  𝓕({∅}; A) sur A : une application de {∅} dans A est entièrement déterminée par sa
  SEULE valeur en ∅.

VOIE FIDÈLE.  On part de la DÉFINITION GÉNÉRALE (E.II.5.2, axiomes de membership
`axiome_exposant`/`axiome_applications`, déjà dans ensembles_abrege) :
    • exposant({∅}, A) = A^{∅} = { G ⊂ {∅}×A | G fonctionnel ∧ dom G = {∅} } ;
    • applications({∅}, A) = 𝓕({∅};A) = { ((G,{∅}),A) | G ∈ A^{∅} }.
Un graphe G ∈ A^{∅} est le singleton {(∅,v)} pour un unique v ∈ A.  On construit la
bijection RÉCIPROQUE de l'évaluation :
        η : A → 𝓕({∅}; A),   v ↦ ((G_v, {∅}), A)   où   G_v = {(∅, v)},
codée par η = graphe_terme(A, ((G_v,{∅}),A), "c"), G_v = graphe_terme({∅}, v, "x").

PALIERS (tous CLOS) :
  (1) [_gv] G_v fonctionnel, dom={∅}, ⊂{∅}×A, ∈ A^{∅} pour v∈A, déterminé par v
      (gv_*), et la caractérisation z∈G_v ⇔ z=(∅,v) (gv_membre) ;
  (2) [_gv] η fonctionnelle, dom η=A, η injective (eta_fonctionnel/eta_domaine/
      eta_valeur/eta_injective) ;
  (3) [_bijection] CŒUR : tout G ∈ A^{∅} est G_{G(∅)} — UNICITÉ du graphe fonctionnel
      de domaine {∅} (exposant_egal_gv) ; d'où (∃v)(v∈A et G=G_v) (exposant_un_est_gv)
      et la SURJECTIVITÉ image(η,A)=𝓕({∅};A) (eta_image) ;
  (4) [_bijection] bijection η (eta_bijection), Eq(A,𝓕) (eq_A_applications), Eq(𝓕,A)
      par symétrie (eq_applications_A), puis a^1 = a (exposant_un_egale) via la
      Proposition 1 (sens direct, version TERME _prop1_direct_t).
"""
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.exposant_un._gv import (
    _t, UN_SOURCE, exposant_cardinal_un,
    _gv, gv_fonctionnel, gv_domaine, gv_couple_dans, gv_inclus_produit,
    gv_dans_exposant, gv_injectif, gv_membre,
    _eta_triple_A, _eta, eta_fonctionnel, eta_domaine, eta_valeur, eta_injective,
)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.exposant_un._bijection import (
    _exposant_conjoints, exposant_couple_dans, exposant_valeur_dans_A,
    exposant_membre_implique_couple, exposant_egal_gv, exposant_un_est_gv,
    _bridge_image_applications, _et_idem_gauche, eta_image, eta_bijection,
    eq_A_applications, eq_applications_A,
    exposant_un_egale, exposant_cardinal_un_egale,
)

__all__ = [
    "exposant_cardinal_un", "UN_SOURCE",
    "gv_fonctionnel", "gv_domaine", "gv_couple_dans", "gv_inclus_produit",
    "gv_dans_exposant", "gv_injectif", "gv_membre",
    "eta_fonctionnel", "eta_domaine", "eta_valeur", "eta_injective",
    "exposant_couple_dans", "exposant_valeur_dans_A",
    "exposant_membre_implique_couple", "exposant_egal_gv", "exposant_un_est_gv",
    "eta_image", "eta_bijection",
    "eq_A_applications", "eq_applications_A",
    "exposant_un_egale", "exposant_cardinal_un_egale",
]
