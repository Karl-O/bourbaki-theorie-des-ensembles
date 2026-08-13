"""§II.1 — MONOTONIE (croissance) de la réunion et de l'intersection binaires.

Bourbaki, Résumé des résultats, E.R.5 nº14 h) (restate de l'algèbre des parties,
Chap II.1) :

    X ⊂ Y  entraîne  X∪Z ⊂ Y∪Z  et  X∩Z ⊂ Y∩Z.

Autrement dit : à Z fixé, les opérations T ↦ T∪Z et T ↦ T∩Z sont CROISSANTES pour
l'inclusion.  C'est de l'algèbre des parties PURE : aucun schéma S8, aucune théorie
dédiée ; les seuls axiomes ensemblistes utilisés sont AXIOME_REUNION / AXIOME_INTER
(membres des 22 axiomes de theorie_ensembles()).

STRATÉGIE (honnête — l'hypothèse X⊂Y n'est PAS déchargée) :
  inclus(X,Y) = (∀z)(z∈X ⇒ z∈Y).  On garde H = assume(inclus(X,Y)) comme HYPOTHÈSE.
  Pour z générique on instancie H : zX_to_zY = (z∈X ⇒ z∈Y).
  • ∪ : z∈X∪Z ⇔ (z∈X ou z∈Z)  [AXIOME_REUNION].  Par `cas` :
        z∈X → z∈Y → z∈Y∪Z   (zX_to_zY puis _oui_g)
        z∈Z → z∈Y∪Z          (_oui_d)
     d'où z∈X∪Z ⇒ z∈Y∪Z ; generalisation(z) ⟹ inclus(X∪Z, Y∪Z).
  • ∩ : z∈X∩Z ⇔ (z∈X et z∈Z)  [AXIOME_INTER].  De (z∈X et z∈Z) :
        z∈Y (via zX_to_zY) ET z∈Z ⟹ (z∈Y et z∈Z) ⇔ z∈Y∩Z.
     d'où z∈X∩Z ⇒ z∈Y∩Z ; generalisation(z) ⟹ inclus(X∩Z, Y∩Z).
  conjonction_intro des deux inclusions ⟹ la conclusion (et …).

INVARIANTS : est_clos == False ; hypotheses == {inclus(X,Y)} EXACTEMENT (X⊂Y non
déchargée — c'est l'hypothèse « honnête » de l'énoncé « X⊂Y entraîne … ») ; la
conclusion (conjonction des deux inclusions) ∉ hypotheses ; theorie_ensembles()
INCHANGÉE = 22 ; aucun axiome ajouté, aucune théorie dédiée / S8.

NB origine Chap II : le Résumé E.R.5 nº14 restate l'algèbre des parties de E.II.1
(les identités (9)/(10) de la même page sont les associativité/distributivité déjà
formalisées ici dans ensembles_algebre_booleenne) ; la monotonie h) est la lecture
ordinale du treillis (∪, ∩) introduit en E.II.1.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, appartient, et, ou, inclus
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _instance_inter(a, b, z):
    """⊢ (z ∈ a∩b) ⇔ (z∈a et z∈b)   (instance de AXIOME_INTER, dans les 22)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _oui_g(a, b):
    """⊢ A ⇒ (A∨B)."""
    return N.s2(a, b)


def _oui_d(a, b):
    """⊢ B ⇒ (A∨B)."""
    return syllogisme(N.s2(b, a), N.s3(b, a))   # B⇒(B∨A)⇒(A∨B)


# @livre Ch.R §1 Prop.14h | E.R.5 L.9-10 | PDF p.308
def monotonie_union_inter(x="X", y="Y", z="Z"):
    """⊢_{X⊂Y}  (X∪Z ⊂ Y∪Z)  et  (X∩Z ⊂ Y∩Z)   (E.R.5 nº14 h) ; restate E.II.1).

    Théorème CLOS-SOUS-L'HYPOTHÈSE-HONNÊTE {inclus(X,Y)} : « X⊂Y entraîne … ».
    L'hypothèse X⊂Y n'est PAS déchargée (séquent {X⊂Y} ⊢ conclusion) ; est_clos
    vaut donc False et hypotheses == {inclus(X,Y)} exactement."""
    vX, vY, vZ, vz = _t(x), _t(y), _t(z), var("z")
    zX, zY, zZ = appartient(vz, vX), appartient(vz, vY), appartient(vz, vZ)

    # Hypothèse honnête X⊂Y = (∀z)(z∈X ⇒ z∈Y), non déchargée.
    H = N.assume(inclus(vX, vY))
    zX_to_zY = instancie(H, vz)                                  # z∈X ⇒ z∈Y   [sous H]

    # ── ∪ : z∈X∪Z ⇒ z∈Y∪Z, puis (∀z) ⟹ X∪Z ⊂ Y∪Z ───────────────────────────
    YuZ = E.reunion(vY, vZ)
    zX_to_YuZ = syllogisme(zX_to_zY, _oui_g(zY, zZ))            # z∈X ⇒ z∈Y ⇒ (z∈Y ou z∈Z)
    zZ_to_YuZ = _oui_d(zY, zZ)                                  # z∈Z ⇒ (z∈Y ou z∈Z)
    disj = equivalence_avant(_instance_reunion(vX, vZ, vz))     # z∈X∪Z ⇒ (z∈X ou z∈Z)
    membre_YuZ = cas(N.assume(ou(zX, zZ)), zX_to_YuZ, zZ_to_YuZ)  # {z∈X∨z∈Z} ⊢ (z∈Y∨z∈Z)
    impl_u = syllogisme(syllogisme(disj,                        # z∈X∪Z ⇒ (z∈X∨z∈Z)
                                   N.loi_deduction(ou(zX, zZ), membre_YuZ)),  # ⇒ (z∈Y∨z∈Z)
                        equivalence_arriere(_instance_reunion(vY, vZ, vz)))   # ⇒ z∈Y∪Z
    incl_u = N.generalisation("z", impl_u)                      # {X⊂Y} ⊢ X∪Z ⊂ Y∪Z

    # ── ∩ : z∈X∩Z ⇒ z∈Y∩Z, puis (∀z) ⟹ X∩Z ⊂ Y∩Z ───────────────────────────
    h_et = N.assume(et(zX, zZ))                                 # z∈X et z∈Z
    membre_YiZ = conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(h_et), zX_to_zY),  # z∈Y
        conjonction_elim_droite(h_et))                            # z∈Z
    impl_i = syllogisme(syllogisme(
        equivalence_avant(_instance_inter(vX, vZ, vz)),         # z∈X∩Z ⇒ (z∈X et z∈Z)
        N.loi_deduction(et(zX, zZ), membre_YiZ)),               # ⇒ (z∈Y et z∈Z)
        equivalence_arriere(_instance_inter(vY, vZ, vz)))       # ⇒ z∈Y∩Z
    incl_i = N.generalisation("z", impl_i)                      # {X⊂Y} ⊢ X∩Z ⊂ Y∩Z

    return conjonction_intro(incl_u, incl_i)


__all__ = ["monotonie_union_inter"]
