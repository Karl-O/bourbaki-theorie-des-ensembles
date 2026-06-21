"""§III.6.3 — Théorème 2 (HESSENBERG, E.III.48-49) : l'EXTENSION FINALE du maximal,
« CLAIM : Card(S₀)=Card(E) ⇒ a²=a ».

CONTEXTE (lu sur le PDF source, E.III.48).  L'argument de Zorn fournit un couple
MAXIMAL (S₀,φ₀)∈𝔉(E), φ₀ : S₀×S₀ → S₀ BIJECTIVE (⇒ 𝔟²=𝔟, 𝔟:=Card S₀,
`maximal_carre_egal`).  Bourbaki conclut Card(S₀)=Card(E)=𝔞 par CONTRADICTION :
si 𝔟 < 𝔞, on prend U⊂E∖S₀ équipotent à S₀ (le complément est « grand »,
`complement_grand`), on pose Z = S₀∪U, et l'on observe

    Z×Z  =  (S₀×S₀)  ⊔  [ (S₀×U) ⊔ (U×S₀) ⊔ (U×U) ]   (réunion DISJOINTE),

dont le « CADRE » F := Z²∖(S₀×S₀) = (S₀×U)⊔(U×S₀)⊔(U×U) a pour cardinal
3𝔟²=3𝔟=𝔟=Card(U) (`trois_b_egal_b_inconditionnel`).  D'où une bijection ψ:F→U,
et g := φ₀∪ψ : Z×Z→Z BIJECTIVE prolongeant φ₀ — contredisant la maximalité de
(S₀,φ₀).  Donc Card(S₀)=𝔞 et 𝔞² = Card(S₀)² = Card(S₀) = 𝔞.

Ce module construit les pièces de cet argument, dans l'ordre du plan :

  (1) `cadre_card_trois_b`  — Card(F) = 3𝔟 = 𝔟 (cardinal du cadre).
  (2) `cadre_bijection`     — Card(F)=Card(U) ⇒ (∃ψ) est_bijection_de(ψ,F,U).
  (3) `phi_etendue_*`       — recollement φ₁ := φ₀∪ψ et sa bijectivité Z×Z→Z.
  (4) `contradiction_maximalite` — frame-membership de (Z,φ₁) + ordre + maximalité.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau dans
theorie_ensembles ; rien postulé ; a²=a n'est JAMAIS supposé, le ≥ dur jamais
supposé vrai.  Les pièces résistantes sont sous HYPOTHÈSES HONNÊTES explicites,
jamais postulées vraies, avec OBSTRUCTION précise documentée.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, existe, pourtout, appartient, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, equipotent, est_bijection_de, inf_egal_card,
    inf_strict_card,
)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_si_cardinal_egal,
)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (2) cadre_bijection — Card(F)=Card(U) ⇒ (∃ψ) ψ : F → U bijective.
#  Route : Prop 1 réciproque (Card F=Card U ⇒ Eq(F,U)) ; Eq(F,U)=(∃ψ)bij(ψ,F,U).
# ════════════════════════════════════════════════════════════════════════════
def cadre_bijection(F="Fcadre", U="Ucadre"):
    """⊢ ( Card(F) = Card(U) ) ⇒ (∃ψ)( est_bijection_de(ψ, F, U) ).         [CLOS, 0 hyp].

    🎯 Étape 2 du plan : du cardinal du cadre à une BIJECTION ψ:F→U.  C'est la Prop 1
    (sens réciproque, `equipotent_si_cardinal_egal`) : Card F=Card U ⇒ Eq(F,U), et
    Eq(F,U) = (∃ψ)(ψ bij. de F sur U) par DÉFINITION de l'équipotence.  La conclusion
    est LITTÉRALEMENT equipotent(F,U) déplié.  theorie=22 ; conclusion ∉ hyps."""
    vF, vU = _t(F), _t(U)
    cible = impl(egal(cardinal(vF), cardinal(vU)), equipotent(vF, vU))
    # equipotent_si_cardinal_egal(X,Y) : (Card X=Card Y) ⇒ Eq(X,Y), construit sur noms
    # frais puis généralisé/instancié aux TERMES (capture-safe, motif _prop1_direct_t).
    base = equipotent_si_cardinal_egal("Xcb", "Ycb")
    gen = N.generalisation("Xcb", N.generalisation("Ycb", base))
    res = instancie(instancie(gen, vF), vU)
    assert res.conclusion == cible, \
        f"cadre_bijection : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cadre_bijection : VACUOUS"
    return res


def cadre_bijection_cible(F="Fcadre", U="Ucadre"):
    """ÉNONCÉ-cible (test miroir)."""
    vF, vU = _t(F), _t(U)
    return impl(egal(cardinal(vF), cardinal(vU)), equipotent(vF, vU))


__all__ = [
    "cadre_bijection",
    "cadre_bijection_cible",
]
