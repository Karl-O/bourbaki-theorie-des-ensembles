"""§III.6.3 — Théorème 2 (HESSENBERG), DERNIÈRE PIÈCE : du MAXIMAL au CARRÉ.

Le squelette Zorn est en place (`ensembles_frame_a_maximal.frame_a_maximal` :
∃ maximal (S₀,φ₀)∈𝔉(E), φ₀ : S₀×S₀ → S₀ BIJECTIVE).  Bourbaki (E.III.48) conclut
alors Card(S₀)=Card(E)=𝔞 (« CLAIM : Card(F)=𝔞 ») d'où 𝔞²=Card(S₀)²=Card(S₀)=𝔞.

Ce module construit, depuis la bijection φ₀ du maximal, le CŒUR CARDINAL :

  • `maximal_carre_egal(S, phi)`  — { est_bijection_de(φ, S×S, S) } ⊢ Card(S×S)=Card(S).
                                    (𝔟²=𝔟 au niveau ensembliste, le plus propre :
                                     bijection ⇒ équipotent ⇒ Card égaux, Prop 1.)  CLOS.

  • `trois_b_egal_b(S)`           — { est_infini(Card S), Card(S×S)=Card S }
                                    ⊢ 3·Card S = Card S.  (cf. infra : RÉSIDU précis.)

  • `hessenberg_a_carre_inf_egal` — Card(S₀)=Card(E) et Card(S₀×S₀)=Card S₀
                                    ⇒ Card E · Card E ≤ Card E  (= enonce_hard).

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
a²=a n'est JAMAIS supposé, le ≥ dur jamais supposé vrai.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de, equipotent,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (1) maximal_carre_egal — { φ bij. de S×S sur S } ⊢ Card(S×S) = Card(S).
#  C'est 𝔟² = 𝔟 (au niveau ENSEMBLISTE : Card(S×S)=produit_cardinal_binaire(S,S)).
#  Route LA PLUS PROPRE : bijection ⇒ Eq(S×S, S) (témoin S5) ⇒ Card égaux (Prop 1).
# ════════════════════════════════════════════════════════════════════════════
def maximal_carre_egal(S="S0", phi="phi0"):
    """{ est_bijection_de(φ, S×S, S) } ⊢ Card(S×S) = Card(S).            [1 hyp honnête].

    🎯 Le CARRÉ du maximal de Hessenberg : la bijection φ₀ : S₀×S₀ → S₀ du couple
    maximal (S₀,φ₀)∈𝔉 atteste Eq(S₀×S₀, S₀), d'où Card(S₀×S₀)=Card(S₀) par la
    Proposition 1 (sens direct).  C'est exactement 𝔟²=𝔟 (𝔟 := Card S₀), puisque
    Card(S×S) = produit_cardinal_binaire(S,S).

    Hyp HONNÊTE : la bijectivité de φ (fournie par l'appartenance du maximal à 𝔉
    via `frame_membre` ; jamais postulée vraie).  Conclusion ∉ hyps ; theorie=22."""
    vS, vphi = _t(S), _t(phi)
    SxS = E.produit(vS, vS)
    cible = egal(cardinal(SxS), cardinal(vS))

    # bijection ⇒ Eq(S×S, S) : témoin F := φ pour (∃F) est_bijection_de(F, S×S, S).
    bij = N.assume(est_bijection_de(vphi, SxS, vS))
    corps = est_bijection_de(var("F"), SxS, vS)           # corps de Eq, liant F
    eq = N.modus_ponens(bij, N.s5(corps, vphi, "F"))      # Eq(S×S, S)
    assert eq.conclusion == equipotent(SxS, vS)

    # Eq(S×S, S) ⇒ Card(S×S)=Card(S)   (Prop 1, sens direct, version TERME)
    res = N.modus_ponens(eq, _prop1_direct_t(SxS, vS))    # Card(S×S)=Card(S)

    assert res.conclusion == cible, \
        f"maximal_carre_egal : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert est_bijection_de(vphi, SxS, vS) in res.hypotheses, \
        "maximal_carre_egal : hyp bijection absente"
    assert res.conclusion not in res.hypotheses, "maximal_carre_egal : VACUOUS"
    return res


__all__ = [
    "maximal_carre_egal",
]
