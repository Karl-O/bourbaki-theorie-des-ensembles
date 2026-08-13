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

OBSTRUCTION PRÉCISE — la pièce `trois_b_egal_b` (3𝔟=𝔟) ET le « CLAIM : Card(S₀)=Card(E) »
(extension+contradiction) restent HONNÊTEMENT non assemblés.  Le verrou EXACT, commun aux
deux, est identifié :

  Bourbaki dérive 𝔟≤2𝔟≤3𝔟≤𝔟²=𝔟 — l'étape DURE étant 3𝔟≤𝔟², qui exige « 3≤𝔟 »,
  c.-à-d. « n≤a pour tout entier n quand a est infini » (E.III.45, remarque de la Déf. 1).
  Or CETTE chaîne est EXPLICITEMENT REPORTÉE dans le dépôt
  (`iii_6_infinis/entiers_infinis/iii_6_3_infinis_denombrables/ensembles_infinis.py`, en-tête : « exige la chaîne 'a infini ⇒ n<a
  pour tout entier n' », NON disponible).  Sans elle :
    • `3≤𝔟` (donc `3𝔟≤𝔟·𝔟`) n'est pas établissable → `trois_b_egal_b` BLOQUÉ ;
    • l'extension du maximal (cadre (S₀∪U)²∖(S₀×S₀) de cardinal 3𝔟²=3𝔟=𝔟=Card U, puis
      bijection sur U prolongeant φ₀, contredisant la maximalité) BLOQUÉE au même point.
  C'est pourquoi `Card(S₀)=Card(E)` reste une HYPOTHÈSE HONNÊTE de
  `hessenberg_a_carre_inf_egal` / `hessenberg_aa_egal_de_maximal` (jamais postulée vraie).

CE QUI EST CLOS (route qui CONTOURNE 3𝔟=𝔟) : une fois `Card S₀=Card E` ADMIS comme hyp
honnête, l'égalité a²=a tombe SANS `trois_b_egal_b` — par bien-déf du produit cardinal
(`maximal_carre_egal`+`produit_cardinal_bien_defini`) + réflexivité + pont Cantor–Bernstein.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
a²=a n'est JAMAIS supposé, le ≥ dur jamais supposé vrai.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de, equipotent, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t, produit_cardinal_bien_defini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hard_aa_inf_egal_a, hessenberg_depuis_hard, enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (1) maximal_carre_egal — { φ bij. de S×S sur S } ⊢ Card(S×S) = Card(S).
#  C'est 𝔟² = 𝔟 (au niveau ENSEMBLISTE : Card(S×S)=produit_cardinal_binaire(S,S)).
#  Route LA PLUS PROPRE : bijection ⇒ Eq(S×S, S) (témoin S5) ⇒ Card égaux (Prop 1).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-26 | PDF p.151  (le maximal (F,f) : f bijective ⇒ Card(F×F)=Card F, « 𝔟 = 𝔟² »)
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


# ════════════════════════════════════════════════════════════════════════════
#  (2) hessenberg_a_carre_inf_egal — du maximal (Card S₀=Card E, Card(S₀×S₀)=Card S₀)
#      à  Card E · Card E ≤ Card E  (= enonce_hard, sous est_infini(Card E)).
#  C'est le « CLAIM : Card(F)=𝔞 ⇒ 𝔞²=Card(F)²=Card(F)=𝔞 » de Bourbaki E.III.48.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.25-26 | PDF p.151  (de Card F = 𝔞 et 𝔟²=𝔟 vers a·a ≤ a)
def hessenberg_a_carre_inf_egal(E_set="E", S="S0"):
    """{ Card(S₀)=Card(E),  Card(S₀×S₀)=Card(S₀) }
        ⊢ est_infini(Card E) ⇒ ( Card E · Card E ≤ Card E ).     [2 hyps honnêtes].

    🎯 Le DERNIER MILE de Hessenberg.  Une fois le maximal (S₀,φ₀) atteignant Card(E)
    (« CLAIM : Card(F)=𝔞 », Bourbaki E.III.48), et le carré de S₀ égal à S₀
    (`maximal_carre_egal` ⇒ Card(S₀×S₀)=Card S₀), on a :

      • bien-déf du produit cardinal (`produit_cardinal_bien_defini` à X=Y=S₀,
        a=b=Card E, sous Card S₀=Card E) :
            Card(S₀×S₀) = Card E · Card E ;
      • or Card(S₀×S₀) = Card S₀ = Card E   (les deux hyps) ;
      • donc Card E · Card E = Card E, d'où Card E · Card E ≤ Card E par réflexivité.

    La conclusion est LITTÉRALEMENT `enonce_hard_aa_inf_egal_a(E)` (le ≥ dur) : la
    décharge sous est_infini(Card E) est triviale (l'inégalité est ici INCONDITIONNELLE
    une fois les deux hyps honnêtes posées, mais on l'enveloppe pour matcher la cible
    du pont `hessenberg_carre`).  Hyps HONNÊTES (jamais postulées vraies, à fournir par
    l'argument de Zorn : maximal atteint Card E + son carré).  theorie=22 ; non vacuous."""
    vE, vS = _t(E_set), _t(S)
    cE = cardinal(vE)
    cS = cardinal(vS)
    SxS = E.produit(vS, vS)
    prod_EE = produit_cardinal_binaire(cE, cE)            # Card E · Card E
    cible = enonce_hard_aa_inf_egal_a(E_set)              # est_infini(Card E)⇒(CardE·CardE≤CardE)

    # hyps honnêtes
    h_card = N.assume(egal(cS, cE))                       # Card S₀ = Card E
    h_carre = N.assume(egal(cardinal(SxS), cS))          # Card(S₀×S₀) = Card S₀

    # bien-déf : (Card S₀=Card E et Card S₀=Card E) ⇒ Card(S₀×S₀)=Card E·Card E
    # ⚠️ τ-HYGIÈNE : appeler produit_cardinal_bien_defini avec X=Y=S₀ (mêmes termes)
    #   casse l'invariance interne (eq_produit_invariant collisionne ses binders).  On
    #   le construit donc sur des VARIABLES distinctes XX,YY,AA,BB puis on généralise et
    #   on instancie aux termes (vS,vS,cE,cE) — motif prop9/prop10 capture-safe.
    bd_var = produit_cardinal_bien_defini("XX", "YY", "AA", "BB")
    bd_gen = N.generalisation("XX", N.generalisation("YY",
        N.generalisation("AA", N.generalisation("BB", bd_var))))
    bd = instancie(instancie(instancie(instancie(bd_gen, vS), vS), cE), cE)
    ant = et(egal(cS, cE), egal(cS, cE))
    assert bd.conclusion == impl(ant, egal(cardinal(SxS), prod_EE)), \
        f"bien_defini forme inattendue\n{bd.conclusion}"
    card_SxS_eq_prod = N.modus_ponens(conjonction_intro(h_card, h_card), bd)  # Card(S₀×S₀)=CardE·CardE

    # Card E·Card E = Card(S₀×S₀)  (symétrie) ;  Card(S₀×S₀)=Card S₀ ; Card S₀=Card E
    prod_eq_SxS = N.modus_ponens(card_SxS_eq_prod, symetrie(cardinal(SxS), prod_EE))  # CardE·CardE=Card(S₀×S₀)
    prod_eq_cS = composer_egalites(prod_eq_SxS, h_carre)  # CardE·CardE = Card S₀
    prod_eq_cE = composer_egalites(prod_eq_cS, h_card)    # CardE·CardE = Card E

    # Card E ≤ Card E  (réflexivité) ; réécrit le LHS Card E → Card E·Card E via S6.
    refl = inf_egal_reflexif("E_refl")
    refl = instancie(N.generalisation("E_refl", refl), cE)   # Card E ≤ Card E
    assert refl.conclusion == inf_egal_card(cE, cE)
    # cE = prod_EE (symétrie de prod_eq_cE) ; S6 sur R(w):= w ≤ Card E.
    cE_eq_prod = N.modus_ponens(prod_eq_cE, symetrie(prod_EE, cE))   # Card E = CardE·CardE
    s6 = N.s6(cE, prod_EE, "w", inf_egal_card(var("w"), cE))         # (CardE=prod)⇒(CardE≤CardE ⇔ prod≤CardE)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_avant
    le = N.modus_ponens(refl, equivalence_avant(N.modus_ponens(cE_eq_prod, s6)))  # CardE·CardE ≤ Card E
    assert le.conclusion == inf_egal_card(prod_EE, cE)

    # envelopper sous est_infini(Card E) pour matcher enonce_hard
    res = N.loi_deduction(est_infini(cE), le)

    assert res.conclusion == cible, \
        f"hessenberg_a_carre_inf_egal : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert egal(cS, cE) in res.hypotheses, "manque hyp Card S₀=Card E"
    assert egal(cardinal(SxS), cS) in res.hypotheses, "manque hyp Card(S₀×S₀)=Card S₀"
    assert res.conclusion not in res.hypotheses, "hessenberg_a_carre_inf_egal : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (3) hessenberg_aa_egal_de_maximal — a²=a (Théorème 2) sous les 2 hyps honnêtes.
#  Branche `hessenberg_a_carre_inf_egal` (≥ dur) sur le PONT `hessenberg_depuis_hard`
#  (diagonale + Cantor–Bernstein closes), livrant l'égalité a²=a.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.25-26 | PDF p.151  (a² = Card(F)² = Card F = a, conclusion depuis le maximal)
def hessenberg_aa_egal_de_maximal(E_set="E", S="S0"):
    """{ Card(S₀)=Card(E),  Card(S₀×S₀)=Card(S₀) }
        ⊢ est_infini(Card E) ⇒ ( Card E · Card E = Card E ).     [2 hyps honnêtes].

    🎯🎯 THÉORÈME 2 (HESSENBERG, E.III.6.3) : 𝔞²=𝔞 pour 𝔞 infini — ASSEMBLÉ sous les
    deux hypothèses honnêtes du maximal de Zorn (le maximal atteint Card E et son carré
    vaut Card S₀).  `hessenberg_a_carre_inf_egal` fournit le ≥ dur (enonce_hard) ; le
    pont `hessenberg_depuis_hard` (diagonale ≤ + Cantor–Bernstein, CLOS) referme
    l'égalité.  La conclusion est LITTÉRALEMENT `enonce_hessenberg(E)`.

    RÉSIDUS HONNÊTES (jamais postulés vrais ; à fournir par la conclusion de l'argument
    de Zorn de Bourbaki, E.III.48) :
       • Card(S₀)=Card(E)        — « CLAIM : Card(F)=𝔞 » (extension+contradiction) ;
       • Card(S₀×S₀)=Card(S₀)    — φ₀ bijective (⇐ `maximal_carre_egal`).
    theorie=22 ; non vacuous."""
    vE = _t(E_set)
    cE = cardinal(vE)
    hard = hessenberg_a_carre_inf_egal(E_set, S)          # {2 hyps} ⊢ enonce_hard(E)
    pont = hessenberg_depuis_hard(E_set)                  # enonce_hard(E) ⇒ enonce_hessenberg(E)
    assert hard.conclusion == enonce_hard_aa_inf_egal_a(E_set), \
        "hessenberg_aa_egal_de_maximal : enonce_hard inattendu"
    res = N.modus_ponens(hard, pont)                      # enonce_hessenberg(E)

    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg
    assert res.conclusion == enonce_hessenberg(E_set), \
        f"hessenberg_aa_egal_de_maximal : conclusion inattendue\n{res.conclusion}"
    cS = cardinal(_t(S))
    SxS = E.produit(_t(S), _t(S))
    assert egal(cS, cE) in res.hypotheses and egal(cardinal(SxS), cS) in res.hypotheses, \
        "hessenberg_aa_egal_de_maximal : hyps honnêtes manquantes"
    assert res.conclusion not in res.hypotheses, "hessenberg_aa_egal_de_maximal : VACUOUS"
    return res


__all__ = [
    "maximal_carre_egal",
    "hessenberg_a_carre_inf_egal",
    "hessenberg_aa_egal_de_maximal",
]
