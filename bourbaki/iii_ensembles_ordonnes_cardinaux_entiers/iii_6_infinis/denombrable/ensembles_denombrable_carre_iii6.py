"""§III.6 (E.III.48, Lemme 2) — ℵ₀·ℵ₀ = ℵ₀, le « carré dénombrable ».

🎯 CIBLE BOURBAKI (Lemme 2, E.III.48) : « L'ensemble ℕ×ℕ est équipotent à ℕ »,
   c.-à-d.  Eq(ℕ×ℕ, ℕ)   (=  Card(ℕ)·Card(ℕ) = Card(ℕ) =  ℵ₀·ℵ₀ = ℵ₀).

   ROUTE NON CIRCULAIRE (élémentaire, INDÉPENDANTE du Théorème 2 général a²=a /
   Hessenberg `hessenberg_a_carre_egal_a_REEL`) : CANTOR–BERNSTEIN sur deux injections
        (A)   ℕ      ≤ ℕ×ℕ      (direction « facile »),
        (B)   ℕ×ℕ   ≤ ℕ        (direction « dure », Bourbaki : développement dyadique),
   d'où, par `cantor_bernstein` (antisymétrie de ≤),  Eq(ℕ×ℕ, ℕ).

═══════════════════════════════════════════════════════════════════════════════
ÉTAT (2026-06-22, branche iii6-denombrable2) — HONNÊTE :

  ✅ DIRECTION (A) — `NN_inf_egal_NN_carre` : ⊢ ℕ ≤ ℕ×ℕ.  CLOS, 0 hyp, theorie=22.
     Via `inf_egal_produit` (« a ≤ a·b si b≠0 », E.III.3.2 — injection x↦(x,e), e∈ℕ
     fixé) instancié à A=B=ℕ, l'hypothèse ¬(ℕ=∅) étant DÉCHARGÉE par `zero_dans_NN`
     (0∈ℕ ⇒ ℕ≠∅).  C'est EXACTEMENT le « ℕ×ℕ contient {0}×ℕ équipotent à ℕ, donc
     Card(ℕ)≤Card(ℕ×ℕ) » du Lemme 2 de Bourbaki.

  ✅ DIRECTION (B) — ℕ×ℕ ≤ ℕ : CLOSE le 22 août 2026 — voir
     `ensembles_denombrable_graphe_pairing.NN_carre_inf_egal_NN` (couplage
     (m,n) ↦ 2^m·3^n, piles W1-W7) et `lemme_deux_NN` = Eq(ℕ×ℕ, ℕ).
     (L'état ci-dessous, conservé pour mémoire, date du 2026-06-22.)
  (périmé) DIRECTION (B) — ℕ×ℕ ≤ ℕ : NON ATTEIGNABLE en l'état (obstruction d'infrastructure).
     Bourbaki construit l'injection f:ℕ×ℕ→ℕ par développement DYADIQUE (la 2-valuation
     donne m, la partie impaire donne n).  L'injection ALTERNATIVE (m,n)↦2^m·3^n est
     injective par UNICITÉ DE LA FACTORISATION.  Or le dépôt n'a AUCUNE arithmétique
     de ℕ de ce niveau :
        • `puissance_entiers(a,b)` (ensembles_entiers_notions_arith) n'est qu'un ALIAS
          de l'exponentiation cardinale a^b — AUCUNE propriété prouvée (pas même a^b∈ℕ,
          qui est « REPORTÉ » faute de la récurrence Prop. 1 §III.5) ;
        • PAS de 2-valuation, PAS d'unicité de factorisation, PAS de primalité de 2/3,
          PAS d'injectivité d'une fonction de couplage (pairing) ℕ×ℕ→ℕ.
     ⇒ PRÉ-REQUIS EXACT de §III.6 (sous-chantier) :  arithmétique multiplicative de ℕ —
        a^b∈ℕ (Cor. 3 §III.5.1, récurrence Prop. 1), puis unicité de la factorisation
        (ou 2-valuation), d'où l'injectivité de (m,n)↦2^m·3^n.  C'est CE chaînon qui
        manque, pas Cantor–Bernstein (présent, MERGED) ni la direction facile (présente).

  CONSÉQUENCE : `denombrable_carre` n'est PAS clos inconditionnellement ; il est ici
  ASSEMBLÉ via `cantor_bernstein` en gardant l'UNIQUE hypothèse résiduelle, SATISFIABLE
  et VRAIE (Lemme 2 de Bourbaki), qu'est la direction (B) :  inf_egal_card(ℕ×ℕ, ℕ).
  La direction (A) est, elle, DÉCHARGÉE (close).  Quand (B) sera prouvée (sous-chantier
  factorisation), `denombrable_carre_de_injection_dure(preuve_B)` la branchera et CLORA
  Eq(ℕ×ℕ, ℕ) sans rien changer d'autre.

INVARIANT : theorie_ensembles() = 22.  Noyau INTACT.  Aucun axiome nouveau.
ANTI-VACUITÉ : les conclusions ont un CONTENU (≠ P⇒P) ; l'unique résidu (B) est
satisfiable (ne contredit rien) et VRAI.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, non
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, equipotent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN, zero_dans_NN
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_cardinaux_bornes_somme import inf_egal_produit
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  DIRECTION (A) — FACILE :  ⊢ ℕ ≤ ℕ×ℕ   (CLOS, 0 hyp).
# ════════════════════════════════════════════════════════════════════════════
def NN_non_vide():
    """🎯 ⊢ ¬(ℕ = ∅).   (CLOS, 0 hyp — ℕ n'est pas vide, car 0 ∈ ℕ.)

    `zero_dans_NN` ⊢ 0∈ℕ donne, par S5 (témoin 0), (∃z)(z∈ℕ) ; et
    `non_vide_ssi_element(ℕ)` ⊢ ¬(ℕ=∅) ⇔ (∃z)(z∈ℕ), sens ⇐.  theorie=22."""
    NN = ensemble_NN()
    zero = zero_dans_NN().conclusion.termes[0]            # le terme « 0 » (= Card ∅)
    z0 = zero_dans_NN()                                   # ⊢ 0 ∈ ℕ
    # (∃z)(z∈ℕ) par témoin 0
    exists = N.modus_ponens(z0, N.s5(E.appartient(var("z"), NN), zero, "z"))
    equiv = non_vide_ssi_element(NN)                      # ¬(ℕ=∅) ⇔ (∃z)(z∈ℕ)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_arriere
    res = N.modus_ponens(exists, equivalence_arriere(equiv))   # ¬(ℕ=∅)
    assert res.conclusion == non(egal(NN, E.VIDE)), \
        f"NN_non_vide : conclusion inattendue\n{res.conclusion}"
    return res


def NN_inf_egal_NN_carre():
    """🎯 ⊢ ℕ ≤ ℕ×ℕ.   (CLOS, 0 hyp — direction FACILE du Lemme 2, E.III.48.)

    `inf_egal_produit` ⊢ ¬(B=∅) ⇒ (A ≤ A×B) (injection x↦(x,e), E.III.3.2) ;
    généralisé en A,B puis instancié au TERME ℕ pour A et B ⇒ ¬(ℕ=∅) ⇒ (ℕ ≤ ℕ×ℕ) ;
    `NN_non_vide` décharge ¬(ℕ=∅).  Bourbaki : « ℕ×ℕ contient {0}×ℕ équipotent à ℕ,
    donc Card(ℕ)≤Card(ℕ×ℕ) ».  theorie=22."""
    NN = ensemble_NN()
    # ¬(B=∅) ⇒ (A ≤ A×B), généralisé puis instancié à A=B=ℕ
    gen_A = N.generalisation("A", inf_egal_produit("A", "B"))   # (∀A)(¬(B=∅)⇒A≤A×B)
    instA = instancie(gen_A, NN)                               # ¬(B=∅) ⇒ (ℕ ≤ ℕ×B)
    gen_B = N.generalisation("B", instA)                       # (∀B)(¬(B=∅)⇒ℕ≤ℕ×B)
    instAB = instancie(gen_B, NN)                              # ¬(ℕ=∅) ⇒ (ℕ ≤ ℕ×ℕ)
    res = N.modus_ponens(NN_non_vide(), instAB)                # ℕ ≤ ℕ×ℕ
    cible = inf_egal_card(NN, E.produit(NN, NN))
    assert res.conclusion == cible, \
        f"NN_inf_egal_NN_carre : conclusion ≠ (ℕ ≤ ℕ×ℕ)\n{res.conclusion}"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE CANTOR–BERNSTEIN — `denombrable_carre` sous l'UNIQUE résidu (B).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Lem.2 | E III.48 L.3-16 | PDF p.151
def denombrable_carre():
    """⊢ inf_egal_card(ℕ×ℕ, ℕ)  ⇒  Eq(ℕ×ℕ, ℕ).   (CLOS sous 1 hyp résiduelle SATISFIABLE.)

    Direction (A) ℕ≤ℕ×ℕ DÉCHARGÉE (`NN_inf_egal_NN_carre`) ; reste l'UNIQUE hypothèse
    (B) ℕ×ℕ≤ℕ (l'injection dyadique de Bourbaki, VRAIE mais hors d'atteinte faute
    d'arithmétique multiplicative de ℕ — cf. en-tête).  `cantor_bernstein(ℕ×ℕ, ℕ)` ⊢
    (ℕ×ℕ≤ℕ et ℕ≤ℕ×ℕ) ⇒ Eq(ℕ×ℕ, ℕ) ; on décharge le 2ᵉ conjoint par (A), laissant
    (B) comme garde honnête.  theorie=22.

    NB : `denombrable_carre_de_injection_dure(preuve_B)` ci-dessous CLÔT Eq(ℕ×ℕ,ℕ)
    dès qu'une preuve close de (B) est fournie."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.cloture._recollement import (
        cantor_bernstein,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    NN = ensemble_NN()
    NN2 = E.produit(NN, NN)
    # ── CANTOR–BERNSTEIN capture-safe : prouvé sur NOMS FRAIS Acb,Bcb (≠ liants de ℕ),
    #    puis généralisation + instanciation aux TERMES lourds ℕ×ℕ, ℕ (motif _prop1_direct_t).
    cb_frais = cantor_bernstein("Acb", "Bcb", "Fcb", "Gcb")   # (Acb≤Bcb et Bcb≤Acb)⇒Eq(Acb,Bcb)
    cb_gen = N.generalisation("Acb", N.generalisation("Bcb", cb_frais))
    cb = instancie(instancie(cb_gen, NN2), NN)   # (ℕ×ℕ≤ℕ et ℕ≤ℕ×ℕ) ⇒ Eq(ℕ×ℕ, ℕ)
    h_dure = N.assume(inf_egal_card(NN2, NN))  # (B) ℕ×ℕ ≤ ℕ   [résidu honnête]
    facile = NN_inf_egal_NN_carre()            # (A) ℕ ≤ ℕ×ℕ    [DÉCHARGÉE]
    res = N.modus_ponens(conjonction_intro(h_dure, facile), cb)   # Eq(ℕ×ℕ, ℕ)  [hyp (B)]
    return N.loi_deduction(inf_egal_card(NN2, NN), res)           # (B) ⇒ Eq(ℕ×ℕ, ℕ)


def denombrable_carre_de_injection_dure(preuve_B):
    """⊢ Eq(ℕ×ℕ, ℕ).   (CLOS dès qu'`preuve_B` ⊢ inf_egal_card(ℕ×ℕ, ℕ) est close.)

    Branche la preuve close de la direction dure (B) sur `denombrable_carre` ⇒
    Eq(ℕ×ℕ, ℕ) inconditionnel (= ℵ₀·ℵ₀ = ℵ₀, Lemme 2, E.III.48)."""
    NN = ensemble_NN()
    NN2 = E.produit(NN, NN)
    assert preuve_B.conclusion == inf_egal_card(NN2, NN), \
        f"preuve_B : conclusion ≠ (ℕ×ℕ ≤ ℕ)\n{preuve_B.conclusion}"
    res = N.modus_ponens(preuve_B, denombrable_carre())   # Eq(ℕ×ℕ, ℕ)
    assert res.conclusion == equipotent(NN2, NN)
    return res


__all__ = [
    "NN_non_vide",
    "NN_inf_egal_NN_carre",
    "denombrable_carre",
    "denombrable_carre_de_injection_dure",
]
