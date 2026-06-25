"""§II.5.4 — Cor. 2 (sens utile) : un facteur vide annule le produit.

  ⊢ ( (α ∈ I) ∧ (X_α = ∅) )  ⇒  ( ∏_{ι∈I} X_ι = ∅ ).

Énoncé Bourbaki (E.II.5.4, Cor. 2 de la Prop. 6) : si l'un des facteurs d'un
produit est vide, le produit est vide.  Ici X_α = valeur_famille(f, α) et
∏ = produit_famille(f, I).  Forme CLOSE (0 hypothèse), l'antécédent honnête étant
déchargé en implication par la loi de déduction (C6).

Stratégie (LCF, primitives N.* uniquement) :
  1. hyp := (α∈I ∧ X_α=∅) ; h := assume(hyp) ; conjonction_elim → h_α, h_vide.
  2. Sous-but (∀F)¬(F∈∏).  Pour F frais :
       projection_dans_facteur(f,I,F,α) donne (F∈∏) ⇒ (α∈I ⇒ pr_α(F)∈X_α) ;
       sous l'hypothèse F∈∏ et avec h_α, on obtient (F∈∏) ⇒ (pr_α(F)∈X_α).
  3. _congruence_appartient(pr_α, X_α, ∅) + h_vide : (pr_α∈X_α) ⇒ (pr_α∈∅).
     Composition (syllogisme) : (F∈∏) ⇒ (pr_α∈∅).
  4. AXIOME_VIDE instancié en pr_α : ¬(pr_α∈∅).  Contraposition de (3) puis
     modus ponens → ¬(F∈∏).  generalisation('F') → (∀F)¬(F∈∏).
  5. vide_ssi_sans_element(∏), sens arrière : (∀z)¬(z∈∏) ⇒ (∏=∅) — après
     α-renommage du liant 'F' en 'z'.  modus ponens → ∏=∅.
  6. loi_deduction(hyp, ∏=∅) → l'implication close cible.

Invariants : aucun Theoreme fabriqué (que des N.*) ; theorie_ensembles()==22 ;
conclusion == impl(hyp, egal(produit_famille(f,I), VIDE)) ; 0 hypothèse.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, non, appartient, pourtout, libres_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
    equivalence_arriere, instancie, contraposition)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import vide_ssi_sans_element
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    projection_dans_facteur)


def _congruence_appartient(t, a, b, w="w"):
    """⊢ (A=B) ⇒ ( (T∈A) ⇒ (T∈B) ).   (réécriture de l'appartenance le long de A=B.)

    Recopie locale du helper de ii_5_6_7_algebre_produit/ensembles_produit_props2.
    Sous A=B, la propriété R{w} := (T∈w) est conservée (S6), d'où le sens ⇒.
    w est un liant FRESH (≠ libres de T, A, B) pour éviter toute capture."""
    libres = set()
    for trm in (t, a, b):
        libres |= set(libres_t(trm))
    while w in libres:
        w = w + "_"
    vw = var(w)
    R = appartient(t, vw)                                # R{w} = (T∈w)
    h = N.assume(egal(a, b))
    equ = N.modus_ponens(h, N.s6(a, b, w, R))            # (T∈A) ⇔ (T∈B)
    return N.loi_deduction(egal(a, b), equivalence_avant(equ))


# @livre Ch.II §5.4 Cor.2 | E II.34 L.18-25 | PDF p.85
def cor2_facteur_vide_donne_produit_vide(f="f", i="I", a="a", ff="F"):
    """⊢ ( (α∈I) ∧ (X_α=∅) ) ⇒ ( ∏_{ι∈I} X_ι = ∅ ).   (E.II.5.4, Cor. 2, sens utile.)

    Un facteur vide rend le produit vide.  X_α = valeur_famille(f, α),
    ∏ = produit_famille(f, I).  Liant d'élément du produit fixé à « z » in fine
    (cohérent avec vide_ssi_sans_element et l'axiome du vide).  Forme close.

    Paramètres : f (famille), i (index I), a (indice distingué α), ff (élément F)."""
    vf, vI, va, vF = var(f), var(i), var(a), var(ff)
    produit = E.produit_famille(vf, vI)              # ∏_{ι∈I} X_ι
    X_a = E.valeur_famille(vf, va)                   # X_α
    pr = E.valeur(vF, va)                            # pr_α(F) = F(α)

    # 1. hypothèse honnête (α∈I ∧ X_α=∅), décomposée.
    hyp = et(appartient(va, vI), egal(X_a, E.VIDE))
    h = N.assume(hyp)
    h_alpha = conjonction_elim_gauche(h)            # α ∈ I
    h_vide = conjonction_elim_droite(h)             # X_α = ∅

    # 2. sous l'hypothèse F∈∏ : pr_α(F) ∈ X_α.
    proj = projection_dans_facteur(f, i, ff, a)     # (F∈∏) ⇒ (α∈I ⇒ pr_α∈X_α)
    hF = N.assume(appartient(vF, produit))
    alpha_imp = N.modus_ponens(hF, proj)            # α∈I ⇒ pr_α∈X_α
    pr_dans_Xa = N.modus_ponens(h_alpha, alpha_imp)  # pr_α ∈ X_α   {hyp, F∈∏}
    imp_F_Xa = N.loi_deduction(appartient(vF, produit), pr_dans_Xa)  # (F∈∏)⇒(pr_α∈X_α)  {hyp}

    # 3. congruence par X_α=∅ puis composition : (F∈∏) ⇒ (pr_α∈∅).
    cong = _congruence_appartient(pr, X_a, E.VIDE)  # (X_α=∅) ⇒ ((pr_α∈X_α)⇒(pr_α∈∅))
    imp_Xa_vide = N.modus_ponens(h_vide, cong)      # (pr_α∈X_α) ⇒ (pr_α∈∅)   {hyp}
    imp_F_vide = syllogisme(imp_F_Xa, imp_Xa_vide)  # (F∈∏) ⇒ (pr_α∈∅)        {hyp}

    # 4. ¬(pr_α∈∅) [axiome du vide], contraposition, MP → ¬(F∈∏).
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    non_pr_vide = instancie(ax_vide, pr)            # ¬(pr_α∈∅)
    contra = contraposition(imp_F_vide)             # ¬(pr_α∈∅) ⇒ ¬(F∈∏)      {hyp}
    non_F = N.modus_ponens(non_pr_vide, contra)     # ¬(F∈∏)                  {hyp}

    # 5. (∀F)¬(F∈∏), α-renommé en (∀z)¬(z∈∏), puis ∏=∅.
    sans_F = N.generalisation(ff, non_F)            # (∀F)¬(F∈∏)              {hyp}
    corps_F = non(appartient(vF, produit))          # ¬(F∈∏)
    sans_z = N.modus_ponens(sans_F, equivalence_avant(alpha_pour_tout(ff, "z", corps_F)))
    equ_vide = vide_ssi_sans_element(produit)       # (∏=∅) ⇔ (∀z)¬(z∈∏)
    prod_vide = N.modus_ponens(sans_z, equivalence_arriere(equ_vide))  # ∏=∅   {hyp}

    # 6. décharge de l'hypothèse → implication close.
    return N.loi_deduction(hyp, prod_vide)


cible = cor2_facteur_vide_donne_produit_vide


__all__ = ["cor2_facteur_vide_donne_produit_vide", "cible"]
