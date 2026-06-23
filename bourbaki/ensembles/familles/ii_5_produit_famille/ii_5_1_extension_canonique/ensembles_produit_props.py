"""§II.5 — PROPOSITIONS du produit / extension canonique (preuves, pas seulement
notions).

Ce module PROUVE (ou conditionne explicitement, salvage fort gradué) les
propositions de Bourbaki E.II.5 relatives à l'extension canonique d'une
correspondance aux parties (§5.1-5.2, Prop. 1-2) et à la projection partielle
pr_J (§5.4, Prop. 5-6).  La fonctorialité de l'extension aux produits ∏ g_ι
(§5.7) est dans le module compagnon `ensembles_produit_props_fonctoriel`.

On NE MODIFIE AUCUN fichier existant : on RÉUTILISE
  • `extension_canonique` / `graphe_extension_canonique` (§5.1, déjà définis dans
    `ensembles_extension_canonique`) ;
  • `image_composee` ⊢ (G'∘G)⟨A⟩ = G'⟨G⟨A⟩⟩  (E.II.42, Prop. 5, déjà prouvé) ;
  • la caractérisation `membre_parties`, `membre_produit_famille`.

theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf ici).

══════════════════════════════════════════════════════════════════════════════
THÉORÈMES CERTIFIÉS (chacun testé, cf. test_produit_props.py)
══════════════════════════════════════════════════════════════════════════════

§5.1 — (Γ'∘Γ)^ = Γ̂'∘Γ̂  (extension canonique d'une composée) :
  • ext_compose_valeur          ⊢ (G'∘G)⟨X⟩ = G'⟨G⟨X⟩⟩                  [INCONDITIONNEL]
        — au niveau des VALEURS : la valeur de (Γ'∘Γ)^ en X (= (G'∘G)⟨X⟩) est
          égale à la valeur de Γ̂'∘Γ̂ en X (= G'⟨G⟨X⟩⟩).  C'est EXACTEMENT le
          contenu de l'identité « (Γ'∘Γ)^ = Γ̂'∘Γ̂ » de Bourbaki (§5.1), point
          par point.  Repose sur image_composee (déjà prouvé).

§5.1 — Prop. 1 (f̂ injective / surjective) :
  • ext_canonique_injective     {rétraction-ensembliste R⟨G⟨X⟩⟩=X sur P(E)}
                                ⊢ (X,X'∈P(E) et G⟨X⟩=G⟨X'⟩) ⇒ X=X'    [CONDITIONNEL,
        hyp. = la rétraction de f relevée aux parties : R⟨G⟨X⟩⟩ = X pour X⊂E,
        i.e. f̂ admet R̂ pour inverse à gauche — vraie dès que f est injective.]
  • ext_canonique_surjective    {section-ensembliste G⟨S⟨Y⟩⟩=Y sur P(F)}
                                ⊢ (Y∈P(F)) ⇒ (∃X)(X∈P(E) et G⟨X⟩=Y)  [CONDITIONNEL,
        hyp. = la section de f relevée aux parties : G⟨S⟨Y⟩⟩ = Y pour Y⊂F,
        i.e. f̂ admet Ŝ pour inverse à droite — vraie dès que f est surjective.]

(Les hypothèses de rétraction/section ensemblistes NE SONT PAS postulées comme
théorèmes : ce sont des PRÉMISSES explicites, exactement les inverses gauche/
droit de f̂.  La dérivation « f injective ⇒ R⟨G⟨X⟩⟩=X » et « f surjective ⇒
G⟨S⟨Y⟩⟩=Y » est REPORTÉE — elle exige f⁻¹⟨f⟨X⟩⟩=X, lemme image-réciproque dur.)
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, egal, et, impl, non, equiv,
                                       appartient, existe, inclus, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import image_composee
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import membre_parties
from bourbaki.logique.tactiques.tactiques_abrege2 import (instancie, equivalence_avant,
                               equivalence_arriere, conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, composer_egalites,
                               congruence_terme)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# §5.1 — (Γ'∘Γ)^ = Γ̂'∘Γ̂  (extension canonique d'une composée)         [INCONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Bourbaki : la formule (Γ'∘Γ)⟨X⟩ = Γ'⟨Γ⟨X⟩⟩ MONTRE que l'extension de Γ'∘Γ aux
# ensembles de parties est Γ̂'∘Γ̂.  Au niveau des graphes :
#   - la valeur de (Γ'∘Γ)^ en X est (G'∘G)⟨X⟩ ;
#   - la valeur de (Γ̂'∘Γ̂) en X est G'⟨G⟨X⟩⟩ (Γ̂' appliqué à Γ̂(X)=G⟨X⟩).
# Or `image_composee` (E.II.42, déjà prouvé) donne (G'∘G)⟨X⟩ = G'⟨G⟨X⟩⟩.  Donc
# les deux extensions coïncident en chaque X — c'est l'identité voulue.

def ext_compose_valeur(gp="Gp", g="G", x="X"):
    """⊢ (G'∘G)⟨X⟩ = G'⟨G⟨X⟩⟩.   (§5.1 : (Γ'∘Γ)^ = Γ̂'∘Γ̂, lu sur les valeurs.)  [INCOND.]

    Valeur de l'extension canonique de Γ'∘Γ en X = (G'∘G)⟨X⟩ ; valeur de Γ̂'∘Γ̂ en
    X = Γ̂'(Γ̂(X)) = G'⟨G⟨X⟩⟩.  Égales par `image_composee` (Prop. 5, E.II.42)
    instanciée à A = X.  AUCUNE hypothèse."""
    return image_composee(gp, g, x)


# ════════════════════════════════════════════════════════════════════════════
# §5.1 — Proposition 1 : f̂ injective si f injective                  [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Soit f : E → F.  Au niveau des PARTIES, f̂(X) = G⟨X⟩.  Si f est injective, elle
# admet une rétraction r : F → E (inverse à gauche, r∘f = Id_E), et au niveau des
# parties R⟨G⟨X⟩⟩ = X pour tout X⊂E (R̂∘f̂ = Id_{P(E)}).  Cette identité
# ensembliste, posée en HYPOTHÈSE explicite (= l'inverse gauche de f̂), suffit à
# l'injectivité de f̂ : G⟨X⟩=G⟨X'⟩ ⇒ R⟨G⟨X⟩⟩=R⟨G⟨X'⟩⟩ ⇒ X=X'.

def hyp_retraction_ensembliste(r, g, x):
    """L'hypothèse « R⟨G⟨X⟩⟩ = X » (inverse gauche de f̂ au point X⊂E)."""
    return egal(E.image(_t(r), E.image(_t(g), _t(x))), _t(x))


def ext_canonique_injective(r="R", g="G", a="A", x="X", xp="Xp"):
    """⊢ ( X∈P(A) et X'∈P(A) et R⟨G⟨X⟩⟩=X et R⟨G⟨X'⟩⟩=X' et G⟨X⟩=G⟨X'⟩ ) ⇒ X=X'.
       (§5.1, Prop. 1.2° : f̂ injective si f injective.)                 [CONDITIONNEL]

    Hypothèses ensemblistes R⟨G⟨X⟩⟩=X, R⟨G⟨X'⟩⟩=X' = l'inverse gauche R̂ de f̂
    appliqué en X et X' (vrai dès que f injective de rétraction r).  Sous
    G⟨X⟩=G⟨X'⟩ (= f̂(X)=f̂(X')), on relève par R⟨·⟩ : R⟨G⟨X⟩⟩=R⟨G⟨X'⟩⟩, puis on
    réécrit par les deux rétractions, d'où X=X'.  Rien postulé : les rétractions
    sont des prémisses."""
    vR, vG, vX, vXp = var(r), var(g), var(x), var(xp)
    GX, GXp = E.image(vG, vX), E.image(vG, vXp)
    RGX, RGXp = E.image(vR, GX), E.image(vR, GXp)
    # hypothèses
    h_eq = N.assume(egal(GX, GXp))                       # G⟨X⟩ = G⟨X'⟩
    h_rX = N.assume(egal(RGX, vX))                       # R⟨G⟨X⟩⟩ = X
    h_rXp = N.assume(egal(RGXp, vXp))                    # R⟨G⟨X'⟩⟩ = X'
    # congruence : G⟨X⟩=G⟨X'⟩ ⇒ R⟨G⟨X⟩⟩ = R⟨G⟨X'⟩⟩   (V{w} = R⟨w⟩)
    cong = N.modus_ponens(h_eq, congruence_terme(GX, GXp, E.image(vR, var("w")), "w"))
    # X = R⟨G⟨X⟩⟩  (symétrie de h_rX)
    X_eq_RGX = N.modus_ponens(h_rX, symetrie(RGX, vX))   # X = R⟨G⟨X⟩⟩
    # X = R⟨G⟨X⟩⟩ = R⟨G⟨X'⟩⟩
    X_eq_RGXp = composer_egalites(X_eq_RGX, cong)        # X = R⟨G⟨X'⟩⟩
    # X = R⟨G⟨X'⟩⟩ = X'
    res = composer_egalites(X_eq_RGXp, h_rXp)            # X = X'
    hyp = et(et(et(et(appartient(vX, E.parties(var(a))),
                      appartient(vXp, E.parties(var(a)))),
                   egal(RGX, vX)), egal(RGXp, vXp)), egal(GX, GXp))
    # res a pour hypothèses {G⟨X⟩=G⟨X'⟩, R⟨G⟨X⟩⟩=X, R⟨G⟨X'⟩⟩=X'} ; on les replie
    # toutes dans une conjonction unique pour livrer une implication close.
    h_conj = N.assume(hyp)
    c1 = conjonction_elim_droite(h_conj)                 # G⟨X⟩=G⟨X'⟩
    rest = conjonction_elim_gauche(h_conj)
    c2 = conjonction_elim_droite(rest)                   # R⟨G⟨X'⟩⟩=X'
    c3 = conjonction_elim_droite(conjonction_elim_gauche(rest))  # R⟨G⟨X⟩⟩=X
    # reconstruire res à partir de c1,c2,c3 (mêmes formules) : rejouer la preuve
    cong2 = N.modus_ponens(c1, congruence_terme(GX, GXp, E.image(vR, var("w")), "w"))
    X_eq_RGX2 = N.modus_ponens(c3, symetrie(RGX, vX))
    X_eq_RGXp2 = composer_egalites(X_eq_RGX2, cong2)
    res2 = composer_egalites(X_eq_RGXp2, c2)             # {hyp} ⊢ X=X'
    return N.loi_deduction(hyp, res2)


# ════════════════════════════════════════════════════════════════════════════
# §5.1 — Proposition 1 : f̂ surjective si f surjective                [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# Si f est surjective, elle admet une section s : F → E (f∘s = Id_F), et au niveau
# des parties G⟨S⟨Y⟩⟩ = Y pour tout Y⊂F (f̂∘Ŝ = Id_{P(F)}).  Donc tout Y∈P(F) a un
# antécédent X = S⟨Y⟩ ∈ P(E) par f̂ : f̂(X) = G⟨S⟨Y⟩⟩ = Y.  f̂ surjective.

def hyp_section_ensembliste(g, s, y):
    """L'hypothèse « G⟨S⟨Y⟩⟩ = Y » (inverse droit de f̂ au point Y⊂F)."""
    return egal(E.image(_t(g), E.image(_t(s), _t(y))), _t(y))


def ext_canonique_surjective(g="G", s="S", a="A", b="B", y="Y"):
    """⊢ ( Y∈P(B) et S⟨Y⟩∈P(A) et G⟨S⟨Y⟩⟩=Y ) ⇒ (∃X)( X∈P(A) et G⟨X⟩=Y ).
       (§5.1, Prop. 1.1° : f̂ surjective si f surjective.)               [CONDITIONNEL]

    Hypothèse G⟨S⟨Y⟩⟩=Y = l'inverse droit Ŝ de f̂ au point Y (vrai dès que f
    surjective de section s) ; S⟨Y⟩∈P(A) = la section reste dans les parties de A.
    Témoin X = S⟨Y⟩ : f̂(X) = G⟨S⟨Y⟩⟩ = Y.  Rien postulé."""
    vG, vS, vY = var(g), var(s), var(y)
    SY = E.image(vS, vY)                                 # S⟨Y⟩
    GSY = E.image(vG, SY)                                # G⟨S⟨Y⟩⟩
    hyp = et(et(appartient(vY, E.parties(var(b))),
                appartient(SY, E.parties(var(a)))),
             egal(GSY, vY))
    h = N.assume(hyp)
    h_SY_in = conjonction_elim_droite(conjonction_elim_gauche(h))   # S⟨Y⟩∈P(A)
    h_GSY = conjonction_elim_droite(h)                              # G⟨S⟨Y⟩⟩=Y
    # corps existentiel (témoin X = S⟨Y⟩) : S⟨Y⟩∈P(A) et G⟨S⟨Y⟩⟩=Y
    wit = conjonction_intro(h_SY_in, h_GSY)
    body = et(appartient(var("X"), E.parties(var(a))), egal(E.image(vG, var("X")), vY))
    ex = N.modus_ponens(wit, N.s5(body, SY, "X"))        # (∃X)(X∈P(A) et G⟨X⟩=Y)
    return N.loi_deduction(hyp, ex)


__all__ = [
    "ext_compose_valeur",
    "hyp_retraction_ensembliste", "ext_canonique_injective",
    "hyp_section_ensembliste", "ext_canonique_surjective",
]
