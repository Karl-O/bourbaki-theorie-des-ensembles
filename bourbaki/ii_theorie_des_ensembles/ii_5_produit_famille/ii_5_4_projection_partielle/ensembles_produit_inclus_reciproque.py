"""§II.5.4 — Corollaire 3 : RÉCIPROQUE de la monotonie du produit (preuve).

Le Corollaire 3 (E.II.5.4) est la réciproque de la Proposition 10 (monotonie,
sens direct = `produit_monotone`, déjà CERTIFIÉ) :

    si  ∏_{ι∈I} X_ι ⊂ ∏_{ι∈I} Y_ι   et   X_ι ≠ ∅ pour tout ι,
    alors  X_ι ⊂ Y_ι  pour tout ι.

──────────────────────────────────────────────────────────────────────────────
FORME FORMALISÉE : POINTWISE, CONDITIONNELLE, HONNÊTE                 [CONDITIONNEL]
──────────────────────────────────────────────────────────────────────────────
On livre la version « ponctuelle » FIDÈLE du Corollaire 3, déchargée en
implication (théorème CLOS, 0 hypothèse pendante) :

    ⊢ ( ∏(f,I) ⊂ ∏(g,I)  ∧  α ∈ I  ∧  F ∈ ∏(f,I)  ∧  F(α) = a )  ⇒  ( a ∈ Y_α )

avec X_ι = valeur_famille(f, ι), Y_ι = valeur_famille(g, ι), Y_α = Y_ι en ι=α,
F(α) = valeur(F, α) = pr_α(F).

POURQUOI cette forme est l'énoncé honnête de Bourbaki.  La preuve « X_α ⊂ Y_α »
exige, pour chaque élément a ∈ X_α, un témoin F ∈ ∏(f,I) tel que F(α) = a (un
prolongement de a à tout I).  L'existence d'un tel témoin EST exactement la
SURJECTIVITÉ de pr_α (Cor. 1, qui dépend de X_ι ≠ ∅ pour tout ι, via choix-τ
`facteur_temoin`).  Dans la lignée de `pr_J_surjective_via_prolongement`, on ne
postule PAS cette surjectivité comme acquise : on la REÇOIT en HYPOTHÈSE honnête
sous la forme des deux antécédents « F ∈ ∏(f,I) » et « F(α) = a », qui sont le
témoin de surjectivité.  Sous ces antécédents (et pas autrement), la conclusion
a ∈ Y_α est obtenue par le SEUL noyau.  Le caractère CONDITIONNEL est porté par
l'antécédent (le témoin = Cor. 1), jamais par la conclusion ni par une hypothèse
non déchargée.

Preuve (purement « pointwise », SANS Card profond, par primitives N.* seules) :
  1. de  ∏(f,I) ⊂ ∏(g,I)  (= (∀z)(z∈∏(f,I) ⇒ z∈∏(g,I)))  instanciée en z := F,
     et de l'antécédent  F ∈ ∏(f,I),  par modus ponens :  F ∈ ∏(g,I) ;
  2. `projection_dans_facteur` sur ∏(g,I) :  F ∈ ∏(g,I) ⇒ (α∈I ⇒ F(α)∈Y_α) ;
     déchargée par les antécédents  F∈∏(g,I)  et  α∈I  :  F(α) ∈ Y_α ;
  3. l'antécédent  F(α) = a  + Leibniz (S6) sur R := (w ∈ Y_α) :
     (F(α)=a) ⇒ ( F(α)∈Y_α ⇔ a∈Y_α ) ;  d'où  a ∈ Y_α ;
  4. `loi_deduction` décharge la conjonction des quatre antécédents honnêtes en
     une implication CLOSE (est_clos = True).

L'hypothèse « X_ι ≠ ∅ pour tout ι » du Cor. 3 N'APPARAÎT PAS ici : elle est
encapsulée dans l'existence du témoin F (antécédent), exactement comme le Cor. 1
la consomme.  La prémisse « a ∈ X_α » serait redondante (elle découle de
F(α)∈X_α et F(α)=a) et N'EST PAS load-bearing dans cette preuve : on ne la met
donc PAS en antécédent (hypothèses = exactement les antécédents load-bearing).

theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf ici).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, appartient, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    projection_dans_facteur)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, equivalence_avant, conjonction_intro,
    conjonction_elim_gauche, conjonction_elim_droite)


def _cible(f="f", g="g", i="I", ff="F", alpha="alpha", a="a"):
    """L'énoncé visé (cible) : conjonction des 4 antécédents honnêtes ⇒ a∈Y_α.

    ⊢ ( ∏(f,I)⊂∏(g,I) ∧ α∈I ∧ F∈∏(f,I) ∧ F(α)=a ) ⇒ ( a ∈ Y_α )."""
    vf, vg, vI, vF, valpha, va = (var(f), var(g), var(i), var(ff),
                                  var(alpha), var(a))
    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    Y_alpha = E.valeur_famille(vg, valpha)
    Fa = E.valeur(vF, valpha)
    hyp = et(et(et(inclus(prodX, prodY), appartient(valpha, vI)),
                appartient(vF, prodX)),
             egal(Fa, va))
    return impl(hyp, appartient(va, Y_alpha))


# @livre Ch.II §5.4 Cor.3 | E II.34 L.32-44 | PDF p.85
# @livre Ch.R §4 Prop.- | E.R.21 item 12a (réciproque : ∏Xι⊂∏Yι et Xι≠∅ ⇒ Xι⊂Yι) | PDF p.324
def facteur_inclus_si_produit_inclus(f="f", g="g", i="I", ff="F",
                                     alpha="alpha", a="a"):
    """⊢ ( ∏(f,I)⊂∏(g,I) ∧ α∈I ∧ F∈∏(f,I) ∧ F(α)=a ) ⇒ ( a ∈ Y_α ).
       (§II.5.4, Cor. 3 : réciproque de la monotonie, forme pointwise.)  [CONDITIONNEL]

    Réciproque HONNÊTE de `produit_monotone` : le témoin « F ∈ ∏(f,I) avec
    F(α)=a » N'EST PAS postulé — c'est une hypothèse, exactement la surjectivité
    de pr_α (Cor. 1, reportée).  Voir l'en-tête de module pour le statut."""
    vf, vg, vI, vF, valpha, va = (var(f), var(g), var(i), var(ff),
                                  var(alpha), var(a))
    prodX = E.produit_famille(vf, vI)
    prodY = E.produit_famille(vg, vI)
    Y_alpha = E.valeur_famille(vg, valpha)
    Fa = E.valeur(vF, valpha)                              # F(α) = pr_α(F)

    # Conjonction des 4 antécédents honnêtes (load-bearing), associée à gauche.
    hyp = et(et(et(inclus(prodX, prodY), appartient(valpha, vI)),
                appartient(vF, prodX)),
             egal(Fa, va))
    h = N.assume(hyp)
    h_incl = conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h)))                       # ∏(f,I) ⊂ ∏(g,I)
    h_alpha = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_gauche(h)))                       # α ∈ I
    h_Fmem = conjonction_elim_droite(conjonction_elim_gauche(h))   # F ∈ ∏(f,I)
    h_eq = conjonction_elim_droite(h)                      # F(α) = a

    # 1. ∏(f,I)⊂∏(g,I) = (∀z)(z∈∏(f,I) ⇒ z∈∏(g,I)) ; instancier en z := F.
    incl_F = instancie(h_incl, vF)                         # F∈∏(f,I) ⇒ F∈∏(g,I)
    F_in_prodY = N.modus_ponens(h_Fmem, incl_F)            # F ∈ ∏(g,I)

    # 2. projection sur ∏(g,I) : F∈∏(g,I) ⇒ (α∈I ⇒ F(α)∈Y_α).
    pdf = projection_dans_facteur(g, i, ff, alpha)         # (F∈∏(g,I)) ⇒ (α∈I ⇒ F(α)∈Y_α)
    Fa_in_Ya = N.modus_ponens(h_alpha,
                              N.modus_ponens(F_in_prodY, pdf))     # F(α) ∈ Y_α

    # 3. Leibniz (S6) sur R := (w ∈ Y_α), w lettre FRAÎCHE (∉ Y_α, F(α), a) :
    #    (F(α)=a) ⇒ ( F(α)∈Y_α ⇔ a∈Y_α ).
    R = appartient(var("w"), Y_alpha)
    leibniz = N.s6(Fa, va, "w", R)                         # (F(α)=a)⇒(F(α)∈Y_α ⇔ a∈Y_α)
    equ = N.modus_ponens(h_eq, leibniz)                    # F(α)∈Y_α ⇔ a∈Y_α
    a_in_Ya = N.modus_ponens(Fa_in_Ya, equivalence_avant(equ))    # a ∈ Y_α

    # 4. décharger la conjonction des 4 antécédents honnêtes en implication CLOSE.
    return N.loi_deduction(hyp, a_in_Ya)


__all__ = ["facteur_inclus_si_produit_inclus", "_cible"]
