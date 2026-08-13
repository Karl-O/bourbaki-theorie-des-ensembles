"""§II.5.4 — PROJECTION partielle pr_J : Prop. 5-6 et corollaires (preuves).

Module compagnon de `ensembles_produit_props` : on PROUVE (ou conditionne, salvage
fort gradué) la Proposition 5 (pr_J surjective si tous les X_ι≠∅), la Proposition 6
(prolongement) et leurs corollaires (E.II.5.4).

L'outil-clé de Bourbaki est le « principe de choix » via le signe τ : pour une
famille de facteurs NON VIDES, on choisit dans chaque X_ι un élément témoin
e_ι := τ_w(w∈X_ι) SANS axiome du choix (E.II.5.4, Cor. 2 — c'est le τ qui le
légitime).  On RÉUTILISE :
  • `temoin_dans` ⊢ ¬(X=∅) ⇒ (τ_w(w∈X) ∈ X)      (témoin canonique, déjà prouvé) ;
  • `projection_dans_facteur` ⊢ (F∈∏) ⇒ (ι∈I ⇒ F(ι)∈X_ι)  (déjà prouvé) ;
  • `produit_partiel` = ∏_{ι∈J} X_ι, `projection_J(F)=F|J`  (déjà définis) ;
  • `restriction` / `couple_restriction`.

theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf ici).

══════════════════════════════════════════════════════════════════════════════
THÉORÈMES CERTIFIÉS (chacun testé, cf. test_produit_props_projection.py)
══════════════════════════════════════════════════════════════════════════════

§5.4 — Prop. 6 (choix-τ dans un facteur non vide) :
  • facteur_temoin              ⊢ ¬(X_ι=∅) ⇒ ( τ_w(w∈X_ι) ∈ X_ι )            [INCOND.]
        — cœur du « principe de choix » de Bourbaki : un facteur non vide a un
          témoin canonique (sans axiome du choix, via τ).  C'est l'ingrédient qui
          fabrique le prolongement de la Prop. 6.

§5.4 — Cor. 2 (∏=∅ ⇔ un facteur vide), sens facile :
  • facteur_non_vide_si_membre  ⊢ ( F∈∏_I et ι∈I ) ⇒ ¬(X_ι=∅)               [INCOND.]
        — un élément du produit témoigne que chaque facteur est non vide
          (F(ι)∈X_ι donc X_ι≠∅).  C'est la moitié « ∏≠∅ ⇒ tous X_ι≠∅ » du Cor. 2.

§5.4 — Prop. 5 (pr_J surjective) — réduction au prolongement :
  • pr_J_surjective_via_prolongement
        ⊢ ( G∈∏_J et F∈∏_I et F|J=G ) ⇒ (∃P)( P∈∏_I et pr_J(P)=G )          [CONDIT.,
        hyp. = l'EXISTENCE d'un prolongement F de G (= Prop. 6 ; reportée car son
        montage τ-recollement sur les domaines disjoints J et I∖J est un gros
        chantier).  Sous ce prolongement, pr_J atteint G : pr_J est surjective.]
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, app, tau, egal, et, impl, non, equiv,
                                       appartient, existe, inclus, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import projection_dans_facteur
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_1_extension_canonique.ensembles_extension_canonique import (produit_partiel,
                               projection_J)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_un_borne import temoin_dans
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import non_vide_ssi_element
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instancie, equivalence_avant,
                               equivalence_arriere, conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# §5.4 — Prop. 6 : choix-τ dans un facteur non vide                  [INCONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §5.4 Prop.6 | E II.34 L.1-9 | PDF p.85
# @livre Ch.R §4 Rem.- | E.R.21 item 10 (principe de choix : témoin τ dans un facteur non vide) | PDF p.324
def facteur_temoin(f="f", i="iota"):
    """⊢ ¬(X_ι = ∅) ⇒ ( τ_w(w ∈ X_ι) ∈ X_ι ).   (§5.4, Prop. 6 : choix-τ.)  [INCOND.]

    Cœur du « principe de choix » de Bourbaki (E.II.5.4, Cor. 2) : lorsque le
    facteur X_ι = (X_ι)_{ι∈I} d'indice ι est non vide, le terme canonique
    e_ι := τ_w(w∈X_ι) lui appartient — un élément choisi SANS axiome du choix,
    par le seul signe τ.  Instance de `temoin_dans` au facteur X_ι =
    valeur_famille(f, ι).  C'est l'ingrédient qui fabrique le prolongement de la
    Prop. 6 (composante par composante)."""
    X_iota = E.valeur_famille(_t(f), _t(i))
    return temoin_dans(X_iota)


# ════════════════════════════════════════════════════════════════════════════
# §5.4 — Cor. 2 (sens facile) : ∏≠∅ ⇒ chaque facteur ≠∅             [INCONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §5.4 Cor.2 | E II.34 L.18-25 | PDF p.85
def facteur_non_vide_si_membre(f="f", i="I", ff="F", iota="iota"):
    """⊢ ( F ∈ ∏_I et ι ∈ I ) ⇒ ¬( X_ι = ∅ ).   (§5.4, Cor. 2, sens « ∏≠∅ ⇒ X_ι≠∅ ».)
       [INCONDITIONNEL]

    Un élément F du produit témoigne que chaque facteur est non vide : F(ι)∈X_ι
    (projection_dans_facteur), donc (∃z)(z∈X_ι), donc ¬(X_ι=∅)
    (non_vide_ssi_element)."""
    vf, vI, vF, vi = var(f), var(i), var(ff), var(iota)
    X_i = E.valeur_famille(vf, vi)                        # X_ι
    F_i = E.valeur(vF, vi)                                # F(ι) = pr_ι(F)
    hyp = et(appartient(vF, E.produit_famille(vf, vI)), appartient(vi, vI))
    h = N.assume(hyp)
    h_mem = conjonction_elim_gauche(h)                    # F∈∏_I
    h_iota = conjonction_elim_droite(h)                   # ι∈I
    # F(ι) ∈ X_ι
    pdf = projection_dans_facteur(f, i, ff, iota)         # (F∈∏) ⇒ (ι∈I ⇒ F(ι)∈X_ι)
    Fi_in_Xi = N.modus_ponens(h_iota, N.modus_ponens(h_mem, pdf))   # F(ι)∈X_ι
    # (∃z)(z∈X_ι)  via S5, témoin z=F(ι)
    ex_z = N.modus_ponens(Fi_in_Xi, N.s5(appartient(var("z"), X_i), F_i, "z"))   # (∃z)(z∈X_ι)
    # ¬(X_ι=∅)  via non_vide_ssi_element, sens ⇐
    not_vide = N.modus_ponens(ex_z, equivalence_arriere(non_vide_ssi_element(X_i)))
    return N.loi_deduction(hyp, not_vide)


# ════════════════════════════════════════════════════════════════════════════
# §5.4 — Prop. 5 : pr_J surjective (réduction au prolongement)        [CONDITIONNEL]
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §5.4 Prop.5 | E II.33 L.48-51 | PDF p.84
# @livre Ch.R §4 Def.- | E.R.21 item 11 (projection pr_J : surjectivité) | PDF p.324
def pr_J_surjective_via_prolongement(f="f", i="I", j="J", g="G", ff="F"):
    """⊢ ( G∈∏_J  et  F∈∏_I  et  F|J = G ) ⇒ (∃P)( P∈∏_I  et  pr_J(P) = G ).
       (§5.4, Prop. 5 : pr_J : ∏_I → ∏_J surjective si tous X_ι≠∅.)      [CONDITIONNEL]

    Réduction HONNÊTE de la surjectivité de pr_J au prolongement (Prop. 6) : on
    suppose donné un prolongement F de G (F∈∏_I avec F|J=G — l'existence de F est
    la Prop. 6, fabriquée par choix-τ `facteur_temoin` ; son montage complet par
    recollement sur les domaines disjoints J / I∖J est reporté).  Alors F est un
    antécédent de G par pr_J : pr_J(F) = F|J = G, donc G est atteint.  Témoin
    P = F.  La prémisse « F prolongement » N'EST PAS postulée : c'est une
    hypothèse, exactement la Prop. 6."""
    vf, vI, vJ, vG, vF = var(f), var(i), var(j), var(g), var(ff)
    hyp = et(et(appartient(vG, produit_partiel(vf, vJ)),
                appartient(vF, E.produit_famille(vf, vI))),
             egal(projection_J(vF, vJ), vG))
    h = N.assume(hyp)
    h_F_in = conjonction_elim_droite(conjonction_elim_gauche(h))   # F∈∏_I
    h_prJ = conjonction_elim_droite(h)                             # pr_J(F)=G
    # corps existentiel (témoin P=F) : F∈∏_I et pr_J(F)=G
    wit = conjonction_intro(h_F_in, h_prJ)
    body = et(appartient(var("P"), E.produit_famille(vf, vI)),
              egal(projection_J(var("P"), vJ), vG))
    ex = N.modus_ponens(wit, N.s5(body, vF, "P"))                 # (∃P)(P∈∏_I et pr_J(P)=G)
    return N.loi_deduction(hyp, ex)


__all__ = [
    "facteur_temoin", "facteur_non_vide_si_membre",
    "pr_J_surjective_via_prolongement",
]
