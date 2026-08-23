# -*- coding: utf-8 -*-
"""§III.6.3 — L'ASSEMBLAGE : LE FRAME DE HESSENBERG A UN ÉLÉMENT MAXIMAL.

🎯 CIBLE (E.III.48, « il existe dans 𝔐 un élément maximal (F,f) ») :

    hess_maximal :  { est_infini(Card E),  donnees_recollement(E) }
                        ⊢ (∃m) element_maximal( Γ𝔉(E), 𝔉(E), m )

DEUX hypothèses, et une seule est encore ouverte :
  • « E est infini » — la donnée du théorème ;
  • donnees_recollement(E) = (∀C)( (chaîne ∧ C≠∅) ⇒ (⋃S,⋃𝔇)∈𝔉(E) ) : le
    recollement d'une chaîne non vide est une frame-pair.  `frame_de_recollement`
    le PROUVE dès qu'on lui fournit les neuf propriétés élémentaires du
    recollement (⋃S⊂E, ⋃S infinie, famille compatible/dirigée/à membres
    injectifs, recollements surjectif et domaine, deux inclusions) ; comme
    celles-ci dépendent de C, elles vivent sous le même ∀C, d'où le maintien
    de l'hypothèse à ce niveau.  Leur dérivation depuis « C chaîne non vide »
    est en chantier et NOMMÉE dans DECISIONS — rien n'est postulé en douce.

Ce qui est acquis SANS aucune hypothèse cachée :
  • H1 (𝔉(E)≠∅) est CERTIFIÉ sous « E infini » (h1_decharge, test 2h28) ;
  • le recollement est une frame-pair dès qu'on lui donne ces données, les
    trois conditions VALEUR étant DÉRIVÉES (frame_de_recollement) ;
  • le témoin (⋃S,⋃𝔇) majore la chaîne (majore_fam) et Zorn s'applique
    (chaine_majoree_fam, maximal_fam).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.decharge.ensembles_h1 import (
    h1_decharge,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_majore_fam import (
    residu_fam, maximal_fam,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def donnees_recollement(E_set="E", C="C", x="xmaj", y="y", z="z"):
    """L'unique hypothèse ouverte : le recollement d'une chaîne non vide est
    une frame-pair —  (∀C)( (chaîne(Γ𝔉,𝔉,C) ∧ C≠∅) ⇒ (⋃S(C),⋃𝔇(C)) ∈ 𝔉(E) ).

    `frame_de_recollement` la prouve pour un C donné, à partir des neuf
    propriétés élémentaires du recollement (cf. docstring du module)."""
    return residu_fam(E_set, C, x, y, z)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151
#   (« il existe dans 𝔐 un élément maximal (F,f) » — Zorn appliqué au frame)
def hess_maximal(E_set="E"):
    """🎯🎯 { est_infini(Card E), donnees_recollement(E) }
       ⊢ (∃m) element_maximal( Γ𝔉(E), 𝔉(E), m )   [2 hyps].

    L'élément maximal (F,f) de Bourbaki.  H1 (𝔉≠∅) est DÉCHARGÉ par le
    Lemme 1, certifié ; il ne subsiste que l'énoncé du recollement."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    base = maximal_fam(E_set)                               # {residu_fam, H1}
    base = N.modus_ponens(h1_decharge(E_set),
                          N.loi_deduction(residu_H1(E_set), base))
    assert base.conclusion == existe("m", element_maximal(
        Gam, Fr, var("m"), "x")), "hess_maximal : forme"
    assert residu_H1(E_set) not in base.hypotheses, \
        "hess_maximal : H1 non déchargé"
    assert len(base.hypotheses) == 2, "hess_maximal : hyps ≠ 2"
    return base


__all__ = ["donnees_recollement", "hess_maximal"]
