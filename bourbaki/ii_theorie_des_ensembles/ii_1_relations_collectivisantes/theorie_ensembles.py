"""Chapitre II — Théorie des ensembles : ∈, ⊂ (et le MUR des quantificateurs τ).

Démarrage du chapitre II — qui révèle un mur ARCHITECTURAL, à documenter
honnêtement plutôt qu'à masquer.

MUR : ∃/∀ sont DÉFINIS par substitution de τ_x(R) (qui contient une copie de R) :
  (∃x)R := (τx(R)|x)R   →   chaque occurrence de x dans R est remplacée par τx(R).
Avec des quantificateurs imbriqués (comme dans A1, A2…), la taille de
l'assemblage développé EXPLOSE (multiplicative par niveau → exponentielle).
Concrètement, construire A1 = (∀x)(∀y)((x⊂y et y⊂x) ⇒ x=y) lève un MemoryError.

C'est FIDÈLE à Bourbaki (ses assemblages formels sont astronomiques — son « 1 »
≈ 10¹² signes ; cf. sa remarque §I.1 sur la nécessité pratique des abréviateurs).
Mais cela impose, pour le chapitre II, de représenter ∀/∃/Coll comme des
ABRÉVIATEURS de premier ordre (niveau arbre), NON développés en τ — une extension
du noyau (quantificateurs primitifs, la τ-expansion restant la justification).
Voir la note de relance dans la mémoire projet.

Ce module fournit donc seulement ce qui ne gonfle pas (∈, ⊂ à un seul niveau).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import (Assemblage, concat, implication, pour_tout)


# Prose de la page E II.1 (chaque ligne comptabilisée) :
#  L.1-16 : présentation de la théorie des ensembles — signes spécifiques =, ∈ de
#   poids 2, schémas S1-S8, axiomes explicites A1 (II, p. 2), A2 (II, p. 4),
#   A3 (II, p. 30), A4 (III, p. 45), théorie égalitaire sans constantes ; rien à
#   formaliser ici, les axiomes et schémas portent leurs marqueurs dans leurs modules.
#  L.21-27 : petit texte, point de vue « naïf » (« ensemble » strictement synonyme
#   de « terme ») — prose, rien à formaliser.
#  L.17-20 : la relation d'appartenance — l'assemblage ∈TU, noté T ∈ U ou
#   « T appartient à U », négation T ∉ U — c'est exactement ce que construit `appartient`.
# @livre Ch.II §1.1 Rem.- | E II.1 L.1-16 | PDF p.52
# @livre Ch.II §1.1 Rem.- | E II.1 L.21-27 | PDF p.52
# @livre Ch.II §1.1 Def.- | E II.1 L.17-20 | PDF p.52
def appartient(x: Assemblage, y: Assemblage) -> Assemblage:
    """x ∈ y  (signe relationnel 'in', poids 2). Ne gonfle pas.  (E II.1, §1.1.)"""
    return concat(concat(Assemblage(("in",)), x), y)


# Page E II.2 (chaque ligne comptabilisée ; L.1 = titre « 2. L'inclusion ») :
#  L.2-5   : Définition 1 — x ⊂ y := (∀z)((z∈x) ⇒ (z∈y)) ; notations y ⊃ x, x ⊄ y —
#            c'est `inclus`.
#  L.6-15  : prose — convention métamathématique de substitution simultanée dans
#            x ⊂ y, + petit texte « on ne signalera plus la convention » ; rien à formaliser.
#  L.16-18 : META (CS12) : (V|x)(T ⊂ U) est identique à (V|x)T ⊂ (V|x)U.  Ici ⊂ est
#            représenté au niveau arbre (pour_tout/implication) : la substitution agit
#            structurellement sur les sous-arbres T et U, d'où l'identité — vrai par
#            construction, JAMAIS un Theoreme du noyau.
#  L.19-20 : META (CF13) : si T et U sont des termes, T ⊂ U est une relation — par
#            construction, `inclus` renvoie pour_tout(z, (z∈T) ⇒ (z∈U)), une relation (CF8).
#  L.21-22 : « relation d'inclusion » = toute relation de la forme T ⊂ U — ce que
#            produit `inclus`.
#  L.23-29 : prose — critères de substitution/formatifs désormais implicites (petit
#            texte) ; méthode pratique « soit z un élément de x » justifiée par C27 ;
#            rien à formaliser.
#  L.30-36 : Prop.1 (L.30-32, avec « partie pleine » L.32) et Prop.2 (L.33-36) —
#            formalisées et marquées dans i_2_theoremes/tactiques
#            (inclusion_reflexive, inclusion_transitive).
# @livre Ch.II §1.2 Rem.- | E II.2 L.6-15 | PDF p.53
# @livre Ch.II §1.2 Crit.CS12 | E II.2 L.16-18 | PDF p.53
# @livre Ch.II §1.2 Crit.CF13 | E II.2 L.19-20 | PDF p.53
# @livre Ch.II §1.2 Def.- | E II.2 L.21-22 | PDF p.53
# @livre Ch.II §1.2 Rem.- | E II.2 L.23-29 | PDF p.53
# @livre Ch.II §1.2 Def.1 | E II.2 L.2-5 | PDF p.53
def inclus(x: Assemblage, y: Assemblage, z: str = "z") -> Assemblage:
    """x ⊂ y := (∀z)((z∈x) ⇒ (z∈y)).  Un seul niveau de quantificateur : OK.

    (E II.2, §1.2, Définition 1.)"""
    zt = Assemblage((z,))
    return pour_tout(z, implication(appartient(zt, x), appartient(zt, y)))


# Énoncés A1, A2, Coll : volontairement NON construits ici (gonflement τ
# exponentiel → MemoryError). Ils nécessitent des quantificateurs abréviateurs
# (extension du noyau, à venir). Voir le docstring du module.

__all__ = ["appartient", "inclus"]
