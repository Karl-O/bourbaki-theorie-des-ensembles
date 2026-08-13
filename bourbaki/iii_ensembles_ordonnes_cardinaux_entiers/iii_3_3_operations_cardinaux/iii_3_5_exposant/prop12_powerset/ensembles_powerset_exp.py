"""§III.3.5 — Card(𝔓(X)) = 2^Card X  (E.III.3.5, Proposition 12).

Bourbaki (Prop. 12) : « Soient X un ensemble et a son cardinal ; le cardinal de
l'ensemble 𝔓(X) des parties de X est 2^a. »  Le « 2 » est le cardinal du
2-élément  2 = {0, 1} = {∅, {∅}} = paire(∅, {∅}).  Et  2^a := Card(𝓕(X; 2)) =
Card(applications(X, 2))  (Définition 4 : a^b = cardinal des applications de b
dans a — ici BASE = 2, EXPOSANT = X, donc l'objet est 𝓕(X; 2), l'ensemble des
fonctions de X dans {0,1}).

⚠ DISCORDANCE D'ÉNONCÉ (signalée, choix MATHÉMATIQUEMENT correct retenu).  La
fiche de mission écrivait la cible « exposant_cardinal_binaire(X, paire(∅,{∅})) ».
Or exposant_cardinal_binaire(a, b) = Card(𝓕(b; a)) (b = EXPOSANT), donc
exposant_cardinal_binaire(X, 2) = Card(𝓕(2; X)) = X^2  ≠  2^Card X.  La bijection
caractéristique décrite (Y ⊂ X ↦ χ_Y : X → {0,1}) RELIE 𝔓(X) à 𝓕(X; 2), c.-à-d.
à exposant_cardinal_binaire(2, X) = Card(𝓕(X; 2)) = 2^Card X.  C'est donc CETTE
forme — fidèle à Bourbaki « 2^a » et à la bijection χ — qui est retenue ici.

CRUX (la bijection complète) NON CLOS — REPORTÉ avec raison précise (cf. __all__
et la docstring de `bijection_caracteristique_REPORTE`).  Ce module livre les
PALIERS SÛRS, tous CERTIFIÉS par le noyau (rien postulé) :

  • deux()                       le 2-élément  2 = {∅, {∅}} ;
  • deux_membre(z)              ⊢ (z ∈ 2) ⇔ (z = ∅ ou z = {∅}) ;
  • zero_dans_deux / un_dans_deux ⊢ ∅ ∈ 2 ,  ⊢ {∅} ∈ 2 ;
  • deux_elements_distincts     ⊢ ¬(∅ = {∅})   (0 ≠ 1 : 2 a bien DEUX éléments) ;
  • exposant_deux_base(X)       ⊢ exposant_cardinal_binaire(2, X) = Card(𝓕(X; 2))
        (= 2^Card X ; pivot DÉFINITIONNEL identifiant 2^a à l'espace de fonctions) ;
  • cible_powerset_exp(X)       l'ÉNONCÉ-CIBLE de la Proposition 12 (formule, pour
        fixer la signature) ;
  • preimage_un_inclus_REPORTE  esquisse du sens facile 𝓕(X;2) → 𝔓(X).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, non, ou, impl, equiv,
                     appartient, existe, pourtout, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (symetrie,
                               composer_egalites, congruence_terme)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_paire
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import exposant_cardinal_binaire


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Le 2-élément  2 = {0, 1} = {∅, {∅}}  (cardinal 2 ; base de l'exponentiation)
# ═══════════════════════════════════════════════════════════════════════════════
# (le 2-élément {α,β} = {vide,{vide}} de la démo de la Prop.12 : « Soient α et β
#  les éléments du cardinal 2 » — socle + pivot 2^a = Card(F(X;2)).)
# @livre Ch.III §3.5 Demo.12 | E III.29 L.21-21 | PDF p.132
def deux():
    """2 := {∅, {∅}} = paire(∅, singleton(∅))  (le 2-élément {0, 1}, base de 2^a).

    0 = ∅ et 1 = {∅} (= Card({∅}) à équipotence près) ; le 2-élément concret
    {0, 1} = {∅, {∅}} sert de support à l'exponentiation 2^a (E.III.3.5)."""
    return E.paire(E.VIDE, E.singleton(E.VIDE))


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  z ∈ 2 ⇔ (z = ∅ ou z = {∅})   (caractérisation des éléments du 2-élément)
# ═══════════════════════════════════════════════════════════════════════════════
def deux_membre(z="z"):
    """⊢ (z ∈ 2) ⇔ (z = ∅ ou z = {∅}).   (instance de l'axiome de la paire en {∅,{∅}}.)"""
    vz = _t(z)
    return _instance_paire(E.VIDE, E.singleton(E.VIDE), vz)


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  ∅ ∈ 2  et  {∅} ∈ 2   (les deux éléments 0 et 1 appartiennent à 2)
# ═══════════════════════════════════════════════════════════════════════════════
def zero_dans_deux():
    """⊢ ∅ ∈ 2.   (0 = ∅ est élément gauche de la paire {∅, {∅}}.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import membre_paire_gauche
    return membre_paire_gauche(E.VIDE, E.singleton(E.VIDE))


def un_dans_deux():
    """⊢ {∅} ∈ 2.   (1 = {∅} est élément droit de la paire {∅, {∅}}.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import membre_paire_droite
    return membre_paire_droite(E.VIDE, E.singleton(E.VIDE))


# ═══════════════════════════════════════════════════════════════════════════════
# (3)  ¬(∅ = {∅})   (0 ≠ 1 : le 2-élément a bien DEUX éléments distincts)
# ═══════════════════════════════════════════════════════════════════════════════
def deux_elements_distincts():
    """⊢ ¬(∅ = {∅}).   (0 ≠ 1 : 2 = {∅, {∅}} contient deux éléments DISTINCTS.)

    Si ∅ = {∅}, comme ∅ ∈ {∅} (singleton_membre, ∅=∅), Leibniz (S6) donne ∅ ∈ ∅,
    qui contredit l'axiome du vide ¬(∅ ∈ ∅).  Donc ∅ ≠ {∅}."""
    s_vide = E.singleton(E.VIDE)                        # {∅}
    # ∅ ∈ {∅}  (via singleton_membre : (∅∈{∅}) ⇔ (∅=∅), et ∅=∅ par réflexivité)
    vide_in_s = N.modus_ponens(N.reflexivite(E.VIDE),
                               equivalence_arriere(singleton_membre(E.VIDE, E.VIDE)))  # ∅∈{∅}
    # ¬(∅ ∈ ∅)  (instance directe de l'axiome du vide au terme ∅)
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    n_vide_in_vide = instancie(ax_vide, E.VIDE)         # ¬(∅∈∅)
    # sous l'hypothèse ∅ = {∅} : Leibniz (∅={∅}) ⇒ ((∅∈{∅}) ⇔ (∅∈∅))
    h = N.assume(egal(E.VIDE, s_vide))                  # ∅ = {∅}
    leib = N.modus_ponens(h, N.s6(E.VIDE, s_vide, "w",
                                  appartient(E.VIDE, var("w"))))  # (∅∈∅) ⇔ (∅∈{∅})
    vide_in_vide = N.modus_ponens(vide_in_s, equivalence_arriere(leib))  # ∅∈∅   [hyp ∅={∅}]
    # ex falso : ∅∈∅ et ¬(∅∈∅) ⟹ ¬(∅={∅})
    a_imp = N.modus_ponens(n_vide_in_vide,
                           N.s2(non(appartient(E.VIDE, E.VIDE)),
                                non(egal(E.VIDE, s_vide))))   # (∅∈∅) ⇒ ¬(∅={∅})
    absurd = N.modus_ponens(vide_in_vide, a_imp)        # ¬(∅={∅})  [hyp ∅={∅}]
    # ⊢ (∅={∅}) ⇒ ¬(∅={∅}), puis idempotence S1 → ¬(∅={∅})
    imp = N.loi_deduction(egal(E.VIDE, s_vide), absurd)  # (∅={∅}) ⇒ ¬(∅={∅})
    return N.modus_ponens(imp, N.s1(non(egal(E.VIDE, s_vide))))   # ¬(∅={∅})


# ═══════════════════════════════════════════════════════════════════════════════
# (4)  2^Card X = Card(𝓕(X; 2))   (pivot définitionnel ; BASE = 2, EXPOSANT = X)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_deux_base(x="X"):
    """⊢ exposant_cardinal_binaire(2, X) = Card(applications(X, 2)).   (= 2^Card X.)

    Identité DÉFINITIONNELLE (réflexivité d'un terme) : par définition,
    exposant_cardinal_binaire(a, b) = Card(𝓕(b; a)) ; avec a = 2 et b = X cela
    donne LITTÉRALEMENT Card(applications(X, 2)) = 2^Card X — l'ensemble des
    fonctions de X dans {0,1}, support de la fonction caractéristique χ_Y.
    C'est l'objet auquel 𝔓(X) doit être équipotent (Proposition 12)."""
    vX = _t(x)
    lhs = exposant_cardinal_binaire(deux(), vX)         # = Card(applications(X, 2))
    rhs = cardinal(E.applications(vX, deux()))
    # lhs et rhs sont le MÊME terme (def. exposant_cardinal_binaire) ; réflexivité.
    assert lhs == rhs, "exposant_cardinal_binaire(2,X) doit être Card(applications(X,2))"
    return N.reflexivite(lhs)                           # ⊢ 2^Card X = Card(𝓕(X;2))


# ═══════════════════════════════════════════════════════════════════════════════
# L'ÉNONCÉ-CIBLE de la Proposition 12  (formule, fixe la signature de la cible)
# ═══════════════════════════════════════════════════════════════════════════════
def cible_powerset_exp(x="X"):
    """L'ÉNONCÉ visé (Proposition 12) : Card(𝔓(X)) = 2^Card X.

    Renvoie la FORMULE (non un théorème) :  Card(parties(X)) =
    exposant_cardinal_binaire(2, X) = Card(applications(X, 2)).  Fournie pour
    documenter exactement la cible `card_parties_egale_deux_exp` et permettre à un
    chantier futur d'en faire l'assertion une fois la bijection χ close."""
    vX = _t(x)
    return egal(cardinal(E.parties(vX)), exposant_cardinal_binaire(deux(), vX))


# ═══════════════════════════════════════════════════════════════════════════════
# CRUX REPORTÉ : la bijection caractéristique  𝔓(X) → 𝓕(X; {0,1})
# ═══════════════════════════════════════════════════════════════════════════════
def bijection_caracteristique_REPORTE():
    """REPORTÉ (non clos) — la bijection χ : 𝔓(X) → 𝓕(X; {0,1}), Y ↦ χ_Y.

    Raison précise du report : la cible `card_parties_egale_deux_exp` exige de
    construire, pour chaque partie Y ⊂ X, la fonction indicatrice χ_Y : X → {0,1}
    (x ↦ 1 si x∈Y, 0 sinon) PUIS de prouver que Y ↦ χ_Y est une bijection de 𝔓(X)
    sur l'espace de fonctions 𝓕(X; 2) (Proposition 12, quatre conjoints :
    fonctionnel, domaine 𝔓(X), injectif, image = 𝓕(X; 2)).  Trois obstacles, tous
    hors du budget de ce round :

      (i)  χ_Y se définit par un SÉLECTEUR conditionnel (« si x∈Y alors 1 sinon 0 »)
           dont le graphe-terme n'est pas un simple graphe_terme(X, T) mais un
           graphe défini par cas (S8 sur (∀x∈X) puis A1) — primitive ABSENTE ;
      (ii) la SURJECTIVITÉ exige, depuis une f ∈ 𝓕(X; 2) arbitraire, de récupérer
           Y = préimage de 1 = {x∈X | f(x)={∅}} et de prouver χ_Y = f par
           extensionnalité de fonctions (égalité de graphes valeur-par-valeur sur
           tout X), machinerie de fonctions lourde non encore disponible ;
      (iii)l'INJECTIVITÉ exige χ_{Y}=χ_{Y'} ⇒ Y=Y' via la préimage, même verrou.

    Paliers SÛRS livrés à la place (tous clos) : deux(), deux_membre,
    zero_dans_deux, un_dans_deux, deux_elements_distincts (2 a bien deux éléments
    distincts), exposant_deux_base (2^Card X = Card(𝓕(X;2))), cible_powerset_exp
    (l'énoncé exact).  La voie complète passera par une primitive « fonction
    définie par cas / sélecteur » (analogue à graphe_terme mais conditionnel) et
    par l'extensionnalité fonctionnelle, à introduire dans un round dédié."""
    raise NotImplementedError(
        "Bijection caractéristique 𝔓(X)→𝓕(X;2) reportée : sélecteur conditionnel "
        "χ_Y + extensionnalité fonctionnelle (surjectivité/injectivité) absents.")


__all__ = ["deux", "deux_membre", "zero_dans_deux", "un_dans_deux",
           "deux_elements_distincts", "exposant_deux_base",
           "cible_powerset_exp", "bijection_caracteristique_REPORTE"]
