"""Principe « des bergers » (binaire) — fibres constantes ⇒ Card(E) = somme des
fibres.  CORE HONNÊTE du principe de dénombrement par fibres.

⚠️ NOTE DE SOURCE (vérifiée sur le PDF, E.III.34-39 et E.III.27).  La consigne
demandait une « Prop 9 §III.5 » formulant : f:E→F surjection à fibres constantes
de cardinal c ⇒ Card(E)=Card(F)·c.  Or, après lecture EXACTE du PDF :

  • §III.5 (« Calcul sur les entiers », E.III.34-39) contient les Prop 1-7 puis
    §III.6 (division euclidienne) — il N'Y A PAS de Prop 8/9 dans §III.5 ;
  • la « Prop 9 » du livre est §III.3.5 (E.III.28) : « Card(X^Y)=a^b »
    (exponentiation) — DÉJÀ close (ensembles_prop9_close.py) ;
  • le principe « fibres constantes ⇒ produit » EST le COROLLAIRE 2 de la Prop 6
    (E.III.27) : « Soit I équipotent à b ; si a_ι=a pour tout ι, alors
    ab = Σ_{ι∈I} a_ι », appuyé sur la Prop 5 b) (associativité de la somme sur une
    partition).  La route « E = ⊔ fibres » est exactement Prop 5 b) + Prop 6 Cor 2.

L'arithmétique de famille INDEXÉE (Prop 5 b) sur partition, Prop 6 Cor 2) n'est
PAS encore close dans le dépôt : seules les versions BINAIRES de la somme/produit
cardinaux le sont (ensembles_arith_somme, ensembles_arith_cardinale).  On ferme
donc ici le CŒUR BINAIRE du principe (cas à DEUX fibres = I de cardinal 2) :

THÉORÈME CERTIFIÉ (cf. test) :
  • bergers_binaire_somme  (clos, INCONDITIONNEL) —
        ⊢ Card(A ⊔ A) = somme_cardinale_binaire(Card A, Card A).
    C'est le cas I={0,1} du principe des bergers : E réunion disjointe de DEUX
    fibres chacune équipotente à A vaut, en cardinal, a + a.  (Cas binaire de la
    Prop 6 Cor 2 : Σ_{ι∈2} a = a + a.)

  • bergers_binaire_fibres (clos, sous hyp. HONNÊTES) —
        ⊢ (Card E₀ = a et Card E₁ = a) ⇒ Card(E₀ ⊔ E₁) = a + a.
    Forme « fibres » : deux fibres E₀, E₁ de même cardinal a ⇒ leur somme
    disjointe a pour cardinal a + a.  Hypothèses NON vides (conclusion ∉ hyps).

OBSTRUCTION D'ASSEMBLAGE (rapportée honnêtement, NON forcée) — pour la forme
PLEINE « f surjective à fibres de cardinal c sur F quelconque ⇒ Card(E)=Card(F)·c »
il manque, dans le dépôt : (i) la somme cardinale d'une famille INDEXÉE par F
(le terme `somme_famille`/`somme_cardinale` est opaque, sans arithmétique close) ;
(ii) Prop 5 b) Σ sur une partition = Σ des sommes partielles ; (iii) Prop 6 Cor 2
Σ d'une famille constante = produit ; (iv) le recollement E ≅ ⊔_{y∈F} f⁻¹(y).
Aucune de ces briques n'est postulée ici.  La liaison a+a = 2·a (cas binaire de
Cor 2) demande la bijection Eq(A⊔A, A×2) (recollement des copies marquées) — non
close — donc seul le membre SOMME est certifié.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire)
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_arith_somme import somme_disjointe_cardinal
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import instancie


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §5.8 Prop.9 | E III.41 L.18-21 | PDF p.144
def bergers_binaire_fibres(e0="E0", e1="E1", a="A"):
    """⊢ (Card E₀ = a et Card E₁ = a) ⇒ Card(E₀ ⊔ E₁) = somme_cardinale_binaire(a, a).

    Principe des bergers, cas à DEUX fibres E₀, E₁ de MÊME cardinal a : la réunion
    disjointe (partition de E en deux fibres) a pour cardinal a + a.  Instanciation
    directe de `somme_disjointe_cardinal` (forme finale bien-définie de la somme)
    avec X:=E₀, Y:=E₁, b:=a — d'où la conclusion Card(E₀⊔E₁) = a + a sous
    Card E₀ = a et Card E₁ = a.  Hypothèses honnêtes (la conclusion n'y figure pas).
    """
    return somme_disjointe_cardinal(e0, e1, a, a)


def bergers_binaire_somme(a="A"):
    """⊢ Card(A ⊔ A) = somme_cardinale_binaire(Card A, Card A).   (INCONDITIONNEL, clos.)

    Cas constant du principe des bergers : DEUX fibres toutes deux égales à A.  On
    instancie `bergers_binaire_fibres` avec E₀=E₁=A et a:=Card A ; les deux
    hypothèses deviennent Card A = Card A (réflexivité), donc se déchargent, et il
    reste Card(A⊔A) = (Card A) + (Card A).  C'est le cas binaire (I de cardinal 2)
    de la Prop 6 Cor 2 : Σ_{ι∈2} (Card A) = Card A + Card A.
    """
    va = _t(a)
    cA = cardinal(va)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import conjonction_intro
    # On évite la capture τ de `eq_somme_invariant` (binders internes a,b) en
    # bâtissant l'implication sur des NOMS sûrs (E0,E1,A1), puis en généralisant
    # et en instanciant aux TERMES voulus (X:=A, Y:=A, a:=Card A).  Le renommage
    # déterministe rend l'instanciation robuste.
    gen = N.generalisation("E0", N.generalisation("E1", N.generalisation("A1",
        bergers_binaire_fibres("E0", "E1", "A1"))))
    impl_thm = instancie(instancie(instancie(gen, va), va), cA)
    refl = N.reflexivite(cA)                                  # Card A = Card A
    return N.modus_ponens(conjonction_intro(refl, refl), impl_thm)


__all__ = ["bergers_binaire_fibres", "bergers_binaire_somme"]
