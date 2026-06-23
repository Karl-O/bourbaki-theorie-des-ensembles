"""§III.3.4 — Structure « + un point marqué » de l'ensemble augmenté A ⊔ {∅}
(briques certifiées du cœur back-and-forth de la Proposition 8).

ÉNONCÉ visé (E.III.3.4, Prop. 8) : « Si a et b sont des cardinaux tels que
a + 1 = b + 1, on a a = b. »  Avec le successeur fidèle a + 1 := Card(A ⊔ {∅})
(1 = Card({∅})), le cœur reporté est

        eq_somme_un_implique_eq :  Eq(A ⊔ {∅}, B ⊔ {∅})  ⇒  Eq(A, B),

dont la preuve « back-and-forth à un coup » (analyse de cas sur l'image du marqueur
* = (∅,1), avec échange) est la partie DURE — surgery de graphe sur un témoin
ABSTRAIT h, même catégorie de difficulté que la bijection-somme entière
(ensembles_somme_equipotence, ~950 lignes).  Cf. la note finale.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE ÉTABLIT (briques CERTIFIÉES, toutes CLOSES) — la CARACTÉRISATION
STRUCTURELLE qui sous-tend la preuve : l'ensemble augmenté est la COPIE DE GAUCHE
A×{0} À LAQUELLE ON ADJOINT, DISJOINTEMENT, l'UNIQUE point marqué * = (∅,1).

En effet  A ⊔ {∅} := (A×{0}) ∪ ({∅}×{1})  et  {∅}×{1}  est le singleton {(∅,1)} :

  • marqueur_dans_somme(A)    (clos) — (∅,1) ∈ A ⊔ {∅}            [le marqueur EST dans
        l'ensemble augmenté ; c'est l'élément « en plus »] ;
  • marqueur_hors_copie_gauche(A) (clos) — ¬((∅,1) ∈ A×{0})       [le marqueur n'est PAS
        dans la copie de gauche : sa 2ᵉ coordonnée vaut 1 ≠ 0 — la DISJONCTION des
        copies, vide_distinct_singleton] ;
  • somme_un_plus_point(A)    (clos) — (z ∈ A⊔{∅}) ⇔ ((z ∈ A×{0}) ou (z = (∅,1)))
        [DÉCOMPOSITION : tout élément de l'ensemble augmenté est soit dans la copie de
        gauche, soit le point marqué — A⊔{∅} = (A×{0}) ⊎ {*}].

Ces trois faits sont EXACTEMENT la structure « ensemble plus un point » sur laquelle
repose l'argument de la Proposition 8 : une bijection h : A⊔{∅} → B⊔{∅} envoie le
point marqué *_A=(∅,1) quelque part dans B⊔{∅} = (B×{0}) ⊎ {*_B}, et le cœur consiste
à « réparer » h en une bijection des copies de gauche A×{0} → B×{0} (puis à transporter
par eq_copies_gauches_implique_eq, déjà certifié dans ensembles_copie_marquee).  Les
briques sont paramétrées (A quelconque) donc valent identiquement pour le côté B.

REPORTÉ honnêtement (anti-faux), le cœur lui-même :
        eq_somme_un_implique_eq(A, B) : Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B),
soit la construction de la bijection A→B par analyse de cas sur h(*_A) :
   • CAS 1 (h(*_A)=*_B) : h restreinte aux copies de gauche est une bijection
        A×{0}→B×{0} — RESTRICTION d'un graphe ABSTRAIT (sous-graphe + 4 conjoints) ;
   • CAS 2 (h(*_A)=(b₀,0)) : ∃a₀, h((a₀,0))=*_B ; on ÉCHANGE a₀↦b₀ et on garde h
        ailleurs — surgery de graphe MODIFIÉ avec sélecteur τ sur un témoin abstrait.
Les deux cas demandent de manipuler la bijection abstraite h au niveau du graphe
(restriction / échange ponctuel) puis de rétablir les 4 conjoints de est_bijection_de
contre les seules hypothèses « h bijection A⊔{∅}→B⊔{∅} » — un investissement de
l'ordre d'un round complet, hors budget de cet agent.  Les briques structurelles
ci-dessous sont la fondation certifiée de ce cœur, et l'ASSEMBLAGE final modulo le
cœur est déjà posé (ensembles_prop8_successeur.reduction_back_and_forth).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, egal, et, ou, non, appartient, equiv)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite,
                               equivalence_avant, equivalence_arriere,
                               equivalence_transitivite, equivalence_symetrie,
                               instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (symetrie, composer_egalites,
                                          congruence_terme)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN,
                                       injection_droite_dans_somme,
                                       membre_somme_caracterise,
                                       _membre_produit_singleton, _ou_congruence,
                                       _dans_singleton)
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
from bourbaki.cardinaux.ensembles_vide_singleton import vide_distinct_singleton


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# Le marqueur de droite 1 = {∅}, le point marqué * = (∅, 1).
_SING = E.singleton(E.VIDE)            # {∅} = 1
_STAR = E.couple(E.VIDE, UN)           # * = (∅, 1)


def marqueur():
    """Le point marqué * := (∅, 1)  (l'unique élément de la copie droite {∅}×{1})."""
    return _STAR


# ═══════════════════════════════════════════════════════════════════════════════
# BRIQUE 1 :  (∅,1) ∈ A ⊔ {∅}   (le marqueur est dans l'ensemble augmenté)
# ═══════════════════════════════════════════════════════════════════════════════
def marqueur_dans_somme(a="A"):
    """⊢ (∅, 1) ∈ A ⊔ {∅}.   (le point marqué appartient à l'ensemble augmenté ; clos.)

    L'ensemble augmenté A⊔{∅} = (A×{0}) ∪ ({∅}×{1}) contient toute la copie droite
    {∅}×{1}, dont (∅,1) est l'élément (∅∈{∅}).  Injection canonique de droite
    (injection_droite_dans_somme) appliquée à ∅∈{∅}."""
    va = _t(a)
    inj = injection_droite_dans_somme(E.VIDE, va, _SING)   # (∅∈{∅}) ⇒ (∅,1)∈A⊔{∅}
    return N.modus_ponens(_dans_singleton(E.VIDE), inj)    # (∅,1) ∈ A⊔{∅}


# ═══════════════════════════════════════════════════════════════════════════════
# BRIQUE 2 :  ¬((∅,1) ∈ A×{0})   (le marqueur est HORS de la copie de gauche)
# ═══════════════════════════════════════════════════════════════════════════════
def marqueur_hors_copie_gauche(a="A"):
    """⊢ ¬((∅, 1) ∈ A×{0}).   (le marqueur n'est pas dans la copie de gauche ; clos.)

    Si (∅,1)∈A×{0}, alors par couple_dans_produit_ssi sa 2ᵉ coordonnée 1∈{0}, donc
    1 = 0 (singleton_membre), donc 0 = 1 (symétrie) — ce qui contredit 0 ≠ 1
    (vide_distinct_singleton : ¬(∅={∅})).  La DISJONCTION des copies marquées
    (marqueur 0 ≠ marqueur 1) sépare * de la copie de gauche."""
    va = _t(a)
    A0 = E.produit(va, E.singleton(ZERO))                 # A×{0}
    star_in = appartient(_STAR, A0)                       # (∅,1)∈A×{0}
    ssi = couple_dans_produit_ssi(E.VIDE, UN, va, E.singleton(ZERO))  # (∅,1)∈A×{0} ⇔ (∅∈A et 1∈{0})
    h = N.assume(star_in)
    un_in = conjonction_elim_droite(N.modus_ponens(h, equivalence_avant(ssi)))  # 1∈{0}
    un_eq_zero = N.modus_ponens(un_in, equivalence_avant(singleton_membre(UN, ZERO)))  # 1=0
    zero_eq_un = N.modus_ponens(un_eq_zero, symetrie(UN, ZERO))   # 0=1
    n01 = vide_distinct_singleton()                       # ¬(0=1)
    # ex falso : (0=1) et ¬(0=1) ⊢ ¬((∅,1)∈A×{0})
    falso = N.modus_ponens(zero_eq_un,
                           N.modus_ponens(n01, N.s2(non(egal(ZERO, UN)), non(star_in))))
    return N.modus_ponens(N.loi_deduction(star_in, falso), N.s1(non(star_in)))


# ═══════════════════════════════════════════════════════════════════════════════
# BRIQUE 3 :  z∈A⊔{∅} ⇔ (z∈A×{0}) ou (z=(∅,1))   (DÉCOMPOSITION « + un point »)
# ═══════════════════════════════════════════════════════════════════════════════
def somme_un_plus_point(a="A", z="z"):
    """⊢ (z ∈ A ⊔ {∅}) ⇔ ((z ∈ A×{0}) ou (z = (∅, 1))).   (z : nom ou terme ; clos.)

    DÉCOMPOSITION de l'ensemble augmenté : tout élément est soit dans la copie de
    gauche A×{0}, soit le point marqué * = (∅,1).  C'est la lecture « A⊔{∅} = A×{0}
    avec un point en plus ».  Preuve :
      • membre_somme_caracterise : z∈A⊔{∅} ⇔ ((∃u)(u∈A et z=(u,0)) ou (∃v)(v∈{∅} et z=(v,1))) ;
      • disjoint gauche : (∃u)(u∈A et z=(u,0)) ⇔ z∈A×{0}  (_membre_produit_singleton) ;
      • disjoint droit : (∃v)(v∈{∅} et z=(v,1)) ⇔ z=(∅,1)  (v∈{∅}⇔v=∅, témoin ∅) ;
      • congruence du « ou »."""
    va, vz = _t(a), _t(z)
    A0 = E.produit(va, E.singleton(ZERO))                 # A×{0}
    msc = membre_somme_caracterise(va, _SING, vz)         # z∈A⊔{∅} ⇔ (gauche ou droite)

    # disjoint gauche : (∃u)(u∈A et z=(u,0)) ⇔ z∈A×{0}
    left_equiv = equivalence_symetrie(_membre_produit_singleton(va, ZERO, vz, "u"))

    # disjoint droit : (∃v)(v∈{∅} et z=(v,1)) ⇔ z=(∅,1)
    vv = var("v")
    body_r = et(appartient(vv, _SING), egal(vz, E.couple(vv, UN)))   # v∈{∅} et z=(v,1)
    # ⇒ : v∈{∅}⇒v=∅, donc z=(v,1)=(∅,1)
    hr = N.assume(body_r)
    v_eq = N.modus_ponens(conjonction_elim_gauche(hr),
                          equivalence_avant(singleton_membre(vv, E.VIDE)))   # v=∅
    cpl_eq = N.modus_ponens(v_eq, congruence_terme(vv, E.VIDE, E.couple(var("w"), UN)))  # (v,1)=(∅,1)
    z_star = composer_egalites(conjonction_elim_droite(hr), cpl_eq)          # z=(∅,1)
    fwd_r = existe_elimination(N.loi_deduction(body_r, z_star), "v")         # (∃v)body_r ⇒ z=(∅,1)
    # ⇐ : z=(∅,1) ⇒ (∃v)body_r, témoin v:=∅
    hz = N.assume(egal(vz, _STAR))
    vide_in = N.modus_ponens(N.reflexivite(E.VIDE),
                             equivalence_arriere(singleton_membre(E.VIDE, E.VIDE)))   # ∅∈{∅}
    wit = conjonction_intro(vide_in, hz)                  # ∅∈{∅} et z=(∅,1)
    ex_v = N.modus_ponens(wit, N.s5(body_r, E.VIDE, "v"))  # (∃v)body_r
    bwd_r = N.loi_deduction(egal(vz, _STAR), ex_v)
    right_equiv = conjonction_intro(fwd_r, bwd_r)         # (∃v)body_r ⇔ z=(∅,1)

    ou_cong = _ou_congruence(left_equiv, right_equiv)     # (gauche ou droite) ⇔ (z∈A×{0} ou z=(∅,1))
    return equivalence_transitivite(msc, ou_cong)         # z∈A⊔{∅} ⇔ (z∈A×{0} ou z=(∅,1))


__all__ = ["marqueur", "marqueur_dans_somme", "marqueur_hors_copie_gauche",
           "somme_un_plus_point"]
