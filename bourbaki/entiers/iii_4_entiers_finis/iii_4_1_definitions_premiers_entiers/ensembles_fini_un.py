"""§III.4.1 — « 1 EST UN ENTIER NATUREL » :  ⊢ Fini(1).  Deuxième entier concret.

Suite du jalon Fini(0) (ensembles_fini_zero.py).  On certifie par le noyau que le
cardinal 1 = Card({∅}) = successeur(0) est un ENTIER NATUREL au sens de Bourbaki,
c.-à-d.  Fini(1)  :⇔  (1 est un cardinal) ∧ (1 ≠ 1 + 1)   (E.III.4.1, Déf. 1).

Le verrou de la finitude est l'argument de cardinalité « 1 ≠ 2 », ici établi
CONCRÈTEMENT par un argument de tiroirs (pigeonhole) :

  LEMME FONDATEUR (pigeonhole)  pigeonhole_un_deux  (clos) :
        ⊢ ¬ Eq({∅}, {∅} ⊔ {∅})      (« 1 ≠ 2 » : un singleton n'a pas autant
                                       d'éléments que la somme disjointe à 2 copies).

    {∅} ⊔ {∅} = ({∅}×{0}) ∪ ({∅}×{1})  contient DEUX éléments distincts (∅,0) et
    (∅,1), distincts car 0 = ∅ ≠ {∅} = 1 (vide_distinct_singleton) ⇒, par la
    Proposition 1 sur les couples (couple_egal_implique_composantes), (∅,0) ≠ (∅,1).
    Une bijection F : {∅} → {∅}⊔{∅} serait surjective : son image (un sous-ensemble
    déterminé par la seule valeur F(∅), puisque {∅} est un singleton) devrait
    contenir À LA FOIS (∅,0) et (∅,1).  De y ∈ image(F,{∅}) on tire (∅,y) ∈ F
    (l'antécédent d'un élément image, dans un singleton, ne peut être que ∅) ; donc
    (∅,(∅,0)) ∈ F et (∅,(∅,1)) ∈ F ; la FONCTIONNALITÉ de F force alors
    (∅,0) = (∅,1), d'où 0 = 1, c.-à-d. ∅ = {∅} — contradiction.  La bijection se
    réfute donc elle-même, d'où ¬Eq.  (Même patron que vide_non_equipotent_singleton :
    on réfute l'existence d'une bijection.)

Puis on relie ce lemme au successeur, FIDÈLEMENT à la définition 𝔞+1 := Card(𝔞⊔{∅}) :

  • un_egale_card_singleton    (clos) — 1 = Card({∅})   (= successeur(0), reprise de
        successeur_zero_egale_un : Ent.UN := successeur(0)) ;
  • eq_un_singleton            (clos) — Eq(1, {∅})      (1 = Card({∅}) est équipotent
        à {∅} : tout ensemble est équipotent à son cardinal) ;
  • successeur_un_egale_card_deux (clos) — successeur(1) = Card({∅} ⊔ {∅})  (« 1+1 = 2 » :
        successeur(1) = Card(1 ⊔ {∅}) et Eq(1⊔{∅}, {∅}⊔{∅}) [invariance de la somme,
        instanciée AUX TERMES, car 1 ≃ {∅}] donne Card(1⊔{∅}) = Card({∅}⊔{∅})) ;
  • un_distinct_successeur_un   (clos) — ¬(1 = 1 + 1)  (« 1 ≠ 1+1 » : Card({∅}) ≠
        Card({∅}⊔{∅}) par contraposée de la Proposition 1 sur le pigeonhole, puis
        réécriture 1 = Card({∅}) et 1+1 = Card({∅}⊔{∅})) ;
  • un_est_un_cardinal         (clos) — 1 est un cardinal  (1 = Card({∅}) = card de {∅}) ;
  • fini_un                    (clos) — Fini(1) = (1 cardinal) ∧ (1 ≠ 1+1)
        =  1 EST UN ENTIER NATUREL  (E.III.4.1, Déf. 1).  JALON : 2e entier concret.

Tout est CERTIFIÉ par le noyau (aucun axiome nouveau, aucun postulat) et TESTÉ
(test_fini_un.py).  L'invariance de la somme (eq_somme_invariant) est appliquée par
GÉNÉRALISATION-puis-INSTANCIATION aux termes (le même contournement que _prop1_direct_t),
car son APPEL DIRECT au τ-cardinal 1 = Card({∅}) déclenche la collision des liants
internes du τ-cardinal (verrou « cardinaux-paramètres » documenté pour produit/somme) ;
la version prouvée d'abord sur des NOMS de variables, puis instanciée par une unique
substitution déterministe, le contourne.

REPORTÉ honnêtement : Fini(2) = (2 cardinal) ∧ (2 ≠ 2+1), c.-à-d. 2 ≠ 3.  Il
demande ¬Eq({∅}⊔{∅}, ({∅}⊔{∅})⊔{∅}) = « 2 ≠ 3 », un pigeonhole « 2 contre 3 » :
les trois éléments ((∅,0),0), ((∅,1),0), (∅,1) de 3 doivent être atteints par une
fonction injective définie sur un 2-élément, ce qui force deux antécédents égaux —
mais l'argument ne se ramène plus à « image d'un singleton = singleton » (le domaine
n'est plus un singleton) : il faut un raisonnement de cardinalité 2→3 (un VRAI
principe des tiroirs, ou la Prop. 8 d'injectivité du successeur 𝔞+1=𝔟+1⇒𝔞=𝔟, ou la
Prop. 1 Fini(𝔞)⇔Fini(𝔞+1)).  Cette généralisation n'est pas encore disponible.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, non, et, appartient, existe
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (est_bijection_de, cardinal, equipotent)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (equipotent_si_cardinal_egal,
                                       equipotence_symetrique)
from bourbaki.cardinaux.ensembles_equipotence import equipotence_reflexive
from bourbaki.cardinaux.ensembles_vide_singleton import vide_distinct_singleton
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (_eq_son_cardinal_terme,
                                            _prop1_direct_t)
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_somme_equipotence import eq_somme_invariant
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import successeur_zero_egale_un, fini_zero
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (somme_disjointe, ZERO, UN as MARQUEUR_UN,
                                       injection_gauche_dans_somme,
                                       injection_droite_dans_somme)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (couple_egal_implique_composantes,
                                  singleton_membre, membre_paire_gauche)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant, instancie)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination


# ── Objets de base : 1 = Card({∅}) = successeur(0) ; les marqueurs 0 = ∅, 1 = {∅} ──
_VIDE = E.VIDE                       # ∅
_SING = E.singleton(_VIDE)           # {∅}  (= 1 comme marqueur ensembliste)
_CARD_SING = cardinal(_SING)         # Card({∅})  (= 1 comme CARDINAL clean set)
_UN = Ent.UN                         # 1 = successeur(0)   (τ-cardinal nesté de Bourbaki)
_DEUX_SET = somme_disjointe(_SING, _SING)   # {∅} ⊔ {∅}  (= « 2 » ensembliste, copies marquées)


def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.   (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


# ═══════════════════════════════════════════════════════════════════════════════
# LEMME FONDATEUR (pigeonhole) :  ⊢ ¬ Eq({∅}, {∅} ⊔ {∅})   (« 1 ≠ 2 »)
# ═══════════════════════════════════════════════════════════════════════════════
def _membre_image_singleton(y):
    """⊢ (y ∈ image(F, {∅})) ⇒ ((∅, y) ∈ F).   (y terme ; F = var('F').)

    L'antécédent d'un élément de l'image directe de {∅} ne peut être que ∅ : par
    AXIOME_IMAGE, y ∈ F⟨{∅}⟩ ⇔ (∃x)(x∈{∅} et (x,y)∈F) ; sous le corps, x∈{∅} force
    x = ∅ (singleton_membre), d'où (∅,y)∈F par réécriture x→∅ ; ∃-élimination (x non
    libre dans (∅,y)∈F) conclut."""
    vF = var("F")
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    car = instancie(instancie(instancie(ax, vF), _SING), y)   # y∈F⟨{∅}⟩ ⇔ (∃x)(x∈{∅} et (x,y)∈F)
    vx = var("x")
    body = et(appartient(vx, _SING), appartient(E.couple(vx, y), vF))   # x∈{∅} et (x,y)∈F
    hb = N.assume(body)
    x_eq_vide = N.modus_ponens(conjonction_elim_gauche(hb),
                               equivalence_avant(singleton_membre(vx, _VIDE)))   # x = ∅
    leib = N.modus_ponens(x_eq_vide,
                          N.s6(vx, _VIDE, "w", appartient(E.couple(var("w"), y), vF)))
    vide_y = N.modus_ponens(conjonction_elim_droite(hb), equivalence_avant(leib))   # (∅,y)∈F
    imp = existe_elimination(N.loi_deduction(body, vide_y), "x")   # (∃x)body ⇒ (∅,y)∈F
    hy = N.assume(appartient(y, E.image(vF, _SING)))
    ex = N.modus_ponens(hy, equivalence_avant(car))               # (∃x)body
    return N.loi_deduction(appartient(y, E.image(vF, _SING)), N.modus_ponens(ex, imp))


def pigeonhole_un_deux():
    """⊢ ¬ Eq({∅}, {∅} ⊔ {∅}).   (LEMME FONDATEUR « 1 ≠ 2 » par principe des tiroirs.)

    Pour une bijection F : {∅} → {∅}⊔{∅}, la surjectivité donne image(F,{∅}) = {∅}⊔{∅},
    qui contient (∅,0) et (∅,1) (injections canoniques, ∅∈{∅}).  Donc (∅,(∅,0))∈F et
    (∅,(∅,1))∈F (_membre_image_singleton) ; la fonctionnalité de F force (∅,0)=(∅,1),
    d'où 0=1 (couple_egal_implique_composantes), soit ∅={∅} — contredisant
    vide_distinct_singleton.  F se réfute, d'où ¬Eq (S1 sur Eq⇒¬Eq via ∃-élim de F)."""
    vF = var("F")
    bij = est_bijection_de(vF, _SING, _DEUX_SET)              # F bijection {∅} → {∅}⊔{∅}
    Eq = equipotent(_SING, _DEUX_SET)                         # (∃F)bij
    hbij = N.assume(bij)
    # est_bijection_de = et(et(func, dom), et(injective_dans, est_surjective))
    func = conjonction_elim_gauche(conjonction_elim_gauche(hbij))   # est_fonctionnel(F)
    surj = conjonction_elim_droite(conjonction_elim_droite(hbij))   # image(F,{∅}) = {∅}⊔{∅}

    c0 = E.couple(_VIDE, ZERO)                               # (∅, 0)
    c1 = E.couple(_VIDE, MARQUEUR_UN)                        # (∅, 1)
    vide_in_sing = membre_paire_gauche(_VIDE, _VIDE)         # ∅ ∈ {∅}   (= {∅,∅})
    c0_in_S = N.modus_ponens(vide_in_sing,
                             injection_gauche_dans_somme(_VIDE, _SING, _SING))   # (∅,0) ∈ {∅}⊔{∅}
    c1_in_S = N.modus_ponens(vide_in_sing,
                             injection_droite_dans_somme(_VIDE, _SING, _SING))   # (∅,1) ∈ {∅}⊔{∅}

    # surjectivité : {∅}⊔{∅} = image(F,{∅})  → réécrire c∈{∅}⊔{∅} en c∈image(F,{∅})
    S_eq_img = N.modus_ponens(surj, symetrie(E.image(vF, _SING), _DEUX_SET))   # {∅}⊔{∅} = image(F,{∅})

    def _into_image(c, c_in_S):
        equ = N.modus_ponens(S_eq_img,
                             N.s6(_DEUX_SET, E.image(vF, _SING), "w", appartient(c, var("w"))))
        return N.modus_ponens(c_in_S, equivalence_avant(equ))   # c ∈ image(F,{∅})

    c0_in_img = _into_image(c0, c0_in_S)
    c1_in_img = _into_image(c1, c1_in_S)
    vc0_in_F = N.modus_ponens(c0_in_img, _membre_image_singleton(c0))   # (∅, (∅,0)) ∈ F
    vc1_in_F = N.modus_ponens(c1_in_img, _membre_image_singleton(c1))   # (∅, (∅,1)) ∈ F

    # fonctionnalité : ((∅,(∅,0))∈F et (∅,(∅,1))∈F) ⇒ (∅,0)=(∅,1)
    func_inst = instancie(instancie(instancie(func, _VIDE), c0), c1)
    c0_eq_c1 = N.modus_ponens(conjonction_intro(vc0_in_F, vc1_in_F), func_inst)   # (∅,0) = (∅,1)
    both = N.modus_ponens(c0_eq_c1, couple_egal_implique_composantes(_VIDE, ZERO, _VIDE, MARQUEUR_UN))
    zero_eq_un = conjonction_elim_droite(both)               # 0 = 1   c.-à-d.  ∅ = {∅}

    vds = vide_distinct_singleton()                          # ¬(∅ = {∅})
    notEq_under = _ex_falso(zero_eq_un, vds, non(Eq))        # ¬Eq   (sous bij)
    Eq_imp = existe_elimination(N.loi_deduction(bij, notEq_under), "F")   # Eq ⇒ ¬Eq  (F non libre)
    return N.modus_ponens(Eq_imp, N.s1(non(Eq)))            # ¬Eq({∅}, {∅}⊔{∅})


# ═══════════════════════════════════════════════════════════════════════════════
# 1 = Card({∅})  et  Eq(1, {∅})
# ═══════════════════════════════════════════════════════════════════════════════
def un_egale_card_singleton():
    """⊢ 1 = Card({∅}).   (« 1 = successeur(0) = Card({∅}) », reprise directe de
    successeur_zero_egale_un : Ent.UN := successeur(0).)"""
    return successeur_zero_egale_un()                         # successeur(0) = Card({∅}) = 1 = Card({∅})


def eq_un_singleton():
    """⊢ Eq(1, {∅}).   (1 = Card({∅}) est équipotent à {∅}.)

    Eq({∅}, Card({∅})) (tout ensemble est équipotent à son cardinal, _eq_son_cardinal_terme),
    symétrie → Eq(Card({∅}), {∅}), puis réécriture Card({∅}) → 1 (par 1 = Card({∅}),
    Leibniz) donne Eq(1, {∅})."""
    eq_sing_CS = _eq_son_cardinal_terme(_SING)               # Eq({∅}, Card({∅}))
    sym_all = N.generalisation("X", N.generalisation("Y", equipotence_symetrique("F", "X", "Y")))
    sym_inst = instancie(instancie(sym_all, _SING), _CARD_SING)   # Eq({∅},Card{∅}) ⇒ Eq(Card{∅},{∅})
    eq_CS_sing = N.modus_ponens(eq_sing_CS, sym_inst)        # Eq(Card({∅}), {∅})
    un_eq = un_egale_card_singleton()                        # 1 = Card({∅})
    CS_eq_un = N.modus_ponens(un_eq, symetrie(_UN, _CARD_SING))   # Card({∅}) = 1
    leib = N.s6(_CARD_SING, _UN, "w", equipotent(var("w"), _SING))   # (Card{∅}=1)⇒(Eq(Card{∅},{∅})⇔Eq(1,{∅}))
    return N.modus_ponens(eq_CS_sing, equivalence_avant(N.modus_ponens(CS_eq_un, leib)))   # Eq(1, {∅})


# ═══════════════════════════════════════════════════════════════════════════════
# « 1 + 1 = 2 »  au niveau du SUCCESSEUR :  successeur(1) = Card({∅} ⊔ {∅})
# ═══════════════════════════════════════════════════════════════════════════════
def successeur_un_egale_card_deux():
    """⊢ successeur(1) = Card({∅} ⊔ {∅}).   (« 1 + 1 = 2 », E.III.4.1.)

    successeur(1) = Card(1 ⊔ {∅})  [définition fidèle du successeur].  Comme Eq(1, {∅})
    (eq_un_singleton) et Eq({∅}, {∅}) (réflexivité), l'INVARIANCE de la somme cardinale
    (eq_somme_invariant) donne Eq(1 ⊔ {∅}, {∅} ⊔ {∅}), d'où Card(1⊔{∅}) = Card({∅}⊔{∅})
    (Proposition 1, sens direct, version TERME).  Donc successeur(1) = Card({∅}⊔{∅}) = 2.

    ⚠ eq_somme_invariant est appliquée par GÉNÉRALISATION-puis-INSTANCIATION aux termes
    (1, {∅}, {∅}, {∅}) : son APPEL DIRECT au τ-cardinal 1 = Card({∅}) casse (collision
    des liants internes du τ-cardinal) ; prouvée d'abord sur des NOMS puis instanciée par
    une unique substitution déterministe, elle traverse — même contournement que _prop1_direct_t."""
    succ1 = Ent.successeur(_UN)                              # = Card(1 ⊔ {∅})
    AB = somme_disjointe(_UN, _SING)                         # 1 ⊔ {∅}
    # Eq(1 ⊔ {∅}, {∅} ⊔ {∅})  via invariance instanciée aux termes
    eq_un = eq_un_singleton()                                # Eq(1, {∅})
    refl_all = N.generalisation("X", equipotence_reflexive("X"))
    eq_sing_sing = instancie(refl_all, _SING)               # Eq({∅}, {∅})
    inv = eq_somme_invariant("F", "G", "A", "B", "A1", "B1")   # (Eq(A,A₁)et Eq(B,B₁))⇒Eq(A⊔B,A₁⊔B₁)
    gen = N.generalisation("A", N.generalisation("B",
        N.generalisation("A1", N.generalisation("B1", inv))))
    inst = instancie(instancie(instancie(instancie(gen, _UN), _SING), _SING), _SING)
    eq_sum = N.modus_ponens(conjonction_intro(eq_un, eq_sing_sing), inst)   # Eq(1⊔{∅}, {∅}⊔{∅})
    # Card(1⊔{∅}) = Card({∅}⊔{∅})  (Proposition 1, sens direct, version TERME)
    prop1 = _prop1_direct_t(AB, _DEUX_SET)                  # Eq(1⊔{∅},{∅}⊔{∅}) ⇒ Card(1⊔{∅})=Card({∅}⊔{∅})
    return N.modus_ponens(eq_sum, prop1)                    # successeur(1) = Card({∅}⊔{∅})


# ═══════════════════════════════════════════════════════════════════════════════
# « 1 ≠ 1 + 1 »  :  ¬(1 = successeur(1))
# ═══════════════════════════════════════════════════════════════════════════════
def un_distinct_successeur_un():
    """⊢ ¬(1 = 1 + 1).   (« 1 ≠ 1+1 » : le successeur de 1 diffère de 1, E.III.4.1.)

    1 = Card({∅}) (un_egale_card_singleton) et 1+1 = successeur(1) = Card({∅}⊔{∅})
    (successeur_un_egale_card_deux).  Or Card({∅}) ≠ Card({∅}⊔{∅}) : sinon, par la
    Proposition 1 (sens Card X=Card Y ⇒ Eq), on aurait Eq({∅}, {∅}⊔{∅}), que réfute le
    pigeonhole (pigeonhole_un_deux).  D'où ¬(Card({∅})=Card({∅}⊔{∅})) ; les réécritures
    Card({∅}) → 1 et Card({∅}⊔{∅}) → successeur(1) (Leibniz) concluent ¬(1=successeur(1))."""
    succ1 = Ent.successeur(_UN)
    card_deux = cardinal(_DEUX_SET)                          # Card({∅}⊔{∅})
    # ¬(Card({∅}) = Card({∅}⊔{∅}))  par contraposée de la Proposition 1 (sens ⇐) sur le pigeonhole
    gen = N.generalisation("X", N.generalisation("Y", equipotent_si_cardinal_egal("X", "Y")))
    esce = instancie(instancie(gen, _SING), _DEUX_SET)      # (Card{∅}=Card{∅}⊔{∅}) ⇒ Eq({∅},{∅}⊔{∅})
    pigeon = pigeonhole_un_deux()                           # ¬Eq({∅}, {∅}⊔{∅})
    h = N.assume(egal(_CARD_SING, card_deux))
    eqES = N.modus_ponens(h, esce)                          # Eq({∅},{∅}⊔{∅})  (sous Card{∅}=Card{∅}⊔{∅})
    falso = N.modus_ponens(eqES, N.modus_ponens(pigeon,
        N.s2(non(equipotent(_SING, _DEUX_SET)), non(egal(_CARD_SING, card_deux)))))
    imp = N.loi_deduction(egal(_CARD_SING, card_deux), falso)
    ne_card = N.modus_ponens(imp, N.s1(non(egal(_CARD_SING, card_deux))))   # ¬(Card{∅}=Card{∅}⊔{∅})

    # réécrire Card({∅}) → 1  (via 1 = Card({∅}))  PUIS  Card({∅}⊔{∅}) → successeur(1)
    un_eq = un_egale_card_singleton()                       # 1 = Card({∅})
    # ¬(1 = Card({∅}⊔{∅}))  :  réécrit la 1ʳᵉ composante Card({∅}) → 1
    leib1 = N.s6(_CARD_SING, _UN, "w", non(egal(var("w"), card_deux)))   # (Card{∅}=1)⇒(¬(Card{∅}=·)⇔¬(1=·))
    CS_eq_un = N.modus_ponens(un_eq, symetrie(_UN, _CARD_SING))          # Card({∅}) = 1
    ne1 = N.modus_ponens(ne_card, equivalence_avant(N.modus_ponens(CS_eq_un, leib1)))   # ¬(1 = Card{∅}⊔{∅})
    # ¬(1 = successeur(1))  :  réécrit la 2ᵉ composante Card({∅}⊔{∅}) → successeur(1)
    succ1_eq = successeur_un_egale_card_deux()              # successeur(1) = Card({∅}⊔{∅})
    cdeux_eq_succ1 = N.modus_ponens(succ1_eq, symetrie(succ1, card_deux))   # Card({∅}⊔{∅}) = successeur(1)
    leib2 = N.s6(card_deux, succ1, "w", non(egal(_UN, var("w"))))   # (Card{∅}⊔{∅}=succ1)⇒(¬(1=·)⇔¬(1=succ1))
    return N.modus_ponens(ne1, equivalence_avant(N.modus_ponens(cdeux_eq_succ1, leib2)))   # ¬(1 = successeur(1))


# ═══════════════════════════════════════════════════════════════════════════════
# « 1 est un cardinal »  (1er conjoint de Fini(1))
# ═══════════════════════════════════════════════════════════════════════════════
def un_est_un_cardinal():
    """⊢ 1 est un cardinal  =  ⊢ (∃X)(1 = Card(X)).   (E.III.3.1, Déf. 2.)

    1 = Card({∅}) (un_egale_card_singleton) est de la forme Card(X) (témoin X := {∅}).
    On part de est_cardinal(Card({∅})) = card_est_un_cardinal({∅}) (∃X)(Card{∅}=Card X),
    et on réécrit Card({∅}) → 1 dans le membre gauche du « = » sous le ∃ (Leibniz)."""
    vX = var("X")
    card_sing_is_card = card_est_un_cardinal(_SING, "X")    # (∃X)(Card({∅}) = Card X)
    un_eq = un_egale_card_singleton()                       # 1 = Card({∅})
    # réécrire Card({∅}) → 1 sous le ∃X : congruence de la matrice (Card{∅}=Card X) ⇔ (1=Card X)
    CS_eq_un = N.modus_ponens(un_eq, symetrie(_UN, _CARD_SING))   # Card({∅}) = 1
    matrice_equiv = N.modus_ponens(CS_eq_un,
        N.s6(_CARD_SING, _UN, "w", egal(var("w"), cardinal(vX))))   # (Card{∅}=Card X)⇔(1=Card X)
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import congruence_existe
    cong = congruence_existe(matrice_equiv, "X")            # (∃X)(Card{∅}=Card X) ⇔ (∃X)(1=Card X)
    return N.modus_ponens(card_sing_is_card, equivalence_avant(cong))   # est_cardinal(1)


# ═══════════════════════════════════════════════════════════════════════════════
# « 1 EST UN ENTIER NATUREL »  :  ⊢ Fini(1)   (JALON, E.III.4.1, Déf. 1)
# ═══════════════════════════════════════════════════════════════════════════════
def fini_un():
    """⊢ Fini(1)  =  (1 est un cardinal) ∧ (1 ≠ 1 + 1).   (1 EST UN ENTIER NATUREL.)

    Déf. 1 (E.III.4.1) : Fini(𝔞) :⇔ (𝔞 cardinal) ∧ (𝔞 ≠ 𝔞+1).  Pour 𝔞 = 1 = Card({∅}),
    les DEUX conjoints sont certifiés : un_est_un_cardinal et un_distinct_successeur_un.
    Leur conjonction EST Fini(1) = est_fini(1).  Deuxième ENTIER NATUREL concret après
    Fini(0), établi par un argument de tiroirs (1 ≠ 2)."""
    card1 = un_est_un_cardinal()                            # 1 est un cardinal
    ne = un_distinct_successeur_un()                       # 1 ≠ 1+1
    return conjonction_intro(card1, ne)                   # Fini(1)


__all__ = ["pigeonhole_un_deux", "un_egale_card_singleton", "eq_un_singleton",
           "successeur_un_egale_card_deux", "un_distinct_successeur_un",
           "un_est_un_cardinal", "fini_un"]
