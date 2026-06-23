"""§III.6.3 (Théorème 2, HESSENBERG) — DESCENTES 2𝔟=𝔟 et 3𝔟=𝔟 INCONDITIONNELLES.

CONTEXTE.  `ensembles_hessenberg_2b3b` prouve 2𝔟=𝔟 / 3𝔟=𝔟 en laissant la SEULE
inégalité DESCENDANTE (𝔟+𝔟 ≤ 𝔟, resp. 𝔟+(𝔟+𝔟) ≤ 𝔟) comme HYPOTHÈSE HONNÊTE
explicite.  Cette descente était « verrouillée » par « 2 ≤ 𝔟 », « 3 ≤ 𝔟 »
(« tout entier n vérifie n ≤ 𝔟 pour 𝔟 infini », E.III.45) — désormais DÉVERROUILLÉ
par `fini_inf_egal_infini` / `deux_inf_egal_infini` / `trois_inf_egal_infini`
(ensembles_fini_inf_egal_infini), inconditionnels.

CE MODULE décharge intégralement cette descente : sous l'hypothèse 𝔟·𝔟 = 𝔟 (=
maximal_carre_egal pour 𝔟 = Card S₀ infini), on dérive 𝔟+𝔟 ≤ 𝔟 (resp. 3𝔟 ≤ 𝔟)
DEPUIS « est_cardinal(𝔟) et est_infini(𝔟) et 𝔟·𝔟 = 𝔟 » seuls, et l'on conclut

  • deux_b_egal_b_inconditionnel(b) :
        ( est_cardinal(𝔟) et est_infini(𝔟) et 𝔟·𝔟 = 𝔟 )  ⇒  𝔟 + 𝔟 = 𝔟.

  • trois_b_egal_b_inconditionnel(b) :
        ( est_cardinal(𝔟) et est_infini(𝔟) et 𝔟·𝔟 = 𝔟 )  ⇒  𝔟 + (𝔟+𝔟) = 𝔟.

ROUTE de la descente 𝔟+𝔟 ≤ 𝔟 (E.III.45-46).  Soit DEUXS = {∅}⊔{∅} un ensemble
concret à 2 éléments.
  (A)  distributivité  Card(𝔟×(SING⊔SING)) = Card((𝔟×SING)⊔(𝔟×SING))
       (`distributivite_cardinale`, close 0-hyp, généralisée/instanciée aux termes).
  (B)  Card(𝔟×SING) = 𝔟 sous est_cardinal(𝔟) (`produit_cardinal_un` : Card(𝔟×{∅}) =
       Card 𝔟 ; Card 𝔟 = 𝔟) ; `_sdc` recolle en Card((𝔟×SING)⊔(𝔟×SING)) = 𝔟+𝔟.
       ⇒ EQ1 : 𝔟+𝔟 = Card(𝔟×DEUXS)  [sous est_cardinal(𝔟)].
  (C)  monotonie  (DEUXS ≤ 𝔟) ⇒ Card(𝔟×DEUXS) ≤ Card(𝔟×𝔟)
       (`produit_cardinale_monotone_droite`, sur noms frais puis instanciée).
  (D)  CRUX : DEUXS ≤ 𝔟 sous (est_cardinal(𝔟) et est_infini(𝔟)).  DEUXS est un
       ensemble FINI concret : Card(DEUXS) = 2 (= DEUX, via la bien-définition de la
       somme cardinale `somme_cardinale_bien_definie` appliquée à Eq({∅},1)∧Eq({∅},{∅}),
       car 2 = Card(1⊔{∅})), donc Fini(Card DEUXS) (transport de `fini_deux`) ;
       `fini_inf_egal_infini(Card DEUXS, 𝔟)` donne Card DEUXS ≤ 𝔟 ; Eq(DEUXS, Card DEUXS)
       (`equipotent_son_cardinal`) donne DEUXS ≤ Card DEUXS ; transitivité ⇒ DEUXS ≤ 𝔟.
  (E)  EQ1 + (C) + (D) ⇒ 𝔟+𝔟 ≤ Card(𝔟×𝔟) = 𝔟·𝔟 = 𝔟 (réécrit par l'hyp 𝔟·𝔟=𝔟) ;
       on décharge l'hyp honnête 𝔟+𝔟 ≤ 𝔟 de `deux_b_egal_b`.  loi_deduction sur le
       3-conjoint conclut.

3𝔟 = 𝔟 : identique, avec TROISS = {∅}⊔({∅}⊔{∅}) (Card = 3 = TROIS) et l'hyp honnête
3𝔟 ≤ 𝔟 de `trois_b_egal_b` déchargée.

INVARIANT : theorie_ensembles() = 22.  Aucun axiome nouveau ; RIEN postulé ; les deux
théorèmes sont des IMPLICATIONS dont l'antécédent (est_cardinal et est_infini et 𝔟·𝔟=𝔟)
est entièrement déchargé par loi_deduction.  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, est_cardinal, equipotent,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN, DEUX, TROIS, est_fini
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_distributivite_cardinale import (
    distributivite_cardinale,
)
from bourbaki.cardinaux.arithmetique.ensembles_produit_petits import produit_cardinal_un
from bourbaki.cardinaux.arithmetique.ensembles_somme_equipotence import (
    somme_cardinale_bien_definie,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import _sdc
from bourbaki.cardinaux.ensembles_cardinal_ordre_props import (
    produit_cardinale_monotone_droite,
)
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import est_cardinal_de_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.ensembles_cardinaux_ordre import (
    equipotence_implique_inf_egal, inf_egal_transitive,
)
from bourbaki.cardinaux.ensembles_equipotence_retrait import equipotence_reflexive_pour
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import un_egale_card_singleton
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_deux import fini_deux
from bourbaki.cardinaux.ensembles_fini_inf_egal_infini import fini_inf_egal_infini

from bourbaki.cardinaux.ensembles_hessenberg_2b3b import deux_b_egal_b, trois_b_egal_b

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)


SING = E.singleton(E.VIDE)                       # {∅}  (singleton, 1 élément)
DEUXS = somme_disjointe(SING, SING)              # {∅}⊔{∅}        (2 éléments)
TROISS = somme_disjointe(SING, DEUXS)            # {∅}⊔({∅}⊔{∅})  (3 éléments)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  Eq({∅}, 1)   ( {∅} équipotent à l'entier 1 = Card{∅} ).
# ════════════════════════════════════════════════════════════════════════════
def _eq_sing_un():
    """⊢ Eq({∅}, 1).   (le singleton {∅} est équipotent à l'entier 1.)

    Eq({∅}, Card{∅}) (equipotent_son_cardinal) ; 1 = Card{∅} (un_egale_card_singleton)
    réécrit Card{∅} → 1 (S6/Leibniz)."""
    eqg = N.generalisation("X", equipotent_son_cardinal("X"))
    eq_sing_card = instancie(eqg, SING)                       # Eq({∅}, Card{∅})
    cs_eq_un = N.modus_ponens(un_egale_card_singleton(),
                              symetrie(UN, cardinal(SING)))    # Card{∅} = 1
    s6 = N.s6(cardinal(SING), UN, "w", equipotent(SING, var("w")))
    res = N.modus_ponens(eq_sing_card, equivalence_avant(N.modus_ponens(cs_eq_un, s6)))
    assert res.conclusion == equipotent(SING, UN), "_eq_sing_un : conclusion inattendue"
    return res                                                # Eq({∅}, 1)


def _bien_definie_t(A, B, A1, B1):
    """⊢ (Eq(A,A₁) et Eq(B,B₁)) ⇒ Card(A⊔B) = Card(A₁⊔B₁),  A,B,A₁,B₁ TERMES.

    somme_cardinale_bien_definie n'est pas capture-safe pour des termes composés
    (binders internes F,G,k du graphe somme) ; on la construit sur des NOMS FRAIS
    puis on généralise/instancie aux termes (motif _prop1_direct_t)."""
    base = somme_cardinale_bien_definie("A", "B", "A1", "B1")     # clos 0-hyp
    gen = N.generalisation("A", N.generalisation("B",
        N.generalisation("A1", N.generalisation("B1", base))))
    return instancie(instancie(instancie(instancie(gen, _t(A)), _t(B)), _t(A1)), _t(B1))


# ════════════════════════════════════════════════════════════════════════════
#  Card(DEUXS) = 2   et   Card(TROISS) = 3   (ensembles concrets, INCONDITIONNELS).
# ════════════════════════════════════════════════════════════════════════════
def _card_deuxs_egale_deux():
    """⊢ Card({∅}⊔{∅}) = 2.   (CLOS 0-hyp.)

    2 = Card(1⊔{∅}) (DEUX = successeur(1)).  Bien-définition de la somme cardinale à
    (A={∅},B={∅},A₁=1,B₁={∅}) sous Eq({∅},1) (_eq_sing_un) et Eq({∅},{∅}) (réflexivité)
    donne Card({∅}⊔{∅}) = Card(1⊔{∅}) = 2."""
    eq_sing_un = _eq_sing_un()                                # Eq({∅},1)
    eq_ss = equipotence_reflexive_pour(SING)                  # Eq({∅},{∅})
    bd = _bien_definie_t(SING, SING, UN, SING)                # (Eq∧Eq)⇒Card({∅}⊔{∅})=Card(1⊔{∅})
    res = N.modus_ponens(conjonction_intro(eq_sing_un, eq_ss), bd)
    assert res.conclusion == egal(cardinal(DEUXS), DEUX), \
        "_card_deuxs_egale_deux : conclusion inattendue"
    return res                                                # Card({∅}⊔{∅}) = 2


def _card_troiss_egale_trois():
    """⊢ Card({∅}⊔({∅}⊔{∅})) = 3.   (CLOS 0-hyp.)

    3 = Card(2⊔{∅}) (TROIS = successeur(2)).  Bien-définition à (A={∅}⊔{∅},B={∅},
    A₁=2,B₁={∅}) sous Eq({∅}⊔{∅},2) (de Card({∅}⊔{∅})=2 + Eq(·,Card·)) et Eq({∅},{∅})
    donne Card(({∅}⊔{∅})⊔{∅}) = Card(2⊔{∅}) = 3 ; commutativité ⇒ Card({∅}⊔({∅}⊔{∅}))."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import (
        somme_cardinale_commutative,
    )
    # Eq(DEUXS, 2)  :  Eq(DEUXS, Card DEUXS) puis réécriture Card DEUXS → 2
    eqg = N.generalisation("X", equipotent_son_cardinal("X"))
    eq_deuxs_card = instancie(eqg, DEUXS)                     # Eq(DEUXS, Card DEUXS)
    cd = _card_deuxs_egale_deux()                             # Card DEUXS = 2
    s6 = N.s6(cardinal(DEUXS), DEUX, "w", equipotent(DEUXS, var("w")))
    eq_deuxs_deux = N.modus_ponens(eq_deuxs_card,
                                   equivalence_avant(N.modus_ponens(cd, s6)))   # Eq(DEUXS, 2)
    assert eq_deuxs_deux.conclusion == equipotent(DEUXS, DEUX)
    eq_ss = equipotence_reflexive_pour(SING)                  # Eq({∅},{∅})
    # Card(DEUXS ⊔ {∅}) = Card(2 ⊔ {∅}) = 3
    bd = _bien_definie_t(DEUXS, SING, DEUX, SING)
    card_deuxs_sing = N.modus_ponens(conjonction_intro(eq_deuxs_deux, eq_ss), bd)
    assert card_deuxs_sing.conclusion == egal(
        cardinal(somme_disjointe(DEUXS, SING)), TROIS)
    # commutativité : Card({∅}⊔DEUXS) = Card(DEUXS⊔{∅})  (sur noms frais → termes)
    cbase = somme_cardinale_commutative("A", "B")            # Card(A⊔B)=Card(B⊔A)
    cgen = N.generalisation("A", N.generalisation("B", cbase))
    comm = instancie(instancie(cgen, SING), DEUXS)           # Card({∅}⊔DEUXS)=Card(DEUXS⊔{∅})
    assert comm.conclusion == egal(cardinal(TROISS),
                                   cardinal(somme_disjointe(DEUXS, SING)))
    res = composer_egalites(comm, card_deuxs_sing)           # Card(TROISS)=3
    assert res.conclusion == egal(cardinal(TROISS), TROIS), \
        "_card_troiss_egale_trois : conclusion inattendue"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CRUX (D) : ensemble fini concret S ≤ 𝔟  pour 𝔟 infini.
# ════════════════════════════════════════════════════════════════════════════
def _set_inf_egal_infini(S, n, fini_n_thm, card_S_eq_n, b="b"):
    """⊢ ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ S ≤ 𝔟,  S ensemble fini concret.

    Données : fini_n_thm ⊢ Fini(n) [clos], card_S_eq_n ⊢ Card S = n [clos], avec n un
    cardinal entier (terme).  Route : Fini(Card S) (transport de Fini(n) par Card S = n) +
    est_cardinal(Card S) (est_cardinal_de_cardinal) + fini_inf_egal_infini(Card S, 𝔟)
    ⇒ Card S ≤ 𝔟 ; Eq(S, Card S) ⇒ S ≤ Card S ; transitivité ⇒ S ≤ 𝔟."""
    vb = _t(b)
    cS = cardinal(S)
    assert card_S_eq_n.conclusion == egal(cS, n)
    assert fini_n_thm.conclusion == est_fini(n)

    # Fini(Card S) : réécrire n → Card S dans Fini(·)   (S6 sur n = Card S)
    n_eq_cS = N.modus_ponens(card_S_eq_n, symetrie(cS, n))   # n = Card S
    s6 = N.s6(n, cS, "w", est_fini(var("w")))                # (n=CardS)⇒(Fini n ⇔ Fini Card S)
    fini_cS = N.modus_ponens(fini_n_thm, equivalence_avant(N.modus_ponens(n_eq_cS, s6)))
    assert fini_cS.conclusion == est_fini(cS)

    # est_cardinal(Card S)
    card_cS = est_cardinal_de_cardinal(S)
    assert card_cS.conclusion == est_cardinal(cS)

    # sous (est_cardinal(𝔟) et est_infini(𝔟))
    hyp = et(est_cardinal(vb), est_infini(vb))
    H = N.assume(hyp)
    card_b = conjonction_elim_gauche(H)
    inf_b = conjonction_elim_droite(H)

    # fini_inf_egal_infini(Card S, 𝔟) : (Fini cS et card cS et card 𝔟 et inf 𝔟) ⇒ cS ≤ 𝔟
    fiei = fini_inf_egal_infini(cS, vb)
    ante = et(et(et(est_fini(cS), est_cardinal(cS)), est_cardinal(vb)), est_infini(vb))
    minor = conjonction_intro(conjonction_intro(conjonction_intro(
        fini_cS, card_cS), card_b), inf_b)
    assert minor.conclusion == ante, "_set_inf_egal_infini : antécédent fiei inattendu"
    cS_le_b = N.modus_ponens(minor, fiei)                    # Card S ≤ 𝔟
    assert cS_le_b.conclusion == inf_egal_card(cS, vb)

    # S ≤ Card S   (Eq(S,Card S) ⇒ S ≤ Card S)
    eqS = instancie(N.generalisation("X", equipotent_son_cardinal("X")), S)   # Eq(S, Card S)
    impg = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))      # F reste libre (témoin)
    imp = instancie(instancie(impg, S), cS)
    S_le_cS = N.modus_ponens(eqS, imp)                       # S ≤ Card S
    assert S_le_cS.conclusion == inf_egal_card(S, cS)

    # transitivité : S ≤ Card S ≤ 𝔟  ⇒  S ≤ 𝔟   (F,G restent libres : témoins internes)
    trg = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    tr = instancie(instancie(instancie(trg, S), cS), vb)
    S_le_b = N.modus_ponens(conjonction_intro(S_le_cS, cS_le_b), tr)
    assert S_le_b.conclusion == inf_egal_card(S, vb), "_set_inf_egal_infini : trans inattendue"

    res = N.loi_deduction(hyp, S_le_b)
    assert res.conclusion == impl(hyp, inf_egal_card(S, vb))
    assert res.conclusion not in res.hypotheses, "_set_inf_egal_infini : VACUOUS"
    return res


def _deuxs_inf_egal_infini(b="b"):
    """⊢ ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ DEUXS ≤ 𝔟.   (DEUXS = {∅}⊔{∅}, |·|=2.)"""
    return _set_inf_egal_infini(DEUXS, DEUX, fini_deux(), _card_deuxs_egale_deux(), b)


def _troiss_inf_egal_infini(b="b"):
    """⊢ ( est_cardinal(𝔟) et est_infini(𝔟) ) ⇒ TROISS ≤ 𝔟.   (TROISS = {∅}⊔({∅}⊔{∅}), |·|=3.)"""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_trois_quatre import fini_trois
    return _set_inf_egal_infini(TROISS, TROIS, fini_trois(), _card_troiss_egale_trois(), b)


# ════════════════════════════════════════════════════════════════════════════
#  Brique (A)+(B)+(C) : n𝔟 ≤ Card(𝔟×𝔟)  via un ensemble fini concret S à n éléments.
#  Pour DEUXS (n=2) : 𝔟+𝔟 ≤ Card(𝔟×𝔟).   Pour TROISS (n=3) : Card(𝔟⊔DEUXS) ≤ Card(𝔟×𝔟)
#  via la copie marquée — ici on traite explicitement DEUXS et TROISS.
# ════════════════════════════════════════════════════════════════════════════
def _card_b_sing_egal_b(vb):
    """{ est_cardinal(𝔟) } ⊢ Card(𝔟×{∅}) = 𝔟.

    produit_cardinal_un : Card(𝔟×{∅}) = Card 𝔟 ; Card 𝔟 = 𝔟 (𝔟 cardinal)."""
    pu = instancie(N.generalisation("A", produit_cardinal_un("A")), vb)   # Card(𝔟×{∅})=Card 𝔟
    cb_eq_b = N.modus_ponens(N.assume(est_cardinal(vb)),
                             _cardinal_est_son_cardinal(vb))               # Card 𝔟 = 𝔟
    res = composer_egalites(pu, cb_eq_b)                                   # Card(𝔟×{∅}) = 𝔟
    assert res.conclusion == egal(cardinal(E.produit(vb, SING)), vb)
    return res


def _distrib_b_deuxs(vb):
    """⊢ Card(𝔟×DEUXS) = Card((𝔟×{∅})⊔(𝔟×{∅})).   (distributivité, instanciée aux termes.)"""
    base = distributivite_cardinale("A", "B", "C")           # clos 0-hyp
    gen = N.generalisation("A", N.generalisation("B", N.generalisation("C", base)))
    di = instancie(instancie(instancie(gen, vb), SING), SING)
    bSING = E.produit(vb, SING)
    assert di.conclusion == egal(cardinal(E.produit(vb, DEUXS)),
                                 cardinal(somme_disjointe(bSING, bSING)))
    return di


def _b_plus_b_egal_card_b_deuxs(vb):
    """{ est_cardinal(𝔟) } ⊢ 𝔟 + 𝔟 = Card(𝔟×DEUXS).   (EQ1.)

    (A) distributivité Card(𝔟×DEUXS) = Card((𝔟×{∅})⊔(𝔟×{∅})) ;
    (B) Card(𝔟×{∅}) = 𝔟 ; _sdc recolle Card((𝔟×{∅})⊔(𝔟×{∅})) = 𝔟+𝔟 ; on compose."""
    bSING = E.produit(vb, SING)
    di = _distrib_b_deuxs(vb)                                # Card(𝔟×DEUXS)=Card((𝔟×{∅})⊔(𝔟×{∅}))
    cbS = _card_b_sing_egal_b(vb)                            # Card(𝔟×{∅}) = 𝔟  [est_card(𝔟)]
    sdc = _sdc(bSING, bSING, vb, vb)                         # (Card=𝔟 ∧ Card=𝔟)⇒Card(⊔)=𝔟+𝔟
    recolle = N.modus_ponens(conjonction_intro(cbS, cbS), sdc)   # Card((𝔟×{∅})⊔(𝔟×{∅}))=𝔟+𝔟
    assert recolle.conclusion == egal(cardinal(somme_disjointe(bSING, bSING)),
                                      somme_cardinale_binaire(vb, vb))
    # Card(𝔟×DEUXS) = 𝔟+𝔟   (composer di + recolle)
    eq = composer_egalites(di, recolle)                      # Card(𝔟×DEUXS)=𝔟+𝔟
    bb = somme_cardinale_binaire(vb, vb)
    res = N.modus_ponens(eq, symetrie(cardinal(E.produit(vb, DEUXS)), bb))   # 𝔟+𝔟=Card(𝔟×DEUXS)
    assert res.conclusion == egal(bb, cardinal(E.produit(vb, DEUXS)))
    return res                                               # EQ1 : 𝔟+𝔟 = Card(𝔟×DEUXS)


def _monotone_b_deuxs(vb):
    """⊢ (DEUXS ≤ 𝔟) ⇒ Card(𝔟×DEUXS) ≤ Card(𝔟×𝔟).   (monotonie, sur noms frais → termes.)"""
    base = produit_cardinale_monotone_droite("Bm", "B1m", "Cm")   # (B≤B1)⇒Card(C×B)≤Card(C×B1)
    gen = N.generalisation("Bm", N.generalisation("B1m", N.generalisation("Cm", base)))
    m = instancie(instancie(instancie(gen, DEUXS), vb), vb)
    assert m.conclusion == impl(inf_egal_card(DEUXS, vb),
        inf_egal_card(cardinal(E.produit(vb, DEUXS)), cardinal(E.produit(vb, vb))))
    return m


# ════════════════════════════════════════════════════════════════════════════
#  (1)  deux_b_egal_b_inconditionnel.
# ════════════════════════════════════════════════════════════════════════════
def deux_b_egal_b_inconditionnel(b="b"):
    """🎯 ⊢ ( est_cardinal(𝔟) et est_infini(𝔟) et 𝔟·𝔟 = 𝔟 ) ⇒ 𝔟 + 𝔟 = 𝔟.   (2𝔟=𝔟.)

    Descente 𝔟+𝔟 ≤ 𝔟 DÉCHARGÉE inconditionnellement : EQ1 (𝔟+𝔟=Card(𝔟×DEUXS)),
    monotonie (Card(𝔟×DEUXS) ≤ Card(𝔟×𝔟)) sous DEUXS ≤ 𝔟 (crux, 𝔟 infini), et
    Card(𝔟×𝔟) = 𝔟·𝔟 = 𝔟 (hyp).  On décharge l'hyp honnête 𝔟+𝔟 ≤ 𝔟 de deux_b_egal_b.
    L'antécédent 3-conjoint est ensuite déchargé par loi_deduction.  theorie=22 ;
    conclusion ∉ hyps."""
    vb = _t(b)
    bb = somme_cardinale_binaire(vb, vb)
    bcarre = produit_cardinal_binaire(vb, vb)                # = Card(𝔟×𝔟)
    assert bcarre == cardinal(E.produit(vb, vb))
    cible_eq = egal(bb, vb)
    A3 = et(et(est_cardinal(vb), est_infini(vb)), egal(bcarre, vb))

    H = N.assume(A3)
    card_b = conjonction_elim_gauche(conjonction_elim_gauche(H))   # est_cardinal(𝔟)
    inf_b = conjonction_elim_droite(conjonction_elim_gauche(H))    # est_infini(𝔟)
    bb_eq_b = conjonction_elim_droite(H)                          # 𝔟·𝔟 = 𝔟  (=Card(𝔟×𝔟)=𝔟)
    assert bb_eq_b.conclusion == egal(bcarre, vb)

    # EQ1 : 𝔟+𝔟 = Card(𝔟×DEUXS)   (décharge est_cardinal(𝔟) par hyp)
    eq1 = _cut(_b_plus_b_egal_card_b_deuxs(vb), est_cardinal(vb), card_b)

    # DEUXS ≤ 𝔟   (crux, décharge est_card(𝔟)∧est_infini(𝔟))
    deuxs_le = N.modus_ponens(conjonction_intro(card_b, inf_b), _deuxs_inf_egal_infini(b))
    assert deuxs_le.conclusion == inf_egal_card(DEUXS, vb)

    # Card(𝔟×DEUXS) ≤ Card(𝔟×𝔟)
    mono = N.modus_ponens(deuxs_le, _monotone_b_deuxs(vb))
    assert mono.conclusion == inf_egal_card(cardinal(E.produit(vb, DEUXS)), bcarre)

    # 𝔟+𝔟 ≤ Card(𝔟×𝔟)   (réécrire Card(𝔟×DEUXS) → 𝔟+𝔟 via EQ1, S6 sur LHS de ≤)
    cbD = cardinal(E.produit(vb, DEUXS))
    s6L = N.s6(cbD, bb, "w", inf_egal_card(var("w"), bcarre))     # (Card(𝔟×DEUXS)=𝔟+𝔟)⇒(≤ ⇔ ≤)
    cbD_eq_bb = N.modus_ponens(eq1, symetrie(bb, cbD))           # Card(𝔟×DEUXS)=𝔟+𝔟
    bb_le_bcarre = N.modus_ponens(mono, equivalence_avant(N.modus_ponens(cbD_eq_bb, s6L)))
    assert bb_le_bcarre.conclusion == inf_egal_card(bb, bcarre)

    # 𝔟+𝔟 ≤ 𝔟   (réécrire Card(𝔟×𝔟) → 𝔟 via hyp 𝔟·𝔟=𝔟, S6 sur RHS de ≤)
    s6R = N.s6(bcarre, vb, "w", inf_egal_card(bb, var("w")))      # (𝔟·𝔟=𝔟)⇒(≤ ⇔ ≤)
    bb_le_b = N.modus_ponens(bb_le_bcarre, equivalence_avant(N.modus_ponens(bb_eq_b, s6R)))
    assert bb_le_b.conclusion == inf_egal_card(bb, vb)

    # deux_b_egal_b : { est_cardinal(𝔟), 𝔟+𝔟 ≤ 𝔟 } ⊢ 𝔟+𝔟 = 𝔟  — décharger les deux hyps
    thm = deux_b_egal_b(b)
    thm = _cut(thm, inf_egal_card(bb, vb), bb_le_b)             # décharge 𝔟+𝔟 ≤ 𝔟
    thm = _cut(thm, est_cardinal(vb), card_b)                  # décharge est_cardinal(𝔟)
    assert thm.conclusion == cible_eq, "deux_b_egal_b_incond : conclusion ≠ 𝔟+𝔟=𝔟"

    res = N.loi_deduction(A3, thm)
    assert res.conclusion == impl(A3, cible_eq), "deux_b_egal_b_incond : énoncé inattendu"
    assert res.conclusion not in res.hypotheses, "deux_b_egal_b_incond : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  Brique 3𝔟 : Card(𝔟×TROISS) = Card(𝔟⊔DEUXS)  et  monotonie.
# ════════════════════════════════════════════════════════════════════════════
def _distrib_b_troiss(vb):
    """⊢ Card(𝔟×TROISS) = Card((𝔟×{∅})⊔(𝔟×DEUXS)).   (distributivité 𝔟×({∅}⊔DEUXS).)"""
    base = distributivite_cardinale("A", "B", "C")
    gen = N.generalisation("A", N.generalisation("B", N.generalisation("C", base)))
    di = instancie(instancie(instancie(gen, vb), SING), DEUXS)
    assert di.conclusion == egal(cardinal(E.produit(vb, TROISS)),
        cardinal(somme_disjointe(E.produit(vb, SING), E.produit(vb, DEUXS))))
    return di


def _card_b_deuxs_egal_b_plus_b(vb):
    """{ est_cardinal(𝔟) } ⊢ Card(𝔟×DEUXS) = 𝔟 + 𝔟.   (symétrique d'EQ1.)"""
    eq1 = _b_plus_b_egal_card_b_deuxs(vb)                     # 𝔟+𝔟 = Card(𝔟×DEUXS)
    bb = somme_cardinale_binaire(vb, vb)
    cbD = cardinal(E.produit(vb, DEUXS))
    res = N.modus_ponens(eq1, symetrie(bb, cbD))
    assert res.conclusion == egal(cbD, bb)
    return res


def _trois_b_egal_card_b_troiss(vb):
    """{ est_cardinal(𝔟) } ⊢ 𝔟 + (𝔟+𝔟) = Card(𝔟×TROISS).   (EQ1 pour 3𝔟.)

    distributivité 𝔟×({∅}⊔DEUXS) = (𝔟×{∅})⊔(𝔟×DEUXS) ; Card(𝔟×{∅})=𝔟,
    Card(𝔟×DEUXS)=𝔟+𝔟 ; _sdc recolle en 𝔟 + (𝔟+𝔟)."""
    bSING = E.produit(vb, SING)
    bDEUXS = E.produit(vb, DEUXS)
    di = _distrib_b_troiss(vb)                               # Card(𝔟×TROISS)=Card((𝔟×{∅})⊔(𝔟×DEUXS))
    cbS = _card_b_sing_egal_b(vb)                            # Card(𝔟×{∅}) = 𝔟
    cbD = _card_b_deuxs_egal_b_plus_b(vb)                    # Card(𝔟×DEUXS) = 𝔟+𝔟
    bb = somme_cardinale_binaire(vb, vb)
    sdc = _sdc(bSING, bDEUXS, vb, bb)                        # (Card=𝔟 ∧ Card=𝔟+𝔟)⇒Card(⊔)=𝔟+(𝔟+𝔟)
    recolle = N.modus_ponens(conjonction_intro(cbS, cbD), sdc)
    threeb = somme_cardinale_binaire(vb, bb)                 # 𝔟+(𝔟+𝔟)
    assert recolle.conclusion == egal(cardinal(somme_disjointe(bSING, bDEUXS)), threeb)
    eq = composer_egalites(di, recolle)                     # Card(𝔟×TROISS)=𝔟+(𝔟+𝔟)
    res = N.modus_ponens(eq, symetrie(cardinal(E.produit(vb, TROISS)), threeb))  # 𝔟+(𝔟+𝔟)=Card(𝔟×TROISS)
    assert res.conclusion == egal(threeb, cardinal(E.produit(vb, TROISS)))
    return res


def _monotone_b_troiss(vb):
    """⊢ (TROISS ≤ 𝔟) ⇒ Card(𝔟×TROISS) ≤ Card(𝔟×𝔟)."""
    base = produit_cardinale_monotone_droite("Bm", "B1m", "Cm")
    gen = N.generalisation("Bm", N.generalisation("B1m", N.generalisation("Cm", base)))
    m = instancie(instancie(instancie(gen, TROISS), vb), vb)
    assert m.conclusion == impl(inf_egal_card(TROISS, vb),
        inf_egal_card(cardinal(E.produit(vb, TROISS)), cardinal(E.produit(vb, vb))))
    return m


# ════════════════════════════════════════════════════════════════════════════
#  (2)  trois_b_egal_b_inconditionnel.
# ════════════════════════════════════════════════════════════════════════════
def trois_b_egal_b_inconditionnel(b="b"):
    """🎯 ⊢ ( est_cardinal(𝔟) et est_infini(𝔟) et 𝔟·𝔟 = 𝔟 ) ⇒ Card(𝔟⊔(𝔟⊔𝔟)) = 𝔟.   (3𝔟=𝔟.)

    Conclusion = somme_cardinale_binaire(𝔟, 𝔟⊔𝔟) = 𝔟, la forme EXACTE de trois_b_egal_b
    (2ᵉ sommant = l'ENSEMBLE 𝔟⊔𝔟).  Même schéma que 2𝔟=𝔟 avec TROISS = {∅}⊔({∅}⊔{∅})
    (|·|=3) ; un PONT (bien-définition, invariance par Card) relie la forme interne
    (2ᵉ sommant cardinal 𝔟+𝔟) à la forme cible (2ᵉ sommant ensemble 𝔟⊔𝔟).  EQ1
    (𝔟+(𝔟+𝔟)=Card(𝔟×TROISS)), monotonie (≤ Card(𝔟×𝔟)) sous TROISS ≤ 𝔟 (crux),
    Card(𝔟×𝔟) = 𝔟·𝔟 = 𝔟.  On décharge l'hyp honnête 3𝔟 ≤ 𝔟 de trois_b_egal_b.
    theorie=22 ; conclusion ∉ hyps."""
    vb = _t(b)
    bb = somme_cardinale_binaire(vb, vb)                     # 𝔟+𝔟 = Card(𝔟⊔𝔟)  (CARDINAL)
    bb_set = somme_disjointe(vb, vb)                          # 𝔟⊔𝔟  (ENSEMBLE)
    threeb = somme_cardinale_binaire(vb, bb)                 # Card(𝔟⊔(𝔟+𝔟))  (forme interne, 2ᵉ sommant CARDINAL)
    # forme « 3𝔟 » EXACTE de trois_b_egal_b : 2ᵉ sommant = ENSEMBLE 𝔟⊔𝔟
    threeb_cible = somme_cardinale_binaire(vb, bb_set)        # Card(𝔟⊔(𝔟⊔𝔟))
    bcarre = produit_cardinal_binaire(vb, vb)
    cible_eq = egal(threeb_cible, vb)
    A3 = et(et(est_cardinal(vb), est_infini(vb)), egal(bcarre, vb))

    H = N.assume(A3)
    card_b = conjonction_elim_gauche(conjonction_elim_gauche(H))
    inf_b = conjonction_elim_droite(conjonction_elim_gauche(H))
    bb_eq_b = conjonction_elim_droite(H)                          # 𝔟·𝔟 = 𝔟

    # EQ1 : 𝔟+(𝔟+𝔟) = Card(𝔟×TROISS)   (décharge est_cardinal(𝔟))
    eq1 = _cut(_trois_b_egal_card_b_troiss(vb), est_cardinal(vb), card_b)

    # TROISS ≤ 𝔟   (crux)
    troiss_le = N.modus_ponens(conjonction_intro(card_b, inf_b), _troiss_inf_egal_infini(b))
    assert troiss_le.conclusion == inf_egal_card(TROISS, vb)

    # Card(𝔟×TROISS) ≤ Card(𝔟×𝔟)
    mono = N.modus_ponens(troiss_le, _monotone_b_troiss(vb))
    cbT = cardinal(E.produit(vb, TROISS))
    assert mono.conclusion == inf_egal_card(cbT, bcarre)

    # 𝔟+(𝔟+𝔟) ≤ Card(𝔟×𝔟)   (réécrire Card(𝔟×TROISS) → 3𝔟 via EQ1)
    s6L = N.s6(cbT, threeb, "w", inf_egal_card(var("w"), bcarre))
    cbT_eq = N.modus_ponens(eq1, symetrie(threeb, cbT))          # Card(𝔟×TROISS)=3𝔟
    threeb_le_bcarre = N.modus_ponens(mono, equivalence_avant(N.modus_ponens(cbT_eq, s6L)))
    assert threeb_le_bcarre.conclusion == inf_egal_card(threeb, bcarre)

    # 3𝔟 ≤ 𝔟   (réécrire Card(𝔟×𝔟) → 𝔟 via hyp)
    s6R = N.s6(bcarre, vb, "w", inf_egal_card(threeb, var("w")))
    threeb_le_b = N.modus_ponens(threeb_le_bcarre, equivalence_avant(N.modus_ponens(bb_eq_b, s6R)))
    assert threeb_le_b.conclusion == inf_egal_card(threeb, vb)

    # PONT vers la forme EXACTE de trois_b_egal_b : threeb_cible = threeb.
    #   Card(𝔟⊔(𝔟⊔𝔟)) = Card(𝔟⊔Card(𝔟⊔𝔟))  via bien-définition (Eq(𝔟,𝔟) ∧ Eq(𝔟⊔𝔟, Card(𝔟⊔𝔟))).
    eq_set_card = instancie(N.generalisation("X", equipotent_son_cardinal("X")), bb_set)  # Eq(𝔟⊔𝔟, Card(𝔟⊔𝔟))
    assert eq_set_card.conclusion == equipotent(bb_set, bb)
    eq_bb = equipotence_reflexive_pour(vb)                       # Eq(𝔟,𝔟)
    bd = _bien_definie_t(vb, bb_set, vb, bb)                     # (Eq∧Eq)⇒Card(𝔟⊔(𝔟⊔𝔟))=Card(𝔟⊔Card(𝔟⊔𝔟))
    bridge = N.modus_ponens(conjonction_intro(eq_bb, eq_set_card), bd)
    assert bridge.conclusion == egal(threeb_cible, threeb)      # threeb_cible = threeb
    # réécrire threeb → threeb_cible dans (threeb ≤ 𝔟)
    thr_eq = N.modus_ponens(bridge, symetrie(threeb_cible, threeb))   # threeb = threeb_cible
    s6B = N.s6(threeb, threeb_cible, "w", inf_egal_card(var("w"), vb))
    threeb_cible_le_b = N.modus_ponens(threeb_le_b,
        equivalence_avant(N.modus_ponens(thr_eq, s6B)))         # threeb_cible ≤ 𝔟
    assert threeb_cible_le_b.conclusion == inf_egal_card(threeb_cible, vb)

    # trois_b_egal_b : { est_cardinal(𝔟), 3𝔟 ≤ 𝔟 } ⊢ 3𝔟 = 𝔟  — décharger les deux hyps
    thm = trois_b_egal_b(b)
    thm = _cut(thm, inf_egal_card(threeb_cible, vb), threeb_cible_le_b)     # décharge 3𝔟 ≤ 𝔟
    thm = _cut(thm, est_cardinal(vb), card_b)                  # décharge est_cardinal(𝔟)
    assert thm.conclusion == cible_eq, "trois_b_egal_b_incond : conclusion ≠ 3𝔟=𝔟"

    res = N.loi_deduction(A3, thm)
    assert res.conclusion == impl(A3, cible_eq), "trois_b_egal_b_incond : énoncé inattendu"
    assert res.conclusion not in res.hypotheses, "trois_b_egal_b_incond : VACUOUS"
    return res


__all__ = ["deux_b_egal_b_inconditionnel", "trois_b_egal_b_inconditionnel"]
