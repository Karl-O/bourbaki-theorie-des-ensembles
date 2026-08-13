"""§III.6 — ℵ₀ EST UN CARDINAL INFINI : conséquences CLOSES de ℵ₀ = ℵ₀ + 1.

🎯 Ce module RÉCOLTE, INCONDITIONNELLEMENT (theorie_ensembles() = 22, rien postulé),
les énoncés §III.6 directement atteignables une fois établie l'ÉQUATION DE L'INFINI

        ℵ₀  =  ℵ₀ + 1            (aleph0_egal_succ, ensembles_aleph0.py — CLOS)

pour le cardinal CONCRET ℵ₀ := Card(ℕ) (ℕ = ensemble_NN(), l'ensemble des entiers).

⚠️ ℵ₀ CONCRET vs ℵ₀ OPAQUE.  ensembles_infinis.py emploie un terme OPAQUE N := app("N")
(la collectivisation « z∈N ⇔ Fini z », Théorème 1, est REPORTÉE), donc son aleph0() =
Card(app("N")) N'EST PAS le cardinal concret.  Tout ce module travaille avec le ℕ
CONCRET ensemble_NN() et son cardinal aleph_0() := Card(ensemble_NN()), pour lesquels
l'équation ℵ₀ = ℵ₀+1 est PROUVÉE.  (Le pont app("N") = ensemble_NN() reste reporté.)

────────────────────────────────────────────────────────────────────────────────
THÉORÈMES CLOS (est_clos = True, 0 hyp, theorie = 22) :

  • aleph0_est_cardinal       ⊢ est_cardinal(ℵ₀)            [Card X est un cardinal]
  • aleph0_plus_un_egal       ⊢ ℵ₀ + 1 = ℵ₀                 [forme « absorption », sym. de
                                  aleph0_egal_succ : successeur(ℵ₀) = ℵ₀+1 LITTÉRALEMENT]
  • aleph0_est_infini         ⊢ est_infini(ℵ₀)              [= ¬Fini(ℵ₀), aleph0_infini]
  • NN_est_infini_ensemble    ⊢ est_infini_ensemble(ℕ)      [ℕ est un ensemble infini]
  • dedekind_aleph0           ⊢ est_infini(ℵ₀) ⇔ (ℵ₀ = ℵ₀+1)  [Dedekind appliqué à ℵ₀,
                                  garde est_cardinal(ℵ₀) DÉCHARGÉE — donc INCONDITIONNEL]
  • aleph0_inf_egal_reflexif  ⊢ ℵ₀ ≤ ℵ₀                     [≤ réflexif ; « ℕ est dénombrable »
                                  au sens cardinal Card(ℕ) ≤ ℵ₀]
  • NN_denombrable            ⊢ est_denombrable(ℕ)          [Déf. 3 : témoin Y=ℕ (ℕ⊂ℕ et Eq(ℕ,ℕ))]
  • existe_cardinal_infini_concret ⊢ (∃a) est_infini(a)     [ℵ₀ témoin — A4 RÉALISÉ
                                  CONCRÈTEMENT, sans recourir à l'axiome A4]

⚠️ INVARIANT : aucun N.axiome ajouté à theorie_ensembles() (=22).  Tous les théorèmes
   ci-dessus sont CLOS (0 hyp).  Pour dedekind_aleph0, la garde honnête est_cardinal(ℵ₀)
   est PROUVÉE (card_est_un_cardinal) puis DÉCHARGÉE — l'équivalence est donc réellement
   inconditionnelle pour ℵ₀.  Anti-vacuité : chaque conclusion a un CONTENU (≠ P⇒P).

⚠️ REPORTÉ (frontière §III.6, anti-faux) :
   • ℵ₀ + n = ℵ₀ pour n entier quelconque, ℵ₀ + ℵ₀ = ℵ₀, ℵ₀·ℵ₀ = ℵ₀ (Th. 2) :
     ARITHMÉTIQUE CARDINALE INFINIE par récurrence / produit infini, absente.
   • ℵ₀ ≤ a pour tout cardinal infini a (ℵ₀ plus petit infini, Th. 1) :
     collectivisation de ℕ + « tout entier ≤ a » + sup, REPORTÉ
     (aleph0_inf_egal_cardinal_infini_enonce, ensembles_infinis_props.py).
   • Prop. 1-5 (clôture des dénombrables : partie/produit fini/réunion de suite ;
     infini dénombrable ≃ ℕ) : reposent sur Th. 2 / arithmétique infinie.
   • Cantor « 𝔓(ℕ) non dénombrable » : Cantor (Card X < Card 𝔓 X) au niveau ℕ.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, egal, et, non, equiv, impl,
                                       inclus, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, equipotent, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import aleph_0, aleph0_egal_succ, aleph0_infini

from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  (1) ℵ₀ EST UN CARDINAL  (ℵ₀ = Card(ℕ), et Card X est toujours un cardinal)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.1 Rem.- | E III.45 L.21-22 | PDF p.148  (« Le cardinal de N se note aussi ℵ₀ » : ℵ₀ est bien un cardinal)
def aleph0_est_cardinal():
    """🎯 ⊢ est_cardinal(ℵ₀).   (THÉORÈME CLOS, 0 hyp — ℵ₀ est un cardinal.)

    ℵ₀ := Card(ℕ) (ℕ = ensemble_NN()).  « Card X est un cardinal » (card_est_un_cardinal,
    1ᵉʳ conjoint de Fini, E.III.3.1) instancié en X := ℕ donne est_cardinal(Card ℕ) =
    est_cardinal(ℵ₀).  theorie = 22."""
    NN = ensemble_NN()
    # binder « X » aligné sur le défaut de est_cardinal (= (∃X)(a = Card X))
    res = card_est_un_cardinal(NN, lieur="X")               # est_cardinal(Card ℕ) = est_cardinal(ℵ₀)
    assert res.conclusion == est_cardinal(aleph_0()), \
        "aleph0_est_cardinal : conclusion ≠ est_cardinal(ℵ₀)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (2) ℵ₀ + 1 = ℵ₀   (ABSORPTION du 1 — forme « somme » de aleph0_egal_succ)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.1 Rem.- | E III.45 L.21-22 | PDF p.148  (ℵ₀+1 = ℵ₀, cas n=1 de « ℵ₀+n = ℵ₀ » — hors texte, sert la Déf. 1)
def aleph0_plus_un_egal():
    """🎯 ⊢ ( ℵ₀ + 1 ) = ℵ₀.   (THÉORÈME CLOS, 0 hyp — l'absorption du 1.)

    successeur(a) := a + 1 := somme_cardinale_binaire(a, {∅}) (E.III.4.1, fidèle à
    Bourbaki).  aleph0_egal_succ établit ℵ₀ = successeur(ℵ₀) = ℵ₀ + 1 ; la SYMÉTRIE de
    l'égalité donne ℵ₀ + 1 = ℵ₀.  C'est le cas n = 1 de « ℵ₀ + n = ℵ₀ » (les n ≥ 2 et
    ℵ₀ + ℵ₀ = ℵ₀ exigent l'arithmétique cardinale infinie, REPORTÉE).  theorie = 22."""
    a0 = aleph_0()                                          # ℵ₀ = Card(ℕ)
    succ_a0 = successeur(a0)                                # ℵ₀ + 1 = somme_cardinale_binaire(ℵ₀,{∅})
    eq = aleph0_egal_succ()                                 # ℵ₀ = ℵ₀ + 1   (CLOS)
    assert eq.conclusion == egal(a0, succ_a0), \
        "aleph0_plus_un_egal : aleph0_egal_succ ≠ (ℵ₀ = ℵ₀+1)"
    res = N.modus_ponens(eq, symetrie(a0, succ_a0))        # ℵ₀ + 1 = ℵ₀
    assert res.conclusion == egal(succ_a0, a0), \
        "aleph0_plus_un_egal : conclusion ≠ (ℵ₀+1 = ℵ₀)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (3) ℵ₀ EST INFINI  (au niveau CARDINAL : est_infini(ℵ₀) = ¬Fini(ℵ₀))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.1 Demo.1 | E III.45 L.10-13 | PDF p.148  (« l'ensemble des entiers E est un ensemble infini » : ℵ₀ infini, réalisé sur le ℕ concret)
def aleph0_est_infini():
    """🎯 ⊢ est_infini(ℵ₀).   (THÉORÈME CLOS, 0 hyp — ℵ₀ est un cardinal infini.)

    est_infini(𝔞) := ¬Fini(𝔞) (Déf. 1, §III.6.1).  aleph0_infini établit ¬Fini(ℵ₀) ;
    c'est LITTÉRALEMENT est_infini(ℵ₀).  PREMIER CARDINAL INFINI CONCRET, ré-exposé au
    niveau du prédicat §III.6.  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
    a0 = aleph_0()
    res = aleph0_infini()                                   # ¬Fini(ℵ₀)
    assert res.conclusion == est_infini(a0), \
        "aleph0_est_infini : ¬Fini(ℵ₀) ≠ est_infini(ℵ₀)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (4) ℕ EST UN ENSEMBLE INFINI  (est_infini_ensemble(ℕ) = ¬Fini(Card ℕ))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.1 Demo.1 | E III.45 L.10-13 | PDF p.148  (ℕ est un ensemble infini)
def NN_est_infini_ensemble():
    """🎯 ⊢ est_infini_ensemble(ℕ).   (THÉORÈME CLOS, 0 hyp — ℕ est un ensemble infini.)

    est_infini_ensemble(E) := ¬Fini(Card E) (Déf. 1, §III.6.1).  Pour E = ℕ =
    ensemble_NN(), Card ℕ = ℵ₀ et aleph0_infini donne ¬Fini(ℵ₀) = ¬Fini(Card ℕ) =
    est_infini_ensemble(ℕ).  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini_ensemble
    NN = ensemble_NN()
    res = aleph0_infini()                                   # ¬Fini(Card ℕ)
    assert res.conclusion == est_infini_ensemble(NN), \
        "NN_est_infini_ensemble : ¬Fini(Card ℕ) ≠ est_infini_ensemble(ℕ)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (5) DEDEKIND POUR ℵ₀  :  est_infini(ℵ₀) ⇔ ( ℵ₀ = ℵ₀ + 1 )   (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.1 Rem.- | E III.45 L.21-22 | PDF p.148  (Dedekind réalisé pour ℵ₀ — hors texte du livre)
def dedekind_aleph0():
    """🎯 ⊢ est_infini(ℵ₀) ⇔ ( ℵ₀ = ℵ₀ + 1 ).   (THÉORÈME CLOS, 0 hyp — DEDEKIND réalisé.)

    Caractérisation de Dedekind (E.III.6) appliquée au cardinal CONCRET ℵ₀ :
    dedekind_cardinal(ℵ₀) ⊢ est_cardinal(ℵ₀) ⇒ ( est_infini(ℵ₀) ⇔ ℵ₀=ℵ₀+1 ) ;
    la garde est_cardinal(ℵ₀) est PROUVÉE (aleph0_est_cardinal) puis déchargée par MP —
    l'équivalence devient donc INCONDITIONNELLE pour ℵ₀.  (Les deux côtés sont d'ailleurs
    individuellement clos : aleph0_est_infini ET aleph0_egal_succ ; ce théorème expose la
    forme « ⇔ » canonique de Dedekind.)  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_props import dedekind_cardinal
    a0 = aleph_0()
    card_a0 = aleph0_est_cardinal()                        # est_cardinal(ℵ₀)
    ded = dedekind_cardinal(a0)                            # est_cardinal(ℵ₀) ⇒ (infini ⇔ ℵ₀=ℵ₀+1)
    res = N.modus_ponens(card_a0, ded)                    # est_infini(ℵ₀) ⇔ (ℵ₀=ℵ₀+1)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
    cible = equiv(est_infini(a0), egal(a0, successeur(a0)))
    assert res.conclusion == cible, \
        "dedekind_aleph0 : conclusion ≠ ( est_infini(ℵ₀) ⇔ ℵ₀=ℵ₀+1 )"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (6) ℵ₀ ≤ ℵ₀   (réflexivité de ≤ ; « ℕ est dénombrable » au sens cardinal)
# ════════════════════════════════════════════════════════════════════════════
def aleph0_inf_egal_reflexif():
    """🎯 ⊢ ℵ₀ ≤ ℵ₀.   (THÉORÈME CLOS, 0 hyp — réflexivité de l'ordre des cardinaux.)

    ℵ₀ ≤ ℵ₀ par réflexivité de ≤ (inf_egal_reflexif, l'identité Δ injecte tout cardinal
    en lui-même), instancié au TERME ℵ₀.  C'est la forme cardinale de « ℕ est dénombrable »
    (est_denombrable_card(ℕ) = Card ℕ ≤ ℵ₀ = ℵ₀ ≤ ℵ₀).  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
    a0 = aleph_0()
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))   # (∀X)(X ≤ X)
    res = instancie(refl_all, a0)                              # ℵ₀ ≤ ℵ₀
    assert res.conclusion == inf_egal_card(a0, a0), \
        "aleph0_inf_egal_reflexif : conclusion ≠ (ℵ₀ ≤ ℵ₀)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (7) ℕ EST DÉNOMBRABLE  (Déf. 3 : (∃Y)(Y⊂ℕ et Eq(ℕ,Y)), témoin Y = ℕ)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.4 Def.3 | E III.49 L.20-22 | PDF p.152  (ℕ est dénombrable : témoin Y=ℕ dans la Déf. 3)
def NN_denombrable(y="Y"):
    """🎯 ⊢ (∃Y)( Y ⊂ ℕ et Eq(ℕ, Y) ).   (THÉORÈME CLOS, 0 hyp — ℕ est dénombrable, Déf. 3.)

    « Un ensemble est dénombrable s'il est équipotent à une partie de ℕ » (Déf. 3,
    §III.6.4).  ℕ EST une partie de ℕ (inclusion réflexive ℕ⊂ℕ) et ℕ est équipotent à
    lui-même (Eq(ℕ,ℕ), réflexivité) : le couple (ℕ⊂ℕ et Eq(ℕ,ℕ)) atteste, par témoin
    Y := ℕ (S5), l'existentiel de la Déf. 3.  ⚠️ Ici ℕ = ensemble_NN() (CONCRET) ET le
    « N » de la Déf. 3 est aussi ce ℕ concret (on N'utilise PAS le N opaque app("N")) —
    la conclusion est donc (∃Y)(Y⊂ℕ_concret et Eq(ℕ_concret,Y)), forme fidèle de la
    dénombrabilité pour le ℕ effectivement construit.  Liant existentiel Y FRAIS (≠ liants
    internes de ℕ).  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import equipotence_reflexive
    NN = ensemble_NN()
    vY = var(y)
    # corps R(Y) = ( Y ⊂ ℕ et Eq(ℕ, Y) )   — liant Y
    corps = et(inclus(vY, NN), equipotent(NN, vY))
    # témoin Y := ℕ : R(ℕ) = ( ℕ ⊂ ℕ et Eq(ℕ, ℕ) )
    # ℕ ⊂ ℕ  (inclusion réflexive)
    NN_incl = _inclusion_reflexive_terme(NN)              # ℕ ⊂ ℕ
    # Eq(ℕ, ℕ)  (réflexivité de l'équipotence, instanciée au terme ℕ)
    eq_all = N.generalisation("X", equipotence_reflexive("X"))   # (∀X) Eq(X,X)
    NN_eq = instancie(eq_all, NN)                                # Eq(ℕ, ℕ)
    temoin = conjonction_intro(NN_incl, NN_eq)                   # ℕ⊂ℕ et Eq(ℕ,ℕ) = R(ℕ)
    # S5 : (Y|ℕ)R(Y) ⇒ (∃Y) R(Y)
    res = N.modus_ponens(temoin, N.s5(corps, NN, y))            # (∃Y)( Y⊂ℕ et Eq(ℕ,Y) )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe
    assert res.conclusion == existe(y, corps), \
        "NN_denombrable : conclusion ≠ (∃Y)(Y⊂ℕ et Eq(ℕ,Y))"
    return res


def _inclusion_reflexive_terme(t):
    """⊢ t ⊂ t   pour un TERME t  (réflexivité de l'inclusion, instanciée)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import inclusion_reflexive
    refl_all = N.generalisation("X", inclusion_reflexive("X"))   # (∀X)(X ⊂ X)
    return instancie(refl_all, _t(t))                            # t ⊂ t


# ════════════════════════════════════════════════════════════════════════════
#  (8) UN CARDINAL INFINI EXISTE — RÉALISÉ CONCRÈTEMENT par ℵ₀  (sans A4 !)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.1 Ax.A4 | E III.45 L.14-15 | PDF p.148  (A4 RÉALISÉ concrètement par ℵ₀, sans invoquer l'axiome)
def existe_cardinal_infini_concret(a="a"):
    """🎯 ⊢ (∃a) est_infini(a).   (THÉORÈME CLOS, 0 hyp — A4 RÉALISÉ par ℵ₀, SANS l'axiome.)

    « Il existe un cardinal infini » : ici DÉMONTRÉ par TÉMOIN CONCRET ℵ₀ (aleph0_est_infini,
    de l'équation ℵ₀=ℵ₀+1) — et NON par l'axiome A4.  est_infini(a) avec a:=ℵ₀ donne
    est_infini(ℵ₀) ; S5 ⇒ (∃a) est_infini(a).  L'axiome de l'infini A4 (§III.6.1) est ainsi
    SATISFAIT dans theorie_ensembles() (=22) sans postulat : ℕ est l'ensemble infini que A4
    affirme exister.  Liant existentiel « a » FRAIS.  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe
    a0 = aleph_0()
    corps = est_infini(var(a))                              # est_infini(a)   — liant a
    inf_a0 = aleph0_est_infini()                            # est_infini(ℵ₀) = (a|ℵ₀)corps
    res = N.modus_ponens(inf_a0, N.s5(corps, a0, a))       # (∃a) est_infini(a)
    assert res.conclusion == existe(a, corps), \
        "existe_cardinal_infini_concret : conclusion ≠ (∃a) est_infini(a)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (9) ℵ₀ < 2^ℵ₀  pour le ℵ₀ CONCRET  (Cantor à ℕ ; la puissance du continu sur ℕ)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.4 Rem.- | E III.50 L.26-27 | PDF p.153  (ℵ₀ < 2^ℵ₀, Cantor sur ℕ concret — appuie « le continu n'est pas dénombrable »)
def aleph0_strict_continu_concret():
    """🎯 ⊢ Card(ℕ) < Card(𝔓 ℕ).   (THÉORÈME CLOS, 0 hyp — ℵ₀ < 2^ℵ₀, ℕ CONCRET.)

    Théorème de Cantor (cantor_strict_cardinal, INCONDITIONNEL) spécialisé au ℕ CONCRET
    ensemble_NN() : ℵ₀ = Card ℕ, 2^ℵ₀ = Card(𝔓 ℕ).  « La puissance du continu dépasse
    STRICTEMENT ℵ₀ » (E.III.6.4, Déf. 4), ici pour le ℕ effectivement construit (et non
    le N opaque app("N") de ensembles_chap3_props_restantes).  N'invoque PAS N_existe
    (Cantor est indépendant de la collectivisation).  theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import cantor_strict_cardinal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_strict_card
    NN = ensemble_NN()
    # Cantor est bâti en NOM SYMBOLIQUE « X » (sa machinerie interne — graphe x↦{x},
    # argument diagonal — emploie des liants génériques qui collisionneraient avec les
    # τ-liants de ℕ si on passait ensemble_NN() DIRECTEMENT) ; on GÉNÉRALISE puis on
    # INSTANCIE au TERME ℕ (robuste, comme aleph0_egal_succ / _prop1_direct_t).
    cantor_gen = N.generalisation("X", cantor_strict_cardinal("X"))   # (∀X)(Card X < Card 𝔓 X)
    res = instancie(cantor_gen, NN)                          # Card ℕ < Card 𝔓 ℕ
    assert res.conclusion == inf_strict_card(cardinal(NN), cardinal(E.parties(NN))), \
        "aleph0_strict_continu_concret : conclusion ≠ (Card ℕ < Card 𝔓 ℕ)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (10) 𝔓(ℕ) N'EST PAS DÉNOMBRABLE  (sens cardinal : ¬(2^ℵ₀ ≤ ℵ₀))  — ℕ CONCRET
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.4 Rem.- | E III.50 L.26-27 | PDF p.153  (« Un ensemble qui a la puissance du continu n'est pas dénombrable (III, p. 30, th. 2) »)
def continu_non_denombrable_concret():
    """🎯 ⊢ ¬( Card(𝔓 ℕ) ≤ Card(ℕ) ).   (THÉORÈME CLOS, 0 hyp — 𝔓(ℕ) non dénombrable.)

    « Un ensemble qui a la puissance du continu n'est PAS dénombrable » (E.III.6.4,
    Déf. 4), pour le ℕ CONCRET : est_denombrable_card(𝔓 ℕ) = (Card 𝔓 ℕ ≤ ℵ₀) ; cet
    énoncé en est la NÉGATION.  Preuve : ℵ₀ < 2^ℵ₀ (aleph0_strict_continu_concret) ;
    asymétrie de l'ordre strict (inf_strict_exclut_reciproque, sous est_cardinal des
    deux membres — Card ℕ, Card 𝔓 ℕ sont des cardinaux par est_cardinal_de_cardinal)
    donne (ℵ₀ < 2^ℵ₀) ⇒ ¬(2^ℵ₀ ≤ ℵ₀).  INCONDITIONNEL (Cantor + antisymétrie de ≤).
    theorie = 22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_chap3_props_restantes import est_cardinal_de_cardinal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import inf_strict_exclut_reciproque
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
    NN = ensemble_NN()
    PN = E.parties(NN)
    cN = cardinal(NN)                                         # ℵ₀ = Card ℕ
    cPN = cardinal(PN)                                        # 2^ℵ₀ = Card 𝔓 ℕ
    strict = aleph0_strict_continu_concret()                 # ℵ₀ < 2^ℵ₀
    # asymétrie bâtie en NOMS SYMBOLIQUES a,b (sa machinerie interne — antisymetrie_
    # cardinaux → cardinal_de_cardinal — substitue dans l'argument, collision avec les
    # τ-liants de Card ℕ / Card 𝔓 ℕ) ; GÉNÉRALISER puis INSTANCIER aux TERMES.
    asym_gen = N.generalisation("a", N.generalisation("b", inf_strict_exclut_reciproque("a", "b")))
    asym = instancie(instancie(asym_gen, cN), cPN)           # est_c(a)⇒(est_c(b)⇒((a<b)⇒¬(b≤a)))
    s1 = N.modus_ponens(est_cardinal_de_cardinal(NN), asym)          # est_c(b)⇒((a<b)⇒¬(b≤a))
    s2 = N.modus_ponens(est_cardinal_de_cardinal(PN), s1)            # (a<b)⇒¬(b≤a)
    res = N.modus_ponens(strict, s2)                         # ¬( 2^ℵ₀ ≤ ℵ₀ )
    assert res.conclusion == non(inf_egal_card(cPN, cN)), \
        "continu_non_denombrable_concret : conclusion ≠ ¬(Card 𝔓 ℕ ≤ Card ℕ)"
    return res


__all__ = [
    "aleph0_est_cardinal",
    "aleph0_plus_un_egal",
    "aleph0_est_infini",
    "NN_est_infini_ensemble",
    "dedekind_aleph0",
    "aleph0_inf_egal_reflexif",
    "NN_denombrable",
    "existe_cardinal_infini_concret",
    "aleph0_strict_continu_concret",
    "continu_non_denombrable_concret",
]
