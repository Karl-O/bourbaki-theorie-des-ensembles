"""§III.4-5 — Entiers naturels & calcul sur les entiers : théorèmes DIRECTS noyau.

§III.5 (CALCUL SUR LES ENTIERS) — théorèmes DIRECTS certifiés (axiome d'intervalle
instancié + projections logiques immédiates) :

  • membre_intervalle_entiers     ⊢ (x∈[a,b]) ⇔ (x cardinal et a≤x et x≤b)   [axiome]
  • intervalle_implique_cardinal  ⊢ (x∈[a,b]) ⇒ (x est un cardinal)
  • intervalle_implique_borne_inf ⊢ (x∈[a,b]) ⇒ (a ≤ x)
  • intervalle_implique_borne_sup ⊢ (x∈[a,b]) ⇒ (x ≤ b)

Les DÉFINITIONS de §III.5 (intervalle, différence b−a, pair/impair, divisibilité,
reste/quotient, fonction caractéristique, suite finie/longueur, factorielle,
coefficient binomial) sont dans ensembles_entiers.py.

REPORTÉ honnêtement (anti-faux — TOUT le contenu mathématique de §III.5 repose sur
la RÉCURRENCE C61 NON disponible et/ou l'arithmétique cardinale binaire +, ·, −,
NON implémentée) :
  • §5.1 Prop. 1 + Cor. 1-4 : clôture de ℕ pour +, ·, ^ (« par récurrence sur b »),
    finitude des réunions/produits/parties finies — récurrence + somme/produit
    cardinaux d'une famille finie.
  • §5.2 Prop. 2 (a<b ⇔ (∃c>0)(b=a+c)), Prop. 3 (stricte croissance ∑/∏), Cor. 1-4
    (monotonie de ^, simplification additive/multiplicative, différence b−a) :
    prop. 13/14 cardinales + prop. 2 finitude.
  • §5.3 Prop. 4 (x↦a+x isomorphisme [0,b]→[a,a+b]), Prop. 5 (Card[a,b]=(b−a)+1,
    « par récurrence sur b »), Prop. 6 (unique isomorphisme E→[1,n]) : translation
    additive + récurrence + bon ordre.
  • §5.4 Suites finies : numérotation par l'unique isomorphisme [1,n]→I (Prop. 6).
  • §5.5 Prop. 7 (φ_{E−A}=1−φ_A, φ_{A∩B}=φ_A·φ_B, φ_{A∪B}+φ_{A∩B}=φ_A+φ_B) :
    arithmétique sur {0,1} (1−·, ·, +).
  • §5.6 Th. 1 (division euclidienne, existence/unicité de q, r) : bon ordre de ℕ
    + stricte monotonie q↦bq (prop. 3).
  • §5.7 Développement de base b (Prop. 8) ; §5.8 factorielle, binôme, Prop. 9-15
    et corollaires (principe des bergers, arrangements, partitions, Pascal,
    ∑_p C(n,p)=2ⁿ, ∑i=n(n+1)/2) : récurrence + arithmétique cardinale complète.

────────────────────────────────────────────────────────────────────────────────
§III.4 — Entiers naturels : théorèmes DIRECTS certifiés par le noyau.

Les DÉFINITIONS (successeur, ZERO/UN/…, est_fini, est_entier, est_fini_ensemble,
de_caractere_fini) sont dans ensembles_entiers.py (lues verbatim §III.4.1/4.5).

Théorème DIRECT atteignable au niveau abrégé :

  • « Card(X) est un cardinal »  (E.III.3.1, Déf. 2 : un cardinal est un objet de
    la forme Card(X)).  C'est le PREMIER conjoint de Fini(𝔞) (E.III.4.1, Déf. 1).
    Preuve : est_cardinal(Card(X)) = (∃X')(Card(X)=Card(X')) ; témoin X':=X donne
    l'instance Card(X)=Card(X) (réflexivité, Théorème 1 E.I.39) ; S5 conclut.

REPORTÉ honnêtement (voir le rapport ; tout repose sur l'arithmétique cardinale
III.3 NON implémentée) :
  • 0 est un entier / ∅ est fini : exigent 𝔞 ≠ 𝔞 + 1 pour 𝔞 = 0 = Card(∅), donc
    Card(∅) ≠ Card(∅) + Card({∅}) ; Bourbaki l'obtient via III.3 prop. 8
    (𝔞=𝔟 ⇔ 𝔞+1=𝔟+1) et la non-équipotence ∅ ≁ {∅}.  La somme cardinale binaire
    et prop. 8 ne sont pas dans le projet.
  • Proposition 1 (Fini(𝔞) ⇔ Fini(𝔞+1)) : repose explicitement sur III.3 prop. 8.
  • Proposition 2, Corollaires 1-4 (tiroirs) : III.3 prop. 13/8/3.
  • C61 (récurrence) : bon ordre de ℕ (III, p.25) + prop. 2 (prédécesseur).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, Terme, egal, et, non, impl, equiv, appartient, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, est_cardinal, inf_egal_card
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, est_fini_ensemble, successeur
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, equivalence_avant, dni,
                               conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


def card_est_un_cardinal(x="X", lieur="X'"):
    """⊢ Card(X) est un cardinal  =  ⊢ (∃X')(Card(X) = Card(X'))   (E.III.3.1, Déf. 2).

    Premier conjoint de Fini(𝔞) pour 𝔞 = Card(X) (E.III.4.1, Déf. 1).
    Témoin X':=X : l'instance (X|X')(Card(X)=Card(X')) est Card(X)=Card(X)
    (réflexivité), puis S5.  Le liant interne par défaut est « X' » (≠ X).
    x : nom de variable (str) OU Terme (ex. ∅, pour « 0 est un cardinal »)."""
    from bourbaki.logique.i_1_termes_relations.formule import Terme
    vX = x if isinstance(x, Terme) else var(x)
    cX = cardinal(vX)
    # corps R{X'} = (Card(X) = Card(X')),  liant X'
    corps = egal(cX, cardinal(var(lieur)))
    # (X | X') R{X'} = Card(X) = Card(X)  — réflexivité (Théorème 1)
    temoin = N.reflexivite(cX)
    # S5 : (X|X')R ⇒ (∃X') R     puis MP
    s5 = N.s5(corps, vX, lieur)
    return N.modus_ponens(temoin, s5)


# ═══════════════════════════════════════════════════════════════════════════════
# §III.4.1 — Déf. 1 (cardinal fini) DÉPLIÉE : théorèmes DIRECTS certifiés noyau
# ═══════════════════════════════════════════════════════════════════════════════
# Déf. 1 (E.III.4.1) :  Fini(𝔞)  :⇔  (𝔞 est un cardinal) ∧ (𝔞 ≠ 𝔞 + 1).
# Les deux CONJOINTS de cette définition sont des conséquences DIRECTES (projections
# de la conjonction), et la caractérisation Fini(𝔞) ⇔ (cardinal ∧ ≠succ) est la
# définition même rendue explicite (A⇔A).  Ce sont des théorèmes FIDÈLES : ils ne
# disent rien de plus que la Déf. 1, mais les exposent comme énoncés certifiés par
# le noyau.  Ils NE supposent PAS la Proposition 1 / l'arithmétique cardinale
# (REPORTÉES) — uniquement le dépliage de la conjonction.

def fini_implique_cardinal(a="a"):
    """⊢ Fini(𝔞) ⇒ (𝔞 est un cardinal)   (E.III.4.1, Déf. 1, 1er conjoint).

    THÉORÈME DIRECT : « un cardinal fini est un cardinal ».  Projection gauche de
    la conjonction Fini(𝔞) = (est_cardinal(𝔞) et 𝔞≠𝔞+1), sous Fini(𝔞) déchargée.
    a : nom de variable (str) OU Terme (ex. Card(X), 0=Card(∅))."""
    va = _t(a)
    hyp = est_fini(va)
    card = conjonction_elim_gauche(N.assume(hyp))      # est_cardinal(𝔞)
    return N.loi_deduction(hyp, card)


def fini_implique_distinct_successeur(a="a"):
    """⊢ Fini(𝔞) ⇒ (𝔞 ≠ 𝔞 + 1)   (E.III.4.1, Déf. 1, 2e conjoint).

    THÉORÈME DIRECT : un cardinal fini diffère de son successeur (c'est la
    caractérisation de Bourbaki).  Projection droite de la conjonction Fini(𝔞)."""
    va = _t(a)
    hyp = est_fini(va)
    distinct = conjonction_elim_droite(N.assume(hyp))  # 𝔞 ≠ 𝔞+1
    return N.loi_deduction(hyp, distinct)


def caracterisation_fini(a="a"):
    """⊢ Fini(𝔞) ⇔ ((𝔞 est un cardinal) et (𝔞 ≠ 𝔞 + 1))   (E.III.4.1, Déf. 1).

    THÉORÈME DIRECT (A⇔A) : la définition même de « 𝔞 est fini » rendue explicite
    comme équivalence certifiée.  Fini(𝔞) EST littéralement cette conjonction ;
    l'équivalence est la conjonction des deux identités Fini(𝔞)⇒Fini(𝔞)."""
    va = _t(a)
    sens = a_implique_a(est_fini(va))
    return conjonction_intro(sens, sens)


def fini_implique_non_infini(a="a"):
    """⊢ Fini(𝔞) ⇒ ¬(𝔞 est infini)   (E.III.4.1 / §III.6.1, Déf. 1).

    THÉORÈME DIRECT : « fini » entraîne « non infini ».  est_infini(𝔞) = ¬Fini(𝔞)
    (Déf. 1, §III.6.1) ; donc ¬(𝔞 infini) = ¬¬Fini(𝔞), atteint par double négation
    (dni) à partir de Fini(𝔞)."""
    va = _t(a)
    return dni(est_fini(va))               # Fini(𝔞) ⇒ ¬¬Fini(𝔞) = Fini(𝔞) ⇒ ¬(infini)


# ── Déf. 1 (suite) : « l'ensemble E est fini » dépliée ────────────────────────
def ensemble_fini_card_est_cardinal(e="E"):
    """⊢ (E est fini) ⇒ (Card(E) est un cardinal)   (E.III.4.1, Déf. 1).

    THÉORÈME DIRECT : un ensemble fini a un cardinal (1er conjoint de Fini(Card E)).
    Projection gauche de Fini(Card E) = est_fini_ensemble(E)."""
    ve = _t(e)
    hyp = est_fini_ensemble(ve)
    card = conjonction_elim_gauche(N.assume(hyp))      # est_cardinal(Card E)
    return N.loi_deduction(hyp, card)


def ensemble_fini_card_distinct_successeur(e="E"):
    """⊢ (E est fini) ⇒ (Card(E) ≠ Card(E) + 1)   (E.III.4.1, Déf. 1).

    THÉORÈME DIRECT : le cardinal d'un ensemble fini diffère de son successeur.
    Projection droite de Fini(Card E)."""
    ve = _t(e)
    hyp = est_fini_ensemble(ve)
    distinct = conjonction_elim_droite(N.assume(hyp))  # Card E ≠ Card E + 1
    return N.loi_deduction(hyp, distinct)


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5.3 — INTERVALLE D'ENTIERS [a, b] : axiome + théorèmes DIRECTS certifiés
# ═══════════════════════════════════════════════════════════════════════════════
# [a, b] := { x | x cardinal et a ≤ x et x ≤ b }   (E.III.5.3, terme collectivisant
# par la Remarque III.25 : « x cardinal et x ≤ a » est collectivisante).  Légitimé
# par S8 (sélection) + A1 (unicité) — exactement comme P(X), produit, image.
#
# L'axiome est défini ICI (et non dans theorie_ensembles() global) parce qu'il fait
# référence à l'ordre des cardinaux (ensembles_cardinaux), qui importe
# ensembles_abrege (et non l'inverse).  Même schéma que theorie_graphe_terme /
# theorie_segment_extremite : une théorie ne contenant que cette instance.
#   (∀a)(∀b)(∀x)( x ∈ [a,b]  ⇔  (x cardinal et a ≤ x et x ≤ b) )
# Liants externes a, b, x.  est_cardinal lie « X », inf_egal_card lie « F » : pas de
# collision avec a, b, x.

def _corps_intervalle(a, b, x):
    """Corps : (x cardinal et a ≤ x et x ≤ b)   (E.III.5.3)."""
    return et(et(est_cardinal(x), inf_egal_card(a, x)), inf_egal_card(x, b))


def axiome_intervalle_entiers(a="a", b="b", x="x"):
    """⊢-schéma  (∀a)(∀b)(∀x)( x ∈ [a,b] ⇔ (x cardinal et a≤x et x≤b) )  (E.III.5.3).

    Axiome caractérisant l'intervalle d'entiers (légitime S8 + A1)."""
    va, vb, vx = var(a), var(b), var(x)
    return pourtout(a, pourtout(b, pourtout(x,
        equiv(appartient(vx, E.intervalle_entiers(va, vb)),
              _corps_intervalle(va, vb, vx)))))


def theorie_intervalle_entiers(a="a", b="b", x="x"):
    """Théorie ne contenant que l'axiome de l'intervalle d'entiers (E.III.5.3)."""
    return N.Theorie("Intervalle-entiers", [axiome_intervalle_entiers(a, b, x)])


def _membre_intervalle(a, b, x):
    """⊢ ( x ∈ [a,b] ⇔ (x cardinal et a≤x et x≤b) )  (axiome instancié)."""
    ax = N.axiome(theorie_intervalle_entiers(), axiome_intervalle_entiers())
    return instancie(instancie(instancie(ax, a), b), x)


def membre_intervalle_entiers(a="a", b="b", x="x"):
    """⊢ ( x ∈ [a,b] ) ⇔ ( x cardinal et a ≤ x et x ≤ b )   (E.III.5.3).

    THÉORÈME DIRECT : instance de l'axiome caractérisant [a,b].  C'est l'analogue,
    pour l'intervalle d'entiers, de membre_parties (axiome A3 instancié)."""
    return _membre_intervalle(var(a), var(b), var(x))


def intervalle_implique_cardinal(a="a", b="b", x="x"):
    """⊢ ( x ∈ [a,b] ) ⇒ ( x est un cardinal )   (E.III.5.3).

    THÉORÈME DIRECT : un élément de l'intervalle [a,b] est un cardinal (1er conjoint
    du corps).  Preuve : sens ⇒ de l'équivalence membre_intervalle, puis projection
    gauche-gauche du corps ((card ∧ a≤x) ∧ x≤b), sous l'hypothèse x∈[a,b] déchargée."""
    va, vb, vx = var(a), var(b), var(x)
    hyp = appartient(vx, E.intervalle_entiers(va, vb))
    avant = equivalence_avant(_membre_intervalle(va, vb, vx))   # x∈[a,b] ⇒ corps
    corps = N.modus_ponens(N.assume(hyp), avant)                # corps
    card = conjonction_elim_gauche(conjonction_elim_gauche(corps))  # x cardinal
    return N.loi_deduction(hyp, card)


def intervalle_implique_borne_inf(a="a", b="b", x="x"):
    """⊢ ( x ∈ [a,b] ) ⇒ ( a ≤ x )   (E.III.5.3).

    THÉORÈME DIRECT : un élément de [a,b] minore par a (borne inférieure).
    Projection gauche-droite du corps."""
    va, vb, vx = var(a), var(b), var(x)
    hyp = appartient(vx, E.intervalle_entiers(va, vb))
    avant = equivalence_avant(_membre_intervalle(va, vb, vx))
    corps = N.modus_ponens(N.assume(hyp), avant)
    borne = conjonction_elim_droite(conjonction_elim_gauche(corps))  # a ≤ x
    return N.loi_deduction(hyp, borne)


def intervalle_implique_borne_sup(a="a", b="b", x="x"):
    """⊢ ( x ∈ [a,b] ) ⇒ ( x ≤ b )   (E.III.5.3).

    THÉORÈME DIRECT : un élément de [a,b] est majoré par b (borne supérieure).
    Projection droite du corps."""
    va, vb, vx = var(a), var(b), var(x)
    hyp = appartient(vx, E.intervalle_entiers(va, vb))
    avant = equivalence_avant(_membre_intervalle(va, vb, vx))
    corps = N.modus_ponens(N.assume(hyp), avant)
    borne = conjonction_elim_droite(corps)                          # x ≤ b
    return N.loi_deduction(hyp, borne)


__all__ = ["card_est_un_cardinal",
           # §III.4.1 — Déf. 1 (cardinal fini) dépliée
           "fini_implique_cardinal", "fini_implique_distinct_successeur",
           "caracterisation_fini", "fini_implique_non_infini",
           "ensemble_fini_card_est_cardinal",
           "ensemble_fini_card_distinct_successeur",
           # §III.5.3 — intervalle d'entiers
           "axiome_intervalle_entiers", "theorie_intervalle_entiers",
           "membre_intervalle_entiers", "intervalle_implique_cardinal",
           "intervalle_implique_borne_inf", "intervalle_implique_borne_sup"]
