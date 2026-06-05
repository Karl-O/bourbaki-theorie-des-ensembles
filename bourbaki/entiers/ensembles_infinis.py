"""§III.6 — Ensembles infinis : AXIOME A4, DÉFINITIONS (abrégées) + théorèmes DIRECTS.

Énoncés lus VERBATIM dans le Texte.tex de §III.6 (V7) :

  • A4 (« axiome de l'infini », §III.6.1) : « Il existe un ensemble infini. »
        A4 := (∃X) ¬Fini(Card(X))     [= (∃X)(X est infini)]
    Axiome NON définitionnel (Bourbaki : « On ne sait pas déduire cet axiome des
    axiomes et schémas introduits jusqu'ici… il est à présumer qu'il en est
    indépendant »).  Il est ajouté tel quel à la théorie (theorie_infini()).

  • Déf. 1 (ensemble infini, cardinal infini, §III.6.1) : « On dit qu'un ensemble
    est infini s'il n'est pas fini.  En particulier, un cardinal est infini s'il
    n'est pas un entier. »
        est_infini(𝔞)          :⇔ ¬Fini(𝔞)            (cardinal infini)
        est_infini_ensemble(E) :⇔ ¬Fini(Card(E))      (ensemble infini)

  • N et ℵ₀ (suite du Théorème 1, §III.6.1) : « On désigne par N l'ensemble des
    entiers… Le cardinal de N se note aussi ℵ₀. »
        N := τ_X(Ent(X) ∧ Ent-collectivisant)  (terme matriciel ; Théorème 1)
        ℵ₀ := Card(N)

  • Déf. 2 (suite, suite infinie, §III.6.1) : « On appelle suite … une famille dont
    l'ensemble d'indices est une partie de N ; la suite est dite infinie si son
    ensemble d'indices est une partie infinie de N. »
        est_suite(f, I)        :⇔ I ⊂ N             (f famille indexée par I⊂N)
        est_suite_infinie(f,I) :⇔ I ⊂ N et I infini

  • Déf. 3 (ensemble dénombrable, §III.6.4) : « On dit qu'un ensemble est dénombrable
    s'il est équipotent à une partie de l'ensemble N des entiers. »
        est_denombrable(E) :⇔ (∃Y)(Y ⊂ N et Eq(E, Y))
    (Forme cardinale équivalente Card(E) ≤ ℵ₀, cf. note Roadmap.)

  • Déf. 4 (puissance du continu, §III.6.4) : « On dit qu'un ensemble a la puissance
    du continu s'il est équipotent à l'ensemble des parties de N. »
        a_puissance_continu(E) :⇔ Eq(E, P(N)) ;  puissance_continu := Card(P(N)) = 2^ℵ₀.

  • Déf. 5 (suite stationnaire, §III.6.5) : « On dit qu'une suite (x_n)_{n∈N}
    d'éléments d'un ensemble E est stationnaire s'il existe un entier m tel que
    x_n = x_m pour tout entier n ≥ m. »
        est_stationnaire(f) :⇔ (∃m)(m entier et (∀n)((n entier et m≤n) ⇒ f(n)=f(m)))

  • Ensemble noethérien (§III.6.5, après Cor. 2 de Prop. 6) : E ordonné noethérien
    ssi toute partie non vide a un élément maximal (≡ toute suite croissante
    stationnaire, Prop. 6).

────────────────────────────────────────────────────────────────────────────────
THÉORÈMES DIRECTS certifiés par le noyau (instances de A4 / dépliage définitionnel) :

  • existe_ensemble_infini    ⊢ (∃X) ¬Fini(Card(X))           [= A4, instancié]
  • infini_non_fini          ⊢ (E infini) ⇒ ¬Fini(Card(E))   [Déf. 1, identité]
  • non_fini_infini          ⊢ ¬Fini(Card(E)) ⇒ (E infini)   [Déf. 1, identité]
  • continu_non_denombrable_si : ⊢ (E pdc et P(N) non dénombrable) ⇒ E non dénombrable
        — transport de la non-dénombrabilité par équipotence (sens DIRECT du
          « un ensemble qui a la puissance du continu n'est pas dénombrable »,
          Déf. 4), SOUS l'hypothèse de Cantor « P(N) non dénombrable » (REPORTÉE).

REPORTÉ honnêtement (anti-faux — tout repose sur l'arithmétique cardinale infinie
III.6.3 et/ou la récurrence C61, NON disponibles ; cf. ensembles_entiers*.py) :
  • Théorème 1 (« x est un entier » est collectivisante) : MÉTAthéorème de
    collectivisation (S8 + comparabilité des cardinaux III.3 prop. 2), hors fragment
    objet — exige la chaîne « a infini ⇒ n<a pour tout entier n ».
  • Théorème 2 (𝔞²=𝔞 pour 𝔞 infini), Lemmes 1-2, Corollaires 1-4 : arithmétique
    cardinale infinie (produit/somme de cardinaux), absente.
  • Propositions 1-5 (dénombrables : parties, produit fini, réunion de suite ;
    infini dénombrable ≃ N ; partition ; 𝔉(E)≃E) : reposent sur Th. 2 / Cor. 1-4.
  • Cantor « P(N) non dénombrable » (2^ℵ₀ > ℵ₀) : Théorème de Cantor (Card X < Card
    P(X)), III.3 — non implémenté.
  • Critères C62/C63 (récurrence forte/simple), Propositions 6-7 (Noether, récurrence
    noethérienne) : récurrence C60/C61 + bon ordre de N, non disponibles.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, tau, egal, et, non, impl, equiv, ou,
                     existe, pourtout, appartient, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent, inf_egal_card
from bourbaki.entiers.ensembles_entiers import est_fini, est_fini_ensemble, est_entier


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ═══════════════════════════════════════════════════════════════════════════════
# N (ensemble des entiers naturels) et ℵ₀   (§III.6.1, suite du Théorème 1)
# ═══════════════════════════════════════════════════════════════════════════════
# N := τ_X(Ent(X) ∧ Ent-collectivisant) — terme matriciel introduit par A4 +
# Théorème 1.  Au niveau abrégé, on l'expose comme un TERME constant app("N") :
# « l'ensemble des entiers ».  Sa propriété caractérisante (z∈N ⇔ z entier) repose
# sur le Théorème 1 (collectivisation), REPORTÉ → N reste un terme opaque, sans
# axiome (aucun théorème direct ne le caractérise sans la collectivisation).
NN = app("N")                       # N : l'ensemble des entiers naturels


def aleph0():
    """ℵ₀ := Card(N)   (cardinal de l'ensemble des entiers, §III.6.1)."""
    return cardinal(NN)


# ═══════════════════════════════════════════════════════════════════════════════
# Déf. 1 — ensemble infini / cardinal infini   (§III.6.1)
# ═══════════════════════════════════════════════════════════════════════════════
def est_infini(a):
    """est_infini(𝔞) := ¬Fini(𝔞)   (un cardinal est infini s'il n'est pas un entier, Déf. 1).

    Négation EXACTE du prédicat Fini de §III.4.1 (est_fini)."""
    return non(est_fini(_t(a)))


def est_infini_ensemble(e):
    """est_infini_ensemble(E) := ¬Fini(Card(E))   (E est infini s'il n'est pas fini, Déf. 1).

    Négation EXACTE de est_fini_ensemble (= Fini(Card(E)))."""
    return non(est_fini_ensemble(_t(e)))


# ═══════════════════════════════════════════════════════════════════════════════
# A4 — axiome de l'infini : « Il existe un ensemble infini »   (§III.6.1)
# ═══════════════════════════════════════════════════════════════════════════════
# A4 := (∃X) ¬Fini(Card(X))  =  (∃X)(X est infini).  Liant externe « X ».
# Axiome NON définitionnel (présumé indépendant des axiomes précédents).
A4 = existe("X", est_infini_ensemble(var("X")))


def theorie_infini():
    """Théorie contenant l'axiome A4 de l'infini (§III.6.1).

    Théorie dédiée (et non theorie_ensembles() global) : A4 fait référence au
    prédicat Fini (ensembles_entiers → ensembles_cardinaux → ensembles_abrege),
    qui importe ensembles_abrege ; même schéma que theorie_intervalle_entiers /
    theorie_segment_extremite."""
    return N.Theorie("Infini(A4)", [A4])


# ═══════════════════════════════════════════════════════════════════════════════
# Déf. 2 — suite, suite infinie   (§III.6.1)
# ═══════════════════════════════════════════════════════════════════════════════
def est_suite(f, i):
    """« (x_n)_{n∈I} est une suite » := I ⊂ N   (famille indexée par une partie de N, Déf. 2).

    f : la famille (codée par sa fonction/graphe) ; i : l'ensemble d'indices I."""
    return inclus(_t(i), NN)


def est_suite_infinie(f, i):
    """« la suite (x_n)_{n∈I} est infinie » := I ⊂ N et I infini   (Déf. 2).

    Son ensemble d'indices I est une partie INFINIE de N."""
    return et(inclus(_t(i), NN), est_infini_ensemble(_t(i)))


# ═══════════════════════════════════════════════════════════════════════════════
# Déf. 3 — ensemble dénombrable   (§III.6.4)
# ═══════════════════════════════════════════════════════════════════════════════
def est_denombrable(e, y="Y"):
    """est_denombrable(E) := (∃Y)(Y ⊂ N et Eq(E, Y))   (Déf. 3, VERBATIM).

    E est dénombrable s'il est équipotent à une partie Y de l'ensemble N des
    entiers.  Liant existentiel « Y » (≠ F de equipotent)."""
    vY = var(y)
    return existe(y, et(inclus(vY, NN), equipotent(_t(e), vY)))


def est_denombrable_card(e):
    """Forme cardinale : Card(E) ≤ ℵ₀   (équivalente à Déf. 3, cf. Roadmap impl.).

    Fournie pour les énoncés cardinaux (Prop. 2…) ; l'équivalence avec est_denombrable
    repose sur Card(E)≤Card(Y)≤Card(N) (III.3), REPORTÉE."""
    return inf_egal_card(cardinal(_t(e)), aleph0())


# ═══════════════════════════════════════════════════════════════════════════════
# Déf. 4 — puissance du continu   (§III.6.4)
# ═══════════════════════════════════════════════════════════════════════════════
def a_puissance_continu(e):
    """a_puissance_continu(E) := Eq(E, P(N))   (Déf. 4, VERBATIM).

    E a la puissance du continu s'il est équipotent à l'ensemble des parties de N."""
    return equipotent(_t(e), E.parties(NN))


def puissance_continu():
    """la puissance du continu := Card(P(N)) = 2^ℵ₀   (Déf. 4, implémentation)."""
    return cardinal(E.parties(NN))


# ═══════════════════════════════════════════════════════════════════════════════
# Déf. 5 — suite stationnaire   (§III.6.5)
# ═══════════════════════════════════════════════════════════════════════════════
def est_stationnaire(f, m="m", n="n"):
    """est_stationnaire((x_n)) := (∃m)(m entier et (∀n)((n entier et m≤n) ⇒ x_n=x_m))
       (Déf. 5, VERBATIM : « il existe un entier m tel que x_n = x_m pour tout n ≥ m »).

    f : la suite (codée par sa fonction) ; x_n = valeur(f, n).  Liants m, n.
    m ≤ n : ordre des entiers (inf_egal_card)."""
    vf = _t(f)
    vm, vn = var(m), var(n)
    cond = et(est_entier(vn), inf_egal_card(vm, vn))           # n entier et m≤n
    interne = pourtout(n, impl(cond, egal(E.valeur(vf, vn), E.valeur(vf, vm))))
    return existe(m, et(est_entier(vm), interne))


# ═══════════════════════════════════════════════════════════════════════════════
# Ensemble noethérien   (§III.6.5, après Cor. 2 de la Prop. 6)
# ═══════════════════════════════════════════════════════════════════════════════
def est_noetherien(R, e, X="X", a="a", w="w"):
    """« E ordonné par R est noethérien » (§III.6.5) :=
       toute partie non vide de E a un élément MAXIMAL :
         (∀X)((X⊂E et ¬(X=∅)) ⇒ (∃a)(a∈X et (∀w)(w∈X ⇒ ¬(a≠w et R{a,w})))).

    Condition (a) de la Prop. 6 (équivalente à : toute suite croissante stationnaire).
    « a maximal dans X » : aucun w∈X strictement plus grand que a (¬(a<w))."""
    vX, va, vw = var(X), var(a), var(w)
    # a maximal : (∀w)(w∈X ⇒ ¬(a≠w et a≤w))   [pas de w∈X avec a<w]
    maximal = pourtout(w, impl(appartient(vw, vX),
                               non(et(non(egal(va, vw)), R(va, vw)))))
    petit_non_vide = et(inclus(vX, e), non(egal(vX, E.VIDE)))
    return pourtout(X, impl(petit_non_vide,
                            existe(a, et(appartient(va, vX), maximal))))


__all__ = ["NN", "aleph0", "est_infini", "est_infini_ensemble",
           "A4", "theorie_infini",
           "est_suite", "est_suite_infinie",
           "est_denombrable", "est_denombrable_card",
           "a_puissance_continu", "puissance_continu",
           "est_stationnaire", "est_noetherien"]
