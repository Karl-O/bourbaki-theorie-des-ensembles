"""§III.6.1 — ℕ COMME OBJET CONCRET : le SET ℕ = NN et ses propriétés caractérisantes.

🎯🎯🎯 ℕ DEVIENT UN OBJET UTILISABLE.  Le Théorème 1 (E.III.6.1) `N_existe`
(ensembles_predecesseur_prop2) prouve INCONDITIONNELLEMENT, à 0 hypothèse,
`coll(x, Fini x)` = (∃y)(∀x)(x∈y ⇔ Fini x) : « la relation "x est un entier" est
collectivisante », autrement dit l'ensemble ℕ des entiers naturels EXISTE.  Mais
`coll(...)` est un énoncé d'EXISTENCE pur — il ne NOMME pas l'ensemble.  Ce module
NOMME ℕ (le terme `NN`) et en DÉRIVE les propriétés qui le rendent utilisable.

────────────────────────────────────────────────────────────────────────────────
DÉFINITION (Bourbaki nomme un ensemble collectivisé par le τ de sa propriété) :

    NN  :=  τ y ( (∀x)( x ∈ y ⇔ Fini x ) )                       (= ensemble_NN())

C'est le τ-terme du CORPS de la propriété collectivisante (la même formule que sous
le ∃ de `coll(x, Fini x)`).  NN est un terme CLOS (aucune variable libre) : un
véritable CONSTANT — l'ensemble des cardinaux finis.

────────────────────────────────────────────────────────────────────────────────
PROPRIÉTÉS DÉRIVÉES (jamais postulées — tirées de `N_existe` via l'AXIOME-τ) :

  • appartenance_NN()   ⊢ (∀z)( z ∈ NN ⇔ Fini z )       [CLOS, 0 hyp]
        LA CARACTÉRISATION.  Route :
          `N_existe()` ⊢ (∃y) R(y)   où R(y) = (∀x)(x∈y ⇔ Fini x) ;
          l'AXIOME-τ (existe_temoin = réciproque de S5 pour le témoin canonique
          T = τy R) donne (∃y)R(y) ⇒ (NN | y) R(y), où NN = τy R ;
          modus ponens ⇒ (NN | y) R(y) = (∀x)( x∈NN ⇔ Fini x ).
        L'équivalence est DÉRIVÉE (un théorème), JAMAIS supposée.  Le binder « x »
        est α-renommé « z » pour la lisibilité de l'énoncé final (alpha_pourtout).

  • zero_dans_NN()       ⊢ 0 ∈ NN                        [CLOS, 0 hyp]
        appartenance_NN instanciée à 0, sens ⇐, déchargé par `fini_zero` (⊢ Fini 0).

  • NN_clos_successeur() ⊢ (∀n)( n ∈ NN ⇒ successeur(n) ∈ NN )   [CLOS, 0 hyp]
        n∈NN ⇒ Fini n (appartenance ⇒) ; Fini n ⇒ Fini(succ n)
        (fini_implique_fini_successeur, INCONDITIONNEL) ; Fini(succ n) ⇒ succ(n)∈NN
        (appartenance ⇐ à succ n).  ℕ contient 0 et est stable par successeur :
        c'est exactement l'ossature de Peano (sans encore la récurrence C61).

⚠️ INVARIANT : theorie_ensembles() = 22 intangible.  NN est défini par τ à partir de
   la collectivisation DÉJÀ PROUVÉE (N_existe) ; AUCUN axiome nouveau n'est requis
   (l'axiome-τ existe_temoin est une primitive logique du noyau, comme S5/S6/S7).
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, tau, egal, equiv, impl, appartient, pourtout, existe, subst_f,
    libres_t,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout

from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import _coll_fini


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  La propriété collectivisante et son corps (réutilisés tels quels depuis coll)
# ════════════════════════════════════════════════════════════════════════════
def _coll(x="x", Y="y"):
    """La formule coll(x, Fini x) = (∃Y)(∀x)(x∈Y ⇔ Fini x), telle que la prouve N_existe.

    On la reconstruit via `_coll_fini` (ensembles_N_collectivise) pour matcher EXACTEMENT
    la conclusion de N_existe (mêmes binders « y » externe, « x » interne)."""
    return _coll_fini(x)                                   # (∃y)(∀x)(x∈y ⇔ Fini x)


def _corps_coll(x="x", Y="y"):
    """Le CORPS R(y) de la propriété collectivisante : (∀x)( x∈y ⇔ Fini x ).

    = le sous-formule directement sous le ∃y de coll(x, Fini x) ; le τ porte sur CE
    corps."""
    return _coll(x, Y).sous[0]                             # R(y) = (∀x)(x∈y ⇔ Fini x)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 DÉFINITION — ℕ comme TERME (le τ du corps collectivisant)
# ════════════════════════════════════════════════════════════════════════════
def ensemble_NN(x="x", Y="y"):
    """🎯 ℕ := τ y ( (∀x)( x ∈ y ⇔ Fini x ) ).   (TERME CLOS — l'ensemble des entiers.)

    Bourbaki nomme un ensemble collectivisé par le τ de sa propriété : ici la propriété
    « y collectivise Fini », c.-à-d. le CORPS R(y) sous le ∃ de coll(x, Fini x).  NN est
    le témoin canonique τy R — un terme SANS variable libre, donc un véritable CONSTANT.
    C'est l'ensemble ℕ = { x | Fini x } des cardinaux finis (= entiers naturels)."""
    return tau(Y, _corps_coll(x, Y))                       # τ y ( (∀x)( x∈y ⇔ Fini x ) )


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CARACTÉRISATION — (∀z)( z ∈ NN ⇔ Fini z )   (DÉRIVÉE de N_existe via l'axiome-τ)
# ════════════════════════════════════════════════════════════════════════════
@lru_cache(maxsize=None)
def _appartenance_NN_cache(x="x", Y="y"):
    """⊢ (∀x)( x ∈ NN ⇔ Fini x )  [CLOS] — cœur MÉMOÏSÉ (construit N_existe UNE seule fois).

    ⚠️ PERF : `N_existe()` est lent (~5 min, τ-cardinaux imbriqués) ; on le construit
    une SEULE fois par session (lru_cache), de sorte que zero_dans_NN / NN_clos_successeur
    réutilisent la caractérisation déjà prouvée au lieu de relancer N_existe à chaque appel."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import N_existe
    R = _corps_coll(x, Y)                                  # R(y) = (∀x)(x∈y ⇔ Fini x)
    coll = _coll(x, Y)                                     # (∃y) R(y)
    # AXIOME-τ : (∃y)R(y) ⇒ (NN | y) R(y)   (existe_temoin = réciproque de S5, T = τy R)
    ax_tau = N.existe_temoin(R, Y)                         # ⊢ (∃y)R ⇒ (τy R | y)R
    assert ax_tau.conclusion.sous[0].sous[0] == coll, \
        "appartenance_NN : l'antécédent de l'axiome-τ ≠ coll(x, Fini x) prouvé par N_existe"
    nexiste = N_existe()                                   # ⊢ coll(x, Fini x) = (∃y)R   [CLOS]
    assert nexiste.conclusion == coll, \
        "appartenance_NN : N_existe ne conclut pas coll(x, Fini x) (forme inattendue)"
    carac_x = N.modus_ponens(nexiste, ax_tau)             # (NN | y)R = (∀x)( x∈NN ⇔ Fini x )
    # vérifie que le résultat EST bien la caractérisation attendue (substitution NN pour y)
    NN = ensemble_NN(x, Y)
    cible_x = subst_f(NN, Y, R)                            # (∀x)( x∈NN ⇔ Fini x )
    assert carac_x.conclusion == cible_x, \
        "appartenance_NN : (NN|y)R inattendu (binder ?)"
    return carac_x


def appartenance_NN(x="x", Y="y", z=None):
    """🎯🎯 ⊢ (∀x)( x ∈ NN ⇔ Fini x ).   (THÉORÈME CLOS, 0 hyp — la CARACTÉRISATION.)

    DÉRIVÉE (jamais supposée) de `N_existe` ⊢ coll(x, Fini x) = (∃y) R(y) :
      • l'AXIOME-τ `existe_temoin(R, "y")` (réciproque de S5 pour le témoin canonique
        T = τy R = NN) donne  (∃y) R(y) ⇒ (NN | y) R(y) ;
      • modus ponens avec N_existe ⊢ (∃y)R(y)  ⇒  (NN | y) R(y) = (∀x)( x∈NN ⇔ Fini x ).
    Le liant universel s'appelle « x » (le binder de coll) ; le NOM du liant est sans
    portée (α-équivalence) — c'est LITTÉRALEMENT « (∀ entier z)( z∈NN ⇔ Fini z ) ».
    Un renommage explicite (paramètre `z`) est offert pour la lisibilité, mais SEULEMENT
    vers un nom NON utilisé comme liant interne de NN (sinon capture-évitement le rend
    structurellement distinct, quoique α-équivalent) — le défaut « x » l'évite.
    CLOS car N_existe est clos et l'axiome-τ est sans hypothèse.  theorie=22."""
    carac_x = _appartenance_NN_cache(x, Y)                # (∀x)( x∈NN ⇔ Fini x )   [CLOS, caché]
    # α-renommage OPTIONNEL du liant « x » → « z »  (lisibilité ; refusé si z capturé par NN)
    if z is None or z == x:
        return carac_x
    NN = ensemble_NN(x, Y)
    if z in libres_t(NN):
        raise ValueError(f"appartenance_NN : renommage vers {z!r} capturé par un liant interne de NN")
    corps_x = equiv(appartient(var(x), NN), est_fini(var(x)))   # x∈NN ⇔ Fini x
    ren = alpha_pour_tout(x, z, corps_x)                  # (∀x)(corps) ⇔ (∀z)(corps[x:=z])
    return N.modus_ponens(carac_x, equivalence_avant(ren))    # (∀z)( z∈NN ⇔ Fini z )


def appartenance_NN_instanciee(t, x="x", Y="y"):
    """⊢ ( T ∈ NN ) ⇔ ( Fini T )   pour un TERME T  (caractérisation instanciée).

    appartenance_NN (∀x) instanciée au terme T."""
    return instancie(appartenance_NN(x, Y), _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 0 ∈ NN   (le plus petit entier appartient à ℕ)
# ════════════════════════════════════════════════════════════════════════════
def zero_dans_NN(x="x", Y="y"):
    """🎯 ⊢ 0 ∈ NN.   (THÉORÈME CLOS, 0 hyp — ℕ contient 0.)

    appartenance_NN instanciée à 0 donne (0∈NN ⇔ Fini 0) ; le sens ⇐ avec `fini_zero`
    (⊢ Fini 0, CLOS) conclut 0∈NN.  CLOS (les deux briques le sont).  theorie=22."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import fini_zero
    equ0 = appartenance_NN_instanciee(ZERO, x, Y)         # (0∈NN) ⇔ (Fini 0)
    fini0 = fini_zero()                                    # ⊢ Fini 0   [CLOS]
    return N.modus_ponens(fini0, equivalence_arriere(equ0))   # 0 ∈ NN


# ════════════════════════════════════════════════════════════════════════════
#  🎯 NN STABLE PAR SUCCESSEUR :  (∀n)( n∈NN ⇒ successeur(n)∈NN )
# ════════════════════════════════════════════════════════════════════════════
def NN_clos_successeur(n="n", x="x", Y="y"):
    """🎯🎯 ⊢ (∀n)( n ∈ NN ⇒ successeur(n) ∈ NN ).   (THÉORÈME CLOS, 0 hyp.)

    ℕ est STABLE par successeur.  Pour un n quelconque :
      • n∈NN ⇒ Fini n        (appartenance_NN à n, sens ⇒) ;
      • Fini n ⇒ Fini(succ n) (fini_implique_fini_successeur, INCONDITIONNEL) ;
      • Fini(succ n) ⇒ succ(n)∈NN  (appartenance_NN à succ n, sens ⇐).
    Composition ⇒ n∈NN ⇒ succ(n)∈NN ; généralisation sur n.  Avec zero_dans_NN, c'est
    l'ossature de Peano (0 ∈ ℕ et ℕ clos par successeur) — sans encore la récurrence
    C61.  CLOS (toutes les briques le sont).  theorie=22."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import fini_implique_fini_successeur
    vn = var(n)
    succ_n = successeur(vn)                                # successeur(n)
    NN = ensemble_NN(x, Y)

    equ_n = appartenance_NN_instanciee(vn, x, Y)          # (n∈NN) ⇔ (Fini n)
    equ_sn = appartenance_NN_instanciee(succ_n, x, Y)     # (succ n∈NN) ⇔ (Fini succ n)
    fwd = fini_implique_fini_successeur(n)                 # Fini n ⇒ Fini(succ n)

    h_n_in = N.assume(appartient(vn, NN))                 # n ∈ NN
    fini_n = N.modus_ponens(h_n_in, equivalence_avant(equ_n))     # Fini n
    fini_sn = N.modus_ponens(fini_n, fwd)                 # Fini(succ n)
    sn_in = N.modus_ponens(fini_sn, equivalence_arriere(equ_sn))  # succ(n) ∈ NN
    imp = N.loi_deduction(appartient(vn, NN), sn_in)      # n∈NN ⇒ succ(n)∈NN
    return N.generalisation(n, imp)                        # (∀n)( n∈NN ⇒ succ(n)∈NN )


__all__ = [
    "ensemble_NN",
    "appartenance_NN", "appartenance_NN_instanciee",
    "zero_dans_NN", "NN_clos_successeur",
]
