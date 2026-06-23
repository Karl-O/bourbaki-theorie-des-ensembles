"""§III.5.8 — FACTORIELLE (E III.41, Définition 2) : caractérisation récursive.

Bourbaki, E III.41, Déf. 2 :
    « Soit n un entier ; on note n! le produit ∏_{i<n}(i+1).  On a 0!=1 et 1!=1 ;
      il est clair que, pour tout entier n, (n+1)!=n!·(n+1).  Cette dernière relation,
      JOINTE à la relation 0!=1, CARACTÉRISE le terme n!, comme on le voit par
      récurrence sur n. »

────────────────────────────────────────────────────────────────────────────────
STATUT HONNÊTE DU TERME `factorielle`.

Le terme déposé `factorielle(n) = app("factorielle", n)` (bourbaki/entiers/
ensembles_entiers.py) est OPAQUE : aucun axiome ne le caractérise.  Sa VALEUR
(0!=1) et sa RÉCURRENCE ((n+1)!=n!·(n+1)) NE SONT donc PAS dérivables pour ce
terme-là sans postuler — ce que la consigne interdit.  Le seul moyen honnête de les
obtenir serait C63 (existence d'une fonction f sur ℕ avec f(0)=1, f(n)=S{f(n-1)}),
mais le C63 déposé (ensembles_c62_recursion) ne livre que l'EXISTENCE D'ESSAIS
(couverture C60), pas la fonction f assemblée, ET sous TROIS hypothèses honnêtes
(ℕ bien ordonné, essais bien formés, règle valuée).  On ne POSTULE donc rien.

────────────────────────────────────────────────────────────────────────────────
CE QU'ON PROUVE (faithful à « la récurrence + 0!=1 caractérisent n! »).

On prend la CARACTÉRISATION de Bourbaki au pied de la lettre : une factorielle est
TOUT terme-fonction f (callable Terme→Terme, opaque) vérifiant

    (R0)  f(0) = 1                                           [valeur initiale]
    (Rs)  (∀n)( est_fini n  ⇒  f(n+1) = (n+1)·f(n) )         [récurrence]

🎯 `factorielle_entier_de(f)` ⊢
    { f(0)=1 ,  (∀n)(Fini n ⇒ f(n+1)=(n+1)·f(n)) }
      ⊢  (∀n)( est_fini n ⇒ est_fini( f(n) ) ).

C'est exactement la Prop. 1 §III.5.1 spécialisée à la factorielle : n! est un
ENTIER NATUREL.  Route : récurrence C61 (`principe_recurrence_preuve`, résidu
prédécesseur DÉCHARGÉ) sur P[n] := est_fini(f(n)) :
    • P[0] :  f(0)=1 (R0) ⇒ est_fini(f(0))  via Fini(1) (fini_un, clos) + Leibniz ;
    • P[n] ⇒ P[n+1] : (Rs) donne f(n+1)=(n+1)·f(n) ; Fini(n+1) (Prop.1 réciproque
      fini_implique_fini_successeur) et Fini(f(n)) ⇒ Fini((n+1)·f(n))
      (produit_binaire_entier, Prop.1 §III.5.1 produit) ; Leibniz.

Les deux PRÉMISSES (R0),(Rs) sont les hypothèses HONNÊTES — ce sont LITTÉRALEMENT
la définition récursive caractérisante de Bourbaki (jamais postulée, jamais vacuous :
la conclusion est_fini(f(n)) ∉ {R0, Rs}).  theorie=22, noyau intact.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, impl, pourtout
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_arriere,
)

from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO, UN
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import fini_un
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import fini_implique_fini_successeur
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import produit_binaire_entier
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ── caractérisation récursive (les deux prémisses honnêtes) ───────────────────
def factorielle_zero_relation(f):
    """(R0)  f(0) = 1.   (1 = UN = successeur(0), un cardinal fini.)"""
    return egal(f(ZERO), UN)


def factorielle_succ_relation(f, n="nfac"):
    """(Rs)  (∀n)( est_fini n ⇒ f(n+1) = (n+1)·f(n) )."""
    vn = var(n)
    return pourtout(n, impl(est_fini(vn),
                            egal(f(successeur(vn)),
                                 produit_cardinal_binaire(successeur(vn), f(vn)))))


# ── P[n] := est_fini(f(n)) ────────────────────────────────────────────────────
def _P_fac(f):
    return lambda b: est_fini(f(_t(b)))


def _produit_binaire_entier_t(x, y):
    """produit_binaire_entier version TERME capture-safe (généralise+instancie)."""
    g = N.generalisation("xpbet", N.generalisation("ypbet",
            produit_binaire_entier("xpbet", "ypbet")))
    return instancie(instancie(g, _t(x)), _t(y))


def _fini_succ_t(x):
    """fini_implique_fini_successeur version TERME : Fini x ⇒ Fini(x+1)."""
    g = N.generalisation("xffst", fini_implique_fini_successeur("xffst"))
    return instancie(g, _t(x))


def _preuve_P0_fac(f, hR0):
    """{ f(0)=1 [hR0] } ⊢ est_fini( f(0) ).   (f(0)=1=UN ; Fini(1)=fini_un, clos.)"""
    f0 = f(ZERO)
    fini_1 = fini_un()                                  # Fini(UN)  (clos)
    assert fini_1.conclusion == est_fini(UN), "fini_un : conclusion inattendue"
    # Leibniz : f(0)=1 ⇒ ( Fini(f(0)) ⇔ Fini(1) )
    leib = N.s6(f0, UN, "wfp0", est_fini(var("wfp0")))  # (f(0)=1)⇒(Fini(f(0))⇔Fini 1)
    eqv = N.modus_ponens(hR0, leib)
    return N.modus_ponens(fini_1, equivalence_arriere(eqv))   # Fini(f(0))


def _preuve_step_fac(f, hRs, n="nstepfac"):
    """{ (Rs) [hRs] } ⊢ (∀n)( ( Fini n et Fini(f(n)) ) ⇒ Fini( f(n+1) ) )."""
    vn = var(n)
    succ_n = successeur(vn)                             # n+1
    fn = f(vn)
    prod = produit_cardinal_binaire(succ_n, fn)         # (n+1)·f(n)
    f_succ = f(succ_n)                                   # f(n+1)

    hstep = N.assume(et(est_fini(vn), est_fini(fn)))
    fini_n = conjonction_elim_gauche(hstep)             # Fini n
    fini_fn = conjonction_elim_droite(hstep)            # Fini(f(n))

    # (Rs) instanciée en n : Fini n ⇒ f(n+1)=(n+1)·f(n)
    rs_n = instancie(hRs, vn)
    eq_fsucc = N.modus_ponens(fini_n, rs_n)             # f(n+1) = (n+1)·f(n)

    # Fini(n+1)  (Prop.1 réciproque : Fini n ⇒ Fini(n+1))
    fini_succ_n = N.modus_ponens(fini_n, _fini_succ_t(vn))   # Fini(n+1)

    # Fini(n+1) et Fini(f(n)) ⇒ Fini((n+1)·f(n))   (produit_binaire_entier)
    pbe = _produit_binaire_entier_t(succ_n, fn)
    fini_prod = N.modus_ponens(conjonction_intro(fini_succ_n, fini_fn), pbe)  # Fini((n+1)·f(n))

    # Leibniz : f(n+1)=(n+1)·f(n) ⇒ ( Fini(f(n+1)) ⇔ Fini((n+1)·f(n)) )
    leib = N.s6(f_succ, prod, "wfst", est_fini(var("wfst")))
    eqv = N.modus_ponens(eq_fsucc, leib)
    fini_f_succ = N.modus_ponens(fini_prod, equivalence_arriere(eqv))   # Fini(f(n+1))

    body = N.loi_deduction(et(est_fini(vn), est_fini(fn)), fini_f_succ)
    return N.generalisation(n, body)


# ══════════════════════════════════════════════════════════════════════════════
#  🎯 FACTORIELLE_ENTIER : n! est un entier (caractérisation récursive)
# ══════════════════════════════════════════════════════════════════════════════
def factorielle_entier_de(f, n="nfe", k="kfe"):
    """🎯 ⊢ { f(0)=1 , (∀n)(Fini n ⇒ f(n+1)=(n+1)·f(n)) }
              ⊢ (∀n)( est_fini n ⇒ est_fini( f(n) ) ).

    Pour TOUT terme-fonction f (Terme→Terme opaque) vérifiant la caractérisation
    récursive de Bourbaki (E III.41, Déf. 2 : f(0)=1 et la récurrence), f(n) est un
    entier naturel pour tout entier n.  Prop. 1 §III.5.1 spécialisée à la factorielle.

    HYPOTHÈSES HONNÊTES = les DEUX prémisses caractérisantes (R0),(Rs) — ce sont
    littéralement la définition récursive de Bourbaki, jamais postulées.  Conclusion
    non vacuous.  theorie=22.  Route : récurrence C61 + produit_binaire_entier."""
    P = _P_fac(f)
    R0 = factorielle_zero_relation(f)
    Rs = factorielle_succ_relation(f, n="nfac")

    hR0 = N.assume(R0)
    hRs = N.assume(Rs)

    p0 = _preuve_P0_fac(f, hR0)                          # est_fini(f(0))   [R0]
    step = _preuve_step_fac(f, hRs, n=n)                 # (∀n)(...)        [Rs]

    assert p0.conclusion == P(ZERO), "P[0] factorielle mal formé"
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import _fini_et_P_implique_succ
    assert step.conclusion == _fini_et_P_implique_succ(P, n), "pas factorielle mal formé"

    # C61 (résidu prédécesseur DÉCHARGÉ)
    princ_imp = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))

    ante = conjonction_intro(p0, step)
    fini_implique_Pn = N.modus_ponens(ante, princ_imp)  # (∀n)(Fini n ⇒ Fini(f(n)))  [R0,Rs]

    cible = pourtout(n, impl(est_fini(var(n)), est_fini(f(var(n)))))
    assert fini_implique_Pn.conclusion == cible, \
        "factorielle_entier_de : conclusion inattendue"
    # honnêteté : non vacuous
    assert fini_implique_Pn.conclusion not in fini_implique_Pn.hypotheses, "VACUOUS"
    assert R0 in fini_implique_Pn.hypotheses, "R0 absente des hypothèses"
    assert Rs in fini_implique_Pn.hypotheses, "Rs absente des hypothèses"
    return fini_implique_Pn


__all__ = [
    "factorielle_zero_relation", "factorielle_succ_relation",
    "factorielle_entier_de",
]
