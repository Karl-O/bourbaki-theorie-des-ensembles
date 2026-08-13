# -*- coding: utf-8 -*-
"""Tests §III.5.8 — FACTORIELLE (E III.41, Déf. 2) : caractérisation récursive.

Deux blocs :
  (1) la forme GÉNÉRIQUE `factorielle_entier_de(f)` sur un f OPAQUE de test ;
  (2) 🎯 le RECOLLEMENT `factorielle_c62_entier` — la générique JOINTE à LA fonction
      C62 réellement assemblée (f=⋃𝔇_tot), avec (R0) « 0!=1 » DÉCHARGÉE.

Le bloc (2) est un TEST MIROIR : la conclusion ET le frozenset des hypothèses sont
RECONSTRUITS À LA MAIN ici, sans appeler aucune fonction du module testé
(`ensembles_factorielle_iii5`) — sinon on comparerait le module à lui-même.  Puis
`test_mutants_tues` MUTE ce miroir (pollution / substitution / α-variant, par gestes
NOYAU purs, en mémoire, sans toucher au dépôt) : un mutant survivant prouverait que
le miroir est décoratif.

⚠️ LENT : `factorielle_entier_de` coûte ~6 min (le prédicat est_fini se déplie en un
τ-terme profond) et le recollement ~10 min ; les deux théorèmes sont donc MÉMOÏSÉS
au niveau module (construits UNE fois, réutilisés par tous les tests).
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, var, egal, impl, pourtout, appartient, alpha_egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO, UN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_equation_restriction import essais_restriction
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_iii5 import (
    factorielle_zero_relation, factorielle_succ_relation, factorielle_entier_de,
    factorielle_c62_entier,
)

_MEMO = {}


def _f(x):
    """Terme-fonction OPAQUE de test : f(x) := app('myfac', x)."""
    return app("myfac", x)


def _generique():
    """`factorielle_entier_de(_f)`, construit UNE fois (~6 min)."""
    if "gen" not in _MEMO:
        _MEMO["gen"] = factorielle_entier_de(_f)
    return _MEMO["gen"]


def _recollement():
    """`factorielle_c62_entier()`, construit UNE fois (~10 min)."""
    if "rec" not in _MEMO:
        _MEMO["rec"] = factorielle_c62_entier()
    return _MEMO["rec"]


# ══════════════════════════════════════════════════════════════════════════════
#  (1) la forme GÉNÉRIQUE sur un f opaque.
# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_22():
    _generique()
    assert len(theorie_ensembles().axiomes) == 22


def test_factorielle_entier_de_conclusion():
    thm = _generique()
    cible = pourtout("nfe", impl(est_fini(var("nfe")),
                                 est_fini(_f(var("nfe")))))
    assert thm.conclusion == cible


def test_factorielle_entier_de_hyps_honnetes():
    """Les DEUX prémisses caractérisantes (R0),(Rs) sont les hypothèses ; non vacuous."""
    thm = _generique()
    R0 = factorielle_zero_relation(_f)                 # f(0)=1
    Rs = factorielle_succ_relation(_f, n="nfac")       # (∀n)(Fini n ⇒ f(n+1)=(n+1)·f(n))
    assert R0 in thm.hypotheses
    assert Rs in thm.hypotheses
    assert thm.conclusion not in thm.hypotheses        # JAMAIS vacuous


def test_relations_formes():
    """R0 = f(0)=1 ; Rs = récurrence (n+1)!=n!·(n+1) avec 1=UN=succ(0)."""
    assert factorielle_zero_relation(_f) == egal(_f(ZERO), UN)
    vn = var("nfac")
    assert factorielle_succ_relation(_f) == pourtout(
        "nfac", impl(est_fini(vn),
                     egal(_f(successeur(vn)),
                          produit_cardinal_binaire(successeur(vn), _f(vn)))))


# ══════════════════════════════════════════════════════════════════════════════
#  (2) MIROIR du RECOLLEMENT — tout reconstruit À LA MAIN, hors du module testé.
# ══════════════════════════════════════════════════════════════════════════════
_ENAT, _GLE, _VFAC = "Enat", "Gle", "Vfac62"


def _f_c62():
    """LE terme f := ⋃𝔇_tot de C62 (construit hors du module testé)."""
    return fonction_globale(_ENAT, _VFAC)


def _conclusion_miroir():
    """(∀nfe)( est_fini nfe ⇒ est_fini( valeur(f, nfe) ) ) — reconstruite à la main."""
    f, vn = _f_c62(), var("nfe")
    return pourtout("nfe", impl(est_fini(vn), est_fini(E.valeur(f, vn))))


def _R0_miroir():
    """(R0) valeur(f, 0) = 1 — reconstruite à la main."""
    return egal(E.valeur(_f_c62(), ZERO), UN)


def _Rs_miroir():
    """(Rs) (∀n)( Fini n ⇒ f(n+1) = (n+1)·f(n) ) — reconstruite à la main."""
    f, vn = _f_c62(), var("nfac")
    return pourtout("nfac", impl(est_fini(vn),
                                 egal(E.valeur(f, successeur(vn)),
                                      produit_cardinal_binaire(successeur(vn),
                                                               E.valeur(f, vn)))))


def _hypotheses_miroir():
    """Le frozenset EXACT des 7 hypothèses attendues, reconstruit à la main.

    `zcard="Zfac62"` est ÉPINGLÉ ici, pas laissé au défaut : il fixe le liant du
    `cardinal` interne de la règle, donc l'identité `==` des trois hypothèses
    règle-dépendantes (deux valeurs donnent des α-variants que le noyau n'identifie
    PAS).  Si un jour `factorielle_zero` change de zcard par défaut, ce miroir doit
    ÉCHOUER — c'est son rôle de détecter la dérive, pas de la suivre."""
    T, R, ve = regle_factorielle(zcard="Zfac62"), _graphe_R(_GLE), var(_ENAT)
    return frozenset({
        E.est_bien_ordonne(R, ve),                                     # (a) bo
        essais_bien_formes(T, _ENAT, _GLE, _VFAC, "qwf", "wwf", "zess"),  # (b)
        rule_codomain(T, _VFAC, "zess"),                               # (c)
        essais_restriction(T, T, _ENAT, _GLE),                         # forme du livre
        appartient(ZERO, ve),                                          # position de 0
        egal(E.segment_extremite(var(_GLE), ve, ZERO), E.VIDE),                # seg(0)=∅
        _Rs_miroir(),                                                  # (Rs) résiduelle
    })


def _verifier(thm):
    """CHECKER du miroir.  N'échoue QUE par AssertionError (sinon le mutant est CASSÉ)."""
    assert thm.conclusion == _conclusion_miroir(), "conclusion ≠ conclusion reconstruite"
    assert frozenset(thm.hypotheses) == _hypotheses_miroir(), \
        "hypothèses ≠ frozenset reconstruit (un `len(...)==7` ne dirait PAS lesquelles)"
    assert _R0_miroir() not in thm.hypotheses, "(R0) n'est pas déchargée"
    assert thm.conclusion not in thm.hypotheses, "VACUOUS"


@pytest.mark.slow
def test_recollement_miroir():
    """🎯 Le recollement coïncide avec la conclusion ET le frozenset reconstruits."""
    _verifier(_recollement())
    assert len(theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_recollement_decharge_R0_garde_Rs():
    """(R0) « 0!=1 » DÉCHARGÉE par factorielle_zero ; (Rs) seule prémisse survivante."""
    thm = _recollement()
    assert _R0_miroir() not in thm.hypotheses          # DÉCHARGÉE — c'est l'apport
    assert _Rs_miroir() in thm.hypotheses              # résidu honnête NOMMÉ
    assert len(thm.hypotheses) == 7
    assert thm.conclusion not in thm.hypotheses


@pytest.mark.slow
def test_mutants_tues():
    """MUTATION du miroir : POLLUTION, SUBSTITUTION, α-VARIANT — tous doivent MOURIR.

    Mutants construits par GESTES NOYAU PURS, en mémoire (le dépôt n'est pas touché) :
      • POLLUTION      : (A et B) puis élimination gauche ⇒ conclusion INTACTE,
                         hypothèse parasite empilée ;
      • SUBSTITUTION   : généralisation / conjonction ⇒ hypothèses INTACTES,
                         conclusion remplacée ;
      • α-VARIANT      : `alpha_bridge` vers (∀nfeALPHA)… — MÊME force logique
                         (alpha_egal True), liant renommé, structurellement ≠.
    Un mutant qui mourrait sur TypeError serait un mutant CASSÉ : son « kill » ne
    prouverait rien — d'où le tri explicite des exceptions ci-dessous."""
    thm = _recollement()
    mutants = {}

    # ── POLLUTION : même conclusion, une hypothèse parasite en plus ──────────
    parasite = appartient(var("xpolmut"), var("Epolmut"))
    mutants["pollution"] = conjonction_elim_gauche(
        conjonction_intro(thm, N.assume(parasite)))

    # ── SUBSTITUTION : mêmes hypothèses, conclusion remplacée ────────────────
    mutants["subst_generalisation"] = N.generalisation("wmut", thm)
    mutants["subst_conjonction"] = conjonction_intro(thm, thm)

    # ── α-VARIANT : même force logique, liant ∀ renommé ──────────────────────
    valpha = var("nfeALPHA")
    cible_alpha = pourtout("nfeALPHA", impl(est_fini(valpha),
                                            est_fini(E.valeur(_f_c62(), valpha))))
    assert alpha_egal(cible_alpha, thm.conclusion), "α-mutant : PAS α-équivalent"
    assert cible_alpha != thm.conclusion, "α-mutant : structurellement identique"
    mutants["alpha_nfe"] = alpha_bridge(thm, cible_alpha)

    # chaque mutant attaque un AXE DIFFÉRENT (sinon un seul axe serait testé)
    assert mutants["pollution"].conclusion == thm.conclusion
    assert frozenset(mutants["subst_generalisation"].hypotheses) == frozenset(thm.hypotheses)
    assert frozenset(mutants["subst_conjonction"].hypotheses) == frozenset(thm.hypotheses)
    assert frozenset(mutants["alpha_nfe"].hypotheses) == frozenset(thm.hypotheses)

    survivants = []
    for nom, mut in mutants.items():
        try:
            _verifier(mut)
        except AssertionError:
            continue                      # tué proprement par une assertion
        except Exception as ex:           # mutant CASSÉ : son « kill » ne prouve rien
            pytest.fail(f"mutant {nom} CASSÉ ({type(ex).__name__}: {ex})")
        survivants.append(nom)
    assert not survivants, f"MIROIR DÉCORATIF — mutants survivants : {survivants}"

    # le miroir laisse évidemment passer l'ORIGINAL (sinon il tuerait tout)
    _verifier(thm)
    assert len(theorie_ensembles().axiomes) == 22
