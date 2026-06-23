"""Tests ISOLÉS du module ensembles_prop9_cloture (CLÔTURE de la Proposition 9).

Vérifie que :
  • bijection_de_conjoints assemble est_bijection_de(W, dom_phi, cod_phi) à partir
    des quatre conjoints (conclusion EXACTE) ;
  • prop9_si_conjoints_durs / prop9_cible_conditionnelle ⊢ la cible Prop 9
    (cible_prop9_exp_somme) sous les DEUX SEULES hypothèses DURES (conclusion EXACTE,
    hypothèses EXACTES) ;
  • conjoints_durs_REPORTE est honnêtement reporté (NotImplementedError).

Chaque théorème SORT du noyau (type Theoreme opaque) : « obtenu » == « certifié ».
"""
import pytest

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.arithmetique.ensembles_prop9_final import (
    W, domaine_phi, codomaine_phi, W_fonctionnel, W_domaine)
from bourbaki.cardinaux.arithmetique.ensembles_prop9_exp_somme import (
    cible_prop9_exp_somme)
from bourbaki.cardinaux.arithmetique.ensembles_prop9_cloture import (
    bijection_de_conjoints, W_injective_hyp, W_image_hyp,
    prop9_si_conjoints_durs, prop9_cible_conditionnelle, conjoints_durs_REPORTE)


A, B, C = var("A"), var("B"), var("C")
DOM = domaine_phi(A, B, C)          # 𝓕(B⊔C;A)
COD = codomaine_phi(A, B, C)        # 𝓕(B;A)×𝓕(C;A)
WT = W(A, B, C)


def _est_theoreme(thm):
    """Garde-fou : un Theoreme opaque du noyau (sort du noyau, donc certifié)."""
    assert isinstance(thm, N.Theoreme)


# ── PALIER ASSEMBLAGE ─────────────────────────────────────────────────────────
def test_bijection_de_conjoints_conclusion_exacte():
    """bijection_de_conjoints recolle les 4 conjoints en est_bijection_de(W,dom,cod)."""
    fonct = W_fonctionnel(A, B, C)
    dom_eq = W_domaine(A, B, C)
    inj = N.assume(W_injective_hyp(A, B, C))
    img = N.assume(W_image_hyp(A, B, C))
    bij = bijection_de_conjoints(fonct, dom_eq, inj, img)
    _est_theoreme(bij)
    assert bij.conclusion == est_bijection_de(WT, DOM, COD)


def test_bijection_de_conjoints_hypotheses_sont_les_durs():
    """L'assemblage ne porte QUE les deux hypothèses DURES (les structurels CLOS)."""
    fonct = W_fonctionnel(A, B, C)
    dom_eq = W_domaine(A, B, C)
    inj = N.assume(W_injective_hyp(A, B, C))
    img = N.assume(W_image_hyp(A, B, C))
    bij = bijection_de_conjoints(fonct, dom_eq, inj, img)
    assert W_injective_hyp(A, B, C) in bij.hypotheses
    assert W_image_hyp(A, B, C) in bij.hypotheses


# ── PALIER DERNIER MILE TIGHT ─────────────────────────────────────────────────
def test_prop9_si_conjoints_durs_conclut_la_cible():
    """⊢ la cible Prop 9 (cible_prop9_exp_somme) sous les deux conjoints DURS."""
    thm = prop9_si_conjoints_durs(A, B, C)
    _est_theoreme(thm)
    assert thm.conclusion == cible_prop9_exp_somme(A, B, C)


def test_prop9_si_conjoints_durs_hypotheses_exactes():
    """Les hypothèses sont EXACTEMENT les deux conjoints DURS — rien d'autre."""
    thm = prop9_si_conjoints_durs(A, B, C)
    hyps = set(thm.hypotheses)
    assert hyps == {W_injective_hyp(A, B, C), W_image_hyp(A, B, C)}


def test_prop9_cible_conditionnelle_alias():
    """prop9_cible_conditionnelle est l'alias arithmétique : même conclusion exacte."""
    thm = prop9_cible_conditionnelle(A, B, C)
    _est_theoreme(thm)
    assert thm.conclusion == cible_prop9_exp_somme(A, B, C)
    assert set(thm.hypotheses) == {W_injective_hyp(A, B, C), W_image_hyp(A, B, C)}


def test_cible_est_egalite_des_cardinaux():
    """Garde-fou de FIDÉLITÉ : la cible est bien une ÉGALITÉ Card(·)=Card(·)."""
    cible = cible_prop9_exp_somme(A, B, C)
    # cible_prop9_exp_somme renvoie egal(Card(𝓕(B⊔C;A)), Card(𝓕(B;A)×𝓕(C;A))).
    assert cible.tag == "="
    assert cible == prop9_si_conjoints_durs(A, B, C).conclusion


def test_parametrisable_sur_termes_generiques():
    """Robustesse : fonctionne aussi sur d'autres noms d'ensembles (P,Q,R)."""
    thm = prop9_si_conjoints_durs("P", "Q", "R")
    _est_theoreme(thm)
    assert thm.conclusion == cible_prop9_exp_somme(var("P"), var("Q"), var("R"))


# ── CŒUR REPORTÉ (honnêteté) ──────────────────────────────────────────────────
def test_conjoints_durs_reporte():
    """Les deux conjoints DURS sont honnêtement reportés (rien postulé)."""
    with pytest.raises(NotImplementedError):
        conjoints_durs_REPORTE()
