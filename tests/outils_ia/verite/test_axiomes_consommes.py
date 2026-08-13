# -*- coding: utf-8 -*-
"""Test miroir de M1 (`outils_ia/verite/axiomes_consommes.py`).

Ce que ces tests doivent EMPÊCHER — un outil décoratif :
  * une sonde qui répond toujours « dette non vide » (⇒ `test_thunk_pur_*`,
    `test_mutation_*` : le MÊME code, une seule théorie changée, doit basculer) ;
  * une sonde qui répond toujours « rien consommé » (⇒ `test_thunk_dedie_*`) ;
  * une sonde branchée sur UN SEUL des deux noyaux (⇒ `test_les_deux_noyaux_*`) ;
  * un faux négatif de mémoïsation passé sous silence (⇒ `test_memoisation_*`,
    qui MESURE le trou au lieu de le taire).
Et l'invariant du dépôt : `theorie_ensembles()` vaut 22 avant ET après.
"""
from __future__ import annotations

import functools
import os
import sys
import time

import pytest

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage, egalite
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau as Ntau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation \
    import ensembles_inter_selection_ii4 as SEL
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme \
    import ensembles_somme_indexee as SOM
from outils_ia.verite.axiomes_consommes import (
    axiomes_consommes, dette, invariant_reel, regles_surveillees)


def T0():
    """La théorie de référence : les 22 axiomes de Bourbaki."""
    return E.theorie_ensembles()


# ── Thunks : deux variantes d'UN MÊME code, une seule théorie de différence ──
def _thunk_instance(theorie, formule):
    """Fabrique `⊢ formule` par la règle `axiome`, puis instancie ∀f ∀I ∀z.

    La forme est IDENTIQUE quelle que soit `theorie` : c'est le support de la
    mutation (c) — si la sonde répondait la même chose dans les deux cas, elle
    ne mesurerait rien."""
    def thunk():
        ax = N.axiome(theorie, formule)
        return instancie(instancie(instancie(ax, E.var("f")), E.var("I")), E.var("z"))
    return thunk


def _pur():
    """Ne consomme QUE `theorie_ensembles()` (AXIOME_REUNION_FAM, l'un des 22)."""
    return _thunk_instance(T0(), E.AXIOME_REUNION_FAM)()


def _dedie():
    """Ne consomme QUE la théorie DÉDIÉE « Somme-famille » (§II.4.8 Déf. 8).

    Choisie parce que `AXIOME_SOMME_FAM` n'est VRAIMENT pas l'un des 22 (⊔ est
    un symbole libre pour `theorie_ensembles()`) : c'est de la dette réelle,
    pas une simple divergence de nom de théorie."""
    return _thunk_instance(SOM.theorie_somme_famille(), SOM.AXIOME_SOMME_FAM)()


def _mixte():
    """Consomme un axiome des 22 ET l'axiome de la théorie dédiée « Somme-famille »."""
    return conjonction_intro(
        _pur(),
        SOM.membre_somme_famille(E.var("f"), E.var("I"), E.var("z")))


# ── (a) un thunk qui ne consomme QUE T0 ─────────────────────────────────────
def test_thunk_pur_invariant_vrai_et_ax_exact():
    theoreme, ax = axiomes_consommes(_pur)
    assert theoreme.est_clos
    # EXACTEMENT un axiome, nommé, et c'est le bon : ni sur- ni sous-comptage.
    assert ax == frozenset({("Ensembles", E.AXIOME_REUNION_FAM)})
    assert invariant_reel(_pur, T0()) is True


def test_thunk_pur_dette_egale_les_hypotheses():
    theoreme, _ = axiomes_consommes(_pur)
    d, etrangers = dette(_pur, T0())
    assert etrangers == frozenset()
    assert d == frozenset(theoreme.hypotheses) == frozenset()


def test_dette_egale_les_hypotheses_quand_elles_sont_NON_vides():
    """`Dette = hypotheses ∪ (axiomes étrangers)` — ici la part hypothèses seule."""
    ouvert = lambda: N.assume(E.AXIOME_REUNION_FAM)          # {A} ⊢ A
    theoreme, ax = axiomes_consommes(ouvert)
    assert ax == frozenset()                                  # `assume` ≠ `axiome`
    d, etrangers = dette(ouvert, T0())
    assert etrangers == frozenset()
    assert d == frozenset(theoreme.hypotheses) == frozenset({E.AXIOME_REUNION_FAM})
    assert invariant_reel(ouvert, T0()) is True               # aucun axiome consommé


def test_thunk_sans_aucun_axiome():
    logique = lambda: N.s1(E.AXIOME_REUNION_FAM)              # ⊢ (R∨R)⇒R
    _, ax = axiomes_consommes(logique)
    assert ax == frozenset()
    assert invariant_reel(logique, T0()) is True
    assert dette(logique, T0())[0] == frozenset()


# ── (b) un thunk qui consomme une théorie DÉDIÉE ────────────────────────────
def test_thunk_dedie_invariant_faux_et_axiome_etranger_NOMME():
    _, ax = axiomes_consommes(_dedie)
    assert ax == frozenset({("Somme-famille", SOM.AXIOME_SOMME_FAM)})
    assert invariant_reel(_dedie, T0()) is False
    d, etrangers = dette(_dedie, T0())
    # l'axiome étranger apparaît NOMMÉ (nom de théorie + formule), pas juste compté
    assert etrangers == frozenset({("Somme-famille", SOM.AXIOME_SOMME_FAM)})
    assert d == frozenset({SOM.AXIOME_SOMME_FAM})
    # et c'est de la VRAIE dette : la formule n'est aucun des 22
    assert not any(SOM.AXIOME_SOMME_FAM == a for a in T0().axiomes)


def test_theoreme_reel_du_depot_clos_mais_endette():
    """`membre_somme_famille` est CLOS (0 hypothèse) et pourtant il DOIT un axiome.

    C'est exactement l'angle mort que l'invariant « 22 » ne voit pas : le
    théorème se présente comme « rien postulé » (aucune hypothèse) alors qu'il
    repose sur l'axiome de définition de ⊔, absent de `theorie_ensembles()`."""
    thunk = lambda: SOM.membre_somme_famille(E.var("f"), E.var("I"), E.var("z"))
    theoreme, ax = axiomes_consommes(thunk)
    assert theoreme.est_clos                        # 0 hypothèse : « rien postulé » apparent
    assert {n for (n, _) in ax} == {"Somme-famille"}
    d, etrangers = dette(thunk, T0())
    assert d == frozenset({SOM.AXIOME_SOMME_FAM})   # la dette, elle, est réelle
    assert etrangers and invariant_reel(thunk, T0()) is False


def test_derivation_mixte_ne_flague_que_letranger():
    """Une preuve qui consomme T0 ET une théorie dédiée : la dette SÉPARE.

    Si l'outil disait « dette non vide » en bloc, ce test ne prouverait rien ;
    ici on exige que l'axiome des 22 NE soit PAS compté comme dette."""
    _, ax = axiomes_consommes(_mixte)
    assert ax == frozenset({("Ensembles", E.AXIOME_REUNION_FAM),
                            ("Somme-famille", SOM.AXIOME_SOMME_FAM)})
    d, etrangers = dette(_mixte, T0())
    assert etrangers == frozenset({("Somme-famille", SOM.AXIOME_SOMME_FAM)})
    assert d == frozenset({SOM.AXIOME_SOMME_FAM})
    assert E.AXIOME_REUNION_FAM not in d
    assert invariant_reel(_mixte, T0()) is False


def test_dette_par_le_NOM_seul_theorie_dediee_perimee():
    """MESURE du 2026-07-26 — « Inter-selection » ne postule plus RIEN.

    `AXIOME_INTER_FAM_SEL` EST devenu, mot pour mot, `E.AXIOME_INTER_FAM`, l'un
    des 22 (réparation de l'incohérence de l'intersection). La théorie dédiée
    `theorie_inter_selection()` sert donc un axiome DÉJÀ dans T0, sous un autre
    NOM. Conformément à la définition arrêtée (`nom != T0.nom`), M1 le compte
    en dette — mais cette dette est DÉCHARGEABLE au sens de M2
    (`classer_residu`), puisque A_T0 ⊢ h en un pas. Ce test FIXE la mesure : si
    `AXIOME_INTER_FAM` rebouge, il tombe et il faudra re-mesurer."""
    assert SEL.AXIOME_INTER_FAM_SEL == E.AXIOME_INTER_FAM
    assert any(SEL.AXIOME_INTER_FAM_SEL == a for a in T0().axiomes)
    d, etrangers = dette(SEL.inter_donne_membres, T0())
    assert etrangers == frozenset({("Inter-selection", SEL.AXIOME_INTER_FAM_SEL)})
    assert d == frozenset({SEL.AXIOME_INTER_FAM_SEL})


# ── (c) MUTATION : la sonde ne dit pas systématiquement « False » ───────────
def test_mutation_seule_la_theorie_change_et_le_verdict_bascule():
    """MÊME formule, MÊME forme de preuve — seul le NOM de la théorie diffère.

    `AXIOME_REUNION_FAM` est l'un des 22 ; le servir depuis une théorie tierce
    doit basculer l'invariant à False. Un outil qui répondrait toujours la même
    chose (True ou False) échoue ici ou en (a)."""
    fidele = _thunk_instance(T0(), E.AXIOME_REUNION_FAM)
    usurpe = _thunk_instance(N.Theorie("Ensembles-bis", [E.AXIOME_REUNION_FAM]),
                             E.AXIOME_REUNION_FAM)
    assert invariant_reel(fidele, T0()) is True
    assert invariant_reel(usurpe, T0()) is False
    assert dette(fidele, T0())[0] == frozenset()
    assert dette(usurpe, T0())[0] == frozenset({E.AXIOME_REUNION_FAM})
    assert axiomes_consommes(usurpe)[1] == frozenset(
        {("Ensembles-bis", E.AXIOME_REUNION_FAM)})


def test_un_appel_axiome_qui_LEVE_nest_pas_compte():
    """`axiome` refuse une formule non-axiome : rien n'entre dans la dérivation."""
    def thunk():
        with pytest.raises(ValueError):
            N.axiome(T0(), SOM.AXIOME_SOMME_FAM)         # pas un des 22
        return N.s1(E.AXIOME_REUNION_FAM)
    _, ax = axiomes_consommes(thunk)
    assert ax == frozenset()
    assert invariant_reel(thunk, T0()) is True


# ── Anti-faux-négatif de sonde : LES DEUX noyaux sont observés ───────────────
def test_les_deux_noyaux_sont_surveilles():
    surveilles = {os.path.basename(c) for c in regles_surveillees()}
    assert surveilles == {"noyau.py", "noyau_abrege.py"}, surveilles


def test_les_deux_noyaux_axiome_tau_est_vu():
    """La règle `axiome` du noyau-τ (`noyau.py`) doit être vue elle aussi.

    Surveiller le seul `noyau_abrege` produirait un faux négatif SILENCIEUX sur
    toute dérivation menée au niveau assemblage-τ."""
    rel = egalite(Assemblage(("a",)), Assemblage(("b",)))
    th_tau = Ntau.Theorie("T-tau-dediee", axiomes=[rel])
    thunk = lambda: Ntau.axiome(th_tau, rel)
    _, ax = axiomes_consommes(thunk)
    assert ax == frozenset({("T-tau-dediee", rel)})
    assert invariant_reel(thunk, T0()) is False


# ── (d) restauration du profileur ───────────────────────────────────────────
def test_profileur_restaure_meme_si_le_thunk_leve():
    avant = sys.getprofile()

    def boum():
        raise ZeroDivisionError("le thunk explose")

    with pytest.raises(ZeroDivisionError):
        axiomes_consommes(boum)
    assert sys.getprofile() is avant


def test_profileur_precedent_restaure_a_lidentique():
    """On rend la main au profileur qu'on a TROUVÉ, pas à `None` aveuglément."""
    avant = sys.getprofile()
    sentinelle = lambda *_a: None
    sys.setprofile(sentinelle)
    try:
        axiomes_consommes(lambda: N.s1(E.AXIOME_REUNION_FAM))
        assert sys.getprofile() is sentinelle
        with pytest.raises(ZeroDivisionError):
            axiomes_consommes(lambda: 1 // 0)
        assert sys.getprofile() is sentinelle
    finally:
        sys.setprofile(avant)


def test_dette_refuse_un_thunk_qui_ne_rend_pas_un_theoreme():
    with pytest.raises(TypeError):
        dette(lambda: "pas un Theoreme", T0())


# ── LIMITE MESURÉE : la mémoïsation fait MANQUER des axiomes ────────────────
def test_memoisation_produit_un_faux_negatif_MESURE():
    """FAUX NÉGATIF documenté : au 2ᵉ appel d'une preuve `lru_cache`, Ax(D)=∅.

    Le corpus mémoïse réellement (ensembles_aleph0, ensembles_ensemble_NN,
    ensembles_gate_onto_top, ensembles_prop8_fini2, transposition/_existence).
    Ce test FIGE le trou : `invariant_reel` MENT au 2ᵉ appel. Corollaire
    opératoire : auditer en process FRAIS, ou au premier appel seulement."""
    @functools.lru_cache(maxsize=None)
    def preuve_memoisee():
        return N.axiome(SOM.theorie_somme_famille(), SOM.AXIOME_SOMME_FAM)

    _, ax1 = axiomes_consommes(preuve_memoisee)               # cache FROID : on voit
    assert ax1 == frozenset({("Somme-famille", SOM.AXIOME_SOMME_FAM)})
    _, ax2 = axiomes_consommes(preuve_memoisee)               # cache CHAUD : on ne voit plus
    assert ax2 == frozenset(), "le faux négatif de mémoïsation a disparu — re-mesurer"
    # …et voici le MENSONGE que ce faux négatif provoque, figé noir sur blanc :
    assert invariant_reel(preuve_memoisee, T0()) is True


# ── Surcoût : garde-fou grossier (le chiffre exact est dans la docstring) ────
def test_surcout_instrumentation_reste_raisonnable():
    """Garde-fou anti-catastrophe (pas un benchmark) : la sonde ne doit pas
    devenir super-linéaire (ex. `realpath` à chaque événement).

    Surcoût MESURÉ le 2026-07-26 : ×3,47 / ×3,09 / ×3,52 (court / moyen / long)
    — voir la docstring du module. Le seuil ci-dessous est LARGE exprès : ce
    test protège d'une régression d'ordre de grandeur, il ne mesure rien."""
    def mesure(fn, tours=40):
        meilleur = float("inf")
        for _ in range(3):
            t = time.perf_counter()
            for _ in range(tours):
                fn()
            meilleur = min(meilleur, time.perf_counter() - t)
        return meilleur

    nu = mesure(_pur)
    instrumente = mesure(lambda: axiomes_consommes(_pur))
    ratio = instrumente / nu if nu else float("inf")
    assert ratio < 10.0, "surcout x%.1f : la sonde a regresse" % ratio


# ── Frontière du dépôt ──────────────────────────────────────────────────────
def test_theorie_ensembles_reste_a_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
    axiomes_consommes(SEL.inter_donne_membres)
    assert len(E.theorie_ensembles().axiomes) == 22
