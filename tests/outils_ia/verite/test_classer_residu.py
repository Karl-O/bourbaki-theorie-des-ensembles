"""Tests V9 — classification d'une hypothèse RÉSIDUELLE (outils_ia/verite/classer_residu).

TEST MIROIR sur les TROIS résidus RÉELS du dépôt, jamais sur des exemples jouets :
  (a) DÉCHARGEABLE  bo(≤,ℕ) = est_bien_ordonne(R_G≤, ℕ)   — `bo_graphe_NN()`, CLOS.
      ⚠️ lent (N_existe) ⇒ marqué `slow`. Le compagnon RAPIDE `test_bo_..._piege`
      mesure, lui, le FAUX MUR que le critère syntaxique seul aurait produit.
  (b) RÉFUTABLE      H-univ := (∃X)(∀x)(x ∈ X)  — l'ensemble universel, réfuté
      par Russell (`pas_ensemble_universel`, E II.6 Rem. → E II.7).
      Le schéma est INSTANCIÉ sur ses liants réels ; aucun nom n'est deviné.
      ⚠️ Ce cas testait, jusqu'au 2026-07-26, H-graphe := (∀G)(G ∈ ∏(u,∅) ⇒
      est_un_graphe(G)) via `hypothese_graphes_produit_vide_refutee`. Ce
      contre-théorème était un artefact du DÉFAUT de `AXIOME_PRODUIT_FAM`
      (conjoint « F ⊂ I × ⋃X_ι » perdu) : l'axiome réparé rend H-graphe
      DÉMONTRABLE, sa réfutation devait donc disparaître. Le schéma a été
      REMPLACÉ, pas supprimé — le registre `SCHEMAS_REFUTATION` reste mesuré.
  (c) INDÉPENDANTE   HW/HN, le pont fam↔valeur de la factorielle Déf.2.

INVARIANT vérifié ici : `theorie_ensembles()` = 22 avant ET après.
Lancement :  python -m pytest tests/outils_ia/verite/test_classer_residu.py -v
             (le cas (a) seul :  -m slow ;  sans lui :  -m "not slow")
"""
from __future__ import annotations

import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, impl, non, pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes import (
    ensembles_pas_ensemble_universel as PEU,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles import (
    ensembles_factorielle_def2_rec as FR,
)
from outils_ia.verite import classer_residu as C

#: Les 20 symboles de fonction mentionnés par les 22 axiomes (mesure 2026-08-02,
#: post-migration valeur_famille := valeur : « fam » a DISPARU du dépôt — les 4
#: axiomes de familles se reconstruisent sur le τ de `valeur`, bâti sur `paire`
#: déjà présent ; le set est donc l'ancien (2026-07-26) moins « fam », rien d'autre).
SYMBOLES_T0 = frozenset({
    "appcanon", "compl_fam", "composee", "diagonale", "difference", "dom",
    "image", "img", "inter", "inter_fam", "paire", "parties", "produit",
    "produit_fam", "quotient", "reciproque", "restriction", "reunion",
    "reunion_fam", "vide",
})


def _T0():
    return E.theorie_ensembles()


def _h_univ(gx="X", gi="x"):
    """H-univ := (∃X)(∀x)(x∈X) — RECONSTRUITE À LA MAIN, hors du module testé."""
    return existe(gx, pourtout(gi, appartient(var(gi), var(gx))))


def _bo_cible():
    """La formule bo(≤,ℕ) — construite comme `bo_graphe_NN` construit SA cible."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
        _graphe_R, G_ordre_NN)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
        ensemble_NN)
    return E.est_bien_ordonne(_graphe_R(G_ordre_NN()), ensemble_NN())


# ── L'invariant, et l'extracteur de symboles ─────────────────────────────────
def test_invariant_22_axiomes_avant_apres():
    assert len(_T0().axiomes) == 22
    C.classer(_h_univ(), _T0())
    C.classer(FR.hypothese_valuation_large(), _T0())
    assert len(_T0().axiomes) == 22


def test_symboles_des_22_axiomes_est_stable():
    assert C.symboles_theorie(_T0()) == SYMBOLES_T0


def test_symboles_parcourt_la_structure_pas_le_texte():
    # descente sous un τ (valeur(f,x) = τy((x,y)∈f)) et sous un `app` imbriqué
    f = E.valeur(E.singleton(E.VIDE), var("x"))
    assert C.symboles(f) == frozenset({"paire", "vide"})
    assert C.symboles(egal(f, f)) == frozenset({"paire", "vide"})
    with pytest.raises(TypeError):
        C.symboles("(x = x)")                       # jamais de chaîne, jamais de regex


# ── (b) RÉFUTABLE — H-univ, schéma INSTANCIÉ sur ses liants (aucun nom deviné) ─
def test_h_univ_est_bien_l_enonce_refute_par_russell():
    """Le schéma du module EST l'énoncé que `pas_ensemble_universel` réfute."""
    neg = PEU.pas_ensemble_universel()
    assert neg.est_clos
    assert neg.conclusion == non(_h_univ())               # ⊢ ¬(∃X)(∀x)(x∈X)


def test_h_univ_est_refutable_sans_prouveur():
    assert C.classer(_h_univ(), _T0()) == "refutable"


def test_h_univ_certificat_reverifie():
    T0, h = _T0(), _h_univ()
    absurde, negation = C.refutation_certifiee(h, T0)
    assert isinstance(absurde, N.Theoreme) and isinstance(negation, N.Theoreme)
    assert absurde.hypotheses == frozenset({h})           # h EXACTEMENT, rien d'autre
    assert absurde.conclusion == appartient(E.VIDE, E.VIDE)
    assert negation.est_clos and negation.conclusion == non(absurde.conclusion)


def test_sosie_de_h_univ_non_apparie():
    """Même forme, liants DIFFÉRENTS : les α-variants ne sont pas égaux dans ce noyau.

    C'est le garde-fou contre l'appariement approximatif — l'égalité
    `schema(gx, gi) == h` doit trancher, pas la ressemblance ; et le certificat
    est re-vérifié, donc un appariement laxiste serait rejeté en aval."""
    T0 = _T0()
    sosie = _h_univ("Xz", "xz")                           # α-variante de H-univ
    assert sosie != _h_univ()
    assert C.refutation_certifiee(sosie, T0) is None
    assert C.classer(sosie, T0) != "refutable"


def test_forme_etrangere_non_appariee():
    """Une formule qui n'a RIEN de la structure de H-univ : pas de faux positif."""
    T0 = _T0()
    etranger = existe("X", appartient(var("X"), var("X")))
    assert C.refutation_certifiee(etranger, T0) is None


# ── (c) LA BASCULE DU 3ᵉ VERDICT — le pont fam↔valeur (HW / HN) ──────────────
@pytest.mark.parametrize("fabrique", [FR.hypothese_valuation_large,
                                      FR.hypothese_valuation_etroite])
def test_pont_fam_valeur_bascule(fabrique):
    """DEUX PASSES, DEUX VERDICTS — la défaisabilité du 3ᵉ verdict, observée.

    AVANT la migration valeur_famille := valeur (2 août 2026), HW/HN étaient
    MESURÉES indépendantes des 22 (l'exemplaire X_ι de l'article).  DEPUIS, ce
    sont des égalités t=t : le classifieur SANS prouveur les étiquette ENCORE
    « independante » (critère d'occurrence seul — le verdict est un DÉFAUT,
    jamais un certificat), et le prouveur-réflexivité l'INVERSE en
    « dechargeable ».  L'indépendance ne s'est pas démontrée fausse : elle
    s'est dissoute par l'encodage — et seul le re-passage AVEC prouveur le voit."""
    T0 = _T0()
    h = fabrique()
    libres = C.symboles_libres(h, T0)
    # HW/HN contiennent `_seg_NN(·)` = seg_ext(G_ordre_NN(), ℕ, ·) — symboles hors
    # des 22 ; « fam », lui, est MORT avec la migration.
    assert libres == frozenset({"graphe_terme", "seg_ext", "G_ordre_NN"})
    assert "fam" not in libres
    assert C.contingente(h)
    assert C.classer(h, T0) == "independante"          # défaut SANS prouveur, défaisable

    # ── le re-passage avec prouveur-réflexivité : le verdict s'inverse ─────────
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import famille_successeurs
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_recursion import _seg_NN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_rec import _HB
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_close import _pont_reflexif
    vn, vi = var("nfr"), var(_HB)
    if fabrique is FR.hypothese_valuation_large:
        W = famille_successeurs(successeur(vn), "ifs")
        th = _pont_reflexif(appartient(vi, _seg_NN(successeur(vn))), E.valeur(W, vi), _HB)
    else:
        Nw = famille_successeurs(vn, "ifs")
        th = _pont_reflexif(appartient(vi, _seg_NN(vn)), E.valeur(Nw, vi), _HB)

    def prouveur(but, theorie):
        return th if th.conclusion == but else None

    assert C.classer(h, T0, prouveur=prouveur) == "dechargeable"   # LA BASCULE


def test_fam_nest_pas_dans_symboles_libres():
    """TOMBEAU DE L'ANCIEN ENCODAGE (migration valeur_famille := valeur, 2 août 2026).

    AVANT : « fam » figurait dans 4 des 22 axiomes, et la nuance honnête disait que
    ce n'était PAS « fam » qui témoignait de l'indépendance de HW, mais
    graphe_terme/seg_ext/G_ordre_NN.  DEPUIS la migration, X_ι = valeur(f, ι) :
    le symbole « fam » a DISPARU du dépôt entier — AXIOMES COMPRIS — et les ponts
    HW/HN sont des égalités t=t, dérivées closes par réflexivité
    (cf. `factorielle_def2_ultime`).  L'indépendance ne s'est pas démontrée : elle
    s'est DISSOUTE par l'encodage fidèle (une famille EST une fonction, E.II.4.1).
    ⚠️ Le classifieur SANS prouveur étiquette encore HW « independante » (critère
    d'occurrence seul, cf. test_pont_fam_valeur_independant) : illustration vivante
    de la défaisabilité du 3ᵉ verdict — le re-passer avec un prouveur-réflexivité
    rend « dechargeable »."""
    T0 = _T0()
    assert "fam" not in C.symboles_theorie(T0)
    assert "fam" not in C.symboles(FR.hypothese_valuation_large())
    porteurs = [a for a in T0.axiomes if "fam" in C.symboles(a)]
    assert len(porteurs) == 0


# ── (a) DÉCHARGEABLE — bo(≤,ℕ), et le FAUX MUR qu'il démasque ─────────────────
def test_bo_graphe_NN_piege_du_critere_syntaxique():
    """RAPIDE : sans prouveur, le critère syntaxique classe bo(≤,ℕ) « indépendante ».

    C'est FAUX (cf. le test `slow` ci-dessous : elle est CLOSE). Ce test fige la
    mesure qui justifie l'ordre imposé dans `classer` — preuve AVANT syntaxe."""
    T0, cible = _T0(), _bo_cible()
    assert C.symboles_libres(cible, T0) == frozenset({"G_ordre_NN"})
    assert C.classer(cible, T0) == "independante"          # le SEPTIÈME faux mur


@pytest.mark.slow
def test_bo_graphe_NN_est_dechargeable_avec_prouveur():
    """LENT (N_existe, ~5-6 min) : avec le prouveur injecté, le verdict s'inverse."""
    T0, cible = _T0(), _bo_cible()

    def prouveur(but, theorie):
        from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
            bo_graphe_NN)
        return bo_graphe_NN() if but == cible else None

    assert C.classer(cible, T0, prouveur=prouveur) == "dechargeable"
    assert len(_T0().axiomes) == 22


# ── « inconnu » n'est PAS « bloqué » : la classe se RE-MESURE ─────────────────
def test_inconnu_se_renverse_quand_le_prouveur_arrive():
    """Même h, deux passes : sans prouveur « inconnu », avec prouveur « déchargeable ».

    h := AXIOME_VIDE lui-même — tous ses symboles sont contraints par T0, donc le
    critère syntaxique ne dit rien : c'est exactement une DETTE DE MESURE."""
    T0 = _T0()
    h = E.AXIOME_VIDE
    assert C.symboles_libres(h, T0) == frozenset()
    assert C.classer(h, T0) == "inconnu"

    def prouveur(but, theorie):
        return N.axiome(theorie, but)                      # règle du noyau, rien d'autre

    assert C.classer(h, T0, prouveur=prouveur) == "dechargeable"


def test_tautologie_nest_jamais_independante():
    """h ⇒ h porte des symboles libres, mais se prouve sans axiome : garde-fou."""
    T0 = _T0()
    hw = FR.hypothese_valuation_large()
    taut = impl(hw, hw)
    assert C.symboles_libres(taut, T0)                     # non vide…
    assert not C.contingente(taut)                         # … mais non contingente
    assert C.classer(taut, T0) == "inconnu"


# ── Frontière de confiance : ce que rend un prouveur est RE-VÉRIFIÉ ───────────
def test_prouveur_menteur_nest_pas_cru():
    T0, h = _T0(), FR.hypothese_valuation_large()
    faux_theoreme = N.reflexivite(var("x"))                # ⊢ x = x, PAS h
    for menteur in (lambda b, t: faux_theoreme,            # bonne classe, mauvaise concl.
                    lambda b, t: "prouvé !",               # pas un Theoreme
                    lambda b, t: N.assume(b)):             # non clos (1 hypothèse)
        assert C.prouve(menteur, h, T0) is None
        assert C.classer(h, T0, prouveur=menteur) == "independante"


def test_prouveur_qui_leve_vaut_pas_de_preuve():
    T0, h = _T0(), E.AXIOME_VIDE

    def explose(but, theorie):
        raise RuntimeError("boum")

    assert C.classer(h, T0, prouveur=explose) == "inconnu"


def test_budget_epuise_rend_inconnu_pas_un_verdict():
    T0, h = _T0(), E.AXIOME_VIDE
    appels = []

    def prouveur(but, theorie):
        appels.append(but)
        return N.axiome(theorie, but)

    assert C.classer(h, T0, prouveur=prouveur, timeout=0) == "inconnu"
    assert appels == []                                    # le prouveur n'a PAS tourné


def test_classer_rejette_les_types_faux():
    with pytest.raises(TypeError):
        C.classer("h", _T0())
    with pytest.raises(TypeError):
        C.classer(E.AXIOME_VIDE, "T0")
