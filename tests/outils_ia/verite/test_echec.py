#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests de `echec.py` — TEST MIROIR sur le cas réel, et il doit MORDRE.

Un `verifier()` qui rend True partout est DÉCORATIF. Chaque test « certificat
correct » est donc suivi de MUTANTS (même objet, un seul détail changé) dont on
exige qu'ils soient REJETÉS. Tous les certificats-théorèmes sont construits par les
primitives PUBLIQUES du noyau (`N.assume`, `N.s2`, `N.modus_ponens`, `N.axiome`,
`instancie`) : aucun `_CLE`, aucun `Theoreme(...)` à la main, aucun monkeypatch.

Rapide (aucun import cardinal) : mesuré ~0,05 s d'import.

Emplacement : `tests/outils_ia/verite/`, comme les deux autres tests du paquet.
Il a vécu dans `outils_ia/verite/` et s'y importait par un `sys.path.insert` :
`echec` devenait alors un module TOP-LEVEL distinct de `outils_ia.verite.echec`
(mesuré le 2026-07-26 : `VE.Echec is TOP.Echec` → False, et `VE.verifier(e)` → False
sur un `Echec` valide bâti par l'autre copie). Ne jamais restaurer ce raccourci.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (   # noqa: E402
    alpha_egal, appartient, egal, existe, non, var)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N  # noqa: E402
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie  # noqa: E402
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E  # noqa: E402

from outils_ia.verite.echec import (Echec, Mur, derive, est_vide_syntaxique,   # noqa: E402
                                    mur_residu_indice_vide, negation_temoin_close,
                                    temoin_absurdite, verifier)

VIDE = E.VIDE


# ── L'invariant, mesuré ici même ──────────────────────────────────────────────
def test_invariant_22_avant_et_apres():
    """Ce module n'ajoute AUCUN axiome : theorie_ensembles() == 22 avant ET après."""
    avant = len(E.theorie_ensembles().axiomes)
    negation_temoin_close()
    mur_residu_indice_vide()
    apres = len(E.theorie_ensembles().axiomes)
    assert avant == 22 and apres == 22, (avant, apres)


def test_temoin_absurdite_a_sa_negation_close():
    """Pas de « faux » primitif : ⊢ ¬(∅∈∅) est un théorème CLOS, refait par le noyau."""
    n = negation_temoin_close()
    assert n.est_clos
    assert n.conclusion == non(temoin_absurdite())
    assert temoin_absurdite() == appartient(VIDE, VIDE)


# ── Cas réel : E2 vacuité (résidu « j∈∅ ») ────────────────────────────────────
def _certificat_vacuite(residu):
    """{residu} ⊢ ∅∈∅ où residu = (j∈∅).  Chaîne : ex falso sur l'axiome du vide."""
    absurde = temoin_absurdite()
    nj = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), var("j"))   # ⊢ ¬(j∈∅)
    imp = N.modus_ponens(nj, N.s2(non(residu), absurde))                       # ⊢ (j∈∅ ⇒ ∅∈∅)
    return N.modus_ponens(N.assume(residu), imp)


def _echec_vacuite_reel():
    residu = appartient(var("j"), VIDE)                # H(I) instancié en I := ∅
    cert = _certificat_vacuite(residu)
    e = Echec(but=egal(var("f"), var("f")), classe="E2", certificat=cert,
              rebroussement="ne plus instancier I:=∅ ; exiger I contenant j",
              perimetre=frozenset({VIDE}))
    return e, residu, cert


def test_E2_correct_est_accepte():
    e, residu, cert = _echec_vacuite_reel()
    assert cert.conclusion == temoin_absurdite()
    assert cert.hypotheses == frozenset({residu})
    assert verifier(e, residu) is True


def test_mutant_meme_certificat_classe_E5_est_rejete():
    """MUTANT 1 — on ne change QUE la classe : E5 exige un certificat CLOS."""
    e, residu, cert = _echec_vacuite_reel()
    mutant = Echec(but=e.but, classe="E5", certificat=cert,
                   rebroussement=e.rebroussement, perimetre=e.perimetre)
    assert verifier(mutant, residu) is False


def test_mutant_E5_a_hypotheses_non_vides_est_rejete():
    """MUTANT 2 — un E5 dont le certificat porte une hypothèse : rejeté."""
    residu = non(appartient(var("z"), VIDE))
    ouvert = N.assume(residu)                                   # {résidu} ⊢ résidu
    mutant = Echec(but=residu, classe="E5", certificat=ouvert,
                   rebroussement="reprouver le résidu sans hypothèse",
                   perimetre=frozenset())
    assert ouvert.hypotheses and ouvert.conclusion == residu
    assert verifier(mutant, residu) is False


def test_mutant_E5_conclusion_qui_n_est_pas_le_residu_est_rejete():
    """MUTANT 3 — certificat clos, mais qui conclut AUTRE CHOSE que le résidu."""
    residu = non(appartient(var("z"), VIDE))
    hors_sujet = N.reflexivite(var("a"))                        # ⊢ a = a  (clos)
    mutant = Echec(but=residu, classe="E5", certificat=hors_sujet,
                   rebroussement="reprouver le résidu",
                   perimetre=frozenset())
    assert hors_sujet.est_clos
    assert verifier(mutant, residu) is False


def test_E5_fantome_reel_est_accepte():
    """Cas réel de fantôme : le « résidu » ¬(z∈∅) est un THÉORÈME CLOS de T0."""
    residu = non(appartient(var("z"), VIDE))
    clos = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), var("z"))
    e = Echec(but=residu, classe="E5", certificat=clos,
              rebroussement="supprimer l'hypothèse : elle se décharge",
              perimetre=frozenset({residu}))
    assert clos.est_clos and clos.conclusion == residu
    assert verifier(e, residu) is True


# ── E2 : les autres mutants (le certificat doit correspondre à la classe) ─────
def test_mutant_E2_sans_residu_est_rejete():
    e, _residu, _c = _echec_vacuite_reel()
    assert verifier(e, None) is False


def test_mutant_E2_hypothese_hors_du_residu_est_rejete():
    """Le certificat prouve ∅∈∅ mais depuis une hypothèse NON invoquée : rejeté."""
    e, residu, _c = _echec_vacuite_reel()
    autre = appartient(var("k"), VIDE)
    assert verifier(e, autre) is False              # {j∈∅} ⊄ {k∈∅}


def test_mutant_E2_conclusion_non_absurde_est_rejete():
    residu = appartient(var("j"), VIDE)
    ouvert = N.assume(residu)                        # conclut le résidu, pas ∅∈∅
    mutant = Echec(but=residu, classe="E2", certificat=ouvert,
                   rebroussement="x", perimetre=frozenset())
    assert verifier(mutant, residu) is False


def test_mutant_E2_certificat_non_theoreme_est_rejete():
    residu = appartient(var("j"), VIDE)
    mutant = Echec(but=residu, classe="E2", certificat="j∈∅ est absurde",
                   rebroussement="x", perimetre=frozenset())
    assert verifier(mutant, residu) is False


# ── E1 dérive : test SYNTAXIQUE, cible reconstruite HORS du module ────────────
def test_derive_vrai_quand_la_conclusion_n_est_pas_la_cible():
    construit = N.reflexivite(var("a"))                       # ⊢ a = a
    cible = egal(var("b"), var("b"))                          # cible RECONSTRUITE ici
    assert derive(construit, cible) is True
    e = Echec(but=cible, classe="E1", certificat=construit,
              rebroussement="viser b, pas a", perimetre=frozenset())
    assert verifier(e) is True


def test_derive_faux_quand_la_cible_est_atteinte():
    construit = N.reflexivite(var("a"))
    assert derive(construit, egal(var("a"), var("a"))) is False
    e = Echec(but=egal(var("a"), var("a")), classe="E1", certificat=construit,
              rebroussement="rien", perimetre=frozenset())
    assert verifier(e) is False              # ce n'est PAS un échec : c'est la cible


def test_derive_faux_si_rien_de_complet_n_a_ete_construit():
    assert derive(None, egal(var("a"), var("a"))) is False
    assert derive("preuve en cours", egal(var("a"), var("a"))) is False


def test_derive_est_syntaxique_pas_alpha():
    """α-égalité = test DISTINCT et PLUS FAIBLE : deux α-variants restent une dérive."""
    fx = existe("x", appartient(var("x"), VIDE))
    fy = existe("y", appartient(var("y"), VIDE))
    assert alpha_egal(fx, fy) is True and fx != fy
    assert derive(N.assume(fx), fy) is True


# ── Mur : le périmètre est CALCULÉ, sur les trois formes réelles ──────────────
def test_predicat_du_mur_sur_les_trois_formes():
    """Réfutable( j∈I ) ⇔ I syntaxiquement ∅ : ∅ dedans, J∪{j} et I variable dehors."""
    j = var("j")
    forme_vide = VIDE
    forme_avec_j = E.reunion(var("J"), E.singleton(j))
    forme_variable = var("I")
    assert est_vide_syntaxique(forme_vide) is True
    assert est_vide_syntaxique(forme_avec_j) is False
    assert est_vide_syntaxique(forme_variable) is False

    mur = mur_residu_indice_vide("j")
    candidats = [forme_vide, forme_avec_j, forme_variable]
    assert mur.portee(candidats) == frozenset({forme_vide})
    assert mur.hors_atteinte(candidats) == frozenset({forme_avec_j, forme_variable})
    assert mur.certificat.est_clos
    assert mur.certificat.conclusion == non(appartient(j, VIDE))


def test_perimetre_calcule_par_le_mur_pas_suppose():
    mur = mur_residu_indice_vide()
    candidats = [VIDE, var("I"), E.reunion(var("J"), E.singleton(var("j")))]
    e = Echec.depuis_mur(but=egal(var("f"), var("f")), classe="E3", mur=mur,
                         rebroussement="fournir I contenant j", candidats=candidats)
    assert e.perimetre == frozenset({VIDE})       # calculé, pas déclaré
    assert verifier(e) is True


def test_mur_mal_forme_et_E3_sans_mur_sont_rejetes():
    assert Mur(condition="", predicat=est_vide_syntaxique).forme_valide() is False
    assert Mur(condition="c", predicat=None).forme_valide() is False
    e = Echec(but=None, classe="E3", certificat=N.reflexivite(var("a")),
              rebroussement="x", perimetre=frozenset())
    assert verifier(e) is False                   # un théorème n'est pas un mur


# ── E4 / E6 / E7 : chaque classe impose sa forme, et le mutant tombe ──────────
def test_E4_dette_forme_correcte_et_mutants():
    dette = frozenset({("Dfam-real-C60", appartient(var("p"), var("D")))})
    ok = Echec(but=None, classe="E4", certificat=dette,
               rebroussement="décharger l'axiome dédié", perimetre=frozenset())
    assert verifier(ok) is True
    vide = Echec(but=None, classe="E4", certificat=frozenset(),
                 rebroussement="x", perimetre=frozenset())
    assert verifier(vide) is False                # dette vide = pas de dette
    mauvais = Echec(but=None, classe="E4", certificat=frozenset({"Dfam-real-C60"}),
                    rebroussement="x", perimetre=frozenset())
    assert verifier(mauvais) is False             # des noms sans les formules


def test_E6_infidelite_exige_un_ecart_reel():
    but = egal(var("a"), var("a"))
    autre = egal(var("a"), var("b"))
    ok = Echec(but=but, classe="E6", certificat=(autre, "E III.2 L.3-14"),
               rebroussement="recaler l'énoncé sur le PDF", perimetre=frozenset())
    assert verifier(ok) is True
    faux = Echec(but=but, classe="E6", certificat=(but, "E III.2 L.3-14"),
                 rebroussement="x", perimetre=frozenset())
    assert verifier(faux) is False                # aucun écart : pas d'infidélité


def test_E7_erreur_de_mesure_exige_deux_chiffres_differents():
    ok = Echec(but=None, classe="E7", certificat=(22, 25),
               rebroussement="recompter avec axiomes_consommes", perimetre=frozenset())
    assert verifier(ok) is True
    faux = Echec(but=None, classe="E7", certificat=(22, 22),
                 rebroussement="x", perimetre=frozenset())
    assert verifier(faux) is False


# ── Garde-fous transverses ────────────────────────────────────────────────────
def test_classe_inconnue_et_rebroussement_vide_sont_rejetes():
    cert = N.reflexivite(var("a"))
    assert verifier(Echec(but=None, classe="E9", certificat=cert,
                          rebroussement="x", perimetre=frozenset())) is False
    assert verifier(Echec(but=egal(var("b"), var("b")), classe="E1", certificat=cert,
                          rebroussement="   ", perimetre=frozenset())) is False
    assert verifier("pas un Echec") is False


def test_echec_et_mur_sont_immuables():
    import dataclasses
    e = Echec(but=None, classe="E7", certificat=(1, 2), rebroussement="x",
              perimetre=frozenset())
    for obj, champ, val in ((e, "classe", "E1"),
                            (mur_residu_indice_vide(), "condition", "autre")):
        try:
            setattr(obj, champ, val)
        except dataclasses.FrozenInstanceError:
            continue
        raise AssertionError(f"{type(obj).__name__} devrait être immuable")
