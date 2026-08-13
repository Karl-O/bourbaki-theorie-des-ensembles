# -*- coding: utf-8 -*-
"""Test §III.6.1 — G_≤ + bo(R_G≤, ℕ) CLOS + C62 sur ℕ à 2 résidus + LE (∃!f) sur ℕ.

⚠️ LOURD : n_bien_ordonne (N_existe ~5 min + gate Zermelo).  slow, fichier seul.
Le (∃!f) sur ℕ est construit UNE SEULE FOIS (fixture de portée module) : le rebâtir
par test coûterait ~2,5 min chacun sans rien prouver de plus.

Ces tests VERROUILLENT L'ÉNONCÉ, pas la constructibilité :
  • la conclusion est RECONSTRUITE À LA MAIN ici (primitives `outil_formule` +
    `ensembles_abrege` seulement) — on n'importe AUCUN constructeur d'énoncé du
    module testé, sinon le test comparerait le module à lui-même ;
  • les hypothèses sont assertées par ÉGALITÉ EXACTE de frozenset (un `len(...) == 2`
    ne dit pas LESQUELLES : il laisserait passer un résidu de complaisance) ;
  • trois MUTANTS sont construits ici et le test montre qu'il les REJETTE :
    substitution (prédicat affaibli à 3 conjoints), pollution (hypothèse parasite
    empilée par gestes noyau purs), α-variant (liant existentiel renommé).
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    couple_dans_G_ordre, G_ordre_NN, bo_graphe_NN, c62_recursion_sur_NN,
    fonction_recursion_NN, existence_unicite_fonction_NN,
)

pytestmark = pytest.mark.slow

_T = lambda t: app("Trule", t)
_V, _ZN, _FB, _GB = "Uval", "zfgl", "fglb", "gcand"


def _residus_regle():
    """Les DEUX résidus honnêtes sur le VRAI ℕ, reconstruits à la main.

    Le troisième résidu de la version « variable » — est_bien_ordonne(R,Enat) — est
    ABSENT : c'est un THÉORÈME ici (`bo_graphe_NN`), pas une hypothèse."""
    NN, Gle = ensemble_NN(), G_ordre_NN()
    return frozenset({
        essais_bien_formes(_T, NN, Gle, _V, "qwf", "wwf", "zess"),
        rule_codomain(_T, _V, "zess"),
    })


def _predicat(t, conjoints=4):
    """P(t) = est_fonctionnel(t) ∧ est_un_graphe(t) ∧ dom(t)=ℕ ∧ (∀z∈ℕ)(t(z)=T(z)).

    `conjoints=3` construit la variante AFFAIBLIE (sans est_un_graphe) — le MUTANT de
    substitution.  Association gauche EXACTE (`et` est binaire)."""
    ve, vz = ensemble_NN(), var(_ZN)
    tete = et(E.est_fonctionnel(t), E.est_un_graphe(t)) if conjoints == 4 else E.est_fonctionnel(t)
    return et(et(tete, egal(E.dom(t), ve)),
              pourtout(_ZN, impl(appartient(vz, ve), egal(E.valeur(t, vz), _T(vz)))))


def _cible(fb=_FB, gb=_GB, conjoints=4):
    """(∃f)( P(f) ∧ (∀g)( P(g) ⇒ g = f ) ), reconstruit à la main."""
    vf, vg = var(fb), var(gb)
    return existe(fb, et(_predicat(vf, conjoints),
                         pourtout(gb, impl(_predicat(vg, conjoints), egal(vg, vf)))))


@pytest.fixture(scope="module")
def exu():
    """Le (∃!f) sur le VRAI ℕ — construit UNE fois pour tout le module."""
    return existence_unicite_fonction_NN(_T, _V, _FB, _GB, _ZN)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_couple_dans_G_ordre_clos():
    """⊢ ((s,t)∈G_≤) ⇔ ordre_induit_NN(s,t) — CLOS."""
    assert couple_dans_G_ordre(var("stest"), var("ttest")).est_clos


def test_bo_graphe_NN_clos():
    """🎯 ⊢ est_bien_ordonne(R_G≤, ℕ) — CLOS (transport par feuilles)."""
    assert bo_graphe_NN().est_clos


def test_c62_sur_NN_2_residus():
    """🎯🎯 C62 sur le vrai ℕ : 2 hyps = données de la règle seulement."""
    th = c62_recursion_sur_NN(_T)
    assert len(th.hypotheses) == 2


def test_fonction_recursion_NN_2_residus():
    """🎯🎯 (∃f) sur le vrai ℕ : 2 hyps ; theorie==22."""
    th = fonction_recursion_NN(_T)
    assert len(th.hypotheses) == 2
    assert th.conclusion.tag == "exists"
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 LE CAPSTONE — le (∃!f) de C62 sur le VRAI ℕ.
# ════════════════════════════════════════════════════════════════════════════
def test_existence_unicite_NN_enonce_exact(exu):
    """🎯🎯🎯 { ebf, rc } ⊢ (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g=f ) ) — énoncé verrouillé."""
    assert exu.conclusion == _cible(), "le (∃!f) sur ℕ n'est pas l'énoncé attendu"
    assert exu.conclusion.tag == "exists"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_existence_unicite_NN_residus_exacts(exu):
    """Le bon ordre est DÉCHARGÉ : il ne reste QUE les deux données de la règle.

    Égalité exacte de frozenset — un `len(...) == 2` laisserait passer la substitution
    d'un résidu honnête par une hypothèse de complaisance."""
    assert exu.hypotheses == _residus_regle(), \
        "résidus ≠ { essais_bien_formes, rule_codomain } — le bon ordre a-t-il fui ?"
    assert exu.conclusion not in exu.hypotheses, "VACUOUS"


def test_mutant_substitution_rejete(exu):
    """MUTANT 1 (substitution) : prédicat affaibli à 3 conjoints ⇒ doit être REJETÉ.

    Retirer `est_un_graphe` rendrait l'unicité FAUSSE : g et g∪{a} (a non-couple) ont
    mêmes fonctionnalité, domaine et valeurs en étant DIFFÉRENTS."""
    affaibli = _cible(conjoints=3)
    assert affaibli != _cible(), "le mutant à 3 conjoints doit différer de la cible"
    assert exu.conclusion != affaibli, \
        "l'énoncé a été affaibli à 3 conjoints : sans est_un_graphe l'unicité est FAUSSE"


def test_mutant_pollution_rejete(exu):
    """MUTANT 2 (pollution) : même conclusion, hypothèse parasite empilée.

    Construit par gestes NOYAU PURS (loi_deduction puis modus ponens sur un `assume`),
    donc c'est un théorème PARFAITEMENT valide — seule l'assertion sur les hypothèses
    le distingue.  Un test qui ne verrouillerait que la conclusion le laisserait vivre."""
    parasite = appartient(var("polluant"), ensemble_NN())
    pollue = N.modus_ponens(N.assume(parasite), N.loi_deduction(parasite, exu))

    # GARDE : un mutant CASSÉ (qui mourrait d'une erreur, pas de l'assertion visée)
    # ne prouverait rien.  On vérifie donc d'abord qu'il est BIEN FORMÉ.
    assert pollue.conclusion == exu.conclusion, "mutant CASSÉ : conclusion altérée"
    assert pollue.hypotheses != exu.hypotheses, "la pollution n'a rien ajouté"
    assert pollue.hypotheses != _residus_regle(), \
        "le mutant pollué passerait l'assertion de résidus — le test est décoratif"
    assert parasite in pollue.hypotheses


def test_mutant_alpha_variant_rejete(exu):
    """MUTANT 3 (α-variant) : même force logique, liant existentiel renommé.

    Le noyau n'identifie PAS les α-variants : la formule est structurellement AUTRE.
    On verrouille donc le liant, sans quoi une dérive de nommage passerait inaperçue."""
    alpha = _cible(fb="fglZ")
    assert alpha != _cible(), "le renommage du liant doit produire une formule ≠"
    assert exu.conclusion != alpha, "l'énoncé a dérivé sur le liant existentiel"
