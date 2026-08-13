# -*- coding: utf-8 -*-
"""Test §III.6.2 — C62 unicité, puis le (∃!f) : existence ET unicité recollées.

Ces tests VERROUILLENT L'ÉNONCÉ, pas la constructibilité :
  • la conclusion est RECONSTRUITE À LA MAIN ici (primitives `outil_formule` +
    `ensembles_abrege` seulement) — on n'importe AUCUN constructeur d'énoncé du
    module testé, sinon le test se contenterait de comparer le module à lui-même ;
  • les hypothèses sont assertées par ÉGALITÉ EXACTE de frozenset (un
    `len(...) == 3` ne dit pas LESQUELLES : il laisserait passer la substitution
    d'un résidu honnête par une hypothèse de complaisance) ;
  • `theorie_ensembles() == 22` (aucun axiome ajouté).

Règle OPAQUE T(t)=app('Trule',t)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, var, egal, et, impl, appartient, existe, pourtout,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_unicite import (
    fonction_globale_inclus_produit, est_un_graphe_fonction_globale,
    unicite_fonction_c62, existence_unicite_fonction_c62,
)

_T = lambda t: app("Trule", t)
_E, _G, _V, _ZN = "Enat", "Gle", "Uval", "zfgl"
_FB, _GB = "fglb", "gcand"


def _residus_c62():
    """Les TROIS résidus honnêtes de C62, reconstruits à la main."""
    return frozenset({
        E.est_bien_ordonne(_graphe_R(_G), var(_E)),            # ℕ bien ordonné
        essais_bien_formes(_T, _E, _G, _V, "qwf", "wwf", "zess"),
        rule_codomain(_T, _V, "zess"),
    })


def _predicat(t):
    """P(t) = est_fonctionnel(t) ∧ est_un_graphe(t) ∧ dom(t)=ℕ ∧ (∀z∈ℕ)(t(z)=T(z)).

    Reconstruit à la main, avec l'association gauche EXACTE (`et` est binaire)."""
    ve, vz = var(_E), var(_ZN)
    return et(et(et(E.est_fonctionnel(t), E.est_un_graphe(t)), egal(E.dom(t), ve)),
              pourtout(_ZN, impl(appartient(vz, ve), egal(E.valeur(t, vz), _T(vz)))))


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inclus_produit_clos():
    """⊢ ⋃𝔇_tot ⊂ ℕ×U — CLOS, 0 hypothèse."""
    th = fonction_globale_inclus_produit(_T)
    assert th.est_clos and th.hypotheses == frozenset()


def test_est_un_graphe_clos():
    """⊢ est_un_graphe(⋃𝔇_tot) — CLOS : le 4ᵉ conjoint est GRATUIT."""
    th = est_un_graphe_fonction_globale(_T)
    assert th.est_clos and th.hypotheses == frozenset()
    assert th.conclusion == E.est_un_graphe(fonction_globale(_E, _V))


def test_unicite_enonce_exact():
    """🎯🎯 {bo, ebf, rc} ⊢ (∀g)( P(g) ⇒ g = ⋃𝔇_tot ) — énoncé verrouillé."""
    th = unicite_fonction_c62(_T, _E, _G, _V, _GB, _ZN)
    vg = var(_GB)
    attendu = pourtout(_GB, impl(_predicat(vg), egal(vg, fonction_globale(_E, _V))))
    assert th.conclusion == attendu
    assert th.hypotheses == _residus_c62()
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_existence_unicite_enonce_exact():
    """🎯🎯🎯 {bo, ebf, rc} ⊢ (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g=f ) ) — LE (∃!f) de C62."""
    th = existence_unicite_fonction_c62(_T, _E, _G, _V, _FB, _GB, _ZN)
    vf, vg = var(_FB), var(_GB)
    attendu = existe(_FB, et(_predicat(vf),
                             pourtout(_GB, impl(_predicat(vg), egal(vg, vf)))))
    assert th.conclusion == attendu, "le (∃!f) n'est pas l'énoncé attendu"
    assert th.conclusion.tag == "exists"
    assert th.hypotheses == _residus_c62(), "résidus ≠ {bo, essais_bien_formes, rule_codomain}"
    assert th.conclusion not in th.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_existence_unicite_naffaiblit_pas_lunicite():
    """GARDE-FOU : le conjoint `est_un_graphe` est bien DANS les deux occurrences de P.

    Le piège de ce chantier était de retirer `est_un_graphe(g)` de l'antécédent de
    l'unicité pour « aligner » sur l'existence à 3 conjoints.  Ce serait FAUX : g et
    g∪{a} (a non-couple) ont mêmes fonctionnalité, domaine et valeurs.  On verrouille
    donc que l'énoncé obtenu N'EST PAS la variante affaiblie à 3 conjoints."""
    ve, vz = var(_E), var(_ZN)

    def _p3(t):                      # la variante AFFAIBLIE (sans est_un_graphe)
        return et(et(E.est_fonctionnel(t), egal(E.dom(t), ve)),
                  pourtout(_ZN, impl(appartient(vz, ve), egal(E.valeur(t, vz), _T(vz)))))

    vf, vg = var(_FB), var(_GB)
    assert _p3(vg) != _predicat(vg), "la variante à 3 conjoints doit différer de P"
    affaibli = existe(_FB, et(_p3(vf), pourtout(_GB, impl(_p3(vg), egal(vg, vf)))))

    th = existence_unicite_fonction_c62(_T, _E, _G, _V, _FB, _GB, _ZN)
    assert th.conclusion != affaibli, \
        "l'énoncé a été affaibli à 3 conjoints : sans est_un_graphe l'unicité est FAUSSE"
    # et le renforcement n'a rien coûté : mêmes résidus que la moitié « unicité ».
    assert th.hypotheses == unicite_fonction_c62(_T, _E, _G, _V, _GB, _ZN).hypotheses
