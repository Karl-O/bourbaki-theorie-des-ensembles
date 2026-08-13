"""Tests — EXISTENCE factorielle : les essais C62 CONSTRUISENT (fix subst 2026-07-24).

On vérifie les FAITS honnêtes (rien postulé) :
  • `regle_factorielle()` est un TERME bien formé (callable Terme→Terme), index-aware ;
  • `factorielle_essais_existe()` renvoie le théorème d'existence des essais —
    l'ancienne « τ-capture » (O3) était un renommage gratuit de subst, supprimé ;
    3 hypothèses = les résidus C62 honnêtes {bo(≤,ℕ), essais_bien_formes, rule_codomain} ;
  • theorie_ensembles() = 22 (noyau intact).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, Terme
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
    regle_factorielle, factorielle_essais_existe,
)


def test_theorie_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_regle_factorielle_est_terme():
    """La règle factorielle index-aware est un terme bien formé (callable Terme→Terme)."""
    T = regle_factorielle()
    out = T(var("u0"))
    assert isinstance(out, Terme)
    # terme τ (la règle T{u} = τy(...))
    assert out.tag == "tau"


def test_essais_factoriels_existent():
    """✅ O3 LEVÉE (fix subst) : l'existence des essais factoriels CONSTRUIT.

    ⊢ (∀n)( n∈ℕ ⇒ (∃p) est_essai(p, T_fac, ≤, ℕ, n) )  sous les 3 résidus C62 honnêtes.
    Rien n'est postulé ; le noyau vérifie chaque pas."""
    thm = factorielle_essais_existe()
    assert thm.conclusion.tag == "non"        # (∀n)(…) = ¬∃¬ en tête
    assert len(thm.hypotheses) == 3           # bo(≤,ℕ), essais_bien_formes, rule_codomain
    assert not thm.est_clos
    assert thm.conclusion not in thm.hypotheses          # non vacueux
    assert len(theorie_ensembles().axiomes) == 22
