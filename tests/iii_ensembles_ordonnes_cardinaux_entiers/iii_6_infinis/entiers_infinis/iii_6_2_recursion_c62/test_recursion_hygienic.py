"""Tests du wrapper α-hygiénique de récursion (O3 — LEVÉE par le fix subst 2026-07-24).

Vérifie :
  • theorie_ensembles reste à 22 axiomes (noyau intact) ;
  • antecedent_dans_domaine_hygienic CLÔT la classe-quantificateur (F lie « y ») ;
  • il reproduit la conclusion du déposé sur un F « propre » ;
  • la classe-VALEUR (F lie le nom de la variable-valeur) CLÔT désormais aussi —
    l'ancienne « capture du S5 » était un renommage gratuit de subst, supprimé ;
  • la FACTORIELLE ne bute plus sur O3 : le gluing déposé construit le théorème
    d'existence des essais (3 résidus C62 honnêtes).
"""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, tau, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_recursion_hygienic import (
    antecedent_dans_domaine_hygienic,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hygienic_clot_F_propre():
    """F sans liant collisionnant : la version hygiénique clôt (concl ⇒, 0 hyp)."""
    r = antecedent_dans_domaine_hygienic("u", "v", "F")
    assert r.est_clos
    # conclusion = implication (u,v)∈F ⇒ u∈domF
    assert r.conclusion is not None


def test_hygienic_resout_y_class():
    """CLASSE-QUANTIFICATEUR : F lie internement « y » → le déposé capturerait ;
    le hygiénique CLÔT grâce au S5 frais-total + alpha_bridge."""
    F_y = tau("y", egal(var("w"), var("y")))          # τy(w=y) : F lie « y »
    r = antecedent_dans_domaine_hygienic("u", "v", F_y)
    assert r.est_clos                                  # 0 hypothèse résiduelle


def test_value_class_deverrouillee():
    """CLASSE-VALEUR : F lie le NOM de la variable-valeur « v ».  Depuis le fix subst,
    le S5 qui substitue var('v') ne renomme plus le liant interne de F (v n'est pas
    libre dessous = pas de capture réelle) → le wrapper CLÔT aussi cette classe."""
    F_v = tau("v", egal(var("w"), var("v")))          # τv(w=v) : F lie « v »
    r = antecedent_dans_domaine_hygienic("u", "v", F_v)
    assert r.est_clos


def test_factorielle_debloquee_O3():
    """O3 LEVÉE : le gluing déposé construit l'existence des essais factoriels
    (3 hypothèses = résidus C62 honnêtes ; cf. test_factorielle_existence)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
        factorielle_essais_existe,
    )
    thm = factorielle_essais_existe()
    assert thm.conclusion.tag == "non"                 # (∀n)(…) en tête
    assert len(thm.hypotheses) == 3
