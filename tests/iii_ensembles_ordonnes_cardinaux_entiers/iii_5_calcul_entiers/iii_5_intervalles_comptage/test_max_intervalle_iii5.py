"""Tests MIROIR — §III.5.3 : le plus grand élément de [0,n] est n, et M([0,n]) = n.

Les trois cibles sont RECONSTRUITES À LA MAIN ici (constructeurs de `outil_formule`
+ `inf_egal_card` + `E.intervalle_entiers` + `ZERO`), JAMAIS via les fonctions
`cible_*` du module — sinon le module serait comparé à lui-même.

Hypothèses assertées par ÉGALITÉ EXACTE de frozenset (`len(...)==1` ne dirait pas
LAQUELLE).  Mutants exercés : POLLUTION, SUBSTITUTION, ALPHA-VARIANTE, VOISIN VRAI
(M sur un autre intervalle ; le τ du plus PETIT élément ; l'antisymétrie close du
même module).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, pourtout, tau, alpha_egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    intervalle_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_max_intervalle_iii5 import (
    antisymetrie_ordre_sur_intervalle, plus_grand_element_intervalle,
    max_intervalle_vaut_n, terme_max_intervalle, max_intervalle_vaut_n_entier,
)

n = var("n")


# ── reconstructions À LA MAIN (hors module) ──────────────────────────────────
def _interv(borne=n):
    return E.intervalle_entiers(ZERO, borne)


def _pge_main(borne=n, elt=n, x="x"):
    """« elt est le plus grand élément de [0,borne] », reconstruit à la main."""
    I = _interv(borne)
    return et(appartient(elt, I),
              pourtout(x, impl(appartient(var(x), I), inf_egal_card(var(x), elt))))


def _M_main(borne=n, m="m", x="x"):
    return tau(m, _pge_main(borne, var(m), x))


def _antisym_main(borne=n, u="u1", v="v1"):
    I = _interv(borne)
    return pourtout(u, pourtout(v, impl(
        et(et(appartient(var(u), I), appartient(var(v), I)),
           et(inf_egal_card(var(u), var(v)), inf_egal_card(var(v), var(u)))),
        egal(var(u), var(v)))))


# ══════════════════════════════════════════════════════════════════════════════
#  (1) ANTISYMÉTRIE SUR [0,n] — CLOSE
# ══════════════════════════════════════════════════════════════════════════════
def test_antisymetrie_conclusion_et_cloture():
    thm = antisymetrie_ordre_sur_intervalle()
    assert thm.conclusion == _antisym_main()
    assert thm.hypotheses == frozenset()       # CLOS : 0 hypothèse, LESQUELLES = aucune
    assert thm.est_clos


# ══════════════════════════════════════════════════════════════════════════════
#  (2) n EST LE PLUS GRAND ÉLÉMENT DE [0,n]
# ══════════════════════════════════════════════════════════════════════════════
def test_plus_grand_conclusion_egale_cible_a_la_main():
    assert plus_grand_element_intervalle().conclusion == _pge_main()


def test_plus_grand_hypotheses_exactes():
    thm = plus_grand_element_intervalle()
    assert thm.hypotheses == frozenset({est_cardinal(n)})
    assert not thm.est_clos                    # honnêteté : CLOS MODULO est_cardinal(n)


def test_plus_grand_non_vacuous():
    thm = plus_grand_element_intervalle()
    assert thm.conclusion not in thm.hypotheses


def test_l_hypothese_n_est_pas_gratuite_elle_decoule_de_la_cible():
    """CERTIFICAT DE NON-GRATUITÉ, démontré (pas affirmé en docstring).

    La cible ⊢ est_cardinal(n) : son 1ᵉʳ conjoint est n ∈ [0,n], et
    `intervalle_implique_cardinal` en tire la cardinalité.  L'hypothèse est donc
    une CONSÉQUENCE de la conclusion — impossible de l'affaiblir."""
    # « x∈[a,b] ⇒ x cardinal » généralisé puis instancié en (0, n, n) — À LA MAIN
    pont = N.generalisation("ia", N.generalisation("ib", N.generalisation(
        "ix", intervalle_implique_cardinal("ia", "ib", "ix"))))
    pont = instancie(instancie(instancie(pont, ZERO), n), n)
    depuis_la_cible = N.modus_ponens(
        conjonction_elim_gauche(N.assume(_pge_main())), pont)
    assert depuis_la_cible.conclusion == est_cardinal(n)
    assert depuis_la_cible.hypotheses == frozenset({_pge_main()})


def test_plus_grand_n_est_pas_le_plus_petit():
    """VOISIN : la version « plus petit élément » a les arguments de ≤ INVERSÉS."""
    I = _interv()
    petit = et(appartient(n, I),
               pourtout("x", impl(appartient(var("x"), I), inf_egal_card(n, var("x")))))
    assert plus_grand_element_intervalle().conclusion != petit


# ══════════════════════════════════════════════════════════════════════════════
#  (3) LE CAPSTONE :  M([0,n]) = n
# ══════════════════════════════════════════════════════════════════════════════
def test_max_conclusion_egale_cible_a_la_main():
    assert max_intervalle_vaut_n().conclusion == egal(_M_main(), n)


def test_le_terme_M_est_bien_le_tau_attendu():
    assert terme_max_intervalle() == _M_main()


def test_max_hypotheses_exactes():
    thm = max_intervalle_vaut_n()
    assert thm.hypotheses == frozenset({est_cardinal(n)})
    assert len(thm.hypotheses) == 1
    assert not thm.est_clos


def test_max_non_vacuous():
    thm = max_intervalle_vaut_n()
    assert thm.conclusion not in thm.hypotheses


# ══════════════════════════════════════════════════════════════════════════════
#  (4) LA FORME DU LIVRE : hypothèse « n ENTIER »
# ══════════════════════════════════════════════════════════════════════════════
def test_forme_entier_conclusion_et_hypothese():
    thm = max_intervalle_vaut_n_entier()
    assert thm.conclusion == egal(_M_main(), n)             # MÊME conclusion
    assert thm.hypotheses == frozenset({est_fini(n)})       # est_entier = est_fini
    assert not thm.est_clos


def test_forme_entier_a_bien_change_d_hypothese():
    """L'hypothèse a bien été RENFORCÉE (entier), pas seulement renommée."""
    faible = max_intervalle_vaut_n()
    fort = max_intervalle_vaut_n_entier()
    assert faible.hypotheses == frozenset({est_cardinal(n)})
    assert fort.hypotheses != faible.hypotheses
    assert est_cardinal(n) not in fort.hypotheses           # elle a été DÉCHARGÉE


# ══════════════════════════════════════════════════════════════════════════════
#  MUTANTS
# ══════════════════════════════════════════════════════════════════════════════
def test_mutant_pollution_est_tue():
    parasite = appartient(var("zzz"), var("Bidon"))
    mutant = conjonction_elim_gauche(
        conjonction_intro(max_intervalle_vaut_n(), N.assume(parasite)))
    assert mutant.conclusion == egal(_M_main(), n)       # conclusion INCHANGÉE
    assert mutant.hypotheses != frozenset({est_cardinal(n)})   # …mais polluée
    assert parasite in mutant.hypotheses


def test_mutant_substitution_est_tue():
    assert max_intervalle_vaut_n().conclusion != egal(_M_main(), var("k"))


def test_mutant_alpha_variante_est_tue():
    """Liant du τ renommé : `==` refuse (assertion utilisée), `alpha_egal` accepterait."""
    alpha = egal(_M_main(m="m2"), n)
    assert max_intervalle_vaut_n().conclusion != alpha
    assert alpha_egal(max_intervalle_vaut_n().conclusion, alpha)


def test_mutant_voisin_vrai_autre_intervalle_est_tue():
    """VOISIN VRAI : M([0,k]) = k est CORRECT et prouvé, mais n'est pas la cible."""
    voisin = max_intervalle_vaut_n("k")
    assert voisin.conclusion == egal(_M_main(var("k")), var("k"))   # il est VRAI
    assert voisin.hypotheses == frozenset({est_cardinal(var("k"))})
    assert voisin.conclusion != egal(_M_main(), n)                  # mais ≠ la cible
    assert voisin.hypotheses != frozenset({est_cardinal(n)})


def test_mutant_voisin_vrai_antisymetrie_close_est_tue():
    """VOISIN VRAI : un théorème CLOS du même module, mais pas la cible.

    Un test qui se contenterait de « est_clos » l'accepterait ; la cible, elle,
    n'est PAS close (elle porte est_cardinal(n))."""
    voisin = antisymetrie_ordre_sur_intervalle()
    assert voisin.est_clos
    assert voisin.conclusion != egal(_M_main(), n)


def test_mutant_voisin_vrai_tau_du_plus_petit_est_tue():
    I = _interv()
    petit = tau("m", et(appartient(var("m"), I),
                        pourtout("x", impl(appartient(var("x"), I),
                                           inf_egal_card(var("m"), var("x"))))))
    assert petit != _M_main()
    assert max_intervalle_vaut_n().conclusion != egal(petit, n)


# ══════════════════════════════════════════════════════════════════════════════
#  INVARIANT
# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22
