"""Tests MIROIR — §III.1.7 : le TERME M_R(A) = τ_m( m plus grand élt de A ).

La cible est RECONSTRUITE À LA MAIN ici, à partir des seuls constructeurs de
`outil_formule` (et, impl, pourtout, appartient, tau, egal) — JAMAIS via
`cible_terme_plus_grand_vaut` du module : sinon on comparerait le module à
lui-même.

Mutants exercés (un mutant SURVIVANT signalerait un test décoratif) :
  • POLLUTION      — hypothèse parasite empilée par gestes PURS du noyau ;
  • SUBSTITUTION   — conclusion remplacée (M = b au lieu de M = a) ;
  • ALPHA-VARIANTE — liant du τ renommé (le noyau n'identifie PAS les α-variants) ;
  • VOISIN VRAI    — un théorème CORRECT et clos du même module, mais pas la cible
                     (M sur un AUTRE ensemble ; et le τ du plus PETIT élément).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, pourtout, tau, alpha_egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_7_plus_grand_plus_petit.ensembles_terme_plus_grand import (
    terme_plus_grand, antisymetrie_sur, terme_plus_grand_vaut, liants_de,
    verifie_liants_frais,
)

A, a, b = var("A"), var("a"), var("b")


def R(p, q):
    """R{p,q} := (p,q) ∈ G — relation OPAQUE (aucun liant interne)."""
    return appartient(E.couple(p, q), var("G"))


# ── reconstructions À LA MAIN (hors module) ──────────────────────────────────
def _pge_main(ens, elt, x="x"):
    """« elt est le plus grand élément de ens » reconstruit à la main."""
    return et(appartient(elt, ens),
              pourtout(x, impl(appartient(var(x), ens), R(var(x), elt))))


def _M_main(ens, m="m", x="x"):
    return tau(m, _pge_main(ens, var(m), x))


def _antisym_main(ens, u="u1", v="v1"):
    return pourtout(u, pourtout(v, impl(
        et(et(appartient(var(u), ens), appartient(var(v), ens)),
           et(R(var(u), var(v)), R(var(v), var(u)))),
        egal(var(u), var(v)))))


def _cible_main(ens=A, elt=a):
    return egal(_M_main(ens), elt)


def _thm():
    return terme_plus_grand_vaut(R, A, a)


# ══════════════════════════════════════════════════════════════════════════════
#  CIBLE ET HYPOTHÈSES
# ══════════════════════════════════════════════════════════════════════════════
def test_conclusion_egale_cible_reconstruite_a_la_main():
    assert _thm().conclusion == _cible_main()


def test_le_terme_M_est_bien_le_tau_attendu():
    assert terme_plus_grand(R, A) == _M_main(A)


def test_hypotheses_exactes_par_frozenset():
    thm = _thm()
    attendu = frozenset({_pge_main(A, a), _antisym_main(A)})
    assert thm.hypotheses == attendu          # LESQUELLES, pas seulement combien
    assert len(thm.hypotheses) == 2
    assert not thm.est_clos


def test_non_vacuous():
    thm = _thm()
    assert thm.conclusion not in thm.hypotheses


def test_les_deux_hypotheses_sont_utiles():
    """Aucune n'est décorative : chacune doit apparaître telle quelle."""
    thm = _thm()
    assert _pge_main(A, a) in thm.hypotheses
    assert _antisym_main(A) in thm.hypotheses


def test_hypotheses_du_module_coincident_avec_la_main():
    """Les constructeurs du module produisent bien les formules reconstruites."""
    assert antisymetrie_sur(R, A) == _antisym_main(A)
    assert E.est_plus_grand_element(R, A, a) == _pge_main(A, a)


# ══════════════════════════════════════════════════════════════════════════════
#  MUTANTS
# ══════════════════════════════════════════════════════════════════════════════
def test_mutant_pollution_est_tue():
    """Hypothèse parasite empilée par gestes PURS du noyau : même conclusion,
    hypothèses différentes → l'assertion par frozenset doit la voir."""
    parasite = appartient(var("zzz"), var("Bidon"))
    mutant = conjonction_elim_gauche(conjonction_intro(_thm(), N.assume(parasite)))
    assert mutant.conclusion == _cible_main()             # conclusion INCHANGÉE
    assert parasite in mutant.hypotheses                  # …mais polluée
    attendu = frozenset({_pge_main(A, a), _antisym_main(A)})
    assert mutant.hypotheses != attendu                   # le test la TUE


def test_mutant_substitution_est_tue():
    """Conclusion remplacée (M = b) : doit différer de la cible."""
    assert _thm().conclusion != egal(_M_main(A), b)


def test_mutant_alpha_variante_est_tue():
    """Liant du τ renommé m → m2 : le noyau n'identifie PAS les α-variants.

    `==` doit REFUSER (c'est l'assertion utilisée par les tests de cible) tandis
    que `alpha_egal` accepterait — d'où l'obligation d'asserter par `==`."""
    alpha = egal(_M_main(A, m="m2"), a)
    assert _thm().conclusion != alpha
    assert alpha_egal(_thm().conclusion, alpha)


def test_mutant_voisin_vrai_autre_ensemble_est_tue():
    """VOISIN VRAI : le MÊME théorème, correct et prouvé, sur un AUTRE ensemble."""
    voisin = terme_plus_grand_vaut(R, var("B"), a)
    assert voisin.conclusion == egal(_M_main(var("B")), a)   # il est VRAI
    assert voisin.conclusion != _cible_main()                # mais ≠ la cible
    assert voisin.hypotheses != _thm().hypotheses


def test_mutant_voisin_vrai_plus_petit_element_est_tue():
    """VOISIN VRAI (dual) : le τ du PLUS PETIT élément n'est pas celui du plus grand."""
    petit = tau("m", et(appartient(var("m"), A),
                        pourtout("x", impl(appartient(var("x"), A),
                                           R(var("m"), var("x"))))))
    assert petit != _M_main(A)
    assert _thm().conclusion != egal(petit, a)


# ══════════════════════════════════════════════════════════════════════════════
#  GARDE-FOU DES LIANTS  (« pour R quelconque » testé sur les noms les plus banals)
# ══════════════════════════════════════════════════════════════════════════════
def test_liants_internes_de_l_ordre_des_cardinaux_sont_mesures():
    """Mesure, pas supposition : `inf_egal_card` lie bel et bien u, v, F…"""
    internes = liants_de(inf_egal_card(var("p"), var("q")))
    assert {"u", "v", "F"} <= internes


def test_garde_refuse_les_liants_u_v_sur_l_ordre_des_cardinaux():
    """Les défauts « u »/« v » entreraient en collision : refus EXPLICITE."""
    import pytest
    with pytest.raises(ValueError, match="liants non frais"):
        terme_plus_grand_vaut(lambda p, q: inf_egal_card(p, q), A, a, u="u", v="v")


def test_garde_refuse_un_A_capturant_les_liants():
    """A contenant m, x, u1 ou v1 LIBRE : capture garantie → refus."""
    import pytest
    for nom in ("m", "x", "u1", "v1"):
        with pytest.raises(ValueError, match="liants non frais"):
            terme_plus_grand_vaut(R, var(nom), a)


def test_garde_accepte_les_noms_banals_non_capturants():
    """Contre-épreuve : sur des noms banals SANS collision, ça passe."""
    for nom in ("i", "f", "u", "v", "G", "E", "n"):
        thm = terme_plus_grand_vaut(R, var(nom), a)
        assert thm.conclusion == egal(_M_main(var(nom)), a)
        assert thm.hypotheses == frozenset({_pge_main(var(nom), a),
                                            _antisym_main(var(nom))})


def test_verifie_liants_frais_ne_leve_pas_a_tort():
    verifie_liants_frais(R, A, a)      # ne doit RIEN lever


# ══════════════════════════════════════════════════════════════════════════════
#  INVARIANT
# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22
