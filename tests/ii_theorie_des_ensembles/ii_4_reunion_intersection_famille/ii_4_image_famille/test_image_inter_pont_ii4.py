# -*- coding: utf-8 -*-
"""Tests du PONT ⋂-de-famille des preuves d'image (§II.4.1 Déf. 2, E II.22).

Miroir de `ensembles_image_inter_pont_ii4`, créé PENDANT la migration du 26 juil.
2026 et resté sans test : un module de fondation non testé est un angle mort —
aucune suite ne verrait sa régression, alors qu'il porte les trois gestes ⋂ de
`ensembles_image_recip_famille_ii4` (Prop. 3/4 + Cor.) et de
`ii_6_4_saturees.ensembles_saturees_famille` (Prop. 10).

CE QUE CES TESTS VERROUILLENT — l'ÉNONCÉ, pas « ça construit » :
  • chaque conclusion est reconstruite À LA MAIN avec les constructeurs de
    `outil_formule` et de `E` (hors du module testé) et comparée à l'identique ;
  • le jeu d'hypothèses est asserté EXACT (`== frozenset({…})`), jamais « ⊂ » ;
  • ANTI-B : aucun des trois gestes n'introduit `(∃i)(i∈I)` ni `¬(I=∅)`.  C'est LA
    propriété qui garde inconditionnelles les inclusions « ⋂ à gauche » (Loi N.1 :
    le témoin d'indice est GRATUIT quand on tient déjà un élément de ⋂) ; un tel
    ajout serait un affaiblissement silencieux de tous les théorèmes d'image ;
  • la route complète x∈⋂ ⊢ … ⊢ y∈⋂ se DÉCHARGE en un théorème CLOS — preuve
    absolue qu'aucune hypothèse d'indice n'a été passée en douce ;
  • le liant d'indice canonique « i » (le noyau n'identifie PAS les α-variants) ;
  • `theorie_ensembles()` vaut 22 axiomes avant ET après.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, egal, impl, appartient, existe, pourtout, tau)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    enonce_inter_par_membres_si_temoin)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille import (
    ensembles_image_inter_pont_ii4 as M)

# Compte relevé À L'IMPORT, avant toute construction de théorème.
_AXIOMES_AVANT = len(E.theorie_ensembles().axiomes)

_X, _I, _x, _y, _a = var("X"), var("I"), var("x"), var("y"), var("a")


# ── Énoncés attendus, reconstruits À LA MAIN (hors du module testé) ───────────
def _corps(z):
    """(∀i)((i∈I) ⇒ (z ∈ X_i))  — le membre droit de la Déf. 2, liant « i »."""
    return pourtout("i", impl(appartient(var("i"), _I),
                              appartient(z, E.valeur_famille(_X, var("i")))))


def _dans_inter(z):
    return appartient(z, E.inter_famille(_X, _I))


# Les deux formes « B » proscrites (et un α-variant de la première : le noyau ne
# les identifie pas, donc on interdit les deux liants usuels).
_B_EXISTE_I = existe("i", appartient(var("i"), _I))
_B_EXISTE_Z = existe("z", appartient(var("z"), _I))
_B_NON_VIDE = non(egal(_I, E.VIDE))


def _aucune_forme_B(thm):
    """Aucune hypothèse d'indice non vide, sous aucune de ses formes."""
    for forme in (_B_EXISTE_I, _B_EXISTE_Z, _B_NON_VIDE):
        assert forme not in thm.hypotheses


# ── 0. Surface exportée ───────────────────────────────────────────────────────
def test_0_surface_exportee_entierement_couverte():
    """`__all__` == les trois gestes testés ici : un ajout non testé casse ce test."""
    assert M.__all__ == ["inter_elim", "temoin_indice_via_inter", "inter_intro"]
    assert len(E.theorie_ensembles().axiomes) == _AXIOMES_AVANT == 22


# ── 1. inter_elim — ÉLIMINATION, inconditionnelle ─────────────────────────────
def test_1_inter_elim_enonce_exact_et_clos():
    """⊢ (x∈⋂_{ι∈I} X_ι) ⇒ (∀i)((i∈I) ⇒ x∈X_i) — CLOS, 0 hypothèse."""
    t = M.inter_elim(_X, _I, _x)
    assert t.conclusion == impl(_dans_inter(_x), _corps(_x))
    assert t.hypotheses == frozenset()
    assert t.est_clos is True


def test_1_inter_elim_liant_d_indice_canonique_i():
    """Le liant est « i » — le noyau n'identifie PAS les α-variants (piège connu)."""
    concl = M.inter_elim(_X, _I, _x).conclusion       # impl == ou(non(A), B)
    quantifie = concl.sous[1].sous[0]                 # pourtout == non(exists(…))
    assert quantifie.tag == "exists" and quantifie.lieur == "i"
    assert concl != impl(_dans_inter(_x), pourtout("j", impl(
        appartient(var("j"), _I), appartient(_x, E.valeur_famille(_X, var("j"))))))


def test_1_inter_elim_accepte_noms_et_termes_composes():
    """Contrat de la docstring : f, I, z sont des noms OU des Termes sans « i » libre."""
    assert M.inter_elim("X", "I", "x").conclusion == M.inter_elim(_X, _I, _x).conclusion
    z = E.valeur_famille(var("g"), var("k"))          # terme composé, « i » non libre
    t = M.inter_elim(_X, _I, z)
    assert t.conclusion == impl(appartient(z, E.inter_famille(_X, _I)),
                                pourtout("i", impl(appartient(var("i"), _I),
                                                   appartient(z, E.valeur_famille(_X, var("i"))))))
    assert t.hypotheses == frozenset() and t.est_clos is True


# ── 2. temoin_indice_via_inter — LE TÉMOIN GRATUIT (Loi N.1) ──────────────────
def test_2_temoin_est_le_tau_canonique_et_conclut_T0_dans_I():
    """De x∈⋂ on tire T₀ := τi(i∈I et x∈X_i) avec ⊢ T₀∈I, sous la SEULE hyp. x∈⋂."""
    h = N.assume(_dans_inter(_x))
    T0, thm = M.temoin_indice_via_inter(_X, _I, _x, h)
    attendu = tau("i", et(appartient(var("i"), _I),
                          appartient(_x, E.valeur_famille(_X, var("i")))))
    assert T0 == attendu
    assert thm.conclusion == appartient(T0, _I)
    assert thm.hypotheses == frozenset({_dans_inter(_x)})   # EXACT : rien d'autre


def test_2_ANTI_B_le_temoin_est_gratuit_et_se_decharge_en_clos():
    """ANTI-B : ⊢ (x∈⋂) ⇒ (T₀∈I) est CLOS — « I≠∅ » n'est PAS une hypothèse.

    C'est la Loi N.1 mise à l'épreuve : ajouter `(∃i)(i∈I)` ou `¬(I=∅)` ici
    affaiblirait gratuitement tous les théorèmes d'image qui en dépendent."""
    h = N.assume(_dans_inter(_x))
    T0, thm = M.temoin_indice_via_inter(_X, _I, _x, h)
    _aucune_forme_B(thm)
    decharge = N.loi_deduction(_dans_inter(_x), thm)
    assert decharge.conclusion == impl(_dans_inter(_x), appartient(T0, _I))
    assert decharge.hypotheses == frozenset()
    assert decharge.est_clos is True


def test_2_le_temoin_propage_les_hypotheses_de_son_antecedent_et_rien_de_plus():
    """Un antécédent portant DEUX hypothèses en transmet exactement deux : 0 ajout.

    Le module ne doit RIEN empiler sur le jeu d'hypothèses qu'on lui donne — sinon
    une hypothèse d'indice pourrait s'y glisser sans que le site d'usage le voie."""
    tierce = appartient(_x, var("A"))                 # x ∈ A
    lien = impl(tierce, _dans_inter(_x))              # (x∈A) ⇒ (x∈⋂)
    antecedent = N.modus_ponens(N.assume(tierce), N.assume(lien))
    assert antecedent.conclusion == _dans_inter(_x)
    assert antecedent.hypotheses == frozenset({tierce, lien})

    _T0, thm = M.temoin_indice_via_inter(_X, _I, _x, antecedent)
    assert thm.hypotheses == frozenset({tierce, lien})   # EXACT : rien de plus
    _aucune_forme_B(thm)


# ── 3. inter_intro — INTRODUCTION sous témoin d'indice ────────────────────────
def test_3_inter_intro_enonce_et_hypotheses_exactes():
    """De a∈I et (∀i)(i∈I ⇒ y∈X_i) conclure y∈⋂ — hypothèses EXACTEMENT ces deux."""
    ha, hc = N.assume(appartient(_a, _I)), N.assume(_corps(_y))
    t = M.inter_intro(_X, _I, _a, ha, hc, _y)
    assert t.conclusion == _dans_inter(_y)
    assert t.hypotheses == frozenset({appartient(_a, _I), _corps(_y)})
    _aucune_forme_B(t)


def test_3_inter_intro_decharge_sur_l_enonce_de_la_fondation():
    """Déchargé, `inter_intro` EST l'introduction de la fondation — ni plus, ni moins."""
    ha, hc = N.assume(appartient(_a, _I)), N.assume(_corps(_y))
    t = M.inter_intro(_X, _I, _a, ha, hc, _y)
    dech = N.loi_deduction(appartient(_a, _I), N.loi_deduction(_corps(_y), t))
    assert dech.conclusion == enonce_inter_par_membres_si_temoin(_X, _I, _a, _y)
    assert dech.hypotheses == frozenset() and dech.est_clos is True


def test_3_le_temoin_est_PORTEUR_pas_decoratif():
    """Sans décharger a∈I, le résultat n'est PAS clos : le témoin fait le travail."""
    ha, hc = N.assume(appartient(_a, _I)), N.assume(_corps(_y))
    t = M.inter_intro(_X, _I, _a, ha, hc, _y)
    partiel = N.loi_deduction(_corps(_y), t)              # corps déchargé seul
    assert partiel.conclusion == impl(_corps(_y), _dans_inter(_y))
    assert partiel.hypotheses == frozenset({appartient(_a, _I)})   # a∈I subsiste
    assert partiel.est_clos is False


# ── 4. La route Loi N.1 de bout en bout ───────────────────────────────────────
def test_4_route_complete_loi_N1_est_CLOSE():
    """⊢ (x∈⋂X_ι) ⇒ ( (∀i)(i∈I ⇒ y∈X_i) ⇒ y∈⋂X_ι ) — CLOS, 0 hypothèse.

    C'est le squelette EXACT des sites d'usage (`image_inter_incluse`,
    `image_recip_inter_incluse`, `saturees` Prop. 10) : le témoin d'indice est
    FABRIQUÉ depuis l'antécédent x∈⋂, jamais supposé.  Une clôture à 0 hypothèse
    est la preuve la plus forte qu'aucune forme « I≠∅ » n'a été introduite."""
    x_in, corps_y = _dans_inter(_x), _corps(_y)
    h = N.assume(x_in)
    T0, t0_dans_I = M.temoin_indice_via_inter(_X, _I, _x, h)
    y_in = M.inter_intro(_X, _I, T0, t0_dans_I, N.assume(corps_y), _y)
    assert y_in.conclusion == _dans_inter(_y)
    assert y_in.hypotheses == frozenset({x_in, corps_y})

    route = N.loi_deduction(x_in, N.loi_deduction(corps_y, y_in))
    assert route.conclusion == impl(x_in, impl(corps_y, _dans_inter(_y)))
    assert route.hypotheses == frozenset()
    assert route.est_clos is True
    _aucune_forme_B(route)


def test_4_elimination_et_introduction_se_recollent_sur_le_meme_element():
    """x∈⋂ ⇒ x∈⋂ par élimination puis réintroduction : la Déf. 2 est bien une ⇔."""
    x_in = _dans_inter(_x)
    h = N.assume(x_in)
    T0, t0_dans_I = M.temoin_indice_via_inter(_X, _I, _x, h)
    corps_x = N.modus_ponens(h, M.inter_elim(_X, _I, _x))
    assert corps_x.conclusion == _corps(_x)
    retour = M.inter_intro(_X, _I, T0, t0_dans_I, corps_x, _x)
    assert retour.conclusion == x_in
    assert retour.hypotheses == frozenset({x_in})
    boucle = N.loi_deduction(x_in, retour)
    assert boucle.conclusion == impl(x_in, x_in) and boucle.est_clos is True


# ── 5. Déterminisme et invariant d'axiomes ────────────────────────────────────
def test_5_determinisme_des_trois_gestes():
    """Deux appels identiques livrent des objets ÉGAUX (conclusions et hypothèses)."""
    a1, a2 = M.inter_elim(_X, _I, _x), M.inter_elim(_X, _I, _x)
    assert a1.conclusion == a2.conclusion and a1.hypotheses == a2.hypotheses

    T1, b1 = M.temoin_indice_via_inter(_X, _I, _x, N.assume(_dans_inter(_x)))
    T2, b2 = M.temoin_indice_via_inter(_X, _I, _x, N.assume(_dans_inter(_x)))
    assert T1 == T2 and b1.conclusion == b2.conclusion and b1.hypotheses == b2.hypotheses

    c1 = M.inter_intro(_X, _I, _a, N.assume(appartient(_a, _I)),
                       N.assume(_corps(_y)), _y)
    c2 = M.inter_intro(_X, _I, _a, N.assume(appartient(_a, _I)),
                       N.assume(_corps(_y)), _y)
    assert c1.conclusion == c2.conclusion and c1.hypotheses == c2.hypotheses


def test_5_theorie_ensembles_reste_a_22_axiomes():
    """INVARIANT DUR : 22 axiomes avant ET après l'usage des trois gestes."""
    assert _AXIOMES_AVANT == 22
    M.inter_elim(_X, _I, _x)
    T0, t0 = M.temoin_indice_via_inter(_X, _I, _x, N.assume(_dans_inter(_x)))
    M.inter_intro(_X, _I, T0, t0, N.assume(_corps(_y)), _y)
    assert len(E.theorie_ensembles().axiomes) == 22
