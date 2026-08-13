# -*- coding: utf-8 -*-
"""Tests — (R-pivot)/(O1) MORTS, et LA JOINTURE du §III.5.8 (E III.41 L.30-32).

Deux blocs :

(1) DÉVERROUILLAGE (ensembles_factorielle_existence_vrai) : aucun théorème factorielle
    n'est asserté ; on vérifie que le pivot construit sur le graphe τ-lourd factoriel
    avec témoins FRAIS **et** PAR DÉFAUT, que la theorie reste 22, et que le chemin LIVE
    C62 factoriel passe de bout en bout (« BUILD OK », plus de site résiduel).

(2) MIROIR de `factorielle_caracterisation` — le test RECONSTRUIT À LA MAIN, ici et
    hors du module, la conclusion attendue ET les DIX hypothèses, puis compare par
    ÉGALITÉ EXACTE (`==` de formule, `==` de frozenset).  Un `len(hyps)==10` ne dirait
    pas LESQUELLES et laisserait passer un résidu de complaisance.
    Le miroir est ensuite MUTÉ pour prouver qu'il n'est pas décoratif : les mutants
    sont fabriqués EN MÉMOIRE par gestes noyau purs à partir du théorème réel (aucune
    écriture dans le dépôt), en trois familles —
      • POLLUTION     : même conclusion, hypothèse parasite empilée (assume + loi_deduction) ;
      • SUBSTITUTION  : conclusion remplacée, hypothèses INCHANGÉES (conjoints permutés,
                        conjoint dupliqué) — invisible à tout test qui ne compte que
                        les hypothèses ;
      • ALPHA-VARIANT : même conclusion, même NOMBRE d'hypothèses, une hypothèse
                        remplacée par une α-variante (liants qrs/wrs renommés) —
                        invisible à tout test qui ne compte que les hypothèses.
    Chaque mutant est d'abord contrôlé BIEN FORMÉ (c'est un théorème du noyau, de
    conclusion non nulle) : un mutant qui mourrait sur TypeError ne prouverait rien.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, appartient, alpha_egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, UN, successeur, est_entier,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_equation_restriction import essais_restriction
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence_vrai import (
    pivot_factorielle_frais_ok, site_residuel_exact, factorielle_caracterisation,
)


# ════════════════════════════════════════════════════════════════════════════
#  (1) Déverrouillage du pivot — (R-pivot) est MORT.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pivot_deverrouille_frais_et_defaut():
    r = pivot_factorielle_frais_ok()
    # F bake bien les binders cardinaux jadis interdits du gluing
    assert {"u", "up", "v", "y", "z"} <= set(r["binders_F"])
    # depuis le fix subst : build par défaut OK **et** build frais OK, non vacuous
    assert r["defaut"] == "BUILD OK"
    assert r["frais_ok"] is True
    assert r["frais_concl_tag"] == "non"      # est_fonctionnel = ¬(...)-formé en tête
    assert r["frais_nb_hyps"] == 3
    assert r["non_vacuous"] is True


def test_chemin_c62_factoriel_passe():
    """Plus de site résiduel : le chemin LIVE C62 factoriel construit de bout en bout."""
    r = site_residuel_exact()
    assert r["statut"] == "BUILD OK"
    assert "site_pivot_defaut" not in r


def test_theorie_toujours_22_apres():
    pivot_factorielle_frais_ok()
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  (2) MIROIR de la jointure — conclusion ET hypothèses reconstruites À LA MAIN.
# ════════════════════════════════════════════════════════════════════════════
_E, _G, _V, _NB = "Enat", "Gle", "Vfac62", "nfsc"
_CACHE = {}


def _capstone():
    """Le théorème réel, construit UNE fois (≈ 6,5 min : le cas succ traverse C61)."""
    if "th" not in _CACHE:
        _CACHE["th"] = factorielle_caracterisation(_E, _G, _V, _NB)
    return _CACHE["th"]


def _cible_a_la_main():
    """La conclusion attendue, RE-ÉCRITE ICI depuis l'énoncé du livre (E III.41 L.30-32).

    « On a 0! = 1 … (n+1)! = n!(n+1) » ⇝  f(0)=1  ∧  f(n+1) = (n+1)·u(n),
    u = f|seg(n+1), f = ⋃𝔇_tot (recâblage du 2 août : facteur Déf.2 + M(D u) réel).
    On n'appelle PAS `factorielle_caracterisation_cible` :
    comparer le module à son propre énoncé ne prouverait rien."""
    ve, vn = var(_E), var(_NB)
    m = successeur(vn)
    f = fonction_globale(_E, _V)
    u = E.restriction(f, E.segment_extremite(var(_G), ve, m))
    return et(
        egal(E.valeur(f, ZERO), UN),
        egal(E.valeur(f, m),
             produit_cardinal_binaire(successeur(vn), E.valeur(u, vn))))


def _hypotheses_a_la_main():
    """Les DIX hypothèses attendues, épelées une par une (frozenset).

    5 partagées par les deux moitiés  : bo, essais_bien_formes, rule_codomain,
                                       essais_restriction, ZERO∈E ;
    1 propre au cas 0                 : seg(0)=∅ ;
    4 propres au cas successeur       : succ n∈E, seg(succ n)=[0,n],
                                       ZERO∈seg(succ n), est_entier(n).
    Les trois hypothèses règle-dépendantes sont bâties sur T_Z = regle_factorielle(
    zcard="Z") : c'est l'UNIQUE lecture de la règle admise par la jointure."""
    T = regle_factorielle(zcard="Z")
    R = _graphe_R(_G)
    ve, vn = var(_E), var(_NB)
    m = successeur(vn)
    return frozenset({
        E.est_bien_ordonne(R, ve),
        essais_bien_formes(T, _E, _G, _V, "qwf", "wwf", "zess"),
        rule_codomain(T, _V, "zess"),
        essais_restriction(T, T, _E, _G),
        appartient(ZERO, ve),
        egal(E.segment_extremite(var(_G), ve, ZERO), E.VIDE),
        appartient(m, ve),
        egal(E.segment_extremite(var(_G), ve, m), E.intervalle_entiers(ZERO, vn)),
        appartient(ZERO, E.segment_extremite(var(_G), ve, m)),
        est_entier(vn),
    })


def _miroir(th):
    """LE MIROIR.  Lève AssertionError avec un tag identifiant le contrôle qui casse."""
    assert th.conclusion == _cible_a_la_main(), "MIROIR-CONCLUSION"
    assert frozenset(th.hypotheses) == _hypotheses_a_la_main(), "MIROIR-HYPOTHESES"
    assert th.conclusion not in th.hypotheses, "MIROIR-VACUOUS"


def _bien_forme(th, nom):
    """Un mutant doit être un THÉORÈME du noyau : sinon son « kill » ne prouve rien."""
    assert hasattr(th, "conclusion") and hasattr(th, "hypotheses"), \
        "%s : mutant CASSÉ (pas un Theoreme)" % nom
    assert th.conclusion is not None, "%s : mutant CASSÉ (conclusion nulle)" % nom
    return th


@pytest.mark.slow
def test_miroir_factorielle_caracterisation():
    """🎯🎯🎯 { 10 hyps épelées } ⊢ (f(0)=1) ∧ (f(n+1)=(n+2)·u([0,n])) — E III.41 L.30-32."""
    th = _capstone()
    _miroir(th)
    assert len(th.hypotheses) == 10
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_mutant_pollution_est_tue():
    """POLLUTION : même conclusion + une hypothèse parasite ⇒ le miroir DOIT refuser."""
    th = _capstone()
    parasite = appartient(var("pollutionMiroir"), var(_E))
    mut = _bien_forme(
        N.modus_ponens(N.assume(parasite), N.loi_deduction(parasite, th)),
        "pollution")
    assert mut.conclusion == th.conclusion          # la conclusion, elle, est intacte
    assert len(mut.hypotheses) == 11
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-HYPOTHESES" in str(exc.value)


@pytest.mark.slow
def test_mutant_substitution_conjoints_permutes_est_tue():
    """SUBSTITUTION : conjoints permutés — MÊMES hypothèses, MÊME compte.

    C'est le mutant qui tue les tests décoratifs : `len(hypotheses)==10` le laisse
    passer, et il n'énonce PAS la phrase du livre (l'ordre « 0!=1 ∧ (n+1)!=… » est la
    forme comparée)."""
    th = _capstone()
    mut = _bien_forme(conjonction_intro(conjonction_elim_droite(th),
                                        conjonction_elim_gauche(th)), "permutation")
    assert frozenset(mut.hypotheses) == frozenset(th.hypotheses)   # indiscernable côté hyps
    assert len(mut.hypotheses) == 10
    assert mut.conclusion != th.conclusion
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-CONCLUSION" in str(exc.value)


@pytest.mark.slow
def test_mutant_substitution_conjoint_duplique_est_tue():
    """SUBSTITUTION : (0!=1) ∧ (0!=1) — la moitié successeur a DISPARU du dit."""
    th = _capstone()
    g = conjonction_elim_gauche(th)
    mut = _bien_forme(conjonction_intro(g, g), "duplication")
    assert len(mut.hypotheses) == 10
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-CONCLUSION" in str(exc.value)


@pytest.mark.slow
def test_mutant_alpha_variant_est_tue():
    """ALPHA-VARIANT : `essais_restriction` remplacée par sa α-variante (liants renommés).

    Même conclusion, même NOMBRE d'hypothèses, même FORCE logique — seul le nom d'un
    liant change.  Le noyau n'identifie pas les α-variants : le miroir doit le voir."""
    th = _capstone()
    T = regle_factorielle(zcard="Z")
    hyp = essais_restriction(T, T, _E, _G)                       # liants qrs/wrs
    hyp_a = essais_restriction(T, T, _E, _G, "qrsALPHA", "wrsALPHA")
    assert hyp != hyp_a and alpha_egal(hyp, hyp_a), "α-variante mal construite"

    pont = alpha_bridge(N.assume(hyp_a), hyp)                    # {hyp_a} ⊢ hyp
    mut = _bien_forme(N.modus_ponens(pont, N.loi_deduction(hyp, th)), "alpha")
    assert mut.conclusion == th.conclusion
    assert len(mut.hypotheses) == 10                             # MÊME compte
    assert hyp_a in mut.hypotheses and hyp not in mut.hypotheses
    with pytest.raises(AssertionError) as exc:
        _miroir(mut)
    assert "MIROIR-HYPOTHESES" in str(exc.value)


@pytest.mark.slow
def test_defaut_historique_inchange_et_desalignement_reel():
    """NON-BREAKING + la NATURE EXACTE du désalignement que la jointure a révélé.

    MESURÉ : `essais_restriction(T_Zfac62)` et `essais_restriction(T_Z)` sont
    α-ÉQUIVALENTES (`alpha_egal` True) mais PAS `==`.  Les deux moitiés du §III.5.8
    parlaient donc bien de la MÊME règle — à un NOM DE τ-LIANT près — et c'est le
    noyau, qui n'identifie pas les α-variants, qui rendait la conjonction informulable.
    Le prix était réel malgré tout : 13 hypothèses au lieu de 10, dont trois comptées
    DEUX FOIS sous deux noms de liant.  (Réparation alternative possible : trois
    `alpha_bridge` ; unifier `zcard` est plus simple et plus lisible.)

    `factorielle_zero()` sans kwarg reste bâtie sur zcard="Zfac62", byte-identique à
    l'historique — la paramétrisation n'a rien cassé en aval."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_zero import factorielle_zero
    T0, TZ = regle_factorielle(), regle_factorielle(zcard="Z")
    er0 = essais_restriction(T0, T0, _E, _G)
    erZ = essais_restriction(TZ, TZ, _E, _G)
    assert er0 != erZ, "les deux règles seraient déjà identiques : plus rien à révéler"
    assert alpha_egal(er0, erZ), "elles ne seraient pas la MÊME règle à α près"
    z_def = factorielle_zero()                          # défaut historique
    assert len(z_def.hypotheses) == 6 and er0 in z_def.hypotheses
    z_can = factorielle_zero(_E, _G, _V, zcard="Z")     # règle canonique
    assert len(z_can.hypotheses) == 6 and erZ in z_can.hypotheses
    # Les DEUX lectures de f(0)=1 ne partagent que les 3 hypothèses SANS règle
    # (bo, ZERO∈E, seg(0)=∅) : les 3 règle-dépendantes divergent par le nom du liant.
    # (Côté zero-vs-succ le partage tombe à 2 — seules bo et ZERO∈E — parce que succ
    #  n'a pas seg(0)=∅ ; d'où l'union 13 au lieu de 10 avant réparation.)
    assert len(frozenset(z_def.hypotheses) & frozenset(z_can.hypotheses)) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
