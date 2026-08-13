"""Tests ISOLÉS du module NEUF
`bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_structures_derivees_props`
(§IV.2 — STRUCTURES DÉRIVÉES : CST10 transitivité initiales, CST11 structure
induite par composition, CST19 transitivité finales, propriétés directes
image réciproque/directe).

Pour chaque théorème on vérifie :
  • la CLÔTURE conditionnelle (hypothèses EXPLICITES = axiomes-schémas (IN)/(FI)/
    (MO_III) instanciés + égalités de composition, jamais des axiomes de la théorie) ;
  • l'ANTI-TAUTOLOGIE (la conclusion n'est PAS l'une des hypothèses) ;
  • l'IDENTITÉ LITTÉRALE de la conclusion à la cible fidèle Bourbaki (plus_fine /
    est_morphisme / égalité de structures / caractérisation d'image réciproque) ;
  • theorie_ensembles() reste à 22 axiomes (aucun axiome créé).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, equiv
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    plus_fine, est_morphisme, _morph_defaut)
import bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_structures_derivees_props as P


def _m():
    return _morph_defaut()


# ════════════════════════════════════════════════════════════════════════════
#  theorie = 22 (invariant intangible)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  1. CST10 — TRANSITIVITÉ DES STRUCTURES INITIALES
# ════════════════════════════════════════════════════════════════════════════
def test_initiale_transitive_un_sens():
    t = P.initiale_transitive_un_sens()
    m = _m()
    # conclusion = plus_fine(E, 𝓘', 𝓘) = « id_E morphisme (E,𝓘')->(E,𝓘) »
    cible = plus_fine(var("E"), var("J"), var("I"), m)
    assert t.conclusion == cible
    # 4 hypothèses : (IN_𝓘), (IN_𝓘'), LIEN, « id morph (E,𝓘') »
    assert len(t.hypotheses) == 4
    # ANTI-TAUTOLOGIE
    assert cible not in t.hypotheses


def test_cst10_initiales_egales():
    t = P.cst10_initiales_egales()
    # conclusion = 𝓘 = 𝓘'
    cible = egal(var("I"), var("J"))
    assert t.conclusion == cible
    # 9 hypothèses (2 sens × {(IN),(IN),LIEN,id} = 8 distinctes + ANTISYM)
    assert len(t.hypotheses) == 9
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  2. CST11 — STRUCTURE INDUITE PAR COMPOSITION (transitivité des induites)
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_par_composition():
    t = P.image_reciproque_par_composition()
    m = _m()
    va, vs, vc = var("A"), var("S"), var("C")
    vg, vh, vk = var("g"), var("h"), var("k")
    vep, vsp, sJ = var("Ep"), var("Sp"), var("SJ")
    gh = E.composee(vg, vh)
    # cible = caractérisation (IN à un indice) de imrec_{g∘h}(𝒮) sur C, à (E',𝒮',k)
    lhs = est_morphisme(vep, vsp, vc, sJ, vk, m)
    rhs = est_morphisme(vep, vsp, va, vs, E.composee(gh, vk), m)
    cible = equiv(lhs, rhs)
    assert t.conclusion == cible
    # 3 hypothèses EXPLICITES : CAR_𝓘, CAR_𝓙, ASSOC (associativité)
    assert len(t.hypotheses) == 3
    # ASSOC (g∘(h∘k) = (g∘h)∘k) est bien une prémisse, pas postulée vraie
    assoc = egal(E.composee(vg, E.composee(vh, vk)), E.composee(gh, vk))
    assert assoc in t.hypotheses
    # ANTI-TAUTOLOGIE : la conclusion (équivalence) n'est aucune des prémisses
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  3. CST19 — TRANSITIVITÉ DES STRUCTURES FINALES (DUAL de CST10)
# ════════════════════════════════════════════════════════════════════════════
def test_finale_transitive_un_sens():
    t = P.finale_transitive_un_sens()
    m = _m()
    # conclusion = plus_fine(E, 𝓕, 𝓕')
    cible = plus_fine(var("E"), var("F"), var("G"), m)
    assert t.conclusion == cible
    assert len(t.hypotheses) == 4
    assert cible not in t.hypotheses


def test_cst19_finales_egales():
    t = P.cst19_finales_egales()
    cible = egal(var("F"), var("G"))
    assert t.conclusion == cible
    assert len(t.hypotheses) == 9
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  4. PROPRIÉTÉS DIRECTES de l'IMAGE RÉCIPROQUE / DIRECTE
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_unicite():
    t = P.image_reciproque_unicite()
    cible = egal(var("I"), var("J"))
    assert t.conclusion == cible
    # 7 hyps : 2 sens × {CAR_sA, CAR_sB, id morph} (CAR partagés) + ANTISYM
    assert len(t.hypotheses) == 7
    assert cible not in t.hypotheses


def test_image_directe_unicite():
    t = P.image_directe_unicite()
    cible = egal(var("F"), var("G"))
    assert t.conclusion == cible
    assert len(t.hypotheses) == 7
    assert cible not in t.hypotheses


def test_image_reciproque_rend_f_morphisme():
    t = P.image_reciproque_rend_f_morphisme()
    m = _m()
    ve, va, vs, vf = var("E"), var("A"), var("S"), var("f")
    # conclusion = morph(E,𝓘,A,𝒮, f∘id_E)
    cible = est_morphisme(ve, var("I"), va, vs,
                          E.composee(vf, E.diagonale(ve)), m)
    assert t.conclusion == cible
    # 2 hypothèses : CAR_𝓘 (caractérisation imrec) + « id morph (E,𝓘) » (MO_III)
    assert len(t.hypotheses) == 2
    assert cible not in t.hypotheses


def test_image_directe_rend_f_morphisme():
    t = P.image_directe_rend_f_morphisme()
    m = _m()
    ve, va, vs, vf = var("E"), var("A"), var("S"), var("f")
    # conclusion = morph(A,𝒮,E,𝓕, id_E∘f)
    cible = est_morphisme(va, vs, ve, var("F"),
                          E.composee(E.diagonale(ve), vf), m)
    assert t.conclusion == cible
    assert len(t.hypotheses) == 2
    assert cible not in t.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  invariant transverse : tous les théorèmes sont des Theoreme (conditionnels)
# ════════════════════════════════════════════════════════════════════════════
def test_tous_conditionnels_non_vides():
    for name in P.__all__:
        if name == "id_est_morphisme":
            continue
        t = getattr(P, name)()
        assert hasattr(t, "conclusion")
        # chacun est CONDITIONNEL (≥1 hyp explicite) — pas de tautologie close vide
        assert len(t.hypotheses) >= 1
