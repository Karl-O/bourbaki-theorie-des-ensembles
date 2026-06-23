"""Tests — §III.4.2 ENSEMBLES FINIS, propositions SUPPLÉMENTAIRES (module NEUF).

Module testé : bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props2.

On vérifie pour chaque théorème INCONDITIONNEL qu'il est CLOS (aucune hypothèse
résiduelle) et que sa CONCLUSION est EXACTEMENT l'énoncé attendu (anti-affaibli /
anti-tautologie).  Pour les formes CONDITIONNELLES, on contrôle l'implication
report ⇒ conclusion ET que l'antécédent (report) DIFFÈRE du conséquent (garde-fou
anti-tautologie).  Pour les énoncés REPORTÉS, on contrôle la formule-cible.
"""
from bourbaki.logique.formule import var, egal, et, ou, non, impl, equiv, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, equipotent, inf_egal_card, inf_strict_card, est_bijection_de,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, est_fini_ensemble
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.ensembles.familles.ensembles_recollement_props import (
    bijection_canonique_reunion_somme,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props2 import (
    equipotent_implique_fini_cardinal,
    equipotent_implique_fini_ensemble,
    equipotent_ssi_fini_ensemble,
    sous_ensemble_card_inf_egal,
    image_card_inf_egal_but,
    cor2_partie_stricte_card_strict_cond,
    reunion_disjointe_finie_cond,
    cor3_image_finie_cond,
    cor3_image_finie_cible,
)

_U, _V = var("U"), var("V")
_X, _E, _F, _A, _B = var("X"), var("E"), var("F"), var("A"), var("B")
_f = var("f")


def _clos(thm):
    """Le théorème ne porte aucune hypothèse résiduelle."""
    return not thm.hypotheses


def _ante(thm):
    """Antécédent d'une implication (encodée ou(non A, B))."""
    return thm.conclusion.sous[0].sous[0]


def _conseq(thm):
    """Conséquent d'une implication."""
    return thm.conclusion.sous[1]


# ══════════════════════════════════════════════════════════════════════════════
#  INCONDITIONNELS — transport de la finitude par équipotence
# ══════════════════════════════════════════════════════════════════════════════
def test_equipotent_implique_fini_cardinal_clos():
    thm = equipotent_implique_fini_cardinal("a", "b")
    assert _clos(thm)
    a, b = var("a"), var("b")
    # Eq(a,b) ⇒ (Fini(Card a) ⇒ Fini(Card b))
    assert thm.conclusion == impl(
        equipotent(a, b),
        impl(est_fini(cardinal(a)), est_fini(cardinal(b))))


def test_equipotent_implique_fini_ensemble_clos():
    thm = equipotent_implique_fini_ensemble("U", "V")
    assert _clos(thm)
    # Eq(U,V) ⇒ (U fini ⇒ V fini)
    assert thm.conclusion == impl(
        equipotent(_U, _V),
        impl(est_fini_ensemble(_U), est_fini_ensemble(_V)))


def test_equipotent_implique_fini_ensemble_pas_tautologie():
    """L'implication interne n'est PAS (U fini ⇒ U fini) : le conséquent porte sur V,
    distinct de U — transport réel via Card U = Card V.  Garde-fou anti-tautologie."""
    thm = equipotent_implique_fini_ensemble("U", "V")
    interne = _conseq(thm)                      # U fini ⇒ V fini
    assert interne.sous[0].sous[0] != interne.sous[1], "effondrement en U fini ⇒ U fini"


def test_equipotent_ssi_fini_ensemble_clos():
    thm = equipotent_ssi_fini_ensemble("U", "V")
    assert _clos(thm)
    # Eq(U,V) ⇒ (U fini ⇔ V fini)
    assert thm.conclusion == impl(
        equipotent(_U, _V),
        equiv(est_fini_ensemble(_U), est_fini_ensemble(_V)))


# ══════════════════════════════════════════════════════════════════════════════
#  INCONDITIONNELS — bornes cardinales (sous-ensemble / image)
# ══════════════════════════════════════════════════════════════════════════════
def test_sous_ensemble_card_inf_egal_clos():
    thm = sous_ensemble_card_inf_egal("X", "E")
    assert _clos(thm)
    # (X ⊂ E) ⇒ Card X ≤ Card E
    assert thm.conclusion == impl(inclus(_X, _E),
                                  inf_egal_card(cardinal(_X), cardinal(_E)))


def test_image_card_inf_egal_but_clos():
    thm = image_card_inf_egal_but("f", "E", "Co")
    assert _clos(thm)
    img = E.image(_f, _E)
    _Co = var("Co")
    # (image(f,E) ⊂ Co) ⇒ Card(image(f,E)) ≤ Card Co   (codomaine Co = le « F » de Bourbaki)
    assert thm.conclusion == impl(inclus(img, _Co),
                                  inf_egal_card(cardinal(img), cardinal(_Co)))


# ══════════════════════════════════════════════════════════════════════════════
#  CONDITIONNELS au contenu non trivial (reports déchargés en antécédent)
# ══════════════════════════════════════════════════════════════════════════════
def test_cor2_partie_stricte_card_strict_cond_clos():
    thm = cor2_partie_stricte_card_strict_cond("X", "E")
    assert _clos(thm)
    cX, cE = cardinal(_X), cardinal(_E)
    ante = et(et(inclus(_X, _E), non(egal(_X, _E))), est_fini(cE))
    H = impl(ante, non(egal(cX, cE)))                    # report : Card X ≠ Card E
    consequent = impl(ante, inf_strict_card(cX, cE))      # Cor. 2 : Card X < Card E
    assert thm.conclusion == impl(H, consequent)


def test_cor2_cond_pas_tautologie():
    """H (report Card X ≠ Card E) DIFFÈRE du conséquent (Card X < Card E) :
    le contenu réel est la conjonction avec le « ≤ » inconditionnel.  Anti-tautologie."""
    thm = cor2_partie_stricte_card_strict_cond("X", "E")
    assert _ante(thm) != _conseq(thm), "le conditionnel s'est effondré en H ⇒ H"


def test_reunion_disjointe_finie_cond_clos():
    thm = reunion_disjointe_finie_cond("A", "B")
    assert _clos(thm)
    union = E.reunion(_A, _B)
    somme = somme_disjointe(_A, _B)
    W = bijection_canonique_reunion_somme(_A, _B)
    bij = est_bijection_de(W, union, somme)
    fini_AB = et(est_fini_ensemble(_A), est_fini_ensemble(_B))
    H_sum = impl(fini_AB, est_fini_ensemble(somme))
    ante = et(bij, H_sum)
    consequent = impl(fini_AB, est_fini_ensemble(union))
    assert thm.conclusion == impl(ante, consequent)


def test_reunion_disjointe_finie_cond_pas_tautologie():
    """L'antécédent (bijection + somme finie) DIFFÈRE du conséquent (réunion finie)."""
    thm = reunion_disjointe_finie_cond("A", "B")
    assert _ante(thm) != _conseq(thm), "effondrement en tautologie"


def test_cor3_image_finie_cond_clos():
    thm = cor3_image_finie_cond("f", "E", "F")
    assert _clos(thm)
    img = E.image(_f, _E)
    fini_E = est_fini_ensemble(_E)
    le_img_E = inf_egal_card(img, _E)
    fini_img = est_fini_ensemble(img)
    H_surj = impl(fini_E, le_img_E)
    H_cor1 = impl(et(le_img_E, fini_E), fini_img)
    ante = et(H_surj, H_cor1)
    consequent = impl(fini_E, fini_img)
    assert thm.conclusion == impl(ante, consequent)


def test_cor3_image_finie_cond_pas_tautologie():
    thm = cor3_image_finie_cond("f", "E", "F")
    assert _ante(thm) != _conseq(thm), "effondrement en tautologie"


# ══════════════════════════════════════════════════════════════════════════════
#  ÉNONCÉ REPORTÉ (formule-cible — PAS un théorème ; on vérifie la forme)
# ══════════════════════════════════════════════════════════════════════════════
def test_cor3_image_finie_cible_enonce():
    f = cor3_image_finie_cible("f", "E", "F")
    img = E.image(_f, _E)
    # (E fini) ⇒ (image(f,E) ⊂ F et image(f,E) fini)   (Cor. 3, reporté)
    assert f == impl(est_fini_ensemble(_E),
                     et(inclus(img, _F), est_fini_ensemble(img)))


# ══════════════════════════════════════════════════════════════════════════════
#  GARDE-FOU GLOBAL — theorie_ensembles() reste à 22 axiomes (intangible)
# ══════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22
