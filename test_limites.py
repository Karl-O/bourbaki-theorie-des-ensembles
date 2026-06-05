"""Tests §III.7 — Limites projectives et inductives (théorèmes DIRECTS).

Chaque test vérifie que la conclusion certifiée par le noyau est EXACTEMENT la
cible attendue (et le statut des hypothèses résiduelles), et non une devinette.
"""
from formule import var, egal, appartient, et, impl, pourtout, equiv
import noyau_abrege as N
import ensembles_abrege as E
import ensembles_limites as L


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


def _fab(a, b):  # f_{ab} projectif
    return L.appl_proj(var("f"), var(a), var(b))


def _val(t, x="x"):
    return E.valeur(t, var(x))


# ── (LP_I) cocycle au niveau des valeurs : f_{αγ}(x)=f_{αβ}(f_{βγ}(x)) ────────
def test_cocycle_valeur_projectif():
    th = L.cocycle_valeur_projectif("f", _leq(), "I")
    fag, fab, fbg = _fab("a", "g"), _fab("a", "b"), _fab("b", "g")
    attendu = egal(_val(fag), E.valeur(fab, _val(fbg)))
    assert th.conclusion == attendu
    # LP_I figure bien parmi les hypothèses résiduelles
    assert L.cocycle_projectif(var("f"), _leq(), var("I")) in th.hypotheses


def test_identite_valeur_projectif():
    th = L.identite_valeur_projectif("f", _leq(), "I")
    attendu = egal(_val(_fab("a", "a")), var("x"))
    assert th.conclusion == attendu
    assert L.identite_projectif(var("f"), _leq(), var("I")) in th.hypotheses
    assert appartient(var("a"), var("I")) in th.hypotheses


# ── duals inductifs (LI_I, LI_II) ────────────────────────────────────────────
def test_cocycle_valeur_inductif():
    th = L.cocycle_valeur_inductif("f", _leq(), "I")
    fga = L.appl_ind(var("f"), var("g"), var("a"))
    fgb = L.appl_ind(var("f"), var("g"), var("b"))
    fba = L.appl_ind(var("f"), var("b"), var("a"))
    attendu = egal(E.valeur(fga, var("x")), E.valeur(fgb, E.valeur(fba, var("x"))))
    assert th.conclusion == attendu


def test_identite_valeur_inductif():
    th = L.identite_valeur_inductif("f", _leq(), "I")
    faa = L.appl_ind(var("f"), var("a"), var("a"))
    assert th.conclusion == egal(E.valeur(faa, var("x")), var("x"))


# ── appartenance à la limite projective (instance de l'axiome, théorème clos) ─
def test_appartient_limite_projective_close():
    th = L.appartient_limite_projective("E", "f", _leq(), "I", "z")
    # théorème CLOS (aucune hypothèse) = équivalence caractérisante
    assert th.hypotheses == frozenset() or len(th.hypotheses) == 0
    vz = var("z")
    gauche = appartient(vz, L.lim_proj(var("E"), var("f")))
    # la conclusion est l'équivalence (z∈lim ⇔ (z∈∏ et condition(1)))
    droite = et(appartient(vz, E.produit_famille(var("E"), var("I"))),
                L._condition_1(var("f"), _leq(), var("I"), vz))
    assert th.conclusion == equiv(gauche, droite)


def test_limite_projective_relation_1():
    th = L.limite_projective_relation_1("E", "f", _leq(), "I", "z", "a", "b")
    va, vb, vz = var("a"), var("b"), var("z")
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))),
              _leq()(va, vb))
    pra = E.projection_indice(vz, va)
    prb = E.projection_indice(vz, vb)
    concl = egal(pra, L.transition_valeur(L.appl_proj(var("f"), va, vb), prb))
    assert th.conclusion == impl(prem, concl)
    assert appartient(vz, L.lim_proj(var("E"), var("f"))) in th.hypotheses


def test_limite_projective_dans_produit():
    th = L.limite_projective_dans_produit("E", "f", _leq(), "I", "z")
    vz = var("z")
    assert th.conclusion == appartient(vz, E.produit_famille(var("E"), var("I")))
    assert appartient(vz, L.lim_proj(var("E"), var("f"))) in th.hypotheses


# ── les définitions se construisent (prédicats clos bien formés) ──────────────
def test_definitions_se_construisent():
    sp = L.est_systeme_projectif(var("f"), _leq(), var("I"))
    si = L.est_systeme_inductif(var("f"), _leq(), var("I"))
    # ce sont des conjonctions (LP_I et LP_II) / (filtrant et LI_I et LI_II)
    assert sp is not None and si is not None
    # axiome de la limite : (∀z)(...) bien formé
    ax = L.axiome_lim_proj(var("E"), var("f"), _leq(), var("I"))
    assert ax is not None
