"""Tests §III.7 — SALVAGE des Propositions des limites projectives/inductives.

Vérifie : (a) que chaque NOTION (commutation pointwise, w_α, séparation) s'introduit
en formule/terme close bien formée ; (b) que les THÉORÈMES certifient EXACTEMENT la
conclusion visée AVEC les hypothèses attendues (non-vacuité : la conclusion n'est ni
une hypothèse, ni une tautologie P⇒P) ; (c) que rien n'est postulé (theorie=22).
"""
from bourbaki.logique.formule import (
    var, app, egal, appartient, et, impl, non, pourtout, existe, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.iii_7_limites import ensembles_limites as L
from bourbaki.ordre.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.ordre.iii_7_limites import ensembles_limites_props as P


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  NOTIONS — commutation pointwise, w_α, séparation : bien formées et closes
# ════════════════════════════════════════════════════════════════════════════
def test_diagramme_valeur_proj_forme():
    """DIAG_proj(α,β,x) = u_α(f_{αβ}(x)) = g_{αβ}(u_β(x)) — égalité bien formée."""
    d = P.diagramme_valeur_proj("u", "f", "g", "a", "b", "x")
    va, vb, vx = var("a"), var("b"), var("x")
    ua = C.u_indice(var("u"), va)
    ub = C.u_indice(var("u"), vb)
    fab = L.appl_proj(var("f"), va, vb)
    gab = L.appl_proj(var("g"), va, vb)
    assert d == egal(E.valeur(ua, E.valeur(fab, vx)), E.valeur(gab, E.valeur(ub, vx)))


def test_commute_valeur_proj_close():
    """commute_valeur_proj est une formule (∀∀∀ ⇒ DIAG) — bien formée."""
    from bourbaki.logique.formule import Formule
    f = P.commute_valeur_proj("u", "f", "g", _leq(), "I")
    assert isinstance(f, Formule)


def test_commute_valeur_ind_close():
    from bourbaki.logique.formule import Formule
    f = P.commute_valeur_ind("u", "f", "g", _leq(), "I")
    assert isinstance(f, Formule)


def test_w_indice_proj_valeur():
    """w_α(x) = v_α(u_α(x)) (composition pointwise)."""
    w = P.w_indice_proj("u", "v", "a")
    vx = var("x")
    ua = C.u_indice(var("u"), var("a"))
    va_ = C.u_indice(var("v"), var("a"))
    assert w(vx) == E.valeur(va_, E.valeur(ua, vx))


def test_critere_separation_proj_forme():
    from bourbaki.logique.formule import Formule
    s = P.critere_separation_proj("u", "F", "I")
    assert isinstance(s, Formule)


# ════════════════════════════════════════════════════════════════════════════
#  Cor. 2 PROP. 1 / PROP. 6 — FONCTORIALITÉ au niveau des valeurs (THÉORÈMES)
# ════════════════════════════════════════════════════════════════════════════
def test_composition_projective_valeur():
    """w_α(f_{αβ}(x)) = h_{αβ}(w_β(x)) — cœur du Cor.2 Prop.1, non vide.

    Conclusion EXACTE attendue : v_α(u_α(f_{αβ}(x))) = h_{αβ}(v_β(u_β(x)))
    avec les DEUX hypothèses DIAG^u et DIAG^v dans le séquent (non postulées)."""
    th = P.composition_projective_valeur("u", "v", "f", "g", "h", "a", "b", "x")
    va, vb, vx = var("a"), var("b"), var("x")
    ua = C.u_indice(var("u"), va); ub = C.u_indice(var("u"), vb)
    va_ = C.u_indice(var("v"), va); vb_ = C.u_indice(var("v"), vb)
    fab = L.appl_proj(var("f"), va, vb)
    gab = L.appl_proj(var("g"), va, vb)
    hab = L.appl_proj(var("h"), va, vb)
    ubx = E.valeur(ub, vx)
    lhs = E.valeur(va_, E.valeur(ua, E.valeur(fab, vx)))      # v_α(u_α(f_{αβ}(x)))
    rhs = E.valeur(hab, E.valeur(vb_, ubx))                   # h_{αβ}(v_β(u_β(x)))
    assert th.conclusion == egal(lhs, rhs)
    # NON-VACUITÉ : conclusion ≠ chacune des hypothèses ; deux hyps distinctes
    H1 = egal(E.valeur(ua, E.valeur(fab, vx)), E.valeur(gab, ubx))
    H2 = egal(E.valeur(va_, E.valeur(gab, ubx)), rhs)
    assert H1 in th.hypotheses
    assert H2 in th.hypotheses
    assert th.conclusion not in th.hypotheses
    assert len(th.hypotheses) == 2


def test_composition_inductive_valeur():
    """w_β(f_{βα}(x)) = h_{βα}(w_α(x)) — cœur du Cor.2 Prop.6, non vide."""
    th = P.composition_inductive_valeur("u", "v", "f", "g", "h", "a", "b", "x")
    va, vb, vx = var("a"), var("b"), var("x")
    ua = C.u_indice(var("u"), va); ub = C.u_indice(var("u"), vb)
    va_ = C.u_indice(var("v"), va); vb_ = C.u_indice(var("v"), vb)
    fba = L.appl_ind(var("f"), vb, va)
    gba = L.appl_ind(var("g"), vb, va)
    hba = L.appl_ind(var("h"), vb, va)
    uax = E.valeur(ua, vx)
    lhs = E.valeur(vb_, E.valeur(ub, E.valeur(fba, vx)))
    rhs = E.valeur(hba, E.valeur(va_, uax))
    assert th.conclusion == egal(lhs, rhs)
    assert th.conclusion not in th.hypotheses
    assert len(th.hypotheses) == 2


def test_composition_projective_sous_commute():
    """Cor.2 Prop.1 assemblé sous les PRÉDICATS commute_valeur_proj.

    Conclusion : (α,β∈I et α≤β) ⇒ DIAG^w(α,β,x) ; hypothèses = les deux
    commutations pointwise (u) et (v)."""
    leq = _leq()
    th = P.composition_projective_sous_commute("u", "v", "f", "g", "h", leq,
                                               "I", "a", "b", "x")
    va, vb, vx = var("a"), var("b"), var("x")
    # forme : implication (prem ⇒ DIAG^w)
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))), leq(va, vb))
    assert th.conclusion.tag == "ou"  # impl encodé (¬prem ou DIAG^w)
    # hypothèses = commutations pointwise de u et de v
    Hu = P.commute_valeur_proj(var("u"), var("f"), var("g"), leq, var("I"), "a", "b", "x")
    Hv = P.commute_valeur_proj(var("v"), var("g"), var("h"), leq, var("I"), "a", "b", "x")
    assert Hu in th.hypotheses
    assert Hv in th.hypotheses
    # l'implication réelle : prem ⇒ DIAG^w
    diag_w = egal(
        E.valeur(C.u_indice(var("v"), va),
                 E.valeur(C.u_indice(var("u"), va),
                          E.valeur(L.appl_proj(var("f"), va, vb), vx))),
        E.valeur(L.appl_proj(var("h"), va, vb),
                 E.valeur(C.u_indice(var("v"), vb),
                          E.valeur(C.u_indice(var("u"), vb), vx))))
    assert th.conclusion == impl(prem, diag_w)


def test_composition_inductive_sous_commute():
    leq = _leq()
    th = P.composition_inductive_sous_commute("u", "v", "f", "g", "h", leq,
                                              "I", "a", "b", "x")
    Hu = P.commute_valeur_ind(var("u"), var("f"), var("g"), leq, var("I"), "a", "b", "x")
    Hv = P.commute_valeur_ind(var("v"), var("g"), var("h"), leq, var("I"), "a", "b", "x")
    assert Hu in th.hypotheses
    assert Hv in th.hypotheses
    assert th.conclusion.tag == "ou"  # implication encodée (¬prem ou DIAG^w)


# ════════════════════════════════════════════════════════════════════════════
#  PROP. 1 (1°) — factorisation (6) & unicité ponctuelle (THÉORÈMES)
# ════════════════════════════════════════════════════════════════════════════
def test_factorisation_valeur_proj():
    """u_α(t)=f_α(u(t)) — relation (6) lue ponctuellement, sous l'hyp de factorisation."""
    th = P.factorisation_valeur_proj("u", "E", "f", "I", "a", "t")
    va, vt = var("a"), var("t")
    ua_t = E.valeur(C.u_indice(var("u"), va), vt)
    fa_uat = C.application_canonique_proj_valeur(var("E"), var("f"), va, E.valeur(var("u"), vt))
    assert th.conclusion == egal(ua_t, fa_uat)
    # dépend de l'hypothèse de factorisation (∀α∀t)
    assert pourtout("a", pourtout("t", egal(ua_t, fa_uat))) in th.hypotheses


def test_unicite_factorisation_ponctuelle():
    """f_α(u(t)) = f_α(u'(t)) — contenu de l'unicité (Prop.1 1°), non vide."""
    th = P.unicite_factorisation_ponctuelle("u", "up", "E", "f", "I", "a", "t")
    va, vt = var("a"), var("t")
    fa_u = C.application_canonique_proj_valeur(var("E"), var("f"), va, E.valeur(var("u"), vt))
    fa_up = C.application_canonique_proj_valeur(var("E"), var("f"), va, E.valeur(var("up"), vt))
    assert th.conclusion == egal(fa_u, fa_up)
    assert th.conclusion not in th.hypotheses
    # deux hypothèses de factorisation distinctes (u et u')
    assert len(th.hypotheses) == 2


# ════════════════════════════════════════════════════════════════════════════
#  PROP. 2 — pont image réciproque
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_composante_proj():
    """M_α = (u_α)^{-1}(x'_α) — α-composante du système image réciproque (Prop.2)."""
    from bourbaki.ordre.iii_7_limites import ensembles_cofinal as CF
    th = P.image_reciproque_composante_proj("u", "xp", "a")
    va = var("a")
    M = CF.systeme_image_reciproque(var("u"), var("xp"))
    Ma = app("M_indice", M, va)
    attendu = egal(Ma, CF.image_reciproque_indice(var("u"), va, var("xp")))
    assert th.conclusion == attendu


# ════════════════════════════════════════════════════════════════════════════
#  HONNÊTETÉ — theorie=22 intangible, REPORTES non vide
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_intacte():
    """Aucun axiome ajouté : theorie_ensembles() reste à 22 axiomes."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reportes_non_vide():
    assert isinstance(P.REPORTES, list) and len(P.REPORTES) >= 5
