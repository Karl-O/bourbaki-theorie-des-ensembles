"""Tests §III.7 — notions COMPLÉMENTAIRES des limites projectives/inductives.

Vérifie : (a) que chaque NOTION s'introduit (prédicat/terme clos bien formé) ;
(b) que les théorèmes DIRECTS certifient EXACTEMENT la cible attendue (et que les
hypothèses résiduelles attendues figurent bien) — pas une devinette.
"""
from bourbaki.logique.formule import (
    var, egal, appartient, et, impl, pourtout, existe, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_limites as L
from bourbaki.ordre import ensembles_limites_canoniques as C


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  PROJECTIF — application canonique f_α : E → E_α
# ════════════════════════════════════════════════════════════════════════════
def test_canonique_proj_valeur_close():
    """f_α(z)=pr_α z : théorème, hypothèses résiduelles z∈lim← et α∈I."""
    th = C.canonique_proj_valeur("E", "f", _leq(), "I", "a", "z")
    va, vz = var("a"), var("z")
    attendu = egal(C.application_canonique_proj_valeur(var("E"), var("f"), va, vz),
                   E.projection_indice(vz, va))
    assert th.conclusion == attendu
    assert appartient(vz, L.lim_proj(var("E"), var("f"))) in th.hypotheses
    assert appartient(va, var("I")) in th.hypotheses


def test_relation_2_projective():
    """(2) f_α(z)=f_{αβ}(f_β(z)) certifiée sur un point de la limite."""
    th = C.relation_2_projective("E", "f", _leq(), "I", "a", "b", "z")
    vE, vf = var("E"), var("f")
    va, vb, vz = var("a"), var("b"), var("z")
    fab = L.appl_proj(vf, va, vb)
    fa = C.application_canonique_proj_valeur(vE, vf, va, vz)
    fb = C.application_canonique_proj_valeur(vE, vf, vb, vz)
    attendu = egal(fa, E.valeur(fab, fb))
    assert th.conclusion == attendu
    # dépend de l'appartenance de z à la limite
    assert appartient(vz, L.lim_proj(vE, vf)) in th.hypotheses


def test_axiome_canonique_proj_dans_theorie():
    """L'axiome de la valeur canonique projective appartient à sa théorie dédiée."""
    leq = _leq()
    ax = C.axiome_canonique_proj(var("E"), var("f"), leq, var("I"))
    th = C.theorie_canonique_proj(var("E"), var("f"), leq, var("I"))
    assert ax in th.axiomes
    # forme : (∀a)(∀z)((z∈lim← et a∈I) ⇒ f_a(z)=pr_a z) — ∀ encodé ¬∃¬, tag "non"
    from bourbaki.logique.formule import Formule
    assert isinstance(ax, Formule)


# ════════════════════════════════════════════════════════════════════════════
#  PROJECTIF — systèmes d'applications / parties / restriction
# ════════════════════════════════════════════════════════════════════════════
def test_systeme_projectif_applications_commute():
    th = C.systeme_projectif_applications_commute("u", "f", "g", _leq(), "I", "a", "b")
    va, vb = var("a"), var("b")
    ua, ub = C.u_indice(var("u"), va), C.u_indice(var("u"), vb)
    fab = L.appl_proj(var("f"), va, vb)
    gab = L.appl_proj(var("g"), va, vb)
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))), _leq()(va, vb))
    concl = egal(E.composee(ua, fab), E.composee(gab, ub))
    assert th.conclusion == impl(prem, concl)
    assert C.est_systeme_projectif_applications(
        var("u"), var("f"), var("g"), _leq(), var("I")) in th.hypotheses


def test_systeme_projectif_parties_inclusion():
    th = C.systeme_projectif_parties_inclusion("M", "f", _leq(), "I", "a", "b")
    va, vb = var("a"), var("b")
    Ma, Mb = C.M_indice(var("M"), va), C.M_indice(var("M"), vb)
    fab = L.appl_proj(var("f"), va, vb)
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))), _leq()(va, vb))
    concl = inclus(E.image(fab, Mb), Ma)
    assert th.conclusion == impl(prem, concl)


def test_restriction_indices_et_g_se_construisent():
    """Restriction à J + application canonique g + son axiome se construisent."""
    rj = C.restriction_systeme_indices(var("E"), var("f"), var("J"))
    g = C.application_canonique_g(var("E"), var("f"), var("J"))
    ax = C.axiome_canonique_g(var("E"), var("f"), _leq(), var("I"), var("J"))
    th = C.theorie_canonique_g(var("E"), var("f"), _leq(), var("I"), var("J"))
    assert rj is not None and g is not None
    assert ax in th.axiomes


def test_lim_proj_applications_terme():
    u = C.lim_proj_applications(var("E"), var("f"), var("Ep"), var("fp"), var("u"))
    assert u is not None


# ════════════════════════════════════════════════════════════════════════════
#  INDUCTIF — relation de cohérence + limite = quotient
# ════════════════════════════════════════════════════════════════════════════
def test_relation_coherence_inductive_forme():
    """R{x,y} = (∃γ)(γ∈I et γ≥λ(x) et γ≥λ(y) et f_{γλx}(x)=f_{γλy}(y))."""
    leq = _leq()
    R = C.relation_coherence_inductive(var("f"), leq, var("I"), var("x"), var("y"), "g")
    assert R.tag == "exists"      # ∃γ
    # la relation packagée s'applique bien à deux termes
    Rfun = C.coherence_rel(var("f"), leq, var("I"))
    assert Rfun(var("x"), var("y")) == R


def test_lim_ind_est_quotient_de_la_somme():
    """E = lim→ E_α est CODÉE comme le quotient de la somme par la cohérence (E.III.7.5)."""
    li = C.lim_ind(var("E"), var("f"), var("I"))
    G = E.somme_famille(var("E"), var("I"))
    GR = C.graphe_coherence(var("f"), var("I"))
    assert li == E.quotient(GR, G)
    assert C.somme_systeme_inductif(var("E"), var("I")) == G


def test_canonique_ind_valeur_close():
    """f_α(x)=Cl_R(x) : théorème, hypothèses résiduelles α∈I et x∈E_α."""
    th = C.canonique_ind_valeur("E", "f", "I", None, "a", "x")
    va, vx = var("a"), var("x")
    GR = C.graphe_coherence(var("f"), var("I"))
    attendu = egal(C.application_canonique_ind_valeur(var("E"), var("f"), var("I"), va, vx),
                   E.classe(GR, vx))
    assert th.conclusion == attendu
    assert appartient(va, var("I")) in th.hypotheses
    assert appartient(vx, E.valeur_famille(var("E"), va)) in th.hypotheses


def test_axiome_canonique_ind_dans_theorie():
    ax = C.axiome_canonique_ind(var("E"), var("f"), var("I"))
    th = C.theorie_canonique_ind(var("E"), var("f"), var("I"))
    assert ax in th.axiomes


# ════════════════════════════════════════════════════════════════════════════
#  INDUCTIF — systèmes d'applications / parties
# ════════════════════════════════════════════════════════════════════════════
def test_systeme_inductif_applications_commute():
    th = C.systeme_inductif_applications_commute("u", "f", "g", _leq(), "I", "a", "b")
    va, vb = var("a"), var("b")
    ua, ub = C.u_indice(var("u"), va), C.u_indice(var("u"), vb)
    fba = L.appl_ind(var("f"), vb, va)
    gba = L.appl_ind(var("g"), vb, va)
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))), _leq()(va, vb))
    concl = egal(E.composee(ub, fba), E.composee(gba, ua))
    assert th.conclusion == impl(prem, concl)


def test_systeme_inductif_parties_inclusion():
    th = C.systeme_inductif_parties_inclusion("M", "f", _leq(), "I", "a", "b")
    va, vb = var("a"), var("b")
    Ma, Mb = C.M_indice(var("M"), va), C.M_indice(var("M"), vb)
    fba = L.appl_ind(var("f"), vb, va)
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))), _leq()(va, vb))
    concl = inclus(E.image(fba, Ma), Mb)
    assert th.conclusion == impl(prem, concl)


def test_lim_ind_applications_terme():
    u = C.lim_ind_applications(var("E"), var("f"), var("Ep"), var("fp"),
                               var("u"), var("I"))
    assert u is not None


# ════════════════════════════════════════════════════════════════════════════
#  Toutes les définitions se construisent (prédicats clos bien formés)
# ════════════════════════════════════════════════════════════════════════════
def test_definitions_se_construisent():
    spa = C.est_systeme_projectif_applications(var("u"), var("f"), var("g"), _leq(), var("I"))
    spp = C.est_systeme_projectif_parties(var("M"), var("f"), _leq(), var("I"))
    sia = C.est_systeme_inductif_applications(var("u"), var("f"), var("g"), _leq(), var("I"))
    sip = C.est_systeme_inductif_parties(var("M"), var("f"), _leq(), var("I"))
    assert all(x is not None for x in (spa, spp, sia, sip))
    # listes des reportés présentes (honnêteté)
    assert isinstance(C.REPORTES, list) and len(C.REPORTES) > 0
