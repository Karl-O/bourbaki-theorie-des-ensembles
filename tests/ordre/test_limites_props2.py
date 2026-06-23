"""Tests §III.7 (vague F) — SALVAGE complémentaire des Propositions des limites.

Vérifie, pour chaque théorème de `ensembles_limites_props2` :
  (a) qu'il PASSE le noyau (construction = certification) ;
  (b) que la CONCLUSION certifiée est EXACTEMENT la cible visée ;
  (c) la NON-VACUITÉ : la conclusion n'est ni une hypothèse, ni de la forme P⇒P ;
  (d) que rien n'est postulé : theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.logique.formule import (
    var, app, egal, appartient, et, impl, non, pourtout, existe, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles import ensembles_limites as L
from bourbaki.ordre.iii_7_limites import ensembles_limites_canoniques as C
from bourbaki.ordre.iii_7_limites import ensembles_limites_props2 as P2


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


# ════════════════════════════════════════════════════════════════════════════
#  1.  factorisation ⇒ compatibilité avec les transitions (Prop. 1 facile)
# ════════════════════════════════════════════════════════════════════════════
def test_relation_2_proj_en_point():
    """f_α(z) = f_{αβ}(f_β(z)) en un TERME z arbitraire (relation (2) au point)."""
    leq = _leq()
    z = E.valeur(var("u"), var("t"))                 # z = u(t), un TERME non-variable
    th = P2.relation_2_proj_en_point("E", "f", leq, "I", z, "a", "b")
    va, vb = var("a"), var("b")
    fa_z = C.application_canonique_proj_valeur(var("E"), var("f"), va, z)
    fb_z = C.application_canonique_proj_valeur(var("E"), var("f"), vb, z)
    fab = L.appl_proj(var("f"), va, vb)
    assert th.conclusion == egal(fa_z, E.valeur(fab, fb_z))
    assert th.conclusion not in th.hypotheses


def test_factorisation_compatible_transitions():
    """f_{αβ}(u_β(t)) = u_α(t) — la factorisation (6) implique la compat. de cône (5).

    SENS FACILE de la Prop. 1.  Conclusion EXACTE + non-vacuité + hypothèse de
    factorisation présente dans le séquent."""
    leq = _leq()
    th = P2.factorisation_compatible_transitions("u", "E", "f", leq, "I", "a", "b", "t")
    va, vb, vt = var("a"), var("b"), var("t")
    ub_t = E.valeur(C.u_indice(var("u"), vb), vt)
    ua_t = E.valeur(C.u_indice(var("u"), va), vt)
    fab = L.appl_proj(var("f"), va, vb)
    assert th.conclusion == egal(E.valeur(fab, ub_t), ua_t)
    assert th.conclusion not in th.hypotheses
    # l'hypothèse de factorisation (∀α∀t) u_α(t)=f_α(u(t)) est portée
    ut = E.valeur(var("u"), vt)
    fa_ut = C.application_canonique_proj_valeur(var("E"), var("f"), va, ut)
    Hfact = pourtout("a", pourtout("t", egal(ua_t, fa_ut)))
    assert Hfact in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  2.  passage à la limite des applications (Cor.1 Prop.1 / Prop.6, facile)
# ════════════════════════════════════════════════════════════════════════════
def test_passage_limite_proj():
    """g_{αβ}(g_β(u(z))) = g_{αβ}(u_β(f_β(z))) — diagramme propagé (proj.), non vide."""
    leq = _leq()
    th = P2.passage_limite_proj("u", "E", "f", "F", "g", leq, "I", "a", "b", "z")
    va, vb, vz = var("a"), var("b"), var("z")
    uz = E.valeur(var("u"), vz)
    g_b_uz = C.application_canonique_proj_valeur(var("F"), var("g"), vb, uz)
    fb_z = C.application_canonique_proj_valeur(var("E"), var("f"), vb, vz)
    ub_fbz = E.valeur(C.u_indice(var("u"), vb), fb_z)
    gab = L.appl_proj(var("g"), va, vb)
    assert th.conclusion == egal(E.valeur(gab, g_b_uz), E.valeur(gab, ub_fbz))
    assert th.conclusion not in th.hypotheses
    assert len(th.hypotheses) == 1                    # le diagramme (∀α∀z)


def test_passage_limite_ind():
    """u(f_β(f_{βα}(x))) = g_β(u_β(f_{βα}(x))) — diagramme inductif transporté."""
    leq = _leq()
    th = P2.passage_limite_ind("u", "E", "f", "F", "g", leq, "I", "a", "b", "x")
    va, vb, vx = var("a"), var("b"), var("x")
    fba = L.appl_ind(var("f"), vb, va)
    fba_x = E.valeur(fba, vx)
    lhs = E.valeur(var("u"),
                   C.application_canonique_ind_valeur(var("E"), var("f"), var("I"), vb, fba_x))
    rhs = C.application_canonique_ind_valeur(
        var("F"), var("g"), var("I"), vb,
        E.valeur(C.u_indice(var("u"), vb), fba_x))
    assert th.conclusion == egal(lhs, rhs)
    assert th.conclusion not in th.hypotheses
    assert len(th.hypotheses) == 1


# ════════════════════════════════════════════════════════════════════════════
#  3.  cofinal ⇒ application canonique g bien définie / compatible (Prop. 3 facile)
# ════════════════════════════════════════════════════════════════════════════
def test_cofinal_canonique_coordonnee():
    """pr_α(g(x)) = f_α(x) — formule (3), coordonnée par coordonnée."""
    leq = _leq()
    th = P2.cofinal_canonique_coordonnee("E", "f", leq, "I", "J", "x", "a")
    va, vx = var("a"), var("x")
    g = C.application_canonique_g(var("E"), var("f"), var("J"))
    pra_gx = E.projection_indice(E.valeur(g, vx), va)
    fa_x = C.application_canonique_proj_valeur(var("E"), var("f"), va, vx)
    assert th.conclusion == egal(pra_gx, fa_x)
    assert th.conclusion not in th.hypotheses


def test_cofinal_canonique_compatible():
    """pr_α(g(x)) = f_{αβ}(pr_β(g(x))) — g(x) satisfait la condition (1) du système
    restreint à J : SENS FACILE de la Prop. 3 (g bien définie à valeurs dans E')."""
    leq = _leq()
    th = P2.cofinal_canonique_compatible("E", "f", leq, "I", "J", "x", "a", "b")
    va, vb, vx = var("a"), var("b"), var("x")
    g = C.application_canonique_g(var("E"), var("f"), var("J"))
    pra_gx = E.projection_indice(E.valeur(g, vx), va)
    prb_gx = E.projection_indice(E.valeur(g, vx), vb)
    fab = L.appl_proj(var("f"), va, vb)
    assert th.conclusion == egal(pra_gx, E.valeur(fab, prb_gx))
    assert th.conclusion not in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  4.  cofinal ⇒ canonique inductive : surjectivité « sens facile » (Prop. 8 facile)
# ════════════════════════════════════════════════════════════════════════════
def test_canonique_ind_atteint():
    """(∃v)(v=x et f_α(v)=Cl_R(x)) — Cl_R(x) est ATTEINT par la canonique f_α."""
    th = P2.canonique_ind_atteint("E", "f", "I", None, "a", "x")
    assert th.conclusion.tag == "exists"
    assert th.conclusion not in th.hypotheses
    # hypothèses = α∈I et x∈E_α (membership, jamais postulées)
    va, vx = var("a"), var("x")
    assert appartient(va, var("I")) in th.hypotheses
    assert appartient(vx, E.valeur_famille(var("E"), va)) in th.hypotheses
    assert len(th.hypotheses) == 2


# ════════════════════════════════════════════════════════════════════════════
#  HONNÊTETÉ — theorie=22 intangible, REPORTES non vide
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_intacte():
    """Aucun axiome ajouté : theorie_ensembles() reste à 22 axiomes."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reportes_non_vide():
    assert isinstance(P2.REPORTES, list) and len(P2.REPORTES) >= 5
