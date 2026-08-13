"""Résumé §3 (E.R.14 item 8) — inclusion de graphes ⇔ inclusion des coupes.

Bourbaki (E.R.14, item 8) : « La relation K ⊂ K' est équivalente à K(x) ⊂ K'(x)
pour tout x. »  (K, K' parties de E×F, i.e. graphes ; K(x)=K{x} coupe suivant x.)

ÉNONCÉ DÉRIVÉ (K graphe, en hypothèse honnête pour le sens ⇐) :

    ⊢ est_un_graphe(K) ⇒ ( K ⊂ K'  ⇔  (∀x)( K{x} ⊂ K'{x} ) )

  · K{x} := coupe(K,x) = K⟨{x}⟩   (E.II.3.2) ;
  · coupe_caracterisation : (y∈K{a}) ⇔ ((a,y)∈K).

DÉMONSTRATION :
  (⇒) K⊂K'.  Pour x, y : y∈K{x} ⇔ (x,y)∈K [coupe] ⇒ (x,y)∈K' [K⊂K'] ⇔ y∈K'{x}.
  (⇐) (∀x)K{x}⊂K'{x}.  Pour z∈K : z est un couple [est_un_graphe(K)], donc
      z=(pr₁z,pr₂z) [couple_egal_projections] ; (pr₁z,pr₂z)∈K ⇒ pr₂z∈K{pr₁z}
      [coupe] ⊂ K'{pr₁z} [hyp en x=pr₁z] ⇒ (pr₁z,pr₂z)∈K' ⇒ z∈K'.
      Pont α : est_un_couple(z) [liants x,y] ⇒ est_couple(z) [liants a,b].

theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient, impl, pourtout, inclus, equiv, existe, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions_complements import (
    coupe, coupe_caracterisation)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couple_caracterisation import (
    couple_egal_projections, est_couple)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _coupe_carac_terme(k_name, t_point, t_elem):
    """⊢ (t_elem ∈ K{t_point}) ⇔ ((t_point,t_elem) ∈ K)  pour des TERMES quelconques.

    coupe_caracterisation(k,"a") a « a » et « y » libres ; on généralise les deux
    (liant interne de coupe_membre = « x », donc « a » sûr) puis on instancie au point
    puis à l'élément (k_name = NOM du graphe)."""
    gen = N.generalisation("a", N.generalisation("y", coupe_caracterisation(k_name, "a")))
    return instancie(instancie(gen, _t(t_point)), _t(t_elem))


def _pont_est_un_couple_vers_est_couple(z):
    """⊢ est_un_couple(z) ⇒ est_couple(z)   (α-pont : liants x,y ↦ a,b)."""
    vz = _t(z)
    vx, vy = var("x"), var("y")
    hz = N.assume(E.est_un_couple(vz))                 # (∃x)(∃y)(z=(x,y))
    hx = N.assume(existe("y", egal(vz, E.couple(vx, vy))))   # (∃y)(z=(x,y))  [x fixé]
    hy = N.assume(egal(vz, E.couple(vx, vy)))          # z=(x,y)
    e_b = N.modus_ponens(hy, N.s5(egal(vz, E.couple(vx, var("b"))), vy, "b"))   # (∃b)(z=(x,b))
    e_ab = N.modus_ponens(e_b, N.s5(existe("b", egal(vz, E.couple(var("a"), var("b")))), vx, "a"))  # (∃a)(∃b)(z=(a,b))
    imp_y = existe_elimination(N.loi_deduction(egal(vz, E.couple(vx, vy)), e_ab), "y")
    ec_sous_x = N.modus_ponens(hx, imp_y)              # est_couple(z)  [x fixé]
    imp_x = existe_elimination(N.loi_deduction(existe("y", egal(vz, E.couple(vx, vy))), ec_sous_x), "x")
    ec = N.modus_ponens(hz, imp_x)                     # est_couple(z)
    return N.loi_deduction(E.est_un_couple(vz), ec)


def enonce_inclusion_ssi_coupes(k="K", kp="Kp"):
    vK, vKp = _t(k), _t(kp)
    rhs = pourtout("a", inclus(coupe(vK, var("a")), coupe(vKp, var("a")), "y"))
    return impl(E.est_un_graphe(vK), equiv(inclus(vK, vKp), rhs))


# ── (⇒)  K⊂K' ⊢ (∀a)( K{a} ⊂ K'{a} )   (point « a » : liant coupe_membre = « x ») ──
def _dir_incl_vers_coupes(k, kp):
    vK, vKp = _t(k), _t(kp)
    h = N.assume(inclus(vK, vKp))                      # (∀z)(z∈K ⇒ z∈K')
    va, vy = var("a"), var("y")
    hy = N.assume(appartient(vy, coupe(vK, va)))       # y ∈ K{a}
    ay_K = N.modus_ponens(hy, equivalence_avant(coupe_caracterisation(k, "a")))   # (a,y) ∈ K
    ay_Kp = N.modus_ponens(ay_K, instancie(h, E.couple(va, vy)))                  # (a,y) ∈ K'
    y_Kp = N.modus_ponens(ay_Kp, equivalence_arriere(coupe_caracterisation(kp, "a")))  # y ∈ K'{a}
    coupe_incl = N.generalisation("y", N.loi_deduction(appartient(vy, coupe(vK, va)), y_Kp))  # K{a}⊂K'{a}
    return N.generalisation("a", coupe_incl)           # (∀a) K{a}⊂K'{a}


# ── (⇐)  { est_un_graphe(K), (∀a)K{a}⊂K'{a} } ⊢ K⊂K' ──────────────────────────
def _dir_coupes_vers_incl(k, kp):
    vK, vKp = _t(k), _t(kp)
    hg = N.assume(E.est_un_graphe(vK))                 # (∀z)(z∈K ⇒ est_un_couple(z))
    rhs = pourtout("a", inclus(coupe(vK, var("a")), coupe(vKp, var("a")), "y"))
    hr = N.assume(rhs)
    vz = var("z")
    hz = N.assume(appartient(vz, vK))                  # z ∈ K
    z_couple = N.modus_ponens(hz, instancie(hg, vz))   # est_un_couple(z)
    z_couple2 = N.modus_ponens(z_couple, _pont_est_un_couple_vers_est_couple(vz))   # est_couple(z)
    z_eq = N.modus_ponens(z_couple2, equivalence_arriere(couple_egal_projections("z")))  # z=(pr₁z,pr₂z)
    p1, p2 = E.pr1(vz), E.pr2(vz)
    cpl = E.couple(p1, p2)
    # (pr₁z,pr₂z) ∈ K  (substituer z par (p1,p2) dans z∈K)
    pc_in_K = N.modus_ponens(hz, equivalence_avant(
        N.modus_ponens(z_eq, N.s6(vz, cpl, "w", appartient(var("w"), vK)))))       # (p1,p2)∈K
    p2_cK = N.modus_ponens(pc_in_K, equivalence_arriere(_coupe_carac_terme(k, p1, p2)))   # p2∈K{p1}
    hr_p1 = instancie(hr, p1)                          # K{p1} ⊂ K'{p1}
    p2_cKp = N.modus_ponens(p2_cK, instancie(hr_p1, p2))   # p2∈K'{p1}
    pc_in_Kp = N.modus_ponens(p2_cKp, equivalence_avant(_coupe_carac_terme(kp, p1, p2)))  # (p1,p2)∈K'
    z_in_Kp = N.modus_ponens(pc_in_Kp, equivalence_arriere(
        N.modus_ponens(z_eq, N.s6(vz, cpl, "w", appartient(var("w"), vKp)))))      # z∈K'
    return N.generalisation("z", N.loi_deduction(appartient(vz, vK), z_in_Kp))     # K⊂K'


# @livre Ch.R §3 Prop.- | E.R.14 item 8 | PDF p.317  (K⊂K' ⇔ K(x)⊂K'(x) ∀x — DÉRIVÉ)
# @livre Ch.R §3 Demo.- | E.R.14 item 8 | PDF p.317  (démo : coupe_caracterisation + décomposition couple sous est_un_graphe)
def inclusion_ssi_coupes(k="K", kp="Kp"):
    """🎯 ⊢ est_un_graphe(K) ⇒ ( K ⊂ K'  ⇔  (∀a)( K{a} ⊂ K'{a} ) ).   (E.R.14 item 8.)

    « K⊂K' équivaut à K(x)⊂K'(x) pour tout x. »  Hypothèse honnête : K graphe
    (nécessaire au sens ⇐ pour décomposer z∈K en couple).  Le point de coupe est
    nommé « a » (le liant interne de coupe_membre est « x »)."""
    vK, vKp = _t(k), _t(kp)
    rhs = pourtout("a", inclus(coupe(vK, var("a")), coupe(vKp, var("a")), "y"))
    sens_avant = N.loi_deduction(inclus(vK, vKp), _dir_incl_vers_coupes(k, kp))
    sens_arriere = N.loi_deduction(rhs, _dir_coupes_vers_incl(k, kp))
    equ = conjonction_intro(sens_avant, sens_arriere)   # (K⊂K' ⇔ rhs)  [sous est_un_graphe(K)]
    res = N.loi_deduction(E.est_un_graphe(vK), equ)
    assert res.conclusion == enonce_inclusion_ssi_coupes(k, kp), \
        "inclusion_ssi_coupes : conclusion ≠ énoncé attendu"
    return res


__all__ = ["enonce_inclusion_ssi_coupes", "inclusion_ssi_coupes"]
