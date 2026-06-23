"""§III.2 — L1b : TOTALITÉ d'un bon ordre.

Un ensemble bien ordonné est TOTALEMENT ordonné :

    est_bien_ordonne(R,E)  ⊢  (∀x)(∀y)( (x∈E et y∈E) ⇒ ( R{x,y} ou R{y,x} ) ).

PREUVE (fidèle Bourbaki E.III.2.1) : application de la clause de PLUS PETIT ÉLÉMENT à
la PAIRE {x,y}.  {x,y} ⊂ E est non vide, donc admet un plus petit m ∈ {x,y} (engine
`plus_petit_de_bon_ordre`, CLOS).  m∈{x,y} ⇒ m=x ou m=y ; si m=x alors R{m,y}=R{x,y},
si m=y alors R{m,x}=R{y,x}.  Dans les deux cas R{x,y} ou R{y,x}.

🎯 RÔLE : la COMPARABILITÉ (`comparables_dans`), prise en HYPOTHÈSE explicite dans
`seg_reflechit_ordre` (ensembles_bien_ordonne_lemme_1_segments) et REQUISE par le
Lemme 4 §III.2 (« f croissante ⇒ x≤f(x) », où il faut comparer x et f(x)), devient ici
un THÉORÈME dérivé du seul bon ordre.  Pièce de l'arc trichotomie_ordinaux → ℕ.

INVARIANT : theorie_ensembles() = 22.  Rien postulé (tout dérivé de l'axiome de la paire
+ du vide + de l'engine du plus petit élément) ; non vacueux (la conclusion R{x,y} ou
R{y,x} n'est aucune hypothèse, le bon ordre est réellement consommé).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, pourtout, inclus, tau,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie, cas,
    equivalence_avant,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import (
    membre_paire_gauche, membre_paire_droite,
)
from bourbaki.cardinaux.iii_4_ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_bon_ordre import (
    bon_ordre_donne_clause_plus_petit,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ── utilitaires autonomes (aucune confiance nouvelle) ─────────────────────────
def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


_HOLE = "hole_tot"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z."""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _instance_paire_avant(x, y, z):
    """⊢ z∈{x,y} ⇒ (z=x ou z=y)  (sens avant de l'axiome de la paire instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)          # ∀x∀y∀z(z∈{x,y}⇔(z=x ou z=y))
    inst = instancie(instancie(instancie(ax, _t(x)), _t(y)), _t(z))
    return equivalence_avant(inst)                               # z∈{x,y} ⇒ (z=x ou z=y)


# ── {x,y} ⊂ E  (sous x∈E, y∈E) ────────────────────────────────────────────────
def _paire_incluse(vx, vy, vE, z="z"):
    """⊢ { x∈E, y∈E } ⊢ {x,y} ⊂ E   (binder « z » canonique de `inclus`)."""
    P = E.paire(vx, vy)
    vz = var(z)
    Hz = N.assume(appartient(vz, P))                             # z∈{x,y}
    disj = N.modus_ponens(Hz, _instance_paire_avant(vx, vy, vz))  # z=x ou z=y
    Hx = N.assume(appartient(vx, vE))                            # x∈E
    Hy = N.assume(appartient(vy, vE))                            # y∈E
    # cas z=x : z∈E
    Hzx = N.assume(egal(vz, vx))
    Hxz = N.modus_ponens(Hzx, symetrie(vz, vx))                  # x=z
    zE_x = _leib(vx, vz, Hxz, lambda w: appartient(w, vE), Hx)   # z∈E
    brx = N.loi_deduction(egal(vz, vx), zE_x)                    # (z=x) ⇒ z∈E
    # cas z=y : z∈E
    Hzy = N.assume(egal(vz, vy))
    Hyz = N.modus_ponens(Hzy, symetrie(vz, vy))                  # y=z
    zE_y = _leib(vy, vz, Hyz, lambda w: appartient(w, vE), Hy)   # z∈E
    bry = N.loi_deduction(egal(vz, vy), zE_y)                    # (z=y) ⇒ z∈E
    zE = cas(disj, brx, bry)                                     # z∈E  [Hz,Hx,Hy]
    body = N.loi_deduction(appartient(vz, P), zE)               # z∈P ⇒ z∈E  [Hx,Hy]
    return N.generalisation(z, body)                            # {x,y}⊂E  [Hx,Hy]


def _paire_non_vide(vx, vy):
    """⊢ {x,y} ≠ ∅   (INCONDITIONNEL : x∈{x,y} et ∅ vide)."""
    P = E.paire(vx, vy)
    x_in_P = membre_paire_gauche(vx, vy)                         # x∈{x,y}
    Hpe = N.assume(egal(P, E.VIDE))                              # {x,y}=∅
    x_in_vide = _leib(P, E.VIDE, Hpe, lambda w: appartient(vx, w), x_in_P)  # x∈∅
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)     # (∀z)¬(z∈∅)
    notx = instancie(ax_vide, vx)                               # ¬(x∈∅)
    falso = _ex_falso(x_in_vide, notx, non(egal(P, E.VIDE)))     # ¬({x,y}=∅)  [Hpe]
    return _refute_self(N.loi_deduction(egal(P, E.VIDE), falso))  # {x,y}≠∅


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TOTALITÉ — un bon ordre est total.
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_est_total(R="R", E_set="E", x="x", y="y"):
    """⊢ { est_bien_ordonne(R,E) } ⊢ (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x}))."""
    Rf = _R_de(R)
    vE, vx, vy = _t(E_set), var(x), var(y)
    P = E.paire(vx, vy)

    # plus petit élément de la paire {x,y} — via la clause CANONIQUE (binder X standard,
    # bo reste est_bien_ordonne(R,E) canonique, chainable), instanciée au TERME {x,y}.
    bo = E.est_bien_ordonne(Rf, vE)                            # est_bien_ordonne(R,E) CANONIQUE
    clause = N.modus_ponens(N.assume(bo), bon_ordre_donne_clause_plus_petit(Rf, E_set))
    inst = instancie(clause, P)                                # ({x,y}⊂E et {x,y}≠∅) ⇒ ∃a(...)
    prem = conjonction_intro(_paire_incluse(vx, vy, vE), _paire_non_vide(vx, vy))
    pp = N.modus_ponens(prem, inst)                            # {bo, x∈E, y∈E} ⊢ ∃a(...)

    # témoin m = plus petit de {x,y}
    va = var("a")
    corps = et(appartient(va, P),
               pourtout("w", impl(appartient(var("w"), P), Rf(va, var("w")))))
    m = tau("a", corps)
    temoin = N.modus_ponens(pp, N.existe_temoin(corps, "a"))     # corps[a:=m]
    m_in_P = conjonction_elim_gauche(temoin)                     # m∈{x,y}
    forall_w = conjonction_elim_droite(temoin)                   # ∀w(w∈{x,y}⇒R{m,w})
    Rmx = N.modus_ponens(membre_paire_gauche(vx, vy), instancie(forall_w, vx))  # R{m,x}
    Rmy = N.modus_ponens(membre_paire_droite(vx, vy), instancie(forall_w, vy))  # R{m,y}
    m_disj = N.modus_ponens(m_in_P, _instance_paire_avant(vx, vy, m))  # m=x ou m=y

    but = ou(Rf(vx, vy), Rf(vy, vx))                            # R{x,y} ou R{y,x}
    # cas m=x : R{m,y} ⇒ R{x,y}
    Hmx = N.assume(egal(m, vx))
    Rxy = _leib(m, vx, Hmx, lambda w: Rf(w, vy), Rmy)           # R{x,y}
    or_x = N.modus_ponens(Rxy, N.s2(Rf(vx, vy), Rf(vy, vx)))     # R{x,y} ou R{y,x}
    brx = N.loi_deduction(egal(m, vx), or_x)
    # cas m=y : R{m,x} ⇒ R{y,x}
    Hmy = N.assume(egal(m, vy))
    Ryx = _leib(m, vy, Hmy, lambda w: Rf(w, vx), Rmx)           # R{y,x}
    or_y0 = N.modus_ponens(Ryx, N.s2(Rf(vy, vx), Rf(vx, vy)))    # R{y,x} ou R{x,y}
    or_y = N.modus_ponens(or_y0, N.s3(Rf(vy, vx), Rf(vx, vy)))   # R{x,y} ou R{y,x}
    bry = N.loi_deduction(egal(m, vy), or_y)
    disj = cas(m_disj, brx, bry)                                # R{x,y} ou R{y,x}  [bo,x∈E,y∈E]

    # recoller x∈E, y∈E en une conjonction (x∈E et y∈E)
    Hxy = N.assume(et(appartient(vx, vE), appartient(vy, vE)))
    px = conjonction_elim_gauche(Hxy)                           # x∈E [Hxy]
    py = conjonction_elim_droite(Hxy)                           # y∈E [Hxy]
    r = _decharge(disj, appartient(vx, vE), px)                 # remplace bare x∈E par Hxy
    r = _decharge(r, appartient(vy, vE), py)                    # remplace bare y∈E par Hxy
    body = N.loi_deduction(et(appartient(vx, vE), appartient(vy, vE)), r)  # Hxy ⇒ disj  [bo]
    return N.generalisation(x, N.generalisation(y, body))       # ∀x∀y(Hxy ⇒ disj)  [bo]


def bon_ordre_est_total_clos(R="R", E_set="E", x="x", y="y"):
    """⊢ est_bien_ordonne(R,E) ⇒ (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x})).

    Forme CLOSE (0 hypothèse) de la totalité : la clause de bon ordre est déchargée."""
    thm = bon_ordre_est_total(R, E_set, x, y)
    bo = list(thm.hypotheses)[0]          # l'unique hypothèse = est_bien_ordonne(R,E)
    return N.loi_deduction(bo, thm)


def bon_ordre_est_total_cible(R="R", E_set="E", x="x", y="y"):
    """ÉNONCÉ-cible (test miroir) de la conclusion de bon_ordre_est_total."""
    Rf = _R_de(R)
    vE = _t(E_set)
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y,
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             ou(Rf(vx, vy), Rf(vy, vx)))))


__all__ = [
    "bon_ordre_est_total",
    "bon_ordre_est_total_clos",
    "bon_ordre_est_total_cible",
]
