"""§III.2 — LEMME 4 (forme tractable) : une application STRICTEMENT CROISSANTE d'un
ensemble bien ordonné DANS LUI-MÊME ne décroît jamais.

    { est_bien_ordonne(R,E),  (∀t)(t∈E ⇒ f(t)∈E),  f strictement croissante E→E }
        ⊢  (∀x)( x∈E ⇒ R{x, f(x)} ).

C'est le cas E=F, g=f de Lemme 4 §III.2 (Bourbaki, E.III.2.6).  Cœur de la preuve
(par minimalité, fidèle Bourbaki) :  soit A = { x∈E | f(x) <_R x } le « mauvais
ensemble » ; si A≠∅, il a un plus petit m ; m∈A donne f(m) <_R m, donc (f strict
croissante) f(f(m)) <_R f(m), donc f(m)∈A ; mais m=min(A) force R{m,f(m)}, et avec
R{f(m),m} l'antisymétrie donne m=f(m), contredisant f(m)≠m.  Donc A=∅ ; par TOTALITÉ
du bon ordre (bon_ordre_est_total), x∈E impose R{x,f(x)} ou R{f(x),x}, et le second
cas force f(x)=x (sinon x∈A=∅), d'où R{x,f(x)}.

A est construit par un AXIOME DÉFINITIONNEL (S8+A1) dans une THÉORIE DÉDIÉE (motif
`axiome_D`) ; theorie_ensembles() reste = 22.  f(x) est manipulé comme TERME OPAQUE
(E.valeur(f,x,b="yv"), cohérent avec est_strictement_croissante) — PAS de pont.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, pourtout, equiv, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import tau
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere, projection_gauche,
    cas, tiers_exclu, dne,
)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import (
    a_implique_a, syllogisme, antecedent_consequent,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.cardinaux.iii_4_ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_bon_ordre import (
    bon_ordre_donne_clause_plus_petit,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_total import bon_ordre_est_total
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg as _seg, membre_segment as _membre_seg,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _decharge(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


_HOLE = "hole_l4"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


def _antisym_de_bo(bo):
    """Extrait ordre_antisymetrique(R) de est_bien_ordonne(R,E)."""
    Hbo = N.assume(bo)
    ord_dans = conjonction_elim_gauche(Hbo)              # est_relation_ordre_dans
    rel_ordre = conjonction_elim_gauche(ord_dans)        # est_relation_ordre
    trans_anti = conjonction_elim_gauche(rel_ordre)      # transitif et antisym
    return conjonction_elim_droite(trans_anti)           # antisym


def _f_dans_E(f, E_set, t="t"):
    """(∀t)(t∈E ⇒ f(t)∈E)."""
    vE = _t(E_set)
    return pourtout(t, impl(appartient(var(t), vE), appartient(_val(f, var(t)), vE)))


def _val(f, x):
    """f(x) au sens Bourbaki, liant interne « j » LETTRE SIMPLE (cohérent avec
    ordre_monotone._val ; alpha_tau-compatible, jamais liant de quantif — audit)."""
    return E.valeur(_t(f), _t(x), b="j")


def _coup(a, b, R):
    """(a,b) ∈ R   (lecture « a ≤ b » pour l'ordre de graphe R)."""
    return appartient(E.couple(_t(a), _t(b)), _t(R))


def _strict(a, b, R):
    """a <_R b := (a,b)∈R et a≠b."""
    return et(_coup(a, b, R), non(egal(_t(a), _t(b))))


# ════════════════════════════════════════════════════════════════════════════
#  Le « mauvais ensemble »  A = { x∈E | f(x) <_R x }  (axiome définitionnel S8+A1).
# ════════════════════════════════════════════════════════════════════════════
def A_bad(R="R", E_set="E", f="f"):
    """Terme opaque A = { x∈E | f(x) <_R x }  (sous-ensemble des points décroissants)."""
    return E.app("A_lemme4_bad", _t(R), _t(E_set), _t(f))


def _corps_A(R, E_set, f, u):
    """φ(u) := u∈E et f(u) <_R u."""
    return et(appartient(_t(u), _t(E_set)), _strict(_val(f, u), u, R))


def axiome_A(R="R", E_set="E", f="f", u="u"):
    """⊢-schéma (∀R)(∀E)(∀f)(∀u)( u∈A ⇔ (u∈E et f(u)<_R u) ).

    Axiome DÉFINITIONNEL du mauvais ensemble (S8 sélection dans E + A1 unicité)."""
    vR, vE, vf, vu = var(R), var(E_set), var(f), var(u)
    return pourtout(R, pourtout(E_set, pourtout(f, pourtout(u,
        equiv(appartient(vu, A_bad(vR, vE, vf)),
              _corps_A(vR, vE, vf, vu))))))


def theorie_A(R="R", E_set="E", f="f", u="u"):
    """Théorie dédiée ne contenant que l'axiome de A (motif axiome_D)."""
    return N.Theorie("A-lemme4-mauvais-ensemble", [axiome_A(R, E_set, f, u)])


def A_membre(R="R", E_set="E", f="f", u="u"):
    """⊢ ( u∈A ) ⇔ ( u∈E et f(u) <_R u ).   (axiome instancié aux TERMES.)"""
    ax = N.axiome(theorie_A(), axiome_A())
    return instancie(instancie(instancie(instancie(ax, _t(R)), _t(E_set)), _t(f)), _t(u))


def A_inclus_E(R="R", E_set="E", f="f", z="z"):
    """⊢ A ⊂ E.   (φ(z) ⇒ z∈E par projection gauche.)"""
    vz = var(z)
    eq = A_membre(R, E_set, f, vz)                       # z∈A ⇔ (z∈E et f(z)<z)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(appartient(vz, _t(E_set)),
                                         _strict(_val(f, vz), vz, R)))
    return N.generalisation(z, z_imp)                    # (∀z)(z∈A ⇒ z∈E) = A⊂E


# ════════════════════════════════════════════════════════════════════════════
#  STAGE 2 — le mauvais ensemble est VIDE :  {bo, f:E→E, f strict crois.} ⊢ A=∅.
# ════════════════════════════════════════════════════════════════════════════
def A_vide(R="R", E_set="E", f="f"):
    """⊢ { est_bien_ordonne(R,E),  (∀t)(t∈E⇒f(t)∈E),  f strict crois. E→E } ⊢ A = ∅.

    Cœur par minimalité : si A≠∅, m=min(A) donne f(m)<m, donc f(f(m))<f(m) (f strict),
    donc f(m)∈A ; mais m=min(A) force R{m,f(m)}, et l'antisymétrie avec R{f(m),m} donne
    m=f(m), contredisant f(m)≠m."""
    vR, vE, vf = var(R), _t(E_set), _t(f)   # f/E_set acceptent un TERME (ex. c=φ'⁻¹∘φ composé)
    Rf = _R_de(R)
    A = A_bad(vR, vE, vf)
    Hfdans = N.assume(_f_dans_E(vf, vE))
    Hscr = N.assume(est_strictement_croissante(vR, vR, vf, vE, vE))  # vf peut être un TERME composé (cf. _t ci-dessus)

    # plus petit élément de A — via la clause CANONIQUE (bo = est_bien_ordonne(R,E)
    # standard, chainable / partagé avec la totalité), instanciée au TERME A.
    Ane = non(egal(A, E.VIDE))
    bo = E.est_bien_ordonne(Rf, vE)                            # est_bien_ordonne(R,E) CANONIQUE
    clause = N.modus_ponens(N.assume(bo), bon_ordre_donne_clause_plus_petit(Rf, E_set))
    inst = instancie(clause, A)                                # (A⊂E et A≠∅) ⇒ ∃a(...)
    prem = conjonction_intro(A_inclus_E(R, E_set, f), N.assume(Ane))
    pp = N.modus_ponens(prem, inst)                            # {bo, A≠∅} ⊢ ∃a(...)

    # témoin m = min(A)
    va = var("a")
    corps = et(appartient(va, A),
               pourtout("w", impl(appartient(var("w"), A), Rf(va, var("w")))))
    m = tau("a", corps)
    temoin = N.modus_ponens(pp, N.existe_temoin(corps, "a"))    # corps[a:=m]
    m_in_A = conjonction_elim_gauche(temoin)
    forall_w = conjonction_elim_droite(temoin)
    # m∈A ⇒ m∈E et f(m)<m
    mbody = N.modus_ponens(m_in_A, equivalence_avant(A_membre(vR, vE, vf, m)))
    m_in_E = conjonction_elim_gauche(mbody)
    fm_lt_m = conjonction_elim_droite(mbody)                    # _strict(f(m),m,R)
    coup_fm_m = conjonction_elim_gauche(fm_lt_m)                # (f(m),m)∈R
    fm_ne_m = conjonction_elim_droite(fm_lt_m)                  # f(m)≠m
    fm = _val(vf, m)
    fm_in_E = N.modus_ponens(m_in_E, instancie(Hfdans, m))      # f(m)∈E
    # f strict croissante en (f(m), m) : f(f(m)) < f(m)
    prem = conjonction_intro(conjonction_intro(fm_in_E, m_in_E), fm_lt_m)
    scr_inst = instancie(instancie(Hscr, fm), m)
    ffm_lt_fm = N.modus_ponens(prem, scr_inst)                  # _strict(f(f(m)),f(m),R)
    # donc f(m) ∈ A
    fm_in_A = N.modus_ponens(conjonction_intro(fm_in_E, ffm_lt_fm),
                             equivalence_arriere(A_membre(vR, vE, vf, fm)))
    # m=min(A) ⇒ R{m,f(m)}
    Rm_fm = N.modus_ponens(fm_in_A, instancie(forall_w, fm))    # (m,f(m))∈R
    # antisymétrie : R{m,f(m)} et R{f(m),m} ⇒ m=f(m)
    anti = _antisym_de_bo(bo)
    anti_inst = instancie(instancie(anti, m), fm)
    m_eq_fm = N.modus_ponens(conjonction_intro(Rm_fm, coup_fm_m), anti_inst)  # m=f(m)
    fm_eq_m = N.modus_ponens(m_eq_fm, symetrie(m, fm))          # f(m)=m
    # contradiction avec f(m)≠m → A=∅
    A_eq_vide = _ex_falso(fm_eq_m, fm_ne_m, egal(A, E.VIDE))    # A=∅  [bo,A≠∅,fdans,scr]
    imp = N.loi_deduction(Ane, A_eq_vide)                       # (A≠∅) ⇒ (A=∅)  [bo,fdans,scr]
    te = tiers_exclu(egal(A, E.VIDE))                          # (A=∅) ou (A≠∅)
    return cas(te, a_implique_a(egal(A, E.VIDE)), imp)          # A=∅  [bo,fdans,scr]


# ════════════════════════════════════════════════════════════════════════════
#  STAGE 3 — LEMME 4 :  x∈E ⇒ R{x, f(x)}.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Lem.4 | E III.22 L.5-7 | PDF p.125
def lemme_4(R="R", E_set="E", f="f", x="x"):
    """⊢ { est_bien_ordonne(R,E), (∀t)(t∈E⇒f(t)∈E), f strict crois. E→E }
            ⊢ (∀x)( x∈E ⇒ R{x, f(x)} ).

    De A=∅ (A_vide) : x∈E impose, par TOTALITÉ, R{x,f(x)} ou R{f(x),x} ; le 2ᵉ cas force
    f(x)=x (sinon x∈A=∅), d'où R{x,f(x)}."""
    vR, vE, vf = var(R), _t(E_set), _t(f)   # f/E_set acceptent un TERME (ex. c=φ'⁻¹∘φ composé)
    Rf = _R_de(R)
    A = A_bad(vR, vE, vf)
    vx = var(x)
    fx = _val(vf, vx)

    A_eq_vide = A_vide(R, E_set, f)                             # {bo,fdans,scr} ⊢ A=∅
    Hfdans = N.assume(_f_dans_E(vf, vE))
    Hx = N.assume(appartient(vx, vE))                          # x∈E

    # ¬( f(x) <_R x )   (sinon x∈A=∅ ⇒ x∈∅, absurde)
    Hlt = N.assume(_strict(fx, vx, vR))                        # f(x)<x
    x_in_A = N.modus_ponens(conjonction_intro(Hx, Hlt),
                            equivalence_arriere(A_membre(vR, vE, vf, vx)))  # x∈A
    x_in_vide = _leib(A, E.VIDE, A_eq_vide, lambda w: appartient(vx, w), x_in_A)  # x∈∅
    notx = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vx)   # ¬(x∈∅)
    notlt = _refute_self(N.loi_deduction(_strict(fx, vx, vR),
                                         _ex_falso(x_in_vide, notx, non(_strict(fx, vx, vR)))))
    #   notlt : ¬(f(x)<x)   [bo,fdans,scr,x∈E]

    # totalité : R{x,f(x)} ou R{f(x),x}
    tot = bon_ordre_est_total(R, E_set)                        # {bo'} ⊢ ∀x∀y((x∈E et y∈E)⇒(…))
    fx_in_E = N.modus_ponens(Hx, instancie(Hfdans, vx))        # f(x)∈E
    disj = N.modus_ponens(conjonction_intro(Hx, fx_in_E),
                          instancie(instancie(tot, vx), fx))   # R{x,f(x)} ou R{f(x),x}

    but = Rf(vx, fx)                                           # R{x,f(x)}
    # cas A : R{x,f(x)} ⇒ but
    brA = a_implique_a(but)
    # cas B : R{f(x),x} ⇒ but   (force f(x)=x puis transporte)
    HRfx = N.assume(Rf(fx, vx))                               # R{f(x),x}
    #   f(x)=x : ¬(f(x)≠x) car (R{f(x),x} et f(x)≠x)=f(x)<x contredit notlt
    Hne = N.assume(non(egal(fx, vx)))
    lt_again = conjonction_intro(HRfx, Hne)                    # f(x)<x
    fx_eq_x_0 = _ex_falso(lt_again, notlt, egal(fx, vx))       # f(x)=x  [Hne,…]
    imp_ne = N.loi_deduction(non(egal(fx, vx)), fx_eq_x_0)     # (f(x)≠x) ⇒ f(x)=x
    te2 = tiers_exclu(egal(fx, vx))                           # (f(x)=x) ou (f(x)≠x)
    fx_eq_x = cas(te2, a_implique_a(egal(fx, vx)), imp_ne)     # f(x)=x
    #   R{x,f(x)} depuis R{f(x),x} et f(x)=x
    Rxx = _leib(fx, vx, fx_eq_x, lambda w: Rf(w, vx), HRfx)    # R{x,x}
    x_eq_fx = N.modus_ponens(fx_eq_x, symetrie(fx, vx))       # x=f(x)
    Rxfx = _leib(vx, fx, x_eq_fx, lambda w: Rf(vx, w), Rxx)    # R{x,f(x)}
    brB = N.loi_deduction(Rf(fx, vx), Rxfx)                    # R{f(x),x} ⇒ R{x,f(x)}

    res = cas(disj, brA, brB)                                  # R{x,f(x)}  [bo,fdans,scr,x∈E,…]
    body = N.loi_deduction(appartient(vx, vE), res)           # x∈E ⇒ R{x,f(x)}
    return N.generalisation(x, body)                          # (∀x)(x∈E ⇒ R{x,f(x)})


def lemme_4_cible(R="R", E_set="E", f="f", x="x"):
    """ÉNONCÉ-cible (test miroir) de la conclusion de lemme_4."""
    Rf = _R_de(R)
    vE, vx = var(E_set), var(x)
    return pourtout(x, impl(appartient(vx, vE), Rf(vx, _val(f, vx))))


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 (E.III.2.6) — aucune application strictement croissante n'envoie E
#  dans un SEGMENT PROPRE  ]←,a[  de E.   (⇒ pas d'iso d'un bon ordre sur un de ses
#  segments propres : un tel iso enverrait E DANS le segment.)
# ════════════════════════════════════════════════════════════════════════════
def _segE(R, E_set, a):
    """seg(R,E,a) = ]←,a[ = { u∈E | R{u,a} et u≠a }  (ground set E, extrémité a)."""
    return _seg(R, E_set, a)


def cor1_pas_dans_segment(R="R", E_set="E", g="g", a="a", t="t"):
    """⊢ { est_bien_ordonne(R,E),  a∈E,  g strict crois. E→E }
            ⊢ ¬ (∀t)( t∈E ⇒ g(t) ∈ seg(R,E,a) ).

    🎯 COR 1 §III.2 : g (strict. croissante E→E) ne peut envoyer E dans le segment
    PROPRE ]←,a[.  Sinon g(a)∈]←,a[ donne g(a) <_R a, mais Lemme 4 donne a ≤_R g(a),
    et l'antisymétrie force a=g(a), contredisant g(a)≠a.  (Un iso de E sur ]←,a[
    enverrait E dans ]←,a[ : impossible — Cor 1.)"""
    vR, vE, vg, va = var(R), var(E_set), var(g), var(a)
    Rf = _R_de(R)
    Sa = _segE(R, E_set, va)
    vt = var(t)
    Hmap_f = pourtout(t, impl(appartient(vt, vE), appartient(_val(vg, vt), Sa)))
    Hmap = N.assume(Hmap_f)
    Ha = N.assume(appartient(va, vE))                          # a∈E

    # (∀t)(t∈E ⇒ g(t)∈E)  dérivé de Hmap + seg⊂E
    Ht = N.assume(appartient(vt, vE))
    gt_in_Sa = N.modus_ponens(Ht, instancie(Hmap, vt))
    gt_unpack = N.modus_ponens(gt_in_Sa,
                               equivalence_avant(_membre_seg(R, E_set, va, _val(vg, vt))))
    gt_in_E = conjonction_elim_gauche(conjonction_elim_gauche(gt_unpack))   # g(t)∈E
    fdans = N.generalisation(t, N.loi_deduction(appartient(vt, vE), gt_in_E))

    # Lemme 4 (f:=g) : a∈E ⇒ R{a,g(a)}
    l4 = lemme_4(R, E_set, g)
    l4 = _decharge(l4, _f_dans_E(vg, vE), fdans)               # décharge f:E→E
    ga = _val(vg, va)
    Rag = N.modus_ponens(Ha, instancie(l4, va))                # R{a, g(a)}

    # g(a)∈]←,a[ ⇒ R{g(a),a} et g(a)≠a
    ga_in_Sa = N.modus_ponens(Ha, instancie(Hmap, va))
    ga_unpack = N.modus_ponens(ga_in_Sa,
                               equivalence_avant(_membre_seg(R, E_set, va, ga)))
    Rga = conjonction_elim_droite(conjonction_elim_gauche(ga_unpack))       # R{g(a),a}
    ga_ne_a = conjonction_elim_droite(ga_unpack)                            # g(a)≠a

    # antisymétrie : a=g(a) ; contradiction avec g(a)≠a
    anti = _antisym_de_bo(E.est_bien_ordonne(Rf, vE))
    anti_inst = instancie(instancie(anti, va), ga)
    a_eq_ga = N.modus_ponens(conjonction_intro(Rag, Rga), anti_inst)        # a=g(a)
    ga_eq_a = N.modus_ponens(a_eq_ga, symetrie(va, ga))                     # g(a)=a
    contra = _ex_falso(ga_eq_a, ga_ne_a, non(Hmap_f))                       # ¬Hmap  [Hmap,…]
    return _refute_self(N.loi_deduction(Hmap_f, contra))                    # ¬Hmap  [bo,a∈E,scr]


def cor1_pas_dans_segment_cible(R="R", E_set="E", g="g", a="a", t="t"):
    """ÉNONCÉ-cible (test miroir) de cor1_pas_dans_segment."""
    vE, vt, va = var(E_set), var(t), var(a)
    Sa = _segE(R, E_set, va)
    return non(pourtout(t, impl(appartient(vt, vE), appartient(_val(g, vt), Sa))))


__all__ = [
    "A_bad", "axiome_A", "theorie_A", "A_membre", "A_inclus_E",
    "A_vide", "lemme_4", "lemme_4_cible",
    "cor1_pas_dans_segment", "cor1_pas_dans_segment_cible",
    "_val", "_strict", "_coup",
]
