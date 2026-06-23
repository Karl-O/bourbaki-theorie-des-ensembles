"""§III.3.5 — EXPONENTIATION CARDINALE FIDÈLE  a^b := Card(𝓕(b;a))  (E.III.3, Déf. 4).

VOIE FIDÈLE (refonte propre — la tentative précédente postulait l'énoncé a^0=1
de la Proposition 11, ce qui est un THÉORÈME de Bourbaki : ÉCARTÉE).  Ici on part
de la DÉFINITION GÉNÉRALE (E.II.5.2, Déf. 4 ; axiomes de membership S8+A1 dans
ensembles_abrege) :

    • exposant(E,F) = F^E = { G ⊂ E×F | G fonctionnel ∧ dom G = E }   (graphes) ;
    • applications(E,F) = 𝓕(E;F) = { ((G,E),F) | G ∈ F^E }           (triples).

Ces deux axiomes sont des DÉFINITIONS (caractérisations d'appartenance), pas des
Propositions : on a le DROIT de les poser (comme AXIOME_PRODUIT_FAM).  Puis on
DÉRIVE comme THÉORÈMES (rien postulé) :

  (a) ∅ est l'UNIQUE graphe fonctionnel de domaine ∅ :
        • exposant_contient_vide(F)   ⊢ ∅ ∈ F^∅       (∅ est fonctionnel, dom ∅=∅,
              ∅ ⊂ ∅×F, tout vacuement) ;
        • exposant_vide_est_vide(F)   ⊢ G ∈ F^∅ ⇒ G = ∅   (G ⊂ ∅×F = ∅, donc G ⊂ ∅,
              donc G = ∅ par extension) ;
  (b) donc 𝓕(∅;F) = { ((∅,∅),F) }  (DÉRIVÉ) :
        • applications_vide_egale_singleton(F)  ⊢ 𝓕(∅;F) = {((∅,∅),F)} ;
  (c) a^0 = Card(𝓕(∅;F)) = Card({((∅,∅),F)}) = Card({∅}) = 1  (Prop. 11) :
        • exposant_zero_egale_un(F)   ⊢ a^0 = Card({∅})  (= 1).

Définition du cardinal : exposant_cardinal_binaire(a,b) := Card(𝓕(b;a)).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, non, ou, impl, appartient,
                     existe, pourtout, inclus, subst_t, subst_f)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, equivalence_transitivite,
                               instancie, projection_gauche, projection_droite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination, alpha_existe
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import egalite_par_extension, vide_sans_element
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre, membre_paire_gauche
from bourbaki.cardinaux.ensembles_cardinaux import cardinal


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# Le cardinal a^b := Card(𝓕(b;a))  (E.III.3, Déf. 4)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_cardinal_binaire(a, b):
    """a ^ b := Card(𝓕(b; a))   (exponentiation cardinale, E.III.3.5, Déf. 4).

    Cardinal de l'ensemble des APPLICATIONS de b dans a (codage FIDÈLE sur le
    support `applications` = 𝓕, l'ensemble des triples ((G,b),a), conformément à
    la Définition 4 de Bourbaki : « le cardinal de l'ensemble des applications de
    b dans a »)."""
    return cardinal(E.applications(_t(b), _t(a)))


# ═══════════════════════════════════════════════════════════════════════════════
# (a.1) ex falso réutilisable
# ═══════════════════════════════════════════════════════════════════════════════
def _ex_falso(thm_a, thm_na, cible):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.   (ex falso : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), cible)))


def _n_in_vide(t):
    """⊢ ¬(t ∈ ∅)  pour un TERME t quelconque.   (instance de AXIOME_VIDE en t.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    return instancie(ax, t)


# ═══════════════════════════════════════════════════════════════════════════════
# (a.2)  ∅ ⊂ X  pour tout X   (le vide est inclus dans tout ensemble, vacuement)
# ═══════════════════════════════════════════════════════════════════════════════
def vide_inclus(x="X", z="z"):
    """⊢ ∅ ⊂ X.   (∀z)(z∈∅ ⇒ z∈X)  — vacuement vrai car z∈∅ est impossible (ex falso)."""
    vX, vz = _t(x), var(z)
    # z∈∅ ⇒ z∈X  par ex falso (z∈∅ est impossible)
    hz = N.assume(appartient(vz, E.VIDE))
    n_in = vide_sans_element(z)                          # ¬(z∈∅)
    z_in_X = _ex_falso(hz, n_in, appartient(vz, vX))     # z∈X  [sous z∈∅]
    body = N.loi_deduction(appartient(vz, E.VIDE), z_in_X)  # z∈∅ ⇒ z∈X
    return N.generalisation(z, body)                     # (∀z)(z∈∅ ⇒ z∈X) = ∅⊂X


# ═══════════════════════════════════════════════════════════════════════════════
# (a.3)  est_fonctionnel(∅)   (le graphe vide est fonctionnel, vacuement)
# ═══════════════════════════════════════════════════════════════════════════════
def vide_est_fonctionnel():
    """⊢ est_fonctionnel(∅).   (∀u)(∀v)(∀z)(((u,v)∈∅ et (u,z)∈∅) ⇒ v=z) — vacuement.

    L'antécédent (u,v)∈∅ est impossible (AXIOME_VIDE) ; ex falso donne v=z."""
    vu, vv, vz = var("u"), var("v"), var("z")
    cuv = E.couple(vu, vv)
    cuz = E.couple(vu, vz)
    hyp = et(appartient(cuv, E.VIDE), appartient(cuz, E.VIDE))   # (u,v)∈∅ et (u,z)∈∅
    h = N.assume(hyp)
    in_uv = conjonction_elim_gauche(h)                  # (u,v)∈∅
    n_uv = _n_in_vide(cuv)                              # ¬((u,v)∈∅)
    v_eq_z = _ex_falso(in_uv, n_uv, egal(vv, vz))       # v=z  [sous l'hypothèse]
    body = N.loi_deduction(hyp, v_eq_z)
    return N.generalisation("u", N.generalisation("v", N.generalisation("z", body)))


# ═══════════════════════════════════════════════════════════════════════════════
# (a.4)  dom(∅) = ∅   (le domaine du graphe vide est vide)
# ═══════════════════════════════════════════════════════════════════════════════
def dom_vide_egale_vide():
    """⊢ dom(∅) = ∅.   (le domaine du graphe vide est vide.)

    x∈dom ∅ ⇔ (∃y)((x,y)∈∅) [AXIOME_DOM].  ⇒ : (x,y)∈∅ impossible → ex falso x∈∅ ;
    ∃-élim.  ⇐ : x∈∅ impossible → ex falso (vide_inclus).  Par extension (A1)."""
    vx, vy = var("x"), var("y")
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car = instancie(instancie(ax_dom, E.VIDE), vx)   # x∈dom∅ ⇔ (∃y)((x,y)∈∅)
    # ⇒ : x∈dom∅ ⇒ x∈∅  via (∃y)((x,y)∈∅), branche impossible
    cxy = E.couple(vx, vy)
    hb = N.assume(appartient(cxy, E.VIDE))               # (x,y)∈∅
    n_cxy = _n_in_vide(cxy)                              # ¬((x,y)∈∅)
    x_in_vide = _ex_falso(hb, n_cxy, appartient(vx, E.VIDE))   # x∈∅  [sous (x,y)∈∅]
    fwd_inner = existe_elimination(N.loi_deduction(appartient(cxy, E.VIDE), x_in_vide), "y")
    fwd = syllogisme(equivalence_avant(dom_car), fwd_inner)    # x∈dom∅ ⇒ x∈∅
    # ⇐ : x∈∅ ⇒ x∈dom∅  par ex falso
    hx = N.assume(appartient(vx, E.VIDE))
    n_x = vide_sans_element("x")
    bwd_concl = _ex_falso(hx, n_x, appartient(vx, E.dom(E.VIDE)))
    bwd = N.loi_deduction(appartient(vx, E.VIDE), bwd_concl)    # x∈∅ ⇒ x∈dom∅
    equiv_x = conjonction_intro(fwd, bwd)               # x∈dom∅ ⇔ x∈∅
    char = N.generalisation("x", equiv_x)
    # AXIOME extension par A1 : on aligne le liant z de egalite_par_extension
    # On reconstruit avec le liant « z » attendu : char est en « x », il faut « z ».
    vz = var("z")
    ax_dom2 = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    dom_car_z = instancie(instancie(ax_dom2, E.VIDE), vz)
    czy = E.couple(vz, vy)
    hbz = N.assume(appartient(czy, E.VIDE))
    n_czy = _n_in_vide(czy)
    z_in_vide = _ex_falso(hbz, n_czy, appartient(vz, E.VIDE))
    fwd_inner_z = existe_elimination(N.loi_deduction(appartient(czy, E.VIDE), z_in_vide), "y")
    fwd_z = syllogisme(equivalence_avant(dom_car_z), fwd_inner_z)
    hxz = N.assume(appartient(vz, E.VIDE))
    bwd_z = N.loi_deduction(appartient(vz, E.VIDE),
                            _ex_falso(hxz, vide_sans_element("z"), appartient(vz, E.dom(E.VIDE))))
    equiv_z = conjonction_intro(fwd_z, bwd_z)           # z∈dom∅ ⇔ z∈∅
    char_z = N.generalisation("z", equiv_z)
    self_vide = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, E.VIDE)), a_implique_a(appartient(vz, E.VIDE))))
    return egalite_par_extension(char_z, self_vide, E.dom(E.VIDE), E.VIDE, "z")


# ═══════════════════════════════════════════════════════════════════════════════
# (a.5)  ∅ ∈ F^∅   (le graphe vide est un graphe fonctionnel de domaine ∅)
# ═══════════════════════════════════════════════════════════════════════════════
def exposant_contient_vide(f="B"):
    """⊢ ∅ ∈ F^∅.   (le graphe vide est l'application vide ∅→F : fonctionnel, dom=∅.)

    AXIOME_EXPOSANT : G∈F^∅ ⇔ (G⊂∅×F et G fonctionnel et dom G=∅).  On vérifie les
    trois conjoints pour G=∅ : ∅⊂∅×F (vide_inclus), est_fonctionnel(∅)
    (vide_est_fonctionnel), dom ∅=∅ (dom_vide_egale_vide)."""
    vF = _t(f)
    ax = N.axiome(E.theorie_exposant(E.VIDE, vF), E.axiome_exposant(E.VIDE, vF))
    car = instancie(ax, E.VIDE)                         # ∅∈F^∅ ⇔ (∅⊂∅×F et ∅ fonct et dom∅=∅)
    incl = vide_inclus(E.produit(E.VIDE, vF))           # ∅ ⊂ ∅×F
    func = vide_est_fonctionnel()                       # est_fonctionnel(∅)
    domeq = dom_vide_egale_vide()                       # dom∅=∅
    corps = conjonction_intro(conjonction_intro(incl, func), domeq)
    return N.modus_ponens(corps, equivalence_arriere(car))   # ∅∈F^∅


# ═══════════════════════════════════════════════════════════════════════════════
# (a.6)  G ∈ F^∅ ⇒ G = ∅   (∅ est l'UNIQUE graphe fonctionnel de domaine ∅)
# ═══════════════════════════════════════════════════════════════════════════════
def produit_vide_gauche(f="B"):
    """⊢ ∅×F = ∅.   (le produit cartésien de domaine vide est vide.)

    z∈∅×F ⇔ (∃p)(∃q)(z=(p,q) et p∈∅ et q∈F) [AXIOME_PRODUIT].  ⇒ : p∈∅ impossible
    → ex falso ; double ∃-élim.  ⇐ : z∈∅ impossible.  Par extension (A1)."""
    vF = _t(f)
    vz, vp, vq = var("z"), var("p"), var("q")
    ax_prod = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT)
    prod_car = instancie(instancie(instancie(ax_prod, E.VIDE), vF), vz)  # z∈∅×F ⇔ (∃p)(∃q)body
    # body = (z=(p,q) et p∈∅) et q∈F
    body = et(et(egal(vz, E.couple(vp, vq)), appartient(vp, E.VIDE)), appartient(vq, vF))
    hb = N.assume(body)
    p_in_vide = conjonction_elim_droite(conjonction_elim_gauche(hb))    # p∈∅
    n_p = vide_sans_element("p")
    z_in_vide = _ex_falso(p_in_vide, n_p, appartient(vz, E.VIDE))       # z∈∅
    fwd_q = existe_elimination(N.loi_deduction(body, z_in_vide), "q")   # (∃q)body ⇒ z∈∅
    fwd_pq = existe_elimination(fwd_q, "p")                             # (∃p)(∃q)body ⇒ z∈∅
    fwd = syllogisme(equivalence_avant(prod_car), fwd_pq)              # z∈∅×F ⇒ z∈∅
    # ⇐ : z∈∅ ⇒ z∈∅×F  par ex falso
    hz = N.assume(appartient(vz, E.VIDE))
    bwd = N.loi_deduction(appartient(vz, E.VIDE),
        _ex_falso(hz, vide_sans_element("z"), appartient(vz, E.produit(E.VIDE, vF))))
    equiv_z = conjonction_intro(fwd, bwd)              # z∈∅×F ⇔ z∈∅
    char = N.generalisation("z", equiv_z)
    self_vide = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, E.VIDE)), a_implique_a(appartient(vz, E.VIDE))))
    return egalite_par_extension(char, self_vide, E.produit(E.VIDE, vF), E.VIDE, "z")


def inclus_vide_implique_egal_vide(g="G", z="z"):
    """⊢ (G ⊂ ∅) ⇒ (G = ∅).   (tout sous-ensemble du vide est vide ; double inclusion.)

    G⊂∅ donné ; ∅⊂G (vide_inclus) toujours ; extensionnalité A1 → G=∅."""
    vG = _t(g)
    h_incl = N.assume(inclus(vG, E.VIDE))               # G⊂∅
    incl_back = vide_inclus(vG)                         # ∅⊂G
    # A1 appliqué : (G⊂∅ et ∅⊂G) ⇒ G=∅
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee
    ext = extensionnalite_appliquee(vG, E.VIDE)         # (G⊂∅ et ∅⊂G) ⇒ G=∅
    g_eq = N.modus_ponens(conjonction_intro(h_incl, incl_back), ext)   # G=∅  [sous G⊂∅]
    return N.loi_deduction(inclus(vG, E.VIDE), g_eq)    # (G⊂∅) ⇒ (G=∅)


def exposant_vide_est_vide(f="B", g="G"):
    """⊢ (G ∈ F^∅) ⇒ (G = ∅).   (∅ est l'UNIQUE graphe fonctionnel de domaine ∅.)

    G∈F^∅ ⇒ G⊂∅×F (1ᵉʳ conjoint de AXIOME_EXPOSANT).  Or ∅×F=∅ (produit_vide_gauche),
    donc G⊂∅ (Leibniz) ; tout sous-ensemble du vide est vide → G=∅."""
    vF, vG = _t(f), _t(g)
    ax = N.axiome(E.theorie_exposant(E.VIDE, vF), E.axiome_exposant(E.VIDE, vF))
    car = instancie(ax, vG)                             # G∈F^∅ ⇔ (G⊂∅×F et G fonct et domG=∅)
    h = N.assume(appartient(vG, E.exposant(E.VIDE, vF)))   # G∈F^∅
    corps = N.modus_ponens(h, equivalence_avant(car))   # (G⊂∅×F et G fonct) et domG=∅
    g_sub_prod = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # G⊂∅×F
    # ∅×F=∅ → G⊂∅  (Leibniz S6 sur le 2ᵉ argument de ⊂)
    pv = produit_vide_gauche(vF)                        # ∅×F=∅
    leib = N.s6(E.produit(E.VIDE, vF), E.VIDE, "w", inclus(vG, var("w")))   # (∅×F=∅)⇒(G⊂∅×F ⇔ G⊂∅)
    g_sub_vide = N.modus_ponens(g_sub_prod,
                    equivalence_avant(N.modus_ponens(pv, leib)))   # G⊂∅
    g_eq_vide = N.modus_ponens(g_sub_vide, inclus_vide_implique_egal_vide(vG))   # G=∅
    return N.loi_deduction(appartient(vG, E.exposant(E.VIDE, vF)), g_eq_vide)


# ═══════════════════════════════════════════════════════════════════════════════
# (b)  𝓕(∅;F) = { ((∅,∅),F) }   (l'application vide est l'unique application ∅→F)
# ═══════════════════════════════════════════════════════════════════════════════
def applications_vide_egale_singleton(f="B"):
    """⊢ 𝓕(∅; F) = { ((∅,∅), F) }.   (l'UNIQUE application de ∅ dans F est l'application
    vide ω = ((∅,∅),F) : graphe vide, source ∅, but F.  DÉRIVÉ, pas postulé.)

    AXIOME_APPLICATIONS : t∈𝓕(∅;F) ⇔ (∃G)(t=((G,∅),F) et G∈F^∅).
      ⇒ : sous le corps, G∈F^∅ ⇒ G=∅ (exposant_vide_est_vide), donc
          t=((G,∅),F)=((∅,∅),F)=ω ; ∃-élim.
      ⇐ : t=ω ⇒ (∃G)(...) avec témoin G:=∅ (∅∈F^∅ par exposant_contient_vide,
          et ω=((∅,∅),F) par réflexivité).
    Donc t∈𝓕(∅;F) ⇔ t=ω ⇔ t∈{ω}.  Par extension (A1)."""
    vF = _t(f)
    omega = E.application_vide(vF)                      # ω = ((∅,∅),F)
    s_omega = E.singleton(omega)                        # {ω}
    # Liant de travail « z » (et non « t ») pour que la généralisation finale et
    # egalite_par_extension (dont A1/inclus fixent le liant à « z ») coïncident.
    vz, vG = var("z"), var("G")
    ax = N.axiome(E.theorie_applications(E.VIDE, vF), E.axiome_applications(E.VIDE, vF))
    app_car = instancie(ax, vz)                         # z∈𝓕(∅;F) ⇔ (∃G)(z=((G,∅),F) et G∈F^∅)
    # corps existentiel : body(G) = (z=((G,∅),F) et G∈F^∅)
    triple = E.couple(E.couple(vG, E.VIDE), vF)         # ((G,∅),F)
    body = et(egal(vz, triple), appartient(vG, E.exposant(E.VIDE, vF)))
    # ── ⇒ : (∃G)body ⇒ z=ω ──────────────────────────────────────────────────────
    hb = N.assume(body)
    z_eq_triple = conjonction_elim_gauche(hb)           # z=((G,∅),F)
    G_in = conjonction_elim_droite(hb)                  # G∈F^∅
    G_eq_vide = N.modus_ponens(G_in, exposant_vide_est_vide(vF))   # G=∅
    # ((G,∅),F)=((∅,∅),F)=ω  via congruence sur le coin G (trou w)
    triple_eq_omega = N.modus_ponens(G_eq_vide,
        congruence_terme(vG, E.VIDE, E.couple(E.couple(var("w"), E.VIDE), vF)))   # ((G,∅),F)=ω
    z_eq_omega = composer_egalites(z_eq_triple, triple_eq_omega)   # z=ω
    fwd_inner = existe_elimination(N.loi_deduction(body, z_eq_omega), "G")   # (∃G)body ⇒ z=ω
    fwd = syllogisme(equivalence_avant(app_car), fwd_inner)        # z∈𝓕(∅;F) ⇒ z=ω
    # ── ⇐ : z=ω ⇒ (∃G)body  via témoin G:=∅ ────────────────────────────────────
    z_eq_omega_hyp = N.assume(egal(vz, omega))          # z=ω
    vide_in_exp = exposant_contient_vide(vF)            # ∅∈F^∅
    # (G|→∅)body = (z=((∅,∅),F) et ∅∈F^∅) = (z=ω et ∅∈F^∅)
    wit = conjonction_intro(z_eq_omega_hyp, vide_in_exp)
    ex_G = N.modus_ponens(wit, N.s5(body, E.VIDE, "G"))            # (∃G)body
    in_app = N.modus_ponens(ex_G, equivalence_arriere(app_car))   # z∈𝓕(∅;F)  [sous z=ω]
    bwd = N.loi_deduction(egal(vz, omega), in_app)                # z=ω ⇒ z∈𝓕(∅;F)
    eq_z_omega = conjonction_intro(fwd, bwd)            # z∈𝓕(∅;F) ⇔ z=ω
    # ── z=ω ⇔ z∈{ω} ────────────────────────────────────────────────────────────
    s_mem = singleton_membre(vz, omega)                 # z∈{ω} ⇔ z=ω
    z_omega_z_s = conjonction_intro(equivalence_arriere(s_mem), equivalence_avant(s_mem))  # z=ω ⇔ z∈{ω}
    chain = equivalence_transitivite(eq_z_omega, z_omega_z_s)      # z∈𝓕(∅;F) ⇔ z∈{ω}
    char = N.generalisation("z", chain)
    self_s = N.generalisation("z", conjonction_intro(
        a_implique_a(appartient(vz, s_omega)), a_implique_a(appartient(vz, s_omega))))
    return egalite_par_extension(char, self_s, E.applications(E.VIDE, vF), s_omega, "z")


# ═══════════════════════════════════════════════════════════════════════════════
# (c)  a^0 = 1   (Proposition 11, E.III.3.5)
# ═══════════════════════════════════════════════════════════════════════════════
def eq_applications_vide_singleton(f="B"):
    """⊢ Eq(𝓕(∅; B), {∅}).   (l'ensemble des applications de ∅ dans B est équipotent
    au singleton {∅} = 1, à équipotence près.)

    𝓕(∅;B) = {ω} (applications_vide_egale_singleton) ; Eq({ω}, {∅}) (eq_singletons,
    deux singletons sont équipotents) ; on transporte le 1ᵉʳ argument de Eq par
    l'égalité d'ensembles via S6 (Leibniz).

    NB : le but B ne doit PAS être nommé « F » — la relation Eq(·,·) lie elle-même
    « F » (Eq(X,Y) := (∃F)bij), donc un ensemble nommé F serait capturé par ce liant.
    Idem pour eq_singletons (témoin var(\"F\")).  Le défaut « B » et tout nom ≠ F,x,y,z
    conviennent (le résultat est valable pour TOUT ensemble, indépendamment du nom)."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_zero_plus_un import eq_singletons
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent
    vF = _t(f)
    omega = E.application_vide(vF)                      # ω
    s_omega = E.singleton(omega)                        # {ω}
    s_vide = E.singleton(E.VIDE)                        # {∅} = 1
    AF = E.applications(E.VIDE, vF)                     # 𝓕(∅;F)
    eq_set = applications_vide_egale_singleton(vF)      # 𝓕(∅;F) = {ω}
    eq_sing = eq_singletons(omega, E.VIDE)              # Eq({ω}, {∅})
    leib = N.s6(AF, s_omega, "w", equipotent(var("w"), s_vide))   # (𝓕=...{ω}) ⇒ (Eq(𝓕,{∅}) ⇔ Eq({ω},{∅}))
    equiv_eq = N.modus_ponens(eq_set, leib)
    return N.modus_ponens(eq_sing, equivalence_arriere(equiv_eq))   # Eq(𝓕(∅;F), {∅})


def exposant_zero_egale_un(f="B"):
    """⊢ Card(𝓕(∅; B)) = Card({∅}).   (= a^0 = 1 ; PROPOSITION 11, E.III.3.5, CLOS.)

    a^0 = exposant_cardinal_binaire(a, 0) = Card(𝓕(∅; B)) où a = Card B (0 = ∅).
    Eq(𝓕(∅;B), {∅}) (eq_applications_vide_singleton) ; la Proposition 1 (sens direct,
    version TERME) conclut Card(𝓕(∅;B)) = Card({∅}) = 1.  But B ≠ « F » (cf. supra)."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
    vF = _t(f)
    AF = E.applications(E.VIDE, vF)                     # 𝓕(∅;F)  (support de a^0)
    s_vide = E.singleton(E.VIDE)                        # {∅}
    eq = eq_applications_vide_singleton(vF)            # Eq(𝓕(∅;F), {∅})
    prop1 = _prop1_direct_t(AF, s_vide)                # Eq(𝓕(∅;F),{∅}) ⇒ Card(𝓕(∅;F))=Card({∅})
    return N.modus_ponens(eq, prop1)                   # Card(𝓕(∅;F)) = Card({∅}) = a^0 = 1


def exposant_cardinal_zero_egale_un(a="a"):
    """⊢ a ^ 0 = Card({∅}).   (= 1 ; PROPOSITION 11, a^0 = 1, formulée sur l'OPÉRATEUR
    exposant_cardinal_binaire pour un cardinal a quelconque.  CLOS.)

    Par définition exposant_cardinal_binaire(a, 0) = Card(𝓕(0; a)) = Card(𝓕(∅; a)).
    On instancie exposant_zero_egale_un au terme a (le but a = Card(a) lui-même pour
    un cardinal) : Card(𝓕(∅; a)) = Card({∅}).  La conclusion est LITTÉRALEMENT
    exposant_cardinal_binaire(a, 0) = Card({∅}) = 1."""
    va = _t(a)
    # exposant_zero_egale_un(a) : Card(applications(∅, a)) = Card({∅}),
    # et exposant_cardinal_binaire(a, 0) = cardinal(applications(∅, a)) (par déf, 0=∅).
    return exposant_zero_egale_un(va)


__all__ = ["exposant_cardinal_binaire",
           "vide_inclus", "vide_est_fonctionnel", "dom_vide_egale_vide",
           "exposant_contient_vide", "produit_vide_gauche",
           "inclus_vide_implique_egal_vide", "exposant_vide_est_vide",
           "applications_vide_egale_singleton",
           "eq_applications_vide_singleton", "exposant_zero_egale_un",
           "exposant_cardinal_zero_egale_un"]
