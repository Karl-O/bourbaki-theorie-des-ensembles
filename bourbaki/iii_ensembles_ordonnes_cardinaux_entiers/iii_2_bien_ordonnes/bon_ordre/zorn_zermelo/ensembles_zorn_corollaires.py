"""§III.2.4 — Corollaire 1 du Théorème 2 (Zorn) : maximal m ≥ a  (E III.21 L.11-14).

Bourbaki, COROLLAIRE 1 : « Soient E un ensemble ordonné inductif, et a un élément
de E ; il existe un élément maximal m de E tel que m ≥ a.  En effet, il résulte de
la déf. 3 que l'ensemble F des éléments x ≥ a de E est inductif, et un élément
maximal de F est aussi élément maximal de E. »

DÉRIVÉ ICI, à partir du THÉORÈME 2 déjà CLOS (`zorn_theoreme`) :

    { est_inductif(G,E), a∈E }  ⊢  (∃m)( element_maximal(G,E,m) et (a,m)∈G ).

CLÉ (aucune infrastructure « ordre induit » requise) : `est_ordre(G,E)` =
reflexivite_sur(G,E) ∧ antisymetrie(G) ∧ transitivite_rel(G) ; antisymétrie et
transitivité ne dépendent PAS du support, et la réflexivité sur F ⊂ E se transfère
depuis E.  On applique donc Zorn au MÊME graphe G sur le sous-ensemble

    F := { x ∈ E | (a,x) ∈ G }   (les éléments ≥ a),

terme opaque + axiome de membership DÉDIÉ (theorie_ensembles reste = 22).

ROUTE (le livre) : F inductif (toute chaîne de F est une chaîne de E, dont un
majorant m vérifie m ≥ a — via un élément de la chaîne, ou a lui-même si elle est
vide — donc m ∈ F) ; Zorn sur (G,F) donne un maximal m ; m ∈ F ⇒ m ≥ a, et m
maximal dans F ⇒ maximal dans E (x ≥ m ≥ a ⇒ x ∈ F ⇒ x = m).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, egal, et, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant, equivalence_arriere, cas, tiers_exclu,
    inclusion_transitive, antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, reflexivite_sur, antisymetrie, transitivite_rel, majorant,
    element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine, est_inductif, enonce_non_vide,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import (
    zorn_theoreme,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _cd(t, u, G):
    """(t,u) ∈ G."""
    return appartient(E.couple(_t(t), _t(u)), _t(G))


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible  (ex falso quodlibet, S2+MP)."""
    a = thm_a.conclusion
    imp = N.modus_ponens(thm_na, N.s2(non(a), cible))
    return N.modus_ponens(thm_a, imp)


# ════════════════════════════════════════════════════════════════════════════
#  F := { x ∈ E | (a,x) ∈ G }   (opaque + axiome DÉDIÉ ; theorie reste 22)
# ════════════════════════════════════════════════════════════════════════════
def _F(G, E_set, a):
    return app("F_maj_de_a", _t(G), _t(E_set), _t(a))


def _axiome_F(G, E_set, a, x="xF"):
    vx = var(x)
    return pourtout(x, equiv(appartient(vx, _F(G, E_set, a)),
                             et(appartient(vx, _t(E_set)), _cd(a, vx, G))))


def _theorie_F(G, E_set, a, x="xF"):
    return N.Theorie("F-elements-superieurs-a-a", [_axiome_F(G, E_set, a, x)])


def _membre_F(G, E_set, a, t, x="xF"):
    """⊢ ( t ∈ F ⇔ ( t ∈ E et (a,t) ∈ G ) )  (instance de l'axiome de F ; clos)."""
    ax = N.axiome(_theorie_F(G, E_set, a, x), _axiome_F(G, E_set, a, x))
    return instancie(ax, _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  Fondation : F ⊂ E, a ∈ F, F ≠ ∅, est_ordre(G,F)  (sous {est_ordre(G,E), a∈E})
# ════════════════════════════════════════════════════════════════════════════
def _F_inclus_E(G, E_set, a):
    """⊢ inclus(F, E)   (0 hyp) : x∈F ⇒ x∈E par l'axiome de F."""
    F = _F(G, E_set, a)
    hz = N.assume(appartient(var("z"), F))
    z_in_E = conjonction_elim_gauche(
        N.modus_ponens(hz, equivalence_avant(_membre_F(G, E_set, a, var("z")))))
    res = N.generalisation("z", N.loi_deduction(appartient(var("z"), F), z_in_E))
    assert res.conclusion == inclus(F, _t(E_set)), "F⊂E : forme inattendue"
    return res


def _refl_de_ordre(thm_ordre, G, E_set):
    """De ⊢ est_ordre(G,E) [ou hyp], extrait reflexivite_sur / antisym / trans."""
    ro = conjonction_elim_gauche(conjonction_elim_gauche(thm_ordre))   # reflexivite_sur(G,E)
    asym = conjonction_elim_droite(conjonction_elim_gauche(thm_ordre)) # antisymetrie(G)
    tr = conjonction_elim_droite(thm_ordre)                            # transitivite_rel(G)
    return ro, asym, tr


def _a_dans_F(G, E_set, a, h_ordre, h_a_in_E):
    """{est_ordre(G,E), a∈E} ⊢ a ∈ F   (a∈E et (a,a)∈G par réflexivité)."""
    ro, _, _ = _refl_de_ordre(h_ordre, G, E_set)
    aa = N.modus_ponens(h_a_in_E, instancie(ro, _t(a)))          # (a,a)∈G
    corps = conjonction_intro(h_a_in_E, aa)                      # a∈E et (a,a)∈G
    return N.modus_ponens(corps, equivalence_arriere(_membre_F(G, E_set, a, a)))  # a∈F


def _est_ordre_F(G, E_set, a, h_ordre):
    """{est_ordre(G,E)} ⊢ est_ordre(G,F)  (réflexivité transférée ; antisym/trans identiques)."""
    F = _F(G, E_set, a)
    ro, asym, tr = _refl_de_ordre(h_ordre, G, E_set)
    # reflexivite_sur(G,F) : x∈F ⇒ x∈E (axiome F) ⇒ (x,x)∈G (réflexivité sur E)
    hx = N.assume(appartient(var("x"), F))
    x_in_E = conjonction_elim_gauche(
        N.modus_ponens(hx, equivalence_avant(_membre_F(G, E_set, a, var("x")))))
    xx = N.modus_ponens(x_in_E, instancie(ro, var("x")))        # (x,x)∈G
    refl_F = N.generalisation("x", N.loi_deduction(appartient(var("x"), F), xx))
    assert refl_F.conclusion == reflexivite_sur(_t(G), F), "reflexivite_sur(G,F) inattendue"
    res = conjonction_intro(conjonction_intro(refl_F, asym), tr)
    assert res.conclusion == est_ordre(_t(G), F), "est_ordre(G,F) inattendu"
    return res


def _est_inductif_F(G, E_set, a, h_indE, h_a_in_E):
    """{est_inductif(G,E), a∈E} ⊢ est_inductif(G,F).

    Toute chaîne C de F est une chaîne de E (C⊂F⊂E) ; un majorant m de C dans E
    est dans F — car si C a un élément c, m ≥ c ≥ a (donc m∈F par transitivité) ;
    et si C est vide, a lui-même majore C dans F.  D'où (∃m) majorant(G,C,m,F)."""
    vG, vE, va = _t(G), _t(E_set), _t(a)
    F = _F(G, E_set, a)
    h_ordre = conjonction_elim_gauche(h_indE)                 # est_ordre(G,E)
    ind_E_all = conjonction_elim_droite(h_indE)               # (∀C)(chaine(G,E,C)⇒∃m maj(G,C,m,E))
    ordre_F = _est_ordre_F(G, E_set, a, h_ordre)              # est_ordre(G,F)
    F_sub_E = _F_inclus_E(G, E_set, a)                        # F⊂E
    a_in_F = _a_dans_F(G, E_set, a, h_ordre, h_a_in_E)        # a∈F
    _, _, tr = _refl_de_ordre(h_ordre, G, E_set)             # transitivite_rel(G)

    vC = var("C")
    hchain = N.assume(chaine(vG, F, vC))                      # C⊂F et totalement_ordonne(G,C)
    C_sub_F = conjonction_elim_gauche(hchain)
    tot_C = conjonction_elim_droite(hchain)
    # C⊂E au binder 'z' (celui de chaine) : z∈C ⇒ z∈F ⇒ z∈E
    z_in_F = N.modus_ponens(N.assume(appartient(var("z"), vC)), instancie(C_sub_F, var("z")))
    z_in_E = N.modus_ponens(z_in_F, instancie(F_sub_E, var("z")))
    C_sub_E = N.generalisation("z", N.loi_deduction(appartient(var("z"), vC), z_in_E))  # inclus(C,E)@z
    chain_C_E = conjonction_intro(C_sub_E, tot_C)             # chaine(G,E,C)
    ex_maj_E = N.modus_ponens(chain_C_E, instancie(ind_E_all, vC))  # ∃m maj(G,C,m,E)

    cible = existe("m", majorant(vG, vC, var("m"), F))        # ∃m maj(G,C,m,F)
    vm = var("m")
    hmajE = N.assume(majorant(vG, vC, vm, vE))                # m∈E et (∀x)(x∈C⇒(x,m)∈G)
    m_in_E = conjonction_elim_gauche(hmajE)
    m_maj = conjonction_elim_droite(hmajE)                    # (∀x)(x∈C⇒(x,m)∈G)

    exC = existe("xc", appartient(var("xc"), vC))
    te = tiers_exclu(exC)                                     # exC ou ¬exC

    # ── branche ∃x(x∈C) : m∈F (m ≥ c ≥ a), donc maj(G,C,m,F) ──
    vc = var("xc")
    hc = N.assume(appartient(vc, vC))                        # c∈C
    c_in_F = N.modus_ponens(hc, instancie(C_sub_F, vc))      # c∈F
    a_c = conjonction_elim_droite(
        N.modus_ponens(c_in_F, equivalence_avant(_membre_F(G, E_set, a, vc))))  # (a,c)∈G
    c_m = N.modus_ponens(hc, instancie(m_maj, vc))           # (c,m)∈G
    a_m = N.modus_ponens(conjonction_intro(a_c, c_m),
                         instancie(instancie(instancie(tr, va), vc), vm))       # (a,m)∈G
    m_in_F = N.modus_ponens(conjonction_intro(m_in_E, a_m),
                            equivalence_arriere(_membre_F(G, E_set, a, vm)))    # m∈F
    majF_m = conjonction_intro(m_in_F, m_maj)                # majorant(G,C,m,F)
    ex_majF_c = N.modus_ponens(majF_m, N.s5(majorant(vG, vC, vm, F), vm, "m"))  # cible
    branche_ex = existe_elimination(N.loi_deduction(appartient(vc, vC), ex_majF_c), "xc")  # exC⇒cible

    # ── branche ¬∃x(x∈C) : a majore C dans F (vacuité) ──
    h_negC = N.assume(non(exC))
    hxC = N.assume(appartient(var("x"), vC))                 # x∈C  (réfutation)
    exC_from_x = N.modus_ponens(hxC, N.s5(appartient(var("xc"), vC), var("x"), "xc"))  # exC
    xa = _ex_falso(exC_from_x, h_negC, _cd(var("x"), va, G)) # (x,a)∈G
    vac = N.generalisation("x", N.loi_deduction(appartient(var("x"), vC), xa))  # (∀x)(x∈C⇒(x,a)∈G)
    majF_a = conjonction_intro(a_in_F, vac)                  # majorant(G,C,a,F)
    ex_majF_a = N.modus_ponens(majF_a, N.s5(majorant(vG, vC, var("m"), F), va, "m"))  # cible
    branche_neg = N.loi_deduction(non(exC), ex_majF_a)       # ¬exC⇒cible

    maj_F_under_majE = cas(te, branche_ex, branche_neg)      # cible  [sous hmajE + …]
    inner = N.loi_deduction(majorant(vG, vC, vm, vE), maj_F_under_majE)  # maj(G,C,m,E)⇒cible
    maj_F_exists = N.modus_ponens(ex_maj_E, existe_elimination(inner, "m"))  # cible
    imp_C = N.loi_deduction(chaine(vG, F, vC), maj_F_exists) # chaine(G,F,C)⇒cible
    gen_C = N.generalisation("C", imp_C)                     # (∀C)(…)

    res = conjonction_intro(ordre_F, gen_C)
    assert res.conclusion == est_inductif(vG, F), "est_inductif(G,F) inattendu"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 (E III.21 L.11-14) — assemblage
# ════════════════════════════════════════════════════════════════════════════
def enonce_cor1(G="Gzc", E_set="Ezc", a="azc", m="m"):
    """(∃m)( element_maximal(G,E,m) et (a,m)∈G )  — « un maximal m ≥ a »."""
    vG, vE, va = var(G), var(E_set), var(a)
    return existe(m, et(element_maximal(vG, vE, var(m)), _cd(va, var(m), vG)))


# @livre Ch.III §2.4 Cor.1 | E III.21 L.11-12 | PDF p.124
# @livre Ch.III §2.4 Demo.- | E III.21 L.13-14 | PDF p.124
def zorn_cor1_maximal_superieur(G="Gzc", E_set="Ezc", a="azc"):
    """🎯 { est_inductif(G,E), a∈E } ⊢ (∃m)( element_maximal(G,E,m) et (a,m)∈G ).

    COROLLAIRE 1 du Théorème 2 (Zorn), E III.21 : on applique Zorn au MÊME graphe G
    sur F = { x∈E | (a,x)∈G } (inductif, cf. _est_inductif_F) ; le maximal m de F
    vérifie m∈F ⇒ (a,m)∈G, et est maximal dans E (x≥m≥a ⇒ x∈F ⇒ x=m)."""
    vG, vE, va = var(G), var(E_set), var(a)
    F = _F(vG, vE, va)
    h_indE = N.assume(est_inductif(vG, vE))
    h_a_in_E = N.assume(appartient(va, vE))
    h_ordre = conjonction_elim_gauche(h_indE)                # est_ordre(G,E)
    _, _, tr = _refl_de_ordre(h_ordre, vG, vE)

    ordre_F = _est_ordre_F(vG, vE, va, h_ordre)              # est_ordre(G,F)
    ind_F = _est_inductif_F(vG, vE, va, h_indE, h_a_in_E)    # est_inductif(G,F)
    a_in_F = _a_dans_F(vG, vE, va, h_ordre, h_a_in_E)        # a∈F
    F_ne = N.modus_ponens(a_in_F, N.s5(appartient(var("x"), F), va, "x"))  # F≠∅

    # ── Zorn instancié à (G,F) ──
    zt = zorn_theoreme(G=G, E_set="EzForZorn")               # clos, libres G, EzForZorn
    zt_F = instancie(N.generalisation("EzForZorn", zt), F)   # ANTE(G,F) ⇒ ∃m elem_max(G,F,m)
    ante, _ = antecedent_consequent(zt_F.conclusion)
    ante_proof = conjonction_intro(conjonction_intro(ordre_F, ind_F), F_ne)
    assert ante_proof.conclusion == ante, "antécédent de Zorn(G,F) non reconstitué"
    ex_max_F = N.modus_ponens(ante_proof, zt_F)              # ∃m element_maximal(G,F,m)

    # ── transfert : maximal de F ⇒ maximal de E, et m ≥ a ──
    vm = var("m")
    hmaxF = N.assume(element_maximal(vG, F, vm))             # m∈F et (∀x)((x∈F et (m,x)∈G)⇒x=m)
    m_in_F = conjonction_elim_gauche(hmaxF)
    m_max_F = conjonction_elim_droite(hmaxF)
    m_mem = N.modus_ponens(m_in_F, equivalence_avant(_membre_F(vG, vE, va, vm)))  # m∈E et (a,m)∈G
    m_in_E = conjonction_elim_gauche(m_mem)
    a_m = conjonction_elim_droite(m_mem)                    # (a,m)∈G

    hx = N.assume(et(appartient(var("x"), vE), _cd(vm, var("x"), vG)))  # x∈E et (m,x)∈G
    x_in_E = conjonction_elim_gauche(hx)
    m_x = conjonction_elim_droite(hx)
    a_x = N.modus_ponens(conjonction_intro(a_m, m_x),
                         instancie(instancie(instancie(tr, va), vm), var("x")))   # (a,x)∈G
    x_in_F = N.modus_ponens(conjonction_intro(x_in_E, a_x),
                            equivalence_arriere(_membre_F(vG, vE, va, var("x"))))  # x∈F
    x_eq_m = N.modus_ponens(conjonction_intro(x_in_F, m_x), instancie(m_max_F, var("x")))  # x=m
    maxE_body = N.generalisation("x", N.loi_deduction(
        et(appartient(var("x"), vE), _cd(vm, var("x"), vG)), x_eq_m))
    max_E = conjonction_intro(m_in_E, maxE_body)            # element_maximal(G,E,m)
    assert max_E.conclusion == element_maximal(vG, vE, vm), "element_maximal(G,E,m) inattendu"

    concl_m = conjonction_intro(max_E, a_m)                 # element_maximal(G,E,m) et (a,m)∈G
    cible_corps = et(element_maximal(vG, vE, var("m")), _cd(va, var("m"), vG))
    ex_concl = N.modus_ponens(concl_m, N.s5(cible_corps, vm, "m"))  # ∃m (…)
    transfer = existe_elimination(
        N.loi_deduction(element_maximal(vG, F, vm), ex_concl), "m")  # ∃m elem_max(G,F,m) ⇒ cible
    res = N.modus_ponens(ex_max_F, transfer)               # cible

    assert res.conclusion == enonce_cor1(G, E_set, a), "Cor.1 : conclusion inattendue"
    assert res.hypotheses == frozenset({est_inductif(vG, vE), appartient(va, vE)}), \
        "Cor.1 : hypothèses ≠ {est_inductif(G,E), a∈E}"
    return res


__all__ = ["enonce_cor1", "zorn_cor1_maximal_superieur"]
