"""§III.6.2 — C62, LE DOMAINE DE LA FONCTION GLOBALE :  dom(f) = E   (f = ⋃𝔇_tot).

Suite de `ensembles_c62_fonction_globale` (f construite, FONCTIONNELLE, CLOS).
Ici la DOUBLE INCLUSION du domaine :

  (⊆) `dom_fonction_inclus_e`   ⊢ dom(f) ⊂ E                          [CLOS, 0 hyp]
      — tout antécédent w de f vient d'un couple d'un essai p (réunion + AXIOME_DOM),
        dont le domaine est seg(n)∪{n} : w∈seg ⇒ w∈E (caractérisation du segment) ;
        w∈{n} ⇒ w=n∈E (le n de la sélection S8 est dans E).  Preuve par cas.

  (⊇) `e_inclus_dom_fonction`   { bo, essais_bien_formes, rule_codomain }
                                 ⊢ E ⊂ dom(f)                        [3 hyps = C62]
      — pour n∈E, C62 (`c62_recursion_sur_N`) fournit un essai p_n ; il est membre
        de 𝔇_tot (`essai_dans_Dtot` : ambiant via le pont bien-formes + sélection S8
        au témoin n) ; n∈dom(p_n)=seg∪{n} ⇒ (n,y)∈p_n ⇒ (n,y)∈⋃𝔇_tot ⇒ n∈dom(f).

  🎯 `dom_fonction_globale`     { bo, essais_bien_formes, rule_codomain }
                                 ⊢ dom(f) = E     [antisymétrie de ⊂ (A1)].

INVARIANT : theorie_ensembles() = 22.  Rien postulé ; les seules hypothèses sont les
TROIS résidus honnêtes de C62 (le sens ⊆ n'en a même aucune).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    est_essai, dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_pont import (
    essai_dans_parties_depuis_bien_formes, essais_bien_formes, rule_codomain,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, _inst_union_famille, _membre_dans_union,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import c62_recursion_sur_N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    Dtot, _inst_Dtot, fonction_globale, ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    membre_reunion_graphes, antecedent_dans_domaine,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import membre_segment
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import inclusion_antisymetrique


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _dom_car(f, u):
    """⊢ ( u∈dom(F) ) ⇔ ( (∃y)( (u,y)∈F ) )   (AXIOME_DOM instancié aux termes)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _t(f)), _t(u))


# ════════════════════════════════════════════════════════════════════════════
#  BRIQUE — l'essai témoin de C62 est MEMBRE de 𝔇_tot (ambiant + sélection S8).
# ════════════════════════════════════════════════════════════════════════════
def essai_dans_Dtot(vh, nt, e="Enat", G="Gle", V="Uval", p="pess"):
    """{ n∈E, est_essai(p,n), essais_bien_formes, rule_codomain } ⊢ p∈𝔇_tot.

    L'ambiant p∈𝔓(E×V) vient du pont `essai_dans_parties_depuis_bien_formes`
    (bien-formes + rule-codomain) ; le sélecteur (∃n')(n'∈E ∧ est_essai(p,n')) par S5
    au témoin n ; l'axiome S8 (sens ⇐) conclut.  nt : le point (Terme)."""
    R = _graphe_R(G)
    ve, vp = _t(e), var(p)
    nt = _t(nt)
    Dt = Dtot(e, V)

    amb = essai_dans_parties_depuis_bien_formes(vh, e, G, nt, V, p=p, z="zess")
    # sélecteur : (∃nDt)( nDt∈E ∧ est_essai(p,nDt) ), témoin nDt := n
    h_n = N.assume(appartient(nt, ve))                           # n∈E        [HONNÊTE]
    h_essai = N.assume(est_essai(vp, vh, G, ve, nt))             # essai(p,n) [HONNÊTE]
    wit = conjonction_intro(h_n, h_essai)
    body = et(appartient(var("nDt"), ve), est_essai(vp, vh, G, ve, var("nDt")))
    sel = N.modus_ponens(wit, N.s5(body, nt, "nDt"))             # (∃nDt)(…)
    corps = conjonction_intro(amb, sel)                          # amb ∧ sel
    res = N.modus_ponens(corps, equivalence_arriere(_inst_Dtot(vh, e, G, vp, V)))

    assert res.conclusion == appartient(vp, Dt), "essai_dans_Dtot : ≠ p∈𝔇_tot"
    assert appartient(nt, ve) in res.hypotheses, "essai_dans_Dtot : n∈E absente"
    assert est_essai(vp, vh, G, ve, nt) in res.hypotheses, "essai_dans_Dtot : essai absente"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (⊆) — dom(f) ⊂ E   [CLOS, 0 hyp].
# ════════════════════════════════════════════════════════════════════════════
def dom_fonction_inclus_e(vh, e="Enat", G="Gle", V="Uval"):
    """⊢ dom(f) ⊂ E,   f = ⋃𝔇_tot                                     [CLOS, 0 hyp].

    w∈dom(f) ⇒ (w,y)∈⋃𝔇 [AXIOME_DOM] ⇒ (∃p∈𝔇)((w,y)∈p) [réunion-famille] ⇒
    w∈dom(p)=seg(n)∪{n} [S8 + est_essai] ⇒ w∈E (par cas : segment ⊆ E / w=n∈E)."""
    R = _graphe_R(G)
    ve = _t(e)
    Dt = Dtot(e, V)
    f = fonction_globale(e, V)
    vz = var("z")

    h_z = N.assume(appartient(vz, E.dom(f)))                     # z∈dom f
    exy = N.modus_ponens(h_z, equivalence_avant(_dom_car(f, vz)))  # (∃y)((z,y)∈f)

    # ── sous le témoin y : (z,y)∈⋃𝔇 ────────────────────────────────────────────
    vy = var("y")
    cpl = E.couple(vz, vy)
    h_y = N.assume(appartient(cpl, f))
    expu = N.modus_ponens(h_y, equivalence_avant(_inst_union_famille(Dt, cpl)))
    # (∃punion)( punion∈𝔇 ∧ (z,y)∈punion )

    # ── sous le témoin punion ──────────────────────────────────────────────────
    vpu = var("punion")
    corps_pu = et(appartient(vpu, Dt), appartient(cpl, vpu))
    h_pu = N.assume(corps_pu)
    puD = conjonction_elim_gauche(h_pu)                          # punion∈𝔇
    zyp = conjonction_elim_droite(h_pu)                          # (z,y)∈punion
    sel = conjonction_elim_droite(N.modus_ponens(
        puD, equivalence_avant(_inst_Dtot(vh, e, G, vpu, V))))   # (∃nDt)(n∈E ∧ essai(punion,n))

    # ── sous le témoin nDt ─────────────────────────────────────────────────────
    vn = var("nDt")
    corps_n = et(appartient(vn, ve), est_essai(vpu, vh, G, ve, vn))
    h_n = N.assume(corps_n)
    nE = conjonction_elim_gauche(h_n)                            # n∈E
    essai = conjonction_elim_droite(h_n)                         # est_essai(punion,n)
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(essai))   # dom punion = seg∪{n}
    de = dom_essai(G, ve, vn)                                    # seg(n)∪{n}
    seg = E.segment_extremite(_t(G), ve, vn)

    z_in_dompu = N.modus_ponens(zyp, antecedent_dans_domaine(vz, vy, vpu))  # z∈dom punion
    # transport le long de dom punion = seg∪{n}
    equivF = N.modus_ponens(dom_eq, N.s6(E.dom(vpu), de, "wdm",
                                         appartient(vz, var("wdm"))))
    z_in_de = N.modus_ponens(z_in_dompu, equivalence_avant(equivF))        # z∈seg∪{n}
    disj = N.modus_ponens(z_in_de, equivalence_avant(
        membre_reunion_graphes(seg, E.singleton(vn), vz)))       # (z∈seg) ∨ (z∈{n})

    # cas gauche : z∈seg ⇒ z∈E  (caractérisation du segment : z∈E ∧ R{z,n} ∧ z≠n)
    ms = membre_segment(G, e, vn, vz)                            # (z∈seg) ⇔ ((z∈E∧R)∧z≠n)
    h_seg = N.assume(appartient(vz, seg))
    car = N.modus_ponens(h_seg, equivalence_avant(ms))
    zE_g = conjonction_elim_gauche(conjonction_elim_gauche(car)) # z∈E
    imp_g = N.loi_deduction(appartient(vz, seg), zE_g)

    # cas droit : z∈{n} ⇒ z=n ⇒ z∈E  (Leibniz depuis n∈E)
    h_sing = N.assume(appartient(vz, E.singleton(vn)))
    z_eq_n = N.modus_ponens(h_sing, equivalence_avant(singleton_membre(vz, vn)))  # z=n
    eqv = N.modus_ponens(z_eq_n, N.s6(vz, vn, "wsm", appartient(var("wsm"), ve)))
    zE_d = N.modus_ponens(nE, equivalence_arriere(eqv))          # z∈E
    imp_d = N.loi_deduction(appartient(vz, E.singleton(vn)), zE_d)

    zE = cas(disj, imp_g, imp_d)                                 # z∈E

    # ── éliminations : nDt, punion, y ──────────────────────────────────────────
    zE = N.modus_ponens(sel, existe_elimination(N.loi_deduction(corps_n, zE), "nDt"))
    zE = N.modus_ponens(expu, existe_elimination(N.loi_deduction(corps_pu, zE), "punion"))
    zE = N.modus_ponens(exy, existe_elimination(N.loi_deduction(appartient(cpl, f), zE), "y"))

    res = N.generalisation("z", N.loi_deduction(appartient(vz, E.dom(f)), zE))
    cible = inclus(E.dom(f), ve)
    assert res.conclusion == cible, "dom_fonction_inclus_e : ≠ dom(f)⊂E"
    assert res.est_clos, "dom_fonction_inclus_e : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (⊇) — E ⊂ dom(f)   [3 hyps = résidus C62].
# ════════════════════════════════════════════════════════════════════════════
def e_inclus_dom_fonction(vh, e="Enat", G="Gle", V="Uval"):
    """{ bo, essais_bien_formes, rule_codomain } ⊢ E ⊂ dom(f),  f = ⋃𝔇_tot.

    Pour z∈E, C62 donne un essai p_z (est_essai(p_z,z)) ; p_z∈𝔇_tot
    (`essai_dans_Dtot`) ; z∈dom(p_z)=seg∪{z} (z∈{z}) ; (z,y)∈p_z [AXIOME_DOM] ;
    (z,y)∈⋃𝔇 [réunion-famille] ; z∈dom(f) [AXIOME_DOM ⇐]."""
    R = _graphe_R(G)
    ve = _t(e)
    Dt = Dtot(e, V)
    f = fonction_globale(e, V)
    vz = var("z")

    h_z = N.assume(appartient(vz, ve))                           # z∈E
    c62 = c62_recursion_sur_N(vh, e, G, V)                       # {bo,ebf,rc} ⊢ (∀x∈E)(∃p)essai
    exp = N.modus_ponens(h_z, instancie(c62, vz))                # (∃pess) est_essai(pess,z)

    # ── sous le témoin pess ────────────────────────────────────────────────────
    vp = var("pess")
    corps_p = est_essai(vp, vh, G, ve, vz)
    h_p = N.assume(corps_p)
    pDt = essai_dans_Dtot(vh, vz, e, G, V, "pess")               # {z∈E, essai, ebf, rc} ⊢ pess∈𝔇
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(h_p))   # dom pess = seg∪{z}
    de = dom_essai(G, ve, vz)
    seg = E.segment_extremite(_t(G), ve, vz)

    # z∈{z} puis z∈seg∪{z}
    z_in_sing = N.modus_ponens(N.reflexivite(vz),
                               equivalence_arriere(singleton_membre(vz, vz)))
    in_sing = appartient(vz, E.singleton(vz))
    in_seg = appartient(vz, seg)
    disj = N.modus_ponens(N.modus_ponens(z_in_sing, N.s2(in_sing, in_seg)),
                          N.s3(in_sing, in_seg))                 # (z∈seg) ∨ (z∈{z})
    z_in_de = N.modus_ponens(disj, equivalence_arriere(
        membre_reunion_graphes(seg, E.singleton(vz), vz)))       # z∈seg∪{z}
    # transport vers dom pess
    eq2 = N.modus_ponens(dom_eq, symetrie(E.dom(vp), de))        # seg∪{z} = dom pess
    equivF = N.modus_ponens(eq2, N.s6(de, E.dom(vp), "wdm", appartient(vz, var("wdm"))))
    z_in_domp = N.modus_ponens(z_in_de, equivalence_avant(equivF))   # z∈dom pess
    exy = N.modus_ponens(z_in_domp, equivalence_avant(_dom_car(vp, vz)))  # (∃y)((z,y)∈pess)

    # ── sous le témoin y : (z,y)∈⋃𝔇 puis z∈dom f ─────────────────────────────
    vy = var("y")
    cpl = E.couple(vz, vy)
    h_y = N.assume(appartient(cpl, vp))
    in_union = _membre_dans_union(Dt, vp, cpl, pDt, h_y)         # (z,y)∈⋃𝔇
    z_dom_f = N.modus_ponens(in_union, antecedent_dans_domaine(vz, vy, f))  # z∈dom f

    z_dom_f = N.modus_ponens(exy, existe_elimination(
        N.loi_deduction(appartient(cpl, vp), z_dom_f), "y"))
    z_dom_f = N.modus_ponens(exp, existe_elimination(
        N.loi_deduction(corps_p, z_dom_f), "pess"))              # z∈dom f  {z∈E,bo,ebf,rc}

    res = N.generalisation("z", N.loi_deduction(appartient(vz, ve), z_dom_f))
    cible = inclus(ve, E.dom(f))
    assert res.conclusion == cible, "e_inclus_dom_fonction : ≠ E⊂dom(f)"
    bo = E.est_bien_ordonne(R, ve)
    assert bo in res.hypotheses, "e_inclus_dom_fonction : bo absente"
    assert len(res.hypotheses) == 3, "e_inclus_dom_fonction : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "e_inclus_dom_fonction : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 dom(f) = E   [3 hyps = résidus C62 ; antisymétrie de ⊂ (A1)].
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Demo.C62 | E III.46 L.14-20 | PDF p.149  (« une application f de ℕ … » : le domaine de la fonction assemblée est ℕ tout entier)
def dom_fonction_globale(vh, e="Enat", G="Gle", V="Uval"):
    """🎯 { bo, essais_bien_formes, rule_codomain } ⊢ dom(f) = E,   f = ⋃𝔇_tot.

    Double inclusion : (⊆) CLOS (`dom_fonction_inclus_e`), (⊇) sous les résidus C62
    (`e_inclus_dom_fonction`) ; l'antisymétrie de ⊂ (= A1) conclut."""
    ve = _t(e)
    f = fonction_globale(e, V)
    sub = dom_fonction_inclus_e(vh, e, G, V)                     # CLOS
    sup = e_inclus_dom_fonction(vh, e, G, V)                     # {bo, ebf, rc}
    res = N.modus_ponens(conjonction_intro(sub, sup),
                         inclusion_antisymetrique(E.dom(f), ve))

    assert res.conclusion == egal(E.dom(f), ve), "dom_fonction_globale : ≠ dom(f)=E"
    assert len(res.hypotheses) == 3, "dom_fonction_globale : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "dom_fonction_globale : VACUOUS"
    return res


__all__ = [
    "essai_dans_Dtot",
    "dom_fonction_inclus_e",       # (⊆) CLOS
    "e_inclus_dom_fonction",       # (⊇) sous les 3 résidus C62
    "dom_fonction_globale",        # 🎯 dom(f)=E
]
