"""§III.6.2 — C62, L'UNICITÉ :  tout candidat g = f   (le « il existe UNE application »).

Complément d'unicité de l'assemblage C62 (fichiers _globale/_domaine/_existence) :

  • `fonction_globale_inclus_produit`  ⊢ ⋃𝔇_tot ⊂ E×V                  [CLOS]
  • `est_un_graphe_fonction_globale`   ⊢ est_un_graphe(⋃𝔇_tot)          [CLOS]
      — chaque membre p vit dans 𝔓(E×V) (1er conjoint du sélecteur S8), donc
        p⊂E×V (AXIOME_PARTIES) et tout w∈⋃𝔇 est dans E×V : un couple.
  • 🎯🎯 `unicite_fonction_c62`   { bo, essais_bien_formes, rule_codomain } ⊢
        (∀g)( ( est_fonctionnel(g) ∧ est_un_graphe(g) ∧ dom(g)=E
                ∧ (∀z)(z∈E ⇒ valeur(g,z)=T(z)) )  ⇒  g = f )
      — l'extensionnalité fonctionnelle `graphe_egal_par_valeurs` (CLOS, E.II.3)
        avec ses 6 prémisses fournies : côté f par les théorèmes de l'assemblage,
        côté g par l'antécédent.  Parmi les GRAPHES (l'hypothèse est_un_graphe(g)
        est REQUISE : fonctionnel seul ne dit pas que tout élément est un couple).
  • 🎯🎯🎯 `existence_unicite_fonction_c62`  { bo, essais_bien_formes, rule_codomain }
        ⊢ (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g = f ) )
      — LE (∃!f) DE C62 : la dernière phrase du critère (« L'ensemble U et
        l'application f sont alors déterminés de façon unique par cette condition »)
        recollée à la première.  Le recollement exigeait de RENFORCER L'EXISTENCE
        (conjoint `est_un_graphe`, GRATUIT car CLOS sur le même témoin), jamais
        d'affaiblir l'unicité — cf. `c62_predicat`.

`c62_predicat` est la SOURCE UNIQUE du prédicat P : l'antécédent de l'unicité et les
deux occurrences du (∃!f) en dérivent, donc l'association de la conjonction (piège
`et` binaire gauche-associatif) ne peut plus se désaccorder silencieusement.

INVARIANT : theorie_ensembles() = 22.  Rien postulé ; 3 résidus C62 seulement.
ÉCART DE FIDÉLITÉ déclaré : niveau VALEUR-RÈGLE f(z)=T(z), pas f(z)=T{f|seg z}
(l'unicité niveau-livre demande une récurrence transfinie — chantier ouvert).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import graphe_egal_par_valeurs
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_application_valeur import _inclus_produit_est_graphe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import membre_parties_t

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import _inst_union_famille
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import ambiant
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    Dtot, _inst_Dtot, fonction_globale, fonction_globale_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import dom_fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_existence import equation_fonction_globale


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  LE PRÉDICAT COMMUN  P(t)  — « t est LA fonction de récursion ».
# ════════════════════════════════════════════════════════════════════════════
def c62_predicat(vh, t, e="Enat", zn="zfgl"):
    """P(t) := est_fonctionnel(t) ∧ est_un_graphe(t) ∧ dom(t)=E ∧ (∀z∈E)(t(z)=T(z)).

    SOURCE UNIQUE de la forme : l'antécédent de `unicite_fonction_c62`, le témoin de
    `existence_unicite_fonction_c62` et les deux occurrences du (∃!f) sont TOUS
    construits par cet appel — l'association de la conjonction (`et` est binaire et
    gauche-associatif) devient donc structurellement impossible à désaccorder.

    ⚠️ `est_un_graphe(t)` est REQUIS et ne doit JAMAIS être retiré pour « aligner » :
    est_fonctionnel, dom et valeur ne LISENT que les couples de t, donc t et t∪{a}
    (a non-couple) auraient mêmes fonctionnalité, domaine et valeurs en étant
    DIFFÉRENTS — l'unicité serait FAUSSE.  Chez Bourbaki une application EST un
    graphe fonctionnel : les 4 conjoints sont la forme FIDÈLE."""
    ve, vz = _t(e), var(zn)
    return et(et(et(E.est_fonctionnel(t), E.est_un_graphe(t)), egal(E.dom(t), ve)),
              pourtout(zn, impl(appartient(vz, ve), egal(E.valeur(t, vz), vh(vz)))))


# ════════════════════════════════════════════════════════════════════════════
#  ⊢ ⋃𝔇_tot ⊂ E×V   puis   ⊢ est_un_graphe(⋃𝔇_tot)   [CLOS].
# ════════════════════════════════════════════════════════════════════════════
def fonction_globale_inclus_produit(vh, e="Enat", G="Gle", V="Uval"):
    """⊢ ⋃𝔇_tot ⊂ E×V                                                 [CLOS, 0 hyp].

    w∈⋃𝔇 ⇒ (∃p∈𝔇)(w∈p) [réunion-famille] ; p∈𝔇 ⇒ p∈𝔓(E×V) [S8, 1er conjoint]
    ⇒ p⊂E×V [AXIOME_PARTIES] ⇒ w∈E×V."""
    ve = _t(e)
    Dt = Dtot(e, V)
    U = fonction_globale(e, V)
    prod = E.produit(ve, _t(V))
    vz = var("z")

    h_w = N.assume(appartient(vz, U))
    dec = N.modus_ponens(h_w, equivalence_avant(_inst_union_famille(Dt, vz)))
    vpu = var("punion")
    corps = et(appartient(vpu, Dt), appartient(vz, vpu))
    h_c = N.assume(corps)
    puD = conjonction_elim_gauche(h_c)                           # p∈𝔇
    zp = conjonction_elim_droite(h_c)                            # z∈p
    amb = conjonction_elim_gauche(N.modus_ponens(
        puD, equivalence_avant(_inst_Dtot(vh, e, G, vpu, V))))   # p∈𝔓(E×V)
    p_sub = N.modus_ponens(amb, equivalence_avant(membre_parties_t(vpu, prod)))  # p⊂E×V
    z_prod = N.modus_ponens(zp, instancie(p_sub, vz))            # z∈E×V
    z_prod = N.modus_ponens(dec, existe_elimination(
        N.loi_deduction(corps, z_prod), "punion"))

    res = N.generalisation("z", N.loi_deduction(appartient(vz, U), z_prod))
    assert res.conclusion == inclus(U, prod), "fonction_globale_inclus_produit : ≠ ⋃𝔇⊂E×V"
    assert res.est_clos, "fonction_globale_inclus_produit : non clos"
    return res


def est_un_graphe_fonction_globale(vh, e="Enat", G="Gle", V="Uval"):
    """⊢ est_un_graphe( ⋃𝔇_tot )                                       [CLOS, 0 hyp]."""
    ve, vV = _t(e), _t(V)
    U = fonction_globale(e, V)
    sub = fonction_globale_inclus_produit(vh, e, G, V)           # ⋃𝔇⊂E×V  [CLOS]
    gr = _inclus_produit_est_graphe(U, ve, vV)                   # {⊂} ⊢ est_un_graphe
    res = N.modus_ponens(sub, N.loi_deduction(inclus(U, E.produit(ve, vV)), gr))

    assert res.conclusion == E.est_un_graphe(U), \
        "est_un_graphe_fonction_globale : ≠ est_un_graphe(⋃𝔇_tot)"
    assert res.est_clos, "est_un_graphe_fonction_globale : non clos"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 UNICITÉ — (∀g)( (func ∧ graphe ∧ dom=E ∧ équation) ⇒ g = f ).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149  (« il existe un ensemble U et UNE application f » — l'unicité de la fonction de récursion, extensionnalité fonctionnelle)
def unicite_fonction_c62(vh, e="Enat", G="Gle", V="Uval", g="gcand", zn="zfgl"):
    """🎯🎯 { bo, essais_bien_formes, rule_codomain } ⊢
        (∀g)( ( est_fonctionnel(g) ∧ est_un_graphe(g) ∧ dom(g)=E
                ∧ (∀z)(z∈E ⇒ valeur(g,z)=T(z)) )  ⇒  g = f ),   f = ⋃𝔇_tot.

    L'UNICITÉ de la fonction C62 parmi les graphes : les 6 prémisses de
    `graphe_egal_par_valeurs(g, f)` sont fournies — côté f par l'assemblage
    (fonctionnalité et graphe CLOS ; domaine et équation sous les 3 résidus),
    côté g par l'antécédent.  L'égalité des valeurs passe par la règle commune :
    valeur(g,x) = T(x) = valeur(f,x) sur dom(g)=E."""
    ve = _t(e)
    f = fonction_globale(e, V)
    vg, vx = var(g), var("x")

    # l'antécédent du candidat = le prédicat commun P(g)
    ante = c62_predicat(vh, vg, e, zn)
    h = N.assume(ante)
    g_func = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(h)))
    g_graphe = conjonction_elim_droite(conjonction_elim_gauche(conjonction_elim_gauche(h)))
    g_dom = conjonction_elim_droite(conjonction_elim_gauche(h))  # dom g = E
    g_eq = conjonction_elim_droite(h)                            # (∀z∈E)(g(z)=T(z))

    # côté f (assemblage)
    f_func = fonction_globale_fonctionnelle(vh, e, G, V)         # CLOS
    f_graphe = est_un_graphe_fonction_globale(vh, e, G, V)       # CLOS
    f_dom = dom_fonction_globale(vh, e, G, V)                    # {bo,ebf,rc} dom f=E
    f_eq = equation_fonction_globale(vh, e, G, V, zn)            # {bo,ebf,rc} (∀z∈E)(f(z)=T(z))

    # dom g = dom f  :  dom g = E = dom f
    dom_gf = composer_egalites(g_dom, N.modus_ponens(f_dom, symetrie(E.dom(f), ve)))

    # (∀x)( x∈dom g ⇒ valeur(g,x)=valeur(f,x) )  — par la règle commune
    h_x = N.assume(appartient(vx, E.dom(vg)))                    # x∈dom g
    eqv = N.modus_ponens(g_dom, N.s6(E.dom(vg), ve, "wdu", appartient(vx, var("wdu"))))
    x_E = N.modus_ponens(h_x, equivalence_avant(eqv))            # x∈E
    gx = N.modus_ponens(x_E, instancie(g_eq, vx))                # g(x)=T(x)
    fx = N.modus_ponens(x_E, instancie(f_eq, vx))                # f(x)=T(x)
    gfx = composer_egalites(gx, N.modus_ponens(fx, symetrie(E.valeur(f, vx), vh(vx))))
    p_val = N.generalisation("x", N.loi_deduction(appartient(vx, E.dom(vg)), gfx))

    # les 6 prémisses de graphe_egal_par_valeurs(g, f) : ((((fG∧fF)∧gG)∧gF)∧dom)∧val
    prem = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(g_func, f_func), g_graphe), f_graphe), dom_gf), p_val)
    egal_gf = N.modus_ponens(prem, graphe_egal_par_valeurs(vg, f))   # g = f

    imp = N.loi_deduction(ante, egal_gf)
    res = N.generalisation(g, imp)

    cible = pourtout(g, impl(ante, egal(vg, f)))
    assert res.conclusion == cible, "unicite_fonction_c62 : ≠ (∀g)(… ⇒ g=f)"
    assert len(res.hypotheses) == 3, "unicite_fonction_c62 : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "unicite_fonction_c62 : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 LE (∃!f) DE C62 — existence ET unicité en UNE seule formule.
# ════════════════════════════════════════════════════════════════════════════
def c62_existe_unique_cible(vh, e="Enat", fb="fglb", gb="gcand", zn="zfgl"):
    """L'ÉNONCÉ-cible :  (∃f)( P(f) ∧ (∀g)( P(g) ⇒ g = f ) ),  P = `c62_predicat`."""
    vf, vg = var(fb), var(gb)
    return existe(fb, et(c62_predicat(vh, vf, e, zn),
                         pourtout(gb, impl(c62_predicat(vh, vg, e, zn), egal(vg, vf)))))


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149  (« Il existe un ensemble U et une application f de ℕ sur U tels que … L'ensemble U et l'application f sont alors déterminés de façon unique par cette condition. » — l'ÉNONCÉ COMPLET de C62, existence ET unicité recollées en un (∃!f) ; niveau valeur-règle)
def existence_unicite_fonction_c62(vh, e="Enat", G="Gle", V="Uval",
                                   fb="fglb", gb="gcand", zn="zfgl"):
    """🎯🎯🎯 { bo, essais_bien_formes, rule_codomain } ⊢
          (∃f)(  ( est_fonctionnel(f) ∧ est_un_graphe(f) ∧ dom(f)=E
                   ∧ (∀z)(z∈E ⇒ valeur(f,z)=T(z)) )
               ∧ (∀g)( ( est_fonctionnel(g) ∧ est_un_graphe(g) ∧ dom(g)=E
                         ∧ (∀z)(z∈E ⇒ valeur(g,z)=T(z)) ) ⇒ g = f )  ).

    LE (∃!f) DE C62 — la DERNIÈRE phrase du critère (« déterminés de façon unique »)
    recollée à la première (« il existe … »).  Les deux moitiés existaient depuis le
    25 juil. mais ne se JOIGNAIENT pas : le capstone d'existence déposé
    (`fonction_recursion_c62`) affirme TROIS conjoints (func ∧ dom ∧ éq) tandis que
    l'antécédent de l'unicité en exige QUATRE (le conjoint `est_un_graphe`) — deux
    prédicats distincts, donc pas de (∃!f) formable.  La réparation RENFORCE
    L'EXISTENCE (jamais n'affaiblit l'unicité) : le 4ᵉ conjoint est GRATUIT côté
    témoin, `est_un_graphe_fonction_globale` étant CLOS à 0 hypothèse sur le MÊME
    témoin f=⋃𝔇_tot.  Les deux moitiés parlent alors du même prédicat `c62_predicat`,
    et S5 au témoin f introduit l'existentiel.

    Rien de neuf n'est postulé : mêmes TROIS résidus honnêtes que les deux moitiés.

    ⚠️ NIVEAU VALEUR-RÈGLE (f(z)=T(z), T appliquée au POINT), comme tout l'assemblage
    C62 déposé — PAS encore la forme du livre f(z)=T{f|seg z}.  Côté existence cette
    forme-là existe (`equation_restriction_fonction`, 4 hyps) ; côté UNICITÉ elle
    n'est PAS assemblable ainsi : l'argument de T diffère entre g et f
    (T{g|seg x} vs T{f|seg x}), l'extensionnalité ne conclut plus et il faudra une
    RÉCURRENCE TRANSFINIE sur la coïncidence g|seg x = f|seg x.  Résidu déclaré."""
    f = fonction_globale(e, V)
    vf, vg = var(fb), var(gb)

    # ---- P(f) pour le témoin f=⋃𝔇_tot : les QUATRE conjoints ----------------
    c_func = fonction_globale_fonctionnelle(vh, e, G, V)          # CLOS
    c_graphe = est_un_graphe_fonction_globale(vh, e, G, V)        # CLOS — le conjoint GRATUIT
    c_dom = dom_fonction_globale(vh, e, G, V)                     # {bo, ebf, rc}
    c_eq = equation_fonction_globale(vh, e, G, V, zn)             # {bo, ebf, rc}
    p_f = conjonction_intro(conjonction_intro(
        conjonction_intro(c_func, c_graphe), c_dom), c_eq)
    # l'association de la conjonction est LOAD-BEARING : on la vérifie AVANT le S5.
    assert p_f.conclusion == c62_predicat(vh, f, e, zn), \
        "existence_unicite_fonction_c62 : P(f) construit ≠ P(f) attendu (association ?)"

    # ---- P(f) ∧ (∀g)(P(g) ⇒ g=f), puis S5 au témoin f ----------------------
    uniq = unicite_fonction_c62(vh, e, G, V, gb, zn)              # {bo, ebf, rc}
    assert uniq.conclusion == pourtout(gb, impl(c62_predicat(vh, vg, e, zn),
                                                egal(vg, f))), \
        "existence_unicite_fonction_c62 : unicité ≠ (∀g)(P(g) ⇒ g=f)"
    temoin = conjonction_intro(p_f, uniq)

    corps = et(c62_predicat(vh, vf, e, zn),
               pourtout(gb, impl(c62_predicat(vh, vg, e, zn), egal(vg, vf))))
    res = N.modus_ponens(temoin, N.s5(corps, f, fb))              # (∃f)(…)

    assert res.conclusion == c62_existe_unique_cible(vh, e, fb, gb, zn), \
        "existence_unicite_fonction_c62 : ≠ cible (∃!f)"
    assert len(res.hypotheses) == 3, "existence_unicite_fonction_c62 : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "existence_unicite_fonction_c62 : VACUOUS"
    return res


__all__ = ["c62_predicat", "fonction_globale_inclus_produit",
           "est_un_graphe_fonction_globale", "unicite_fonction_c62",
           "c62_existe_unique_cible", "existence_unicite_fonction_c62"]
