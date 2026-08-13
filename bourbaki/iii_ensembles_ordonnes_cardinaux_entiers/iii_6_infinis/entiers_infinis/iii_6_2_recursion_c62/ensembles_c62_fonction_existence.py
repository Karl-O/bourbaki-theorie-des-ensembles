"""§III.6.2 — C62, L'EXISTENCE DE LA FONCTION :  (∃f)( func ∧ dom=ℕ ∧ équation ).

Aboutissement de l'assemblage (fichiers `_globale` : f=⋃𝔇_tot fonctionnelle CLOS ;
`_domaine` : dom(f)=E sous les 3 résidus C62).  Ici :

  • `valeur_fonction_globale`    { z∈E, bo, ebf, rc } ⊢ valeur(f,z) = T(z)
      — z est dans le domaine de SON essai p_z (C62) ; valeur(⋃𝔇,z)=valeur(p_z,z)
        (`valeur_union_famille`, famille_compatible CLOS) ; =T(z) (équation d'essai).
  • `equation_fonction_globale`  { bo, ebf, rc } ⊢ (∀z)( z∈E ⇒ valeur(f,z)=T(z) )
  • 🎯🎯 `fonction_recursion_c62` { bo, ebf, rc } ⊢
        (∃f)( est_fonctionnel(f) ∧ dom(f)=E ∧ (∀z)(z∈E ⇒ valeur(f,z)=T(z)) )
      — S5 au témoin f=⋃𝔇_tot.  C'EST « il existe une application f de ℕ telle que
        f(n)=T(n) » : la conclusion de C62 du livre, au niveau valeur-règle.

⚠️ LIANTS EXOTIQUES « zfgl » (équation) et « fglb » (∃) : la règle T peut lier en
interne u/v/y/z (règle factorielle : τ-cardinaux) — quantifier sur un nom que T lie
CAPTURERAIT la variable à la construction.  zfgl/fglb ne sont liés par aucune règle.

ÉCART DE FIDÉLITÉ documenté (comme pour C62 déposé) : l'équation est au niveau
VALEUR-RÈGLE (f(z)=T(z), T appliquée au POINT), pas encore f(z)=T{f|seg(z)} (la règle
lisant la RESTRICTION) — le pont restriction est le chantier suivant.

INVARIANT : theorie_ensembles() = 22.  TROIS hypothèses honnêtes = résidus C62.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    est_essai, dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    famille_compatible, valeur_union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import c62_recursion_sur_N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    Dtot, fonction_globale, famille_compatible_tot, fonction_globale_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import (
    essai_dans_Dtot, dom_fonction_globale,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import membre_reunion_graphes
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _z_dans_dom_essai(vh, e, G, zn, p):
    """{ est_essai(p,z) } ⊢ z∈dom(p)   (z∈{z} ⇒ z∈seg∪{z} = dom p, transport s6)."""
    R = _graphe_R(G)
    ve, vz, vp = _t(e), var(zn), var(p)
    h_p = N.assume(est_essai(vp, vh, G, ve, vz))
    dom_eq = conjonction_elim_droite(conjonction_elim_gauche(h_p))   # dom p = seg∪{z}
    de = dom_essai(G, ve, vz)
    seg = E.segment_extremite(_t(G), ve, vz)

    z_in_sing = N.modus_ponens(N.reflexivite(vz),
                               equivalence_arriere(singleton_membre(vz, vz)))
    in_sing = appartient(vz, E.singleton(vz))
    in_seg = appartient(vz, seg)
    disj = N.modus_ponens(N.modus_ponens(z_in_sing, N.s2(in_sing, in_seg)),
                          N.s3(in_sing, in_seg))                 # (z∈seg) ∨ (z∈{z})
    z_in_de = N.modus_ponens(disj, equivalence_arriere(
        membre_reunion_graphes(seg, E.singleton(vz), vz)))       # z∈seg∪{z}
    eq2 = N.modus_ponens(dom_eq, symetrie(E.dom(vp), de))        # seg∪{z} = dom p
    equivF = N.modus_ponens(eq2, N.s6(de, E.dom(vp), "wdm", appartient(vz, var("wdm"))))
    res = N.modus_ponens(z_in_de, equivalence_avant(equivF))     # z∈dom p
    assert res.conclusion == appartient(vz, E.dom(vp)), "_z_dans_dom_essai : ≠ z∈dom p"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 L'ÉQUATION AU POINT — valeur(f, z) = T(z)  pour z∈E.
# ════════════════════════════════════════════════════════════════════════════
def valeur_fonction_globale(vh, e="Enat", G="Gle", V="Uval", zn="zfgl"):
    """{ z∈E, bo, essais_bien_formes, rule_codomain } ⊢ valeur(f,z) = T(z).

    C62 fournit l'essai p_z ; z∈dom(p_z) ; valeur(⋃𝔇,z)=valeur(p_z,z)
    (`valeur_union_famille` ; famille_compatible(𝔇_tot) CLOS, p_z∈𝔇_tot par
    `essai_dans_Dtot`) ; l'équation d'essai donne valeur(p_z,z)=T(z).  Chaîne."""
    R = _graphe_R(G)
    ve, vz = _t(e), var(zn)
    Dt = Dtot(e, V)
    f = fonction_globale(e, V)
    vp = var("pess")

    h_z = N.assume(appartient(vz, ve))                           # z∈E
    c62 = c62_recursion_sur_N(vh, e, G, V)
    exp = N.modus_ponens(h_z, instancie(c62, vz))                # (∃pess) est_essai(pess,z)

    corps_p = est_essai(vp, vh, G, ve, vz)
    pDt = essai_dans_Dtot(vh, vz, e, G, V, "pess")               # {z∈E, essai, ebf, rc}
    z_domp = _z_dans_dom_essai(vh, e, G, zn, "pess")             # {essai} ⊢ z∈dom pess

    # valeur(⋃𝔇, z) = valeur(pess, z)   (compat CLOS ; p∈𝔇 ; z∈dom p déchargées)
    vuf = valeur_union_famille(Dt, "pess", vz)
    compat = famille_compatible_tot(vh, e, G, V)                 # CLOS (liants pcf/qcf)
    # l'hypothèse de valeur_union_famille(p="pess") porte le LIANT pess : α-pont dérivé
    fc_pess = famille_compatible(Dt, p="pess")
    compat_pess = alpha_bridge(compat, fc_pess)                  # CLOS (α-variant certifié)
    vuf = N.modus_ponens(compat_pess, N.loi_deduction(fc_pess, vuf))
    vuf = N.modus_ponens(pDt, N.loi_deduction(appartient(vp, Dt), vuf))
    vuf = N.modus_ponens(z_domp, N.loi_deduction(appartient(vz, E.dom(vp)), vuf))

    # valeur(pess, z) = T(z)   (équation d'essai instanciée en z)
    h_p = N.assume(corps_p)
    eq_rec = conjonction_elim_droite(h_p)                        # (∀zess)(…⇒ valeur(p,·)=T(·))
    eq_z = N.modus_ponens(z_domp, instancie(eq_rec, vz))         # valeur(pess,z)=T(z)
    assert eq_z.conclusion == egal(E.valeur(vp, vz), vh(vz)), \
        "valeur_fonction_globale : équation d'essai ≠ valeur(p,z)=T(z)"

    chaine = composer_egalites(vuf, eq_z)                        # valeur(f,z)=T(z)
    # élimination du témoin pess (non libre dans la conclusion ni dans z∈E/bo/ebf/rc)
    res = N.modus_ponens(exp, existe_elimination(
        N.loi_deduction(corps_p, chaine), "pess"))

    cible = egal(E.valeur(f, vz), vh(vz))
    assert res.conclusion == cible, "valeur_fonction_globale : ≠ valeur(f,z)=T(z)"
    assert appartient(vz, ve) in res.hypotheses, "valeur_fonction_globale : z∈E absente"
    assert len(res.hypotheses) == 4, "valeur_fonction_globale : hyps ≠ 4"
    assert res.conclusion not in res.hypotheses, "valeur_fonction_globale : VACUOUS"
    return res


def equation_fonction_globale(vh, e="Enat", G="Gle", V="Uval", zn="zfgl"):
    """{ bo, essais_bien_formes, rule_codomain } ⊢ (∀z)( z∈E ⇒ valeur(f,z)=T(z) )."""
    ve, vz = _t(e), var(zn)
    val = valeur_fonction_globale(vh, e, G, V, zn)
    res = N.generalisation(zn, N.loi_deduction(appartient(vz, ve), val))

    f = fonction_globale(e, V)
    cible = pourtout(zn, impl(appartient(vz, ve), egal(E.valeur(f, vz), vh(vz))))
    assert res.conclusion == cible, "equation_fonction_globale : ≠ (∀z)(z∈E⇒f(z)=T(z))"
    assert len(res.hypotheses) == 3, "equation_fonction_globale : hyps ≠ 3"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 CAPSTONE — (∃f)( est_fonctionnel(f) ∧ dom(f)=E ∧ équation ).
# ════════════════════════════════════════════════════════════════════════════
def c62_fonction_cible(vh, e="Enat", V="Uval", fb="fglb", zn="zfgl"):
    """L'ÉNONCÉ-cible :  (∃f)( est_fonctionnel(f) ∧ dom(f)=E ∧ (∀z∈E)(f(z)=T(z)) )."""
    ve, vf, vz = _t(e), var(fb), var(zn)
    corps = et(et(E.est_fonctionnel(vf), egal(E.dom(vf), ve)),
               pourtout(zn, impl(appartient(vz, ve), egal(E.valeur(vf, vz), vh(vz)))))
    return existe(fb, corps)


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149  (« il existe un ensemble U et une application f de ℕ … f(n)=T(…) » — l'EXISTENCE de la fonction, assemblée ; équation au niveau valeur-règle)
def fonction_recursion_c62(vh, e="Enat", G="Gle", V="Uval", fb="fglb", zn="zfgl"):
    """🎯🎯 { bo, essais_bien_formes, rule_codomain } ⊢
          (∃f)( est_fonctionnel(f) ∧ dom(f)=E ∧ (∀z)(z∈E ⇒ valeur(f,z)=T(z)) ).

    LA CONCLUSION DE C62 (niveau valeur-règle) : témoin f := ⋃𝔇_tot, dont les trois
    clauses sont démontrées (fonctionnalité CLOS ; domaine et équation sous les 3
    résidus honnêtes de C62) ; S5 introduit l'existentiel.  theorie == 22.

    ⚠️ CE N'EST PAS le (∃!f) du livre, et ces TROIS conjoints NE SE RECOLLENT PAS
    tels quels avec l'unicité, dont l'antécédent en exige QUATRE (il ajoute
    `est_un_graphe`) — le désaccord a fait passer le capstone pour acquis pendant
    un mois alors qu'il n'existait pas.  Le (∃!f) est
    `ensembles_c62_fonction_unicite.existence_unicite_fonction_c62` : il reprend
    cette preuve en AJOUTANT le conjoint `est_un_graphe` (gratuit, CLOS sur le même
    témoin), et son prédicat commun est `c62_predicat`.  Ne PAS retirer le conjoint
    côté unicité pour « aligner » : ce serait FAUX (cf. la docstring de
    `c62_predicat`).  La présente fonction est conservée telle quelle — elle est la
    forme à 3 conjoints, plus faible, encore consommée en aval."""
    ve = _t(e)
    f = fonction_globale(e, V)
    vf, vz = var(fb), var(zn)

    c_func = fonction_globale_fonctionnelle(vh, e, G, V)         # CLOS
    c_dom = dom_fonction_globale(vh, e, G, V)                    # {bo, ebf, rc}
    c_eq = equation_fonction_globale(vh, e, G, V, zn)            # {bo, ebf, rc}
    wit = conjonction_intro(conjonction_intro(c_func, c_dom), c_eq)

    corps = et(et(E.est_fonctionnel(vf), egal(E.dom(vf), ve)),
               pourtout(zn, impl(appartient(vz, ve), egal(E.valeur(vf, vz), vh(vz)))))
    res = N.modus_ponens(wit, N.s5(corps, f, fb))                # (∃f)(…)

    cible = c62_fonction_cible(vh, e, V, fb, zn)
    assert res.conclusion == cible, "fonction_recursion_c62 : ≠ cible (∃f)(…)"
    R = _graphe_R(G)
    assert E.est_bien_ordonne(R, ve) in res.hypotheses, "fonction_recursion_c62 : bo absente"
    assert len(res.hypotheses) == 3, "fonction_recursion_c62 : hyps ≠ 3"
    assert res.conclusion not in res.hypotheses, "fonction_recursion_c62 : VACUOUS"
    return res


__all__ = [
    "valeur_fonction_globale", "equation_fonction_globale",
    "c62_fonction_cible", "fonction_recursion_c62",
]
