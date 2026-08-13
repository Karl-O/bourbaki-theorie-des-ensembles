"""§III.6.2 — C62, L'ÉQUATION FIDÈLE :  f(n) = T{ f|seg(n) }   (la forme du LIVRE).

C62 (E III.46) : « f(n) = T{f⁽ⁿ⁾}, où f⁽ⁿ⁾ désigne la restriction de f à [0,n[ ».
Le déposé donne l'équation au POINT (f(n)=vh(n), vh la valeur-règle réifiée).  Ici :

  • `essais_restriction(T, vh)`  — l'hypothèse HONNÊTE de LECTURE-RESTRICTION :
        (∀q)(∀w)( est_essai(q,vh,R,E,w) ⇒ vh(w) = T( q|seg(R,E,w) ) )
    « la valeur-règle au point w EST T appliquée à la restriction de l'essai ».
    C'est le LIEN entre l'encodage-point déposé et la lecture-restriction du livre
    (même style que `regle_locale` / `essais_bien_formes` : la donnée naturelle de la
    règle, jamais postulée — une HYPOTHÈSE de tout théorème qui l'utilise).

  • 🎯🎯 `equation_restriction_fonction`
        { bo, essais_bien_formes, rule_codomain, essais_restriction } ⊢
          (∀n)( n∈E ⇒ valeur(f, n) = T( restriction(f, seg(R,E,n)) ) )
    LA FORME DU LIVRE, sur le TERME OUVERT f=⋃𝔇_tot.  Preuve : f(n)=vh(n)
    (équation-point, fichier _existence) ; vh(n)=T(p_n|seg(n)) (hypothèse à l'essai
    témoin) ; p_n|seg(n)=f|seg(n) (LE PONT RESTRICTION, égalité de graphes, fichier
    _restriction) ; congruence de T.

  • 🎯🎯🎯 `existence_fonction_restriction_c62`   (ajouté le 26 juil. 2026)
        mêmes 4 hypothèses ⊢
          (∃f)( est_fonctionnel(f) ∧ est_un_graphe(f) ∧ dom(f)=E
                ∧ (∀n)( n∈E ⇒ valeur(f,n) = T( restriction(f, seg(R,E,n)) ) ) )
    L'EXISTENCE DE C62 À LA LETTRE.  Cette JOINTURE-là n'avait jamais été tentée : le
    dépôt avait le paquet ∃ au niveau VALEUR-RÈGLE (`fonction_recursion_c62`) et
    l'équation de niveau LIVRE sur le terme OUVERT — jamais les deux ensemble.  Le pas
    load-bearing est le S5 qui substitue le témoin τ-profond ⋃𝔇_tot SOUS l'argument
    `restriction(·, seg)` de la règle, donc à travers ses liants internes.

INVARIANT : theorie_ensembles() = 22.  QUATRE hypothèses honnêtes (les deux conjoints
supplémentaires du paquet ∃ sont CLOS, donc gratuits).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import est_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import c62_recursion_sur_N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    Dtot, fonction_globale,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import essai_dans_Dtot
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_existence import valeur_fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_restriction import restriction_egale_essai_seg


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def essais_restriction(T, vh, e="Enat", G="Gle", q="qrs", w="wrs"):
    """(∀q)(∀w)( est_essai(q, vh, G, E, w) ⇒ vh(w) = T( restriction(q, seg(R,E,w)) ) ).

    L'HYPOTHÈSE de lecture-restriction : au point-extrémité w de tout essai, la
    valeur-règle vh(w) EST T appliquée à la restriction de l'essai au segment.
    Donnée naturelle de la règle (le sens même de « T lit f⁽ⁿ⁾ »), style regle_locale."""
    R = _graphe_R(G)
    ve = _t(e)
    vq, vw = var(q), var(w)
    seg = E.segment_extremite(_t(G), ve, vw)
    return pourtout(q, pourtout(w, impl(
        est_essai(vq, vh, G, ve, vw),
        egal(vh(vw), T(E.restriction(vq, seg))))))


def _congruence_T(T, A, B):
    """De ⊢ A=B (termes) déduit ⊢ (A=B) ⇒ (T(A)=T(B))  (congruence par le trou wct).

    Motif _inst_gen : (wct=B)⇒(T(wct)=T(B)) [congruence_terme], ∀-clos sur wct puis
    instancié à A — substitution PURE dans un théorème clos, aucun renommage (les
    liants internes de T n'appartiennent pas aux libres de A)."""
    imp = congruence_terme(var("wct"), _t(B), T(var("wct")), "wct")
    return instancie(N.generalisation("wct", imp), _t(A))


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 L'ÉQUATION FIDÈLE — f(n) = T( f|seg(n) )  sur tout E.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149  (« f(n) = T{f⁽ⁿ⁾}, où f⁽ⁿ⁾ désigne la restriction de f à l'intervalle [0,n[ » — LA forme du livre, dérivée)
def equation_restriction_fonction(T, vh, e="Enat", G="Gle", V="Uval", zn="zfgl"):
    """🎯🎯 { bo, essais_bien_formes, rule_codomain, essais_restriction(T,vh) } ⊢
          (∀n)( n∈E ⇒ valeur(f, n) = T( restriction(f, seg(R,E,n)) ) ).

    LA FORME DU LIVRE (E III.46) pour la fonction assemblée f=⋃𝔇_tot :
      valeur(f,n) = vh(n)                    [équation-point, _existence] ;
      vh(n) = T(p_n|seg(n))                  [essais_restriction au témoin p_n] ;
      p_n|seg(n) = f|seg(n)                  [LE PONT restriction, _restriction] ;
      congruence de T + chaîne d'égalités."""
    R = _graphe_R(G)
    ve, vz = _t(e), var(zn)
    f = fonction_globale(e, V)
    Dt = Dtot(e, V)
    vp = var("pess")
    seg = E.segment_extremite(_t(G), ve, vz)
    fseg = E.restriction(f, seg)
    pseg = E.restriction(vp, seg)

    h_z = N.assume(appartient(vz, ve))                           # n∈E
    h_er = N.assume(essais_restriction(T, vh, e, G))             # lecture-restriction [HONNÊTE]
    c62 = c62_recursion_sur_N(vh, e, G, V)
    exp = N.modus_ponens(h_z, instancie(c62, vz))                # (∃pess) est_essai(pess,n)

    corps_p = est_essai(vp, vh, G, ve, vz)
    h_p = N.assume(corps_p)

    # (1) valeur(f,n) = vh(n)   [{n∈E, bo, ebf, rc} — indépendant du témoin]
    val_f = valeur_fonction_globale(vh, e, G, V, zn)

    # (2) vh(n) = T(pess|seg(n))   [hypothèse instanciée à (pess, n)]
    er_pn = N.modus_ponens(h_p, instancie(instancie(h_er, vp), vz))

    # (3) pess|seg(n) = f|seg(n)   [LE PONT, sens symétrique]
    rest_eq = restriction_egale_essai_seg(vh, e, G, V, zn, "pess")   # {pess∈𝔇, essai}
    pDt = essai_dans_Dtot(vh, vz, e, G, V, "pess")                   # {n∈E, essai, ebf, rc}
    rest_eq = N.modus_ponens(pDt, N.loi_deduction(appartient(vp, Dt), rest_eq))
    rest_sym = N.modus_ponens(rest_eq, symetrie(fseg, pseg))         # pess|seg = f|seg

    # (4) T(pess|seg) = T(f|seg)   [congruence de T par le trou]
    T_eq = N.modus_ponens(rest_sym, _congruence_T(T, pseg, fseg))

    # chaîne : valeur(f,n) = vh(n) = T(pess|seg) = T(f|seg)
    chaine = composer_egalites(composer_egalites(val_f, er_pn), T_eq)

    # élimination du témoin pess (la conclusion ne mentionne que f)
    res = N.modus_ponens(exp, existe_elimination(
        N.loi_deduction(corps_p, chaine), "pess"))
    res = N.generalisation(zn, N.loi_deduction(appartient(vz, ve), res))

    cible = pourtout(zn, impl(appartient(vz, ve),
                              egal(E.valeur(f, vz), T(fseg))))
    assert res.conclusion == cible, "equation_restriction_fonction : ≠ (∀n∈E)(f(n)=T(f|seg(n)))"
    assert essais_restriction(T, vh, e, G) in res.hypotheses, \
        "equation_restriction_fonction : essais_restriction absente"
    assert len(res.hypotheses) == 4, "equation_restriction_fonction : hyps ≠ 4"
    assert res.conclusion not in res.hypotheses, "equation_restriction_fonction : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 LE PAQUET ∃ AU NIVEAU DU LIVRE — (∃f)( … ∧ f(n)=T{f⁽ⁿ⁾} ).
# ════════════════════════════════════════════════════════════════════════════
def c62_livre_cible(T, e="Enat", V="Uval", fb="fglb", zn="zfgl", G="Gle"):
    """L'ÉNONCÉ-cible de C62 tel que Bourbaki l'écrit (E III.46) :

        (∃f)( est_fonctionnel(f) ∧ est_un_graphe(f) ∧ dom(f)=E
              ∧ (∀n)( n∈E ⇒ valeur(f,n) = T( restriction(f, seg(R,E,n)) ) ) ).

    SOURCE UNIQUE de la forme : `existence_fonction_restriction_c62` compare à ceci ce
    qu'elle construit, donc l'association de la conjonction (`et` binaire, gauche-
    associatif) ne peut pas se désaccorder silencieusement — c'est le désaccord qui
    avait fait passer le (∃!f) valeur-règle pour acquis pendant un mois.

    Les QUATRE conjoints sont ceux de `c62_predicat` (est_un_graphe INCLUS : chez
    Bourbaki une application EST un graphe fonctionnel, et sans lui l'unicité serait
    FAUSSE) — l'équation seule change : elle lit la RESTRICTION, pas le point."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et, existe
    ve, vf, vz = _t(e), var(fb), var(zn)
    seg = E.segment_extremite(_t(G), ve, vz)
    corps = et(et(et(E.est_fonctionnel(vf), E.est_un_graphe(vf)), egal(E.dom(vf), ve)),
               pourtout(zn, impl(appartient(vz, ve),
                                 egal(E.valeur(vf, vz), T(E.restriction(vf, seg))))))
    return existe(fb, corps)


# @livre Ch.III §6.2 Crit.C62 | E III.46 L.14-20 | PDF p.149  (« Il existe un ensemble U et une application f de ℕ sur U tels que, pour tout entier n, on ait f(n) = T{f⁽ⁿ⁾} » — l'EXISTENCE de C62 À LA LETTRE : la règle lit la RESTRICTION f⁽ⁿ⁾, pas le point)
def existence_fonction_restriction_c62(T, vh, e="Enat", G="Gle", V="Uval",
                                       fb="fglb", zn="zfgl"):
    """🎯🎯🎯 { bo, essais_bien_formes, rule_codomain, essais_restriction(T,vh) } ⊢
          (∃f)( est_fonctionnel(f) ∧ est_un_graphe(f) ∧ dom(f)=E
                ∧ (∀n)( n∈E ⇒ valeur(f,n) = T( restriction(f, seg(R,E,n)) ) ) ).

    L'EXISTENCE DE C62 À LA LETTRE DU LIVRE.  Les deux moitiés étaient au dépôt depuis
    le 25 juil. mais ne s'étaient JAMAIS jointes :
      • le paquet ∃ existait au niveau VALEUR-RÈGLE seulement (`fonction_recursion_c62`,
        `existence_unicite_fonction_c62` : f(n)=T(n), la règle appliquée au POINT) ;
      • l'équation de niveau LIVRE existait seulement sur le TERME OUVERT f=⋃𝔇_tot
        (`equation_restriction_fonction`), jamais sous un ∃.
    Ici les quatre conjoints sont prouvés sur le MÊME témoin f=⋃𝔇_tot (fonctionnalité
    et graphe CLOS ; domaine sous les 3 résidus ; équation-restriction sous les 4) puis
    S5 introduit l'existentiel.  QUATRE hypothèses — les mêmes que l'équation seule :
    les deux conjoints supplémentaires sont GRATUITS ou déjà couverts.

    ⚠️ Le pas load-bearing est le S5 : il substitue le témoin τ-profond f=⋃𝔇_tot sous
    l'argument `restriction(fb, seg)` de T, donc À TRAVERS les liants internes de la
    règle.  MESURÉ le 26 juil. : passe pour une règle OPAQUE (2,8 s) ET pour la règle
    FACTORIELLE τ-lourde (15,4 s), conclusion == cible, non vacuous.  Avant le fix
    `subst` du 24 juil. c'est exactement là qu'un renommage gratuit aurait α-divergé.

    RÉSIDU DÉCLARÉ : c'est l'EXISTENCE seule.  L'UNICITÉ au niveau LIVRE n'est PAS
    assemblable de la même façon (l'argument de T diffère entre g et f : T{g|seg x} vs
    T{f|seg x}, l'extensionnalité ne conclut plus) — il y faudra une récurrence
    transfinie sur la coïncidence g|seg x = f|seg x.  Cf. `ensembles_c62_fonction_unicite`."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale_fonctionnelle
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import dom_fonction_globale
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_unicite import est_un_graphe_fonction_globale

    f = fonction_globale(e, V)
    c_func = fonction_globale_fonctionnelle(vh, e, G, V)          # CLOS
    c_graphe = est_un_graphe_fonction_globale(vh, e, G, V)        # CLOS
    c_dom = dom_fonction_globale(vh, e, G, V)                     # {bo, ebf, rc}
    c_eq = equation_restriction_fonction(T, vh, e, G, V, zn)      # + essais_restriction
    wit = conjonction_intro(conjonction_intro(conjonction_intro(c_func, c_graphe),
                                              c_dom), c_eq)

    cible = c62_livre_cible(T, e, V, fb, zn, G)
    res = N.modus_ponens(wit, N.s5(cible.sous[0], f, fb))         # S5 au témoin ⋃𝔇_tot

    assert res.conclusion == cible, \
        "existence_fonction_restriction_c62 : ≠ cible (∃f)(… f(n)=T(f|seg n))"
    assert essais_restriction(T, vh, e, G) in res.hypotheses, \
        "existence_fonction_restriction_c62 : essais_restriction absente"
    assert len(res.hypotheses) == 4, "existence_fonction_restriction_c62 : hyps ≠ 4"
    assert res.conclusion not in res.hypotheses, "existence_fonction_restriction_c62 : VACUOUS"
    return res


__all__ = ["essais_restriction", "equation_restriction_fonction",
           "c62_livre_cible", "existence_fonction_restriction_c62"]
