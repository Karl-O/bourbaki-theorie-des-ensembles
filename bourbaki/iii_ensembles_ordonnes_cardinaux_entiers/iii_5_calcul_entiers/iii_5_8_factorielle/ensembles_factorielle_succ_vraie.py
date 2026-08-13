"""§III.5.8 — LA PHRASE DU LIVRE :  f(n+1) = (n+1)·f(n)   (E III.41 L.30-32).

`factorielle_succ_vraie` compose le cas successeur recâblé (2 août 2026 :
f(succ n) = (succ n)·u(n), u = f|seg(succ n)) avec l'ACCORD DE LA RESTRICTION
en son point n :

    restriction_valeur : { func f, n∈seg, n∈dom f } ⊢ u(n) = f(n)

— `func f` est DÉCHARGÉE par `fonction_globale_fonctionnelle` [CLOS, 0 hyp] ;
— `n∈dom f` est DÉRIVÉ : n∈seg + seg⊂E [`seg_inclus_e`, CLOS] + dom f = E
  [`dom_fonction_globale`, résidus bo/ebf/rc DÉJÀ portés par le cas successeur] ;
— `n∈seg(succ n)` reste la donnée de position HONNÊTE (comme ZERO∈seg) : c'est la
  SEULE hypothèse nouvelle — dix au total.

Écart mort à ce fichier : c'était la brique (B3) de `ensembles_factorielle_iii5`
(l'ex-écart « u(n) vs f(n) » déclaré par la caractérisation).  Reste (B4) : la
∀-clôture de (Rs) sous son antécédent Fini n, vers la décharge dans
`factorielle_c62_entier`.
INVARIANT : theorie_ensembles() = 22.  Noyau et subst INTOUCHÉS.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient, pourtout, impl,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import restriction_valeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, est_fini, ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    fonction_globale, fonction_globale_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import dom_fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import (
    factorielle_succ_fallback, seg_inclus_e,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _dech(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 f(succ n) = (succ n)·f(n)   — LA PHRASE DU LIVRE, dérivée.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« pour tout entier n, (n+1)! = n!(n+1) » — la relation elle-même, au point succ n : f(succ n) = (succ n)·f(n))
def factorielle_succ_vraie(e="Enat", G="Gle", V="Vfac62", n="nfsc"):
    """🎯🎯🎯 { bo, ebf, rc, essais_restriction(T_Z,T_Z), succ n∈E, seg(succ n)=[0,n],
              ZERO∈E, ZERO∈seg(succ n), est_entier(n), n∈seg(succ n) } ⊢
        valeur(f, succ n) = produit( successeur(n), valeur(f, n) )      [10 hyps]

    LA PHRASE DU LIVRE (E III.41 L.30-32) : f(n+1) = (n+1)·f(n) — le facteur, le
    point ET la fonction du livre, plus aucune lecture à travers la restriction.

    Chaîne : `factorielle_succ_fallback` (recâblé : f(succ n) = (succ n)·u(n))
    puis u(n) = f(n) par `restriction_valeur`, dont les trois prémisses sont
    déchargées ou dérivées (func f CLOS ; n∈dom f depuis n∈seg ; n∈seg reste).
    La 10e hypothèse n∈seg(succ n) est une donnée de position honnête — au terme
    ℕ/G_ordre_NN elle deviendra dérivable (n < succ n), chantier instanciation."""
    R = _graphe_R(G)
    ve, vn = _t(e), var(n)
    m = successeur(vn)
    T = regle_factorielle(zcard="Z")
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, m)
    u = E.restriction(f, seg)

    # (1) le cas successeur recâblé : f(succ n) = (succ n)·u(n)          [9 hyps]
    fb = factorielle_succ_fallback(e, G, V, n)

    # (2) l'accord de la restriction : u(n) = f(n)
    h_ns = N.assume(appartient(vn, seg))                 # n∈seg(succ n)  [HONNÊTE]
    n_E = N.modus_ponens(h_ns, instancie(seg_inclus_e(e, G, m), vn))     # n∈E
    domE = dom_fonction_globale(T, e, G, V)              # dom f = E  [bo, ebf, rc]
    e_eq = N.modus_ponens(domE, symetrie(E.dom(f), ve))  # E = dom f
    eqF = N.modus_ponens(e_eq, N.s6(ve, E.dom(f), "wde", appartient(vn, var("wde"))))
    n_dom = N.modus_ponens(n_E, equivalence_avant(eqF))  # n∈dom f
    rv = restriction_valeur(f, seg, vn)                  # {func f, n∈seg, n∈dom f} ⊢ u(n)=f(n)
    rv = _dech(rv, E.est_fonctionnel(f),
               fonction_globale_fonctionnelle(T, e, G, V))               # func f [CLOS]
    rv = _dech(rv, appartient(vn, E.dom(f)), n_dom)      # reste {n∈seg, bo, ebf, rc}

    # (3) réécrire u(n) → f(n) dans le produit
    tpl = produit_cardinal_binaire(successeur(vn), var("wvf"))
    imp = congruence_terme(var("wvf"), E.valeur(f, vn), tpl, "wvf")
    e7 = N.modus_ponens(rv, instancie(N.generalisation("wvf", imp), E.valeur(u, vn)))
    res = composer_egalites(fb, e7)

    cible = egal(E.valeur(f, m),
                 produit_cardinal_binaire(successeur(vn), E.valeur(f, vn)))
    assert res.conclusion == cible, "factorielle_succ_vraie : ≠ f(succ n)=(succ n)·f(n)"
    assert appartient(vn, seg) in res.hypotheses, "factorielle_succ_vraie : n∈seg absente"
    assert len(res.hypotheses) == 10, "factorielle_succ_vraie : hyps ≠ 10"
    assert res.conclusion not in res.hypotheses, "factorielle_succ_vraie : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 (Rs) DÉRIVÉE :  (∀n)( Fini n ⇒ f(succ n) = (succ n)·f(n) )
# ════════════════════════════════════════════════════════════════════════════
def donnees_ordre_closes(e="Enat", G="Gle", nb="nfac"):
    """Les QUATRE données de position, ∀-closes sous Fini n (hypothèses n-libres).

    Sur le couple VARIABLE (E,G) elles sont honnêtes ; au terme ℕ/G_ordre_NN
    chacune devient dérivable (n < succ n, seg semi-ouvert = fermé décalé…) —
    chantier instanciation.  L'ordre de la liste est celui des coupes."""
    ve, vb = _t(e), var(nb)
    segb = E.segment_extremite(_t(G), ve, successeur(vb))
    return [
        pourtout(nb, impl(est_fini(vb), appartient(successeur(vb), ve))),
        pourtout(nb, impl(est_fini(vb), egal(segb, E.intervalle_entiers(ZERO, vb)))),
        pourtout(nb, impl(est_fini(vb), appartient(ZERO, segb))),
        pourtout(nb, impl(est_fini(vb), appartient(vb, segb))),
    ]


# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« pour tout entier n, (n+1)! = n!(n+1) » — LA relation (Rs) elle-même, ∀-close sous son antécédent Fini n)
def factorielle_rs(e="Enat", G="Gle", V="Vfac62", n="nfac"):
    """🎯🎯 { bo, ebf, rc, essais_restriction(T_Z,T_Z), ZERO∈E,
             H1..H4 (données d'ordre ∀-closes) } ⊢
        (∀n)( Fini n ⇒ valeur(f, succ n) = produit(successeur(n), valeur(f, n)) )

    LA MOITIÉ (Rs) DE BOURBAKI, DÉRIVÉE — plus une équation au point, LA relation.
    Les cinq hypothèses n-dépendantes de `factorielle_succ_vraie` sont traitées :
    est_entier(n) EST est_fini(n) (même formule, synonyme) → absorbée par
    l'antécédent ; les quatre données de position → coupées par leurs ∀-clôtures
    H1..H4, instanciées sous Fini n supposé localement.  Il ne reste AUCUNE
    hypothèse où n est libre ⇒ la généralisation est légale (C27 respecté).
    NEUF hypothèses, toutes n-closes."""
    ve, vn = _t(e), var(n)
    m = successeur(vn)
    f = fonction_globale(e, V)
    seg = E.segment_extremite(_t(G), ve, m)
    I0n = E.intervalle_entiers(ZERO, vn)

    sv = factorielle_succ_vraie(e, G, V, n)              # 10 hyps, 5 n-dépendantes
    h_fin = N.assume(est_fini(vn))                       # l'antécédent (== est_entier)
    datas = [appartient(m, ve), egal(seg, I0n),
             appartient(ZERO, seg), appartient(vn, seg)]
    for Hi, data in zip(donnees_ordre_closes(e, G, nb=n), datas):
        di = N.modus_ponens(h_fin, instancie(N.assume(Hi), vn))   # {Fini n, Hi} ⊢ data
        sv = _dech(sv, data, di)
    res = N.generalisation(n, N.loi_deduction(est_fini(vn), sv))

    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_iii5 import factorielle_succ_relation
    cible = factorielle_succ_relation(lambda x: E.valeur(f, _t(x)), n=n)
    assert res.conclusion == cible, "factorielle_rs : ≠ (Rs) du livre"
    assert len(res.hypotheses) == 9, "factorielle_rs : hyps ≠ 9"
    # (la n-clôture des hypothèses est garantie par la generalisation du noyau : C27)
    assert res.conclusion not in res.hypotheses, "factorielle_rs : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯🎯 LE CAPSTONE COMPLET :  n! est un entier — (R0) ET (Rs) DÉRIVÉES.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.8 Rem.- | E III.41 L.30-32 | PDF p.144  (« (n+1)!=n!(n+1) … jointe à la relation 0!=1, caractérise le terme n! » — les DEUX moitiés désormais DÉRIVÉES sur la fonction C62 ; plus aucune moitié supposée)
def factorielle_entier_complet(e="Enat", G="Gle", V="Vfac62"):
    """🎯🎯🎯 { bo, ebf, rc, essais_restriction(T_Z,T_Z), ZERO∈E, seg(0)=∅,
              H1..H4 (données d'ordre ∀-closes) } ⊢
        (∀n)( est_fini n ⇒ est_fini( valeur(f, n) ) )                 [10 hyps]

    « n! est un entier », sur LA fonction C62 réelle, avec les DEUX moitiés de la
    caractérisation de Bourbaki DÉRIVÉES : (R0) l'était depuis
    `factorielle_c62_entier` (via `factorielle_zero`), (Rs) l'est ici via
    `factorielle_rs`.  Aucune moitié supposée : les 10 hypothèses restantes sont
    les résidus C62 + les données de position, TOUTES n-closes.
    zcard="Z" DES DEUX CÔTÉS (leçon α-variants de la caractérisation).
    ⚠️ LENT (~15-20 min) : traverse C61 deux fois (c62_entier + succ_vraie)."""
    f = fonction_globale(e, V)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_iii5 import (
        factorielle_c62_entier, factorielle_succ_relation,
    )
    base = factorielle_c62_entier(e, G, V, zcard="Z")    # 7 hyps dont (Rs)
    rs = factorielle_rs(e, G, V)                         # 9 hyps, (Rs) dérivée
    Rs = factorielle_succ_relation(lambda x: E.valeur(f, _t(x)), n="nfac")
    assert Rs in base.hypotheses, "factorielle_entier_complet : (Rs) absente de base"
    res = _dech(base, Rs, rs)                            # (Rs) DÉCHARGÉE

    assert Rs not in res.hypotheses, "factorielle_entier_complet : (Rs) PAS déchargée"
    assert len(res.hypotheses) == 10, \
        "factorielle_entier_complet : hyps ≠ 10 (%d) — zcard désaligné ?" % len(res.hypotheses)
    assert res.conclusion == base.conclusion, "factorielle_entier_complet : conclusion altérée"
    assert res.conclusion not in res.hypotheses, "factorielle_entier_complet : VACUOUS"
    return res


__all__ = ["factorielle_succ_vraie", "donnees_ordre_closes", "factorielle_rs",
           "factorielle_entier_complet"]
