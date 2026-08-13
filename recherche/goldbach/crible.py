# -*- coding: utf-8 -*-
"""Goldbach — LA FORME CRIBLE : la conjecture comme rencontre de deux ensembles.

🎯 CIBLE de ce module :
    `equivalence_crible()` :
        ⊢ ∀k(  (∃m)( m ∈ P₂ₖ ∧ m ∈ Q₂ₖ )   ⟺   DEC(2k)  )      [les DEUX sens]

où, pour un terme borne `b` :

    P_b := { x : premier_ent(x) ∧ x ∈ [0,b] }      les premiers ≤ b
    Q_b := { x : (∃y)( premier_ent(y) ∧ b = x+y ) } son « miroir »

et `DEC(2k)` = (∃p)(∃q)( premier_ent(p) ∧ premier_ent(q) ∧ 2k = p+q ).

STRATÉGIE.
  (⇐) d'un point `m` de la rencontre on tire `premier_ent(m)` (par P) et un
      témoin `y` premier avec `2k = m+y` (par Q) : la route-témoin `s5` ×2
      referme le double existentiel, puis `existe_elimination` décharge `m`.
  (⇒) des témoins `p, q` de DEC on tire `p ≤ 2k` — **c'est ici que la garde
      `Fini(p)` est consommée** (prop2_sous_fini) — donc `p ∈ [0,2k]`, donc
      `p ∈ P₂ₖ` ; et `p ∈ Q₂ₖ` avec le témoin interne `q`.

⚠️ L'ÉNONCÉ EST GARDÉ. `premier_ent(p) := Fini(p) ∧ est_premier(p)`. La garde
n'est pas cosmétique : `est_premier` du dépôt ne contraint pas son argument à
être un entier (un objet non-cardinal n'est divisible par rien, donc la clause
universelle est vraie à vide et « premier » s'y réduit à `p ≠ 1`). Sans elle,
le sens (⇒) est **indémontrable** — et l'énoncé de Goldbach serait plus faible
que la conjecture. Voir `docs/journal/ANOMALIES.md`, 2026-08-10.

⚠️ Le miroir est défini par un **∃ interne**, pas par une soustraction : ni
`diff_somme`, ni commutativité, ni cardinalité du complément ne sont requises.

Les deux ensembles sont des termes opaques caractérisés par un axiome dans une
**théorie dédiée** (le moule de l'intervalle d'entiers, E III.5.3) : la
sélection est BORNÉE par `[0,b]` pour P — jamais de compréhension non bornée
(cf. l'incohérence de l'intersection, 2026-07-26). `theorie_ensembles()` reste
à 22 axiomes : la théorie du crible est SÉPARÉE.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, appartient, egal, equiv, et, existe, pourtout, var,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_droite, conjonction_elim_gauche, conjonction_intro,
    instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_intervalle import (
    membre_intervalle_entiers_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    zero_inf_egal_cardinal,
)
from outils_ia.arithmetique.machine_num import NUM, fic_t
from outils_ia.arithmetique.lemmes_conjectures import prop2_sous_fini
from outils_ia.conjectures.goldbach import est_premier

_mp = N.modus_ponens
ZERO = NUM(0)

#: liants FIXÉS de ce module (frais vis-à-vis de `est_premier` et de `[0,b]`)
LIANT_K = "kgb"
LIANT_P, LIANT_Q = "pgb", "qgb"
LIANT_M, LIANT_Y = "mrx", "ymi"


def premier_ent(t, d="d1", q="q1"):
    """« t est un entier premier » := Fini(t) ∧ est_premier(t).

    LA GARDE `Fini` EST ESSENTIELLE (cf. l'entête du module) : sans elle
    l'énoncé porterait sur des témoins non entiers."""
    return et(est_fini(t), est_premier(t, d=d, q=q))


def premiers_bornes(b):
    """P_b := { x : premier_ent(x) ∧ x ∈ [0,b] }   (terme opaque)."""
    return app("premiers_ent_bornes", b)


def miroir(b):
    """Q_b := { x : (∃y)( premier_ent(y) ∧ b = x+y ) }   (terme opaque)."""
    return app("miroir_ent", b)


def axiome_premiers_bornes(b="bpe", x="xpe"):
    """(∀b)(∀x)( x ∈ P_b ⇔ ( premier_ent(x) ∧ x ∈ [0,b] ) ).

    Sélection BORNÉE par [0,b] : légitimée par S8 + A1, forme C51-sûre."""
    vb, vx = var(b), var(x)
    return pourtout(b, pourtout(x, equiv(
        appartient(vx, premiers_bornes(vb)),
        et(premier_ent(vx), appartient(vx, E.intervalle_entiers(ZERO, vb))))))


def axiome_miroir(b="bmi", x="xmi", y=LIANT_Y):
    """(∀b)(∀x)( x ∈ Q_b ⇔ (∃y)( premier_ent₂(y) ∧ b = x+y ) ).

    ⚠️ GRAPHIE `d2/q2` — celle du SECOND témoin de `decomposition_gardee`.
    Les liants de `est_premier` doivent rester frais d'un appel à l'autre
    (deux primalités imbriquées sur le même liant entreraient en collision) ;
    la cohérence des habits évite ici tout pont-α."""
    vb, vx = var(b), var(x)
    return pourtout(b, pourtout(x, equiv(
        appartient(vx, miroir(vb)),
        existe(y, et(premier_ent(var(y), "d2", "q2"),
                     egal(vb, SC(vx, var(y))))))))


def theorie_crible():
    """La théorie DÉDIÉE aux deux ensembles — séparée de theorie_ensembles()."""
    return N.Theorie("Crible-Goldbach",
                     [axiome_premiers_bornes(), axiome_miroir()])


def membre_premiers_bornes(b, x):
    """⊢ x ∈ P_b ⇔ ( premier_ent(x) ∧ x ∈ [0,b] )   pour des TERMES b, x."""
    ax = N.axiome(theorie_crible(), axiome_premiers_bornes())
    return instancie(instancie(ax, b), x)


def membre_miroir(b, x):
    """⊢ x ∈ Q_b ⇔ (∃y)( premier_ent(y) ∧ b = x+y )   pour des TERMES b, x."""
    ax = N.axiome(theorie_crible(), axiome_miroir())
    return instancie(instancie(ax, b), x)


def _double(k=LIANT_K):
    """Le terme 2k := k + k."""
    return SC(var(k), var(k))


def decomposition_gardee(k=LIANT_K):
    """DEC(2k) := (∃p)(∃q)( premier_ent(p) ∧ premier_ent(q) ∧ 2k = p+q )."""
    M = _double(k)
    mat = et(et(premier_ent(var(LIANT_P), "d1", "q1"),
                premier_ent(var(LIANT_Q), "d2", "q2")),
             egal(M, SC(var(LIANT_P), var(LIANT_Q))))
    return existe(LIANT_P, existe(LIANT_Q, mat))


def rencontre(k=LIANT_K):
    """(∃m)( m ∈ P₂ₖ ∧ m ∈ Q₂ₖ )   — « les premiers ≤ 2k rencontrent leur miroir »."""
    M = _double(k)
    vm = var(LIANT_M)
    return existe(LIANT_M, et(appartient(vm, premiers_bornes(M)),
                              appartient(vm, miroir(M))))


def crible_implique_decomposition(k=LIANT_K):
    """🎯 ⊢ ∀k( rencontre(k) ⇒ DEC(2k) ).   [CLOS, 0 hypothèse]

    Sens (⇐). Sous un point `m` de la rencontre : `premier_ent(m)` vient de P ;
    le témoin `y` (premier, `2k = m+y`) vient de Q ; la route-témoin `s5` ×2
    referme le double ∃ ; `existe_elimination` décharge `y` puis `m`."""
    M = _double(k)
    vm, vy = var(LIANT_M), var(LIANT_Y)
    DEC = decomposition_gardee(k)
    inner = DEC.sous[0]                                   # (∃q) mat

    hm = N.assume(et(appartient(vm, premiers_bornes(M)),
                     appartient(vm, miroir(M))))
    prem_m = conjonction_elim_gauche(
        _mp(conjonction_elim_gauche(hm),
            conjonction_elim_gauche(membre_premiers_bornes(M, vm))))
    corps_Q = _mp(conjonction_elim_droite(hm),
                  conjonction_elim_gauche(membre_miroir(M, vm)))

    #   ⚠️ PIÈGE DES LIANTS : ne PAS reconstruire la matrice du ∃ du miroir —
    #   le noyau a pu α-renommer son liant. On LIT celui qu'il a produit.
    exY = corps_Q.conclusion
    assert exY.tag == "exists", "crible : corps du miroir n'est pas un ∃"
    ly, maty = exY.lieur, exY.sous[0]
    vy = var(ly)
    hy = N.assume(maty)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        subst_f,
    )
    inner_m = subst_f(vm, LIANT_P, inner)
    mat_my = inner_m.sous[0]
    c_b = conjonction_intro(conjonction_intro(prem_m,
                                              conjonction_elim_gauche(hy)),
                            conjonction_elim_droite(hy))
    assert c_b.conclusion == subst_f(vy, LIANT_Q, mat_my), \
        "crible : matrice reconstruite ≠ matrice substituée"
    dec_y = _mp(_mp(c_b, N.s5(mat_my, vy, LIANT_Q)), N.s5(inner, vm, LIANT_P))
    assert dec_y.conclusion == DEC
    dec_m = _mp(corps_Q, existe_elimination(N.loi_deduction(maty, dec_y), ly))
    th = N.generalisation(
        k, existe_elimination(N.loi_deduction(hm.conclusion, dec_m), LIANT_M))
    assert th.est_clos and not th.hypotheses, "crible (⇐) non clos"
    return th


def decomposition_implique_crible(k=LIANT_K):
    """🎯 ⊢ ∀k( DEC(2k) ⇒ rencontre(k) ).   [CLOS, 0 hypothèse]

    Sens (⇒) — CELUI QUI CONSOMME LA GARDE. De `2k = p+q` et `Fini(p)`,
    `prop2_sous_fini` donne `p ≤ 2k` ; avec `card p` et `0 ≤ p` on place `p`
    dans `[0,2k]`, donc dans P₂ₖ ; et `p ∈ Q₂ₖ` avec le témoin interne `q`.
    Sans `Fini(p)`, aucune de ces étapes n'est disponible."""
    M = _double(k)
    vp, vq = var(LIANT_P), var(LIANT_Q)
    DEC = decomposition_gardee(k)
    inner = DEC.sous[0]
    mat = inner.sous[0]

    h = N.assume(mat)
    fini_p = conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h)))
    prem_p = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_gauche(h)))
    prem_ent_q = conjonction_elim_droite(conjonction_elim_gauche(h))
    somme = conjonction_elim_droite(h)

    #   p ≤ 2k   (prop2_sous_fini est CURRYFIÉ : Fini a ⇒ (b = a+c ⇒ a ≤ b))
    p2 = instancie(instancie(instancie(
        N.generalisation("a", N.generalisation("b", N.generalisation(
            "c", prop2_sous_fini("a", "b", "c")))), vp), M), vq)
    le_p = _mp(somme, _mp(fini_p, p2))
    card_p = _mp(fini_p, fic_t(vp))
    zero_le_p = _mp(card_p, N.loi_deduction(est_cardinal(vp),
                                            zero_inf_egal_cardinal(vp)))
    p_in_int = _mp(conjonction_intro(conjonction_intro(card_p, zero_le_p), le_p),
                   conjonction_elim_droite(
                       membre_intervalle_entiers_t(ZERO, M, vp)))
    p_in_P = _mp(conjonction_intro(conjonction_intro(fini_p, prem_p), p_in_int),
                 conjonction_elim_droite(membre_premiers_bornes(M, vp)))

    #   p ∈ Q₂ₖ avec le témoin y := q — on LIT le liant produit par le noyau
    impQ = conjonction_elim_droite(membre_miroir(M, vp))
    exY = impQ.conclusion.sous[0].sous[0]
    assert exY.tag == "exists", "crible : forme du ∃ du miroir inattendue"
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        subst_f,
    )
    fourni = conjonction_intro(prem_ent_q, somme)
    assert fourni.conclusion == subst_f(vq, exY.lieur, exY.sous[0]), \
        "crible : matrice du miroir ≠ attendue"
    p_in_Q = _mp(_mp(fourni, N.s5(exY.sous[0], vq, exY.lieur)), impQ)

    vm = var(LIANT_M)
    mat_renc = et(appartient(vm, premiers_bornes(M)), appartient(vm, miroir(M)))
    ex_m = _mp(conjonction_intro(p_in_P, p_in_Q), N.s5(mat_renc, vp, LIANT_M))
    assert ex_m.conclusion == rencontre(k)

    imp_q = existe_elimination(N.loi_deduction(mat, ex_m), LIANT_Q)
    imp_p = existe_elimination(
        N.loi_deduction(inner, _mp(N.assume(inner), imp_q)), LIANT_P)
    th = N.generalisation(k, imp_p)
    assert th.est_clos and not th.hypotheses, "crible (⇒) non clos"
    return th


def equivalence_crible(k=LIANT_K):
    """🎯🎯 Les DEUX sens : (crible ⇒ DEC, DEC ⇒ crible), tous deux CLOS."""
    return crible_implique_decomposition(k), decomposition_implique_crible(k)


__all__ = [
    "premier_ent", "premiers_bornes", "miroir",
    "axiome_premiers_bornes", "axiome_miroir", "theorie_crible",
    "membre_premiers_bornes", "membre_miroir",
    "decomposition_gardee", "rencontre",
    "crible_implique_decomposition", "decomposition_implique_crible",
    "equivalence_crible",
]
