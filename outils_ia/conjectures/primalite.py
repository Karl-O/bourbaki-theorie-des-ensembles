"""Primalité effective  —  ⊢ est_premier( N(p) )  pour p premier.

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE DÉMONTRE.  L'énoncé `goldbach.est_premier`, appliqué au numéral
N(p), pour un p premier quelconque.  Mesuré : p = 7 en 57 s à froid, puis 2, 3,
5, 11, 13, 17 en moins de 8 s chacun — tous CLOS, 0 hypothèse.

Ce n'est pas `est_premier(2)` en plus grand.  Pour 2, l'énumération donne {0,1,2}
et les cas autorisés sont {1,2} : il ne restait que d = 0 à écarter, sans aucune
arithmétique.  Ici les cas 2, 3, 4, 5, 6 doivent être écartés par un vrai calcul,
fourni par `non_divisibilite.non_divise`.

────────────────────────────────────────────────────────────────────────────────
🔴 LE PIÈGE DE FIDÉLITÉ, MESURÉ LE 6 AOÛT 2026, ET SA RÉPARATION.

`goldbach.est_premier` compare le diviseur au « 1 » CONSTRUIT `un() = Card{∅}`.
Les numéraux, eux, valent `N(1) = successeur(Card ∅)`.  Mesure : `N(1) == UN` est
VRAI, mais `N(1) == goldbach.un()` est FAUX — ce sont deux TERMES distincts.  Les
conjoindre sans précaution reviendrait à écrire un énoncé portant sur deux objets
différents : exactement la faute déjà consignée pour `application_canonique_g`.

⚠️ LA RÉPARATION INTERDITE aurait été de réécrire `goldbach.est_premier` pour
qu'il colle aux numéraux.  Adapter l'ÉNONCÉ à la preuve est la faute capitale :
elle rend le théorème vrai et sans valeur.  `goldbach.py` n'est pas touché.

On adapte la PREUVE, par un pont explicite qui est un théorème CLOS DU DÉPÔT :

        `un_egale_card_singleton()`   ⊢  UN = Card{∅}     soit  N(1) = un()

puis Leibniz (S6).  La conclusion est ensuite comparée — égalité de formules — à
`goldbach.est_premier(N(p))` reconstruit depuis le module d'énoncé.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE.  est_premier(p)  =  ¬(p = 1)  et  (∀d)( (Fini d et d|p) ⇒ (d=1 ou d=p) ).

  GAUCHE.  `ne_num_sym(1, p)` donne ¬( N(p) = N(1) ) ; le pont le transporte.
  DROITE.  Sous l'antécédent, `diviseur_majore` donne d ≤ N(p) et `enum` referme
           le domaine.  Le « ou » de l'énoncé étant ¬(¬A et ¬B), on suppose
           (¬A et ¬B) et l'on ferme les p+1 branches par TROIS recettes :
             · j = 1  : d = N(1) = un() = A          contredit ¬A ;
             · j = p  : d = N(p) = B                 contredit ¬B ;
             · sinon  : d = N(j) transporte d | N(p) en N(j) | N(p), que
                        `non_divise` réfute — c'est là que passe l'arithmétique.
           Puis S1 décharge (¬A et ¬B), la loi de déduction décharge
           l'antécédent, et l'on généralise sur d.

────────────────────────────────────────────────────────────────────────────────
LE CONTRÔLE QUI COMPTE.  Sur un COMPOSÉ la machine doit ÉCHOUER.  `garde=True`
dit où (la branche j = p/i) — mais **une garde Python ne prouve rien**.  Avec
`garde=False`, propagé JUSQU'À `non_divise`, la machine meurt dans `ne_num` sur
`assert a != b` : il lui faudrait ¬( N(9) = N(9) ).  Mesuré sur 4, 9 et 15 ; et
p = 7 continue de clore, donc rien n'est cassé par la désactivation.

⚠️ Ce contrôle a d'abord été FAUX : `garde` n'était pas propagé, et l'échec venait
de la garde Python de `non_divise`, pas de l'arithmétique.  Une recette qui
réussit partout ne prouve rien ; une recette dont on ne sait pas OÙ elle échoue
n'en dit guère plus.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (
    un_egale_card_singleton,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C
from outils_ia.arithmetique import non_divisibilite as D
from outils_ia.conjectures import goldbach as GB

mp = N.modus_ponens
NUM = M.NUM

_PONT = None


def pont_un():
    """⊢ N(1) = un()  —  c'est `un_egale_card_singleton` du dépôt, tel quel.

    Vérifié ici, et pas supposé : si le « 1 » de l'énoncé changeait, l'assertion
    tomberait au lieu de laisser passer un théorème portant sur un autre terme."""
    global _PONT
    if _PONT is None:
        th = un_egale_card_singleton()
        assert th.est_clos and not th.hypotheses, "le pont doit être clos"
        assert th.conclusion == egal(NUM(1), GB.un()), (
            "le pont ne relie pas N(1) au « 1 » de est_premier")
        _PONT = th
    return _PONT


def pont_un_cible():
    """Énoncé visé : N(1) = un() (compagne zéro-arg pour le gate du volant)."""
    return egal(NUM(1), GB.un())


pont_un_gate_caches = ("_PONT",)   # sans ce voile, le gate relit le cache et ne teste rien


def obstruction(p):
    """Les j de l'énumération qu'aucune des trois recettes ne ferme.

    Un j est fermable s'il vaut 1 (donne A), s'il vaut p (donne B), ou si N(j) ne
    divise pas N(p).  Reste exactement l'ensemble des diviseurs propres non
    triviaux — vide si et seulement si p est premier."""
    return [j for j in range(2, p) if p % j == 0]


def est_premier_num(p, d="dgb", q="qgb", garde=True):
    """⊢ est_premier( N(p) )  pour p premier.               [CLOS, 0 hypothèse]

    `garde=False` désactive les refus Python À TOUS LES ÉTAGES (y compris dans
    `non_divise`) : c'est ainsi, et seulement ainsi, que le contrôle adversarial
    montre où l'ARITHMÉTIQUE bloque sur un composé."""
    assert p >= 2, "primalité : p >= 2 attendu"
    bad = obstruction(p)
    if bad and garde:
        raise ValueError(
            "OBSTRUCTION en p=%d : la branche j=%d de l'énumération est INFERMABLE "
            "— N(%d) divise VRAIMENT N(%d) (quotient %d), et j n'est ni 1 ni p."
            % (p, bad[0], bad[0], p, p // bad[0]))

    vd, Np, pont = var(d), NUM(p), pont_un()
    A = egal(vd, GB.un())                     # d = 1  (le « 1 » de l'énoncé)
    B = egal(vd, Np)                          # d = N(p)
    but = non(et(non(A), non(B)))             # le « ou » de est_premier
    ante = et(est_fini(vd), divise_propre(vd, Np, q=q))

    # ── GAUCHE : ¬( N(p) = un() ), par transport de ¬( N(p) = N(1) ) ─────────
    gauche = M.reecrit(pont, M.ne_num_sym(1, p), non(egal(Np, var(M._HOLE))))
    assert gauche.conclusion == non(egal(Np, GB.un())) and gauche.est_clos

    # ── DROITE : sous l'antécédent, on referme le domaine du diviseur ────────
    h = N.assume(ante)
    fini_d = conjonction_elim_gauche(h)
    div_d = conjonction_elim_droite(h)                              # d | N(p)
    le_d = mp(conjonction_intro(conjonction_intro(fini_d, M.ne_num_sym(0, p)), div_d),
              D.diviseur_majore_t(vd, Np, lieur=q))                 # d ≤ N(p)
    disj_thm = mp(le_d, C.enum(vd, p, card_d=mp(fini_d, M.fic_t(vd))))

    h2 = N.assume(et(non(A), non(B)))
    nA, nB = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)

    def branche(j):
        """⊢ ( d = N(j) ) ⇒ ¬(¬A et ¬B),  par l'une des TROIS recettes."""
        hj = N.assume(egal(vd, NUM(j)))
        if j == 1:
            falso = M.ex_falso(composer_egalites(hj, pont), nA, but)   # d = un()
        elif j == p:
            falso = M.ex_falso(hj, nB, but)                            # d = N(p)
        else:
            div_j = M.reecrit(hj, div_d, divise_propre(var(M._HOLE), Np, q=q))
            assert div_j.conclusion == divise_propre(NUM(j), Np, q=q)
            # ⚠️ `garde` est PROPAGÉ : sinon le contrôle adversarial mourrait sur
            # la garde Python de `non_divise`, et non sur l'arithmétique.
            falso = M.ex_falso(div_j, D.non_divise(j, p, q=q, garde=garde), but)
        return N.loi_deduction(egal(vd, NUM(j)), falso)

    cur = branche(0)
    for j in range(1, p + 1):
        dj = C.disj(vd, j)
        cur = N.loi_deduction(dj, cas(N.assume(dj), cur, branche(j)))

    droite = N.loi_deduction(ante, M.neg_intro(et(non(A), non(B)), mp(disj_thm, cur)))
    assert droite.est_clos, "résidu avant généralisation : %s" % (droite.hypotheses,)
    univ = N.generalisation(d, droite)
    assert univ.conclusion == pourtout(d, droite.conclusion)

    res = conjonction_intro(gauche, univ)
    assert res.conclusion == GB.est_premier(Np, d=d, q=q), (
        "est_premier_num(%d) : la conclusion n'est PAS l'énoncé de goldbach.py" % p)
    assert res.est_clos and not res.hypotheses, "est_premier_num(%d) non clos" % p
    return res


__all__ = ["pont_un", "pont_un_cible", "obstruction", "est_premier_num"]
