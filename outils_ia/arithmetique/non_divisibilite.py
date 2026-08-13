"""Non-divisibilité effective  —  ⊢ ¬( N(i) | N(p) )  dès que i ∤ p.

────────────────────────────────────────────────────────────────────────────────
L'ENJEU.  `est_premier(2)` était clos depuis le 5 août 2026, mais sa preuve ne
contenait AUCUNE arithmétique : l'énumération donne {0,1,2}, les cas autorisés
sont {1,2}, il ne restait que d = 0 à écarter.  C'était un accident de petitesse.

Pour 7 il faut vraiment établir que 2, 3, 4, 5 et 6 ne divisent pas 7.  Ce module
est le premier calcul arithmétique réel du corpus : la conclusion dépend de la
valeur des nombres, pas de la forme de l'énoncé.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE, en cinq maillons, tous paramétriques en (i, p).
Supposons N(i) | N(p), c'est-à-dire (∃q)( Fini q  et  N(p) = N(i)·q ).

 1. COMMUTATION.  N(p) = N(i)·q donne N(p) = q·N(i) par
    `produit_cardinal_commutatif`.  Ce basculement fait du QUOTIENT un DIVISEUR.
 2. MAJORATION DU QUOTIENT.  `diviseur_majore` (dépôt, clos) appliqué DE L'AUTRE
    CÔTÉ — d := q, témoin N(i) — donne q ≤ N(p).  C'est le pas décisif : un lemme
    d'ORDRE devient un outil de CALCUL parce qu'on l'applique au quotient.
    L'antécédent ¬( N(p) = 0 ) vient de `ne_num_sym(0, p)`.
 3. ÉNUMÉRATION.  `enum` referme le domaine : q ≤ N(p) ⇒ q = N(0) ou … ou N(p).
 4. CALCUL, cas par cas.  Sous q = N(j) : N(p) = N(i)·N(j) = N(i·j) par
    `produit_num`.  Comme i ∤ p, on a i·j ≠ p pour TOUT j ≤ p, donc `ne_num`
    contredit.  p+1 branches, toutes fermées, aucune gratuite.
 5. FERMETURE.  Recollement par `cas`, élimination de l'existentielle, puis S1.

⚠️ COLLISION DE LIANTS.  Le lieur de la divisibilité passée à `diviseur_majore`
DOIT différer de celui de l'existentielle extérieure : les laisser égaux capture
la variable et produit N(p) = q·q.  D'où les deux noms `qdiv` et `qmaj`.

────────────────────────────────────────────────────────────────────────────────
DEUX CONTRÔLES, parce qu'une négation gratuite ne vaudrait rien.

 · ANTI-VACUITÉ.  `divise_positif` PROUVE la divisibilité quand elle a lieu, sur
   exactement le même `divise_propre` importé du dépôt.  Le prédicat est donc
   satisfiable : les négations ne sont pas l'artefact d'une définition vide.
 · NON-UNIVERSALITÉ.  Sur i | p la recette doit ÉCHOUER.  La garde Python dit où
   (branche j = p/i) ; mais **une garde Python ne prouve rien** : le contrôle qui
   compte se fait `garde=False`, et la machine meurt alors dans `ne_num`, faute
   de pouvoir produire ¬( N(p) = N(p) ).  Mesuré : en POSANT cette formule fausse
   en hypothèse on dérive n'importe quoi, avec une hypothèse jamais déchargeable
   puisque ⊢ N(p) = N(p) est clos — fermer la branche rendrait le corpus
   incohérent.  C'est là, et pas dans un `assert`, qu'est le vrai verrou.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, existe, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO, est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_commutatif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_diviseur_majore import (
    diviseur_majore,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C

mp = N.modus_ponens
NUM = M.NUM

#: QDIV = lieur de l'existentielle EXTÉRIEURE ; QMAJ = celui, obligatoirement
#: DISTINCT, de la divisibilité interne passée à `diviseur_majore`.
QDIV, QMAJ = "qdiv", "qmaj"

_COMM = None
_DM: dict[str, object] = {}


def _comm_t(ta, tb):
    """⊢ A·B = B·A   pour des TERMES A, B."""
    global _COMM
    if _COMM is None:
        base = produit_cardinal_commutatif("Xcm", "Ycm")
        assert base.est_clos, "produit_cardinal_commutatif non clos"
        _COMM = N.generalisation("Xcm", N.generalisation("Ycm", base))
    r = instancie(instancie(_COMM, ta), tb)
    assert r.conclusion == egal(produit_cardinal_binaire(ta, tb),
                                produit_cardinal_binaire(tb, ta)) and r.est_clos
    return r


def diviseur_majore_t(td, tp, lieur=QMAJ):
    """⊢ ( Fini(D) et ¬(P = 0) et (∃lieur)(Fini lieur et P = D·lieur) ) ⇒ D ≤ P.

    ⚠️ Le `lieur` doit être celui de la divisibilité QUE L'ON CONSOMME.  Un lieur
    différent produirait un antécédent que l'on ne possède pas ; le même que le
    quantificateur extérieur produirait une capture."""
    if lieur not in _DM:
        base = diviseur_majore("ddm", "pdm", lieur)
        assert base.est_clos, "diviseur_majore non clos"
        _DM[lieur] = N.generalisation("pdm", N.generalisation("ddm", base))
    return instancie(instancie(_DM[lieur], tp), td)


def cible(i, p, q=QDIV):
    """La formule  ¬( N(i) | N(p) ),  construite avec le `divise_propre` du dépôt."""
    return non(divise_propre(NUM(i), NUM(p), q=q))


def obstruction(i, p):
    """Le j de l'énumération qu'aucune contradiction ne ferme, ou None.

    C'est exactement le quotient p/i quand i divise p : là, N(i)·N(j) = N(p) est
    VRAI, et il n'y a rien à en tirer."""
    temoins = [j for j in range(p + 1) if i * j == p]
    return temoins[0] if temoins else None


def non_divise(i, p, q=QDIV, garde=True):
    """⊢ ¬( divise_propre(N(i), N(p)) )   pour i ∤ p.       [CLOS, 0 hypothèse]

    `garde=False` désactive le refus Python en amont : le contrôle adversarial
    s'en sert pour vérifier que sur un cas faux c'est l'ARITHMÉTIQUE qui bloque."""
    j_bad = obstruction(i, p)
    if j_bad is not None and garde:
        raise ValueError(
            "OBSTRUCTION en (i=%d, p=%d) : la branche j=%d de l'énumération est "
            "INFERMABLE — N(%d)·N(%d) = N(%d) EST N(%d), il n'y a aucune "
            "contradiction à y tirer." % (i, p, j_bad, i, j_bad, i * j_bad, p))

    vq = var(q)
    div = divise_propre(NUM(i), NUM(p), q=q)
    corps = et(est_fini(vq), egal(NUM(p), produit_cardinal_binaire(NUM(i), vq)))
    assert existe(q, corps) == div, "le corps ne recompose pas divise_propre"
    but = non(div)

    h = N.assume(corps)
    fini_q = conjonction_elim_gauche(h)
    eq_p = conjonction_elim_droite(h)                     # N(p) = N(i)·q

    # ── (1) + (2)  le quotient est majoré ────────────────────────────────────
    matrice = et(est_fini(var(QMAJ)),
                 egal(NUM(p), produit_cardinal_binaire(vq, var(QMAJ))))
    div_q = mp(conjonction_intro(M.fini_num(i),
                                 composer_egalites(eq_p, _comm_t(NUM(i), vq))),
               N.s5(matrice, NUM(i), QMAJ))               # q | N(p)
    assert div_q.conclusion == divise_propre(vq, NUM(p), q=QMAJ)
    ne_p0 = M.ne_num_sym(0, p)
    assert ne_p0.conclusion == non(egal(NUM(p), ZERO))
    le_q = mp(conjonction_intro(conjonction_intro(fini_q, ne_p0), div_q),
              diviseur_majore_t(vq, NUM(p)))              # q ≤ N(p)

    # ── (3) le domaine du quotient est fini et connu ─────────────────────────
    disj_thm = mp(le_q, C.enum(vq, p, card_d=mp(fini_q, M.fic_t(vq))))

    def branche(j):
        """⊢ ( q = N(j) ) ⇒ ¬div    (i·j ≠ p : le calcul contredit)."""
        eq_ij = M.reecrit(N.assume(egal(vq, NUM(j))), eq_p,
                          egal(NUM(p), produit_cardinal_binaire(NUM(i), var(M._HOLE))))
        eq_ij = composer_egalites(eq_ij, C.produit_num(i, j))
        assert eq_ij.conclusion == egal(NUM(p), NUM(i * j))
        return N.loi_deduction(egal(vq, NUM(j)),
                               M.ex_falso(eq_ij, M.ne_num_quelconque(p, i * j), but))

    # ── (5) recollement, puis fermeture ──────────────────────────────────────
    cur = branche(0)
    for j in range(1, p + 1):
        d_j = C.disj(vq, j)
        cur = N.loi_deduction(d_j, cas(N.assume(d_j), cur, branche(j)))
    assert cur.conclusion == impl(C.disj(vq, p), but)

    imp = N.loi_deduction(corps, mp(disj_thm, cur))
    assert imp.est_clos, "résidu d'hypothèse avant l'élimination : %s" % (imp.hypotheses,)
    assert q not in libres_f(but), "le lieur %s fuit dans la conclusion" % q
    res = mp(existe_elimination(imp, q), N.s1(but))

    assert res.conclusion == cible(i, p, q), "non_divise(%d,%d) : ≠ cible" % (i, p)
    assert res.est_clos and not res.hypotheses, "non_divise(%d,%d) non clos" % (i, p)
    return res


def divise_positif(i, p, q=QDIV):
    """⊢ divise_propre( N(i), N(p) )   quand i | p   (témoin q = N(p/i)).

    CONTRÔLE D'ANTI-VACUITÉ : sans lui, `non_divise` pourrait n'être que la
    négation d'un prédicat vide, et ne rien dire d'arithmétique."""
    assert i > 0 and p % i == 0, "divise_positif : i doit diviser p"
    j = p // i
    eq = mp(C.produit_num(i, j),
            symetrie(produit_cardinal_binaire(NUM(i), NUM(j)), NUM(p)))
    matrice = et(est_fini(var(q)), egal(NUM(p), produit_cardinal_binaire(NUM(i), var(q))))
    # le motif « ∃-intro par témoin vérifié », désormais tactique nommée (ev.283)
    r = M.existe_temoin_verifie(conjonction_intro(M.fini_num(j), eq),
                                matrice, NUM(j), q)
    assert r.conclusion == divise_propre(NUM(i), NUM(p), q=q)
    assert r.est_clos and not r.hypotheses
    return r


__all__ = ["QDIV", "QMAJ", "cible", "obstruction", "non_divise", "divise_positif",
           "diviseur_majore_t"]
