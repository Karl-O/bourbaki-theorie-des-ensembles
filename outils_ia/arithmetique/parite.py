# -*- coding: utf-8 -*-
"""RÉFUTER LA PARITÉ D'UN IMPAIR —  ⊢ ¬(∃m)( N(i) = m + m )   [CLOS, 0 hypothèse].

────────────────────────────────────────────────────────────────────────────────
CE QUE C'EST.  `goldbach.py` écrit « n est pair » par  (∃k)( n = k + k )  sur la
somme cardinale.  Cette formule quantifie sur des ENSEMBLES quelconques : rien n'y
dit que k est un cardinal, encore moins un entier.  Réfuter la parité de N(3) n'est
donc PAS un calcul de parité — c'est montrer qu'AUCUN ensemble m, si tordu soit-il,
ne vérifie N(3) = Card(m ⊔ m).

C'est exactement le chantier que `goldbach_borne.py` avait CONTOURNÉ en paramétrant
par la moitié k (cf. sa docstring : « écrit sur n, l'énoncé demanderait de savoir
ÉCARTER les impairs — c'est-à-dire démontrer ¬(∃m)( N(3) = m+m ) »).  Le voici
fait, et pour i = 3, 5, 7, 9, 11.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE, EN CINQ PAS.  Sous l'hypothèse  h : N(i) = m + m  (m = le liant de
l'existentielle, aucune hypothèse sur lui) :

 1. BORNE.  `inf_egal_somme_gauche_binaire(m, m)` donne ⊢ Card(m) ≤ m + m, et ce
    lemme est INCONDITIONNEL (vérifié clos ici même, pas supposé).  Réécrit par h
    renversée (Leibniz S6) :   Card(m) ≤ N(i).

 2. m DEVIENT UN CARDINAL — gratuitement.  `est_cardinal(a)` est (∃X)(a = Card X) ;
    en a := Card(m) le témoin X := m est fourni par la RÉFLEXIVITÉ seule.  ⚠️ Le
    liant doit rester le liant PAR DÉFAUT « X », celui qu'`enum` reconnaît.

 3. DOMAINE REFERMÉ.  `enum(Card m, i, card_d=·)` transforme Card(m) ≤ N(i) en la
    disjonction FINIE   Card m = N(0)  ou … ou  Card m = N(i).

 4. CHAQUE BRANCHE EST ARITHMÉTIQUE.  Sous Card m = N(j), le PONT DE CARDINALITÉ
    (⊢ m+m = Card m + Card m, clos pour un m ARBITRAIRE) donne m+m = N(j)+N(j),
    puis `somme_num(j,j)` donne N(2j).  Avec h : N(i) = N(2j).  Or i est IMPAIR,
    donc i ≠ 2j pour TOUT j, et `ne_num_quelconque(i, 2j)` réfute.

 5. RECOLLEMENT.  `cas` sur la disjonction, `loi_deduction`, `existe_elimination`
    (le liant n'est pas libre dans la cible ¬(∃m)…), puis S1.

────────────────────────────────────────────────────────────────────────────────
POURQUOI LE PONT EST INDISPENSABLE, ET PAS UN CONFORT.  Sans lui, l'étape 4 est
bloquée : `enum` parle de Card(m), l'hypothèse h parle de m+m = Card(m ⊔ m), et
RIEN dans le noyau ne permet de remplacer m par Card m sous la somme disjointe —
la somme cardinale binaire est Card(a ⊔ b), pas Card(Card a ⊔ Card b) (piège 3 de
la campagne).  Le pont est précisément l'égalité de ces deux termes, démontrée
sans aucune hypothèse sur m.

────────────────────────────────────────────────────────────────────────────────
LE CONTRÔLE DE NON-UNIVERSALITÉ.  La recette DOIT échouer sur un i PAIR, et pour
la bonne raison.  `non_pair(4, garde=False)` échoue dans

    outils_ia/arithmetique/machine_num.py:245
        assert a != b, "ne_num_quelconque : a != b attendu"

à la branche j = 2, où l'on demanderait ⊢ ¬( N(4) = N(4) ).  L'échec est donc
ARITHMÉTIQUE — c'est le noyau qui refuse de réfuter une égalité vraie —, et non un
garde-fou cosmétique du script.  Idem pour i = 6 à la branche j = 3.

INVARIANT : aucun `Theoreme` fabriqué, aucun `_CLE`, aucun monkeypatch ;
`theorie_ensembles()` reste à 22 axiomes.  Aucun fichier du dépôt n'est modifié.
"""
from __future__ import annotations

import os
import sys
import time

RACINE = r"C:\Users\KARL\OneDrive\Bureau\Apprendre\Livre\Bourbakie\Theorie_des_ensembles\V9"
SCRATCH = os.path.dirname(os.path.abspath(__file__))
for p in (RACINE, SCRATCH):
    if p not in sys.path:
        sys.path.insert(0, p)
sys.setrecursionlimit(200000)

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, existe, pourtout, afficher_f, libres_t, libres_f, subst_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
    inf_egal_somme_gauche_binaire,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures import goldbach_borne as GBB

from outils_ia.arithmetique.pont_cardinal import pont_card

mp = N.modus_ponens
NUM = M.NUM

#: le liant de l'existentielle de parité — celui de `goldbach.goldbach()`.
K_PAIR = "kgb"


# ══════════════════════════════════════════════════════════════════════════════
#  L'ÉNONCÉ — construit avec les briques du dépôt, jamais recopié à la main
# ══════════════════════════════════════════════════════════════════════════════
def corps_pair(t, k=K_PAIR):
    """Le corps de la parité :  T = k + k   (somme cardinale binaire)."""
    vk = var(k)
    return egal(t, SC(vk, vk))


def est_pair(t, k=K_PAIR):
    """« T est pair » := (∃k)( T = k + k ).   C'est LA formule de `goldbach()`."""
    return existe(k, corps_pair(t, k))


def cible_non_pair(i, k=K_PAIR):
    """LA cible :  ¬(∃k)( N(i) = k + k ).

    N(i) est un terme CLOS (libres_t = ∅, vérifié) : aucune capture possible."""
    return non(est_pair(NUM(i), k))


def fidelite_verifiee():
    """`est_pair` EST la parité de `goldbach.goldbach()` — rebâti, pas supposé.

    On reconstruit l'énoncé complet de Goldbach à partir de la brique `est_pair`
    d'ici (et de `decomposition` de goldbach_borne, déjà certifiée fidèle) et l'on
    exige l'égalité de formules avec `GB.goldbach()`."""
    vn = var("ngb")
    ante = et(et(et(est_fini(vn), est_pair(vn)), non(egal(vn, GB.zero()))),
              non(egal(vn, GB.deux())))
    return pourtout("ngb", impl(ante, GBB.decomposition(vn))) == GB.goldbach()


# ══════════════════════════════════════════════════════════════════════════════
#  LES DEUX BRIQUES LOCALES (chacune vérifiée à la construction)
# ══════════════════════════════════════════════════════════════════════════════
_BORNE: dict = {}


def borne_gauche(vm):
    """⊢ Card(m) ≤ ( m + m ).   INCONDITIONNEL — mesuré clos, pas supposé.

    C'est `inf_egal_somme_gauche_binaire` du dépôt (E.III.5.2), instancié en
    a := b := m.  La clôture est VÉRIFIÉE ici : c'est elle qui permet d'attaquer
    un m sur lequel on ne suppose rien."""
    cle = repr(vm)
    if cle not in _BORNE:
        th = inf_egal_somme_gauche_binaire(vm, vm)
        assert th.conclusion == inf_egal_card(cardinal(vm), SC(vm, vm)), \
            "borne_gauche : conclusion inattendue"
        assert th.est_clos and not th.hypotheses, \
            "borne_gauche : lemme NON clos (%d hyps)" % len(th.hypotheses)
        _BORNE[cle] = th
    return _BORNE[cle]


def card_est_cardinal(vm):
    """⊢ est_cardinal( Card m )   pour un TERME m quelconque.   GRATUIT.

    est_cardinal(a) := (∃X)( a = Card X ) ; en a := Card m le témoin est m, et
    l'antécédent de S5 est Card m = Card m — la réflexivité (Th.1, E.I.39).

    ⚠️ Le liant reste « X », le liant PAR DÉFAUT de `est_cardinal` : c'est celui
    qu'`enum` reconnaît (piège n°2 de la campagne — un nom « frais » choisi par
    réflexe anti-collision casserait la reconnaissance)."""
    R = egal(cardinal(vm), cardinal(var("X")))
    assert subst_f(vm, "X", R) == egal(cardinal(vm), cardinal(vm)), \
        "card_est_cardinal : (m|X)R n'est pas Card m = Card m (capture ?)"
    th = mp(N.reflexivite(cardinal(vm)), N.s5(R, vm, "X"))
    assert th.conclusion == est_cardinal(cardinal(vm)) and th.est_clos
    return th


# ══════════════════════════════════════════════════════════════════════════════
#  LA PREUVE
# ══════════════════════════════════════════════════════════════════════════════
def non_pair(i, k=K_PAIR, garde=True):
    """⊢ ¬(∃k)( N(i) = k + k )   pour i IMPAIR.        [CLOS, 0 hypothèse]

    `garde=False` DÉSACTIVE la seule vérification Python de parité : la recette
    est alors lancée telle quelle sur un i pair et doit échouer pour une raison
    ARITHMÉTIQUE (cf. l'en-tête, contrôle de non-universalité)."""
    if garde:
        assert i % 2 == 1, "non_pair : i IMPAIR attendu (garde=False pour le contrôle)"
    assert i >= 1

    vm = var(k)
    R = corps_pair(NUM(i), k)                 # N(i) = m + m
    CIBLE = non(existe(k, R))                 # ¬(∃m)( N(i) = m+m )
    assert k not in libres_f(CIBLE), "le liant est libre dans la cible"

    h = N.assume(R)

    # ── 1. Card m ≤ m+m  (inconditionnel), réécrit en Card m ≤ N(i) ────────────
    eq_sym = mp(h, symetrie(NUM(i), SC(vm, vm)))          # m+m = N(i)   [sous R]
    borne_i = M.reecrit(eq_sym, borne_gauche(vm),
                        inf_egal_card(cardinal(vm), var(M._HOLE)))
    assert borne_i.conclusion == inf_egal_card(cardinal(vm), NUM(i))

    # ── 2-3. Card m est un cardinal ⟹ enum referme le domaine ─────────────────
    disj_thm = mp(borne_i, C.enum(cardinal(vm), i, card_d=card_est_cardinal(vm)))
    assert disj_thm.conclusion == C.disj(cardinal(vm), i)

    # ── 4. le pont : m+m = Card m + Card m  (CLOS, m arbitraire) ──────────────
    pont = pont_card(vm)
    assert pont.conclusion == egal(SC(vm, vm), SC(cardinal(vm), cardinal(vm)))
    assert pont.est_clos and not pont.hypotheses, "le pont n'est pas clos"

    w = var(M._HOLE)

    def branche(j):
        """⊢ ( Card m = N(j) ) ⇒ ¬(∃m)( N(i) = m+m )   —  par l'absurde."""
        hj = N.assume(egal(cardinal(vm), NUM(j)))
        # m+m = Card m + Card m  ↦  m+m = N(j) + N(j)   (les DEUX trous voulus)
        eq1 = M.reecrit(hj, pont, egal(SC(vm, vm), SC(w, w)))
        assert eq1.conclusion == egal(SC(vm, vm), SC(NUM(j), NUM(j)))
        eq2 = composer_egalites(eq1, C.somme_num(j, j))       # m+m = N(2j)
        eq3 = composer_egalites(h, eq2)                       # N(i) = N(2j)
        assert eq3.conclusion == egal(NUM(i), NUM(2 * j))
        # i IMPAIR ⟹ i ≠ 2j pour TOUT j.  C'est ICI que la parité joue.
        th = M.ex_falso(eq3, M.ne_num_quelconque(i, 2 * j), CIBLE)
        return N.loi_deduction(egal(cardinal(vm), NUM(j)), th)

    cur = branche(0)
    for j in range(1, i + 1):
        dj = C.disj(cardinal(vm), j)
        cur = N.loi_deduction(dj, cas(N.assume(dj), cur, branche(j)))

    # ── 5. recollement ────────────────────────────────────────────────────────
    sous_h = mp(disj_thm, cur)                     # CIBLE, sous la seule hyp. R
    imp = N.loi_deduction(R, sous_h)               # ⊢ R ⇒ ¬(∃m)R
    assert imp.est_clos, "résidu avant élimination du ∃ : %s" % (imp.hypotheses,)
    ex_imp = existe_elimination(imp, k)            # ⊢ (∃m)R ⇒ ¬(∃m)R
    res = mp(ex_imp, N.s1(CIBLE))                  # S1 : (¬F ou ¬F) ⇒ ¬F

    assert res.conclusion == cible_non_pair(i, k), "non_pair(%d) : ≠ cible" % i
    assert res.est_clos and not res.hypotheses, \
        "non_pair(%d) NON clos : %d hyps" % (i, len(res.hypotheses))
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  AFFICHAGE / RAPPORT
# ══════════════════════════════════════════════════════════════════════════════
FORME = "non (∃kgb) ( N(i) = somme_cardinale_binaire(kgb, kgb) )"


def _noeuds(obj, cap):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme
    n, pile = 0, [obj]
    while pile and n < cap:
        u = pile.pop()
        n += 1
        if isinstance(u, Terme):
            pile.extend(u.args)
        else:
            pile.extend(u.termes)
            pile.extend(u.sous)
    return n


def _apercu(f, cap=20000, n=420):
    if _noeuds(f, cap) >= cap:
        return "<formule géante : ≥%d nœuds> — forme : %s" % (cap, FORME)
    s = afficher_f(f)
    return s if len(s) <= n else s[:n] + " …[+%d car.]" % (len(s) - n)


def _echec(fn, *a, **kw):
    """Lance fn et rend (type, message, fichier, ligne) de l'échec ATTENDU."""
    import traceback
    try:
        fn(*a, **kw)
        return None
    except Exception as exc:
        tb = traceback.extract_tb(sys.exc_info()[2])[-1]
        return (type(exc).__name__, str(exc), tb.filename, tb.lineno, tb.line)


def main():
    print("=" * 78)
    print("RÉFUTER LA PARITÉ D'UN IMPAIR :  |- non (∃m)( N(i) = m + m )")
    print("=" * 78)

    # (a) fidélité de l'énoncé : c'est la parité de goldbach(), rebâtie
    print("\n[fidélité] est_pair EST la parité de goldbach.goldbach() (rebâti) :",
          fidelite_verifiee())
    print("[fidélité] libres_t(NUM(3)) =", sorted(libres_t(NUM(3))),
          " → terme CLOS, aucune capture possible")
    print("[def] est_cardinal(a) = (∃X)(a = Card X) ; liant PAR DÉFAUT 'X' (celui d'enum)")
    print("[def] cible :", FORME)

    # (b) les deux briques, mesurées closes
    vm = var(K_PAIR)
    t0 = time.time()
    bg = borne_gauche(vm)
    print("\n[brique] inf_egal_somme_gauche_binaire(m,m) : clos=%s nb_hyps=%d (%.2f s)"
          % (bg.est_clos, len(bg.hypotheses), time.time() - t0))
    print("         %s" % _apercu(bg.conclusion, n=200))
    t0 = time.time()
    ec = card_est_cardinal(vm)
    print("[brique] est_cardinal(Card m)              : clos=%s nb_hyps=%d (%.3f s)"
          % (ec.est_clos, len(ec.hypotheses), time.time() - t0))
    t0 = time.time()
    pt = pont_card(vm)
    print("[brique] pont_card(m)                      : clos=%s nb_hyps=%d (%.2f s)"
          % (pt.est_clos, len(pt.hypotheses), time.time() - t0))

    # (c) LES CIBLES : i = 3, 5, 7, 9, 11
    res = []
    for i in (3, 5, 7, 9, 11):
        t0 = time.time()
        th = non_pair(i)
        dt = time.time() - t0
        clos = th.est_clos and not th.hypotheses
        print("\n" + "-" * 78)
        print("i = %d   CLOS = %s   nb_hyps = %d   (%.2f s)  [%d branches]"
              % (i, clos, len(th.hypotheses), dt, i + 1))
        print("  |-  %s" % _apercu(th.conclusion))
        print("  conclusion == cible_non_pair(%d) reconstruite : %s"
              % (i, th.conclusion == cible_non_pair(i)))
        res.append((i, clos, len(th.hypotheses), dt))

    # (d) CONTRÔLE DE NON-UNIVERSALITÉ — garde Python DÉSACTIVÉE, i PAIR
    print("\n" + "=" * 78)
    print("CONTRÔLE DE NON-UNIVERSALITÉ (garde=False, i PAIR — doit ÉCHOUER)")
    print("=" * 78)
    for i in (4, 6):
        e = _echec(non_pair, i, garde=False)
        assert e is not None, "### i=%d : la recette a RÉUSSI sur un pair — FAUX ###" % i
        typ, msg, fic, lig, src = e
        rel = os.path.relpath(fic, RACINE) if fic.startswith(RACINE) else fic
        print("\n  i = %d   ÉCHEC %s: %s" % (i, typ, msg))
        print("     à  %s:%d" % (rel.replace("\\", "/"), lig))
        print("     source : %s" % (src or "").strip())
        print("     branche fautive : j = %d, où 2j = %d = i  ⟹  il faudrait "
              "|- ¬( N(%d) = N(%d) )" % (i // 2, i, i, i))
        arith = ("ne_num_quelconque" in (src or "")) and rel.endswith("machine_num.py")
        print("     échec ARITHMÉTIQUE (ne_num sur i == 2j), pas un assert cosmétique : %s"
              % arith)
        assert arith, "### l'échec n'est PAS arithmétique — le contrôle ne contrôle rien ###"

    # (e) et la raison profonde : pour i pair, N(i) EST pair (témoin exhibé)
    print("\n  RAISON PROFONDE — pour i pair il n'y a rien à réfuter : le témoin")
    print("  m := N(i/2) rend l'existentielle VRAIE.  Vérifié dans le noyau :")
    for i in (4, 6):
        j = i // 2
        eq = mp(C.somme_num(j, j), symetrie(SC(NUM(j), NUM(j)), NUM(i)))  # N(i)=N(j)+N(j)
        th = mp(eq, N.s5(corps_pair(NUM(i)), NUM(j), K_PAIR))
        assert th.conclusion == est_pair(NUM(i)) and th.est_clos
        print("     |- (∃k)( N(%d) = k+k )   CLOS (témoin k := N(%d))   nb_hyps=%d"
              % (i, j, len(th.hypotheses)))

    # (f) bilan + invariant
    print("\n" + "=" * 78)
    print("BILAN")
    for i, clos, nh, dt in res:
        print("   i=%-3d %s  nb_hyps=%d   %.2f s" % (i, "CLOS" if clos else "HYPS", nh, dt))
    n_ax = len(E.theorie_ensembles().axiomes)
    print("\nINVARIANT : theorie_ensembles() = %d axiomes   %s"
          % (n_ax, "OK" if n_ax == 22 else "### ÉCHEC ###"))
    assert n_ax == 22, "invariant cassé : %d axiomes" % n_ax
    print("=" * 78)
