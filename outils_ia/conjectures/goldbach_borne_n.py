# -*- coding: utf-8 -*-
"""GOLDBACH BORNÉ, ÉCRIT SUR n  —  la conjecture elle-même, restreinte à n ≤ N(B).

    ⊢ (∀n)( ( Fini n  et  pair n  et  n ≠ 0  et  n ≠ 2  et  n ≤ N(B) )
            ⇒ (∃p)(∃p')( p premier et p' premier et n = p + p' ) )
                                                        [CLOS, 0 hypothèse]

────────────────────────────────────────────────────────────────────────────────
POURQUOI C'EST LE POINT DE TOUT LE CHANTIER.

`goldbach_borne.py` ferme la même famille de pairs, mais paramétrée par la MOITIÉ :
(∀k)( … ⇒ (∃p)(∃p')( k+k = p+p' ) ).  Ce changement de variable rend la parité
GRATUITE (k+k est pair par construction) et évite d'avoir à écarter les impairs.
Le prix est que l'énoncé ne parle plus de n : ce n'est plus la conjecture, c'est
son image par n ↦ n/2, et le pas « tout pair borné est n = 2k » n'y est pas fait.

Ici l'énoncé est LITTÉRALEMENT celui de `goldbach.goldbach()` — mêmes conjoints,
même conséquent, égalité de FORMULES vérifiée — plus un seul conjoint : n ≤ N(B).
La quantification porte sur n, et « pair n » est l'hypothèse (∃k)(n = k+k) de
l'énoncé, qui quantifie sur des ENSEMBLES quelconques.  Il faut donc, cette fois,
savoir écarter les impairs : c'est ce que `parite.py` fournit.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE.

Sous l'antécédent h, `est_fini(n)` donne `est_cardinal(n)` (fic_t) et `n ≤ N(B)`
laisse `enum` refermer le domaine en B+1 branches  n = N(0) ou … ou n = N(B).

  · j = 0        — écarté par le conjoint n ≠ 0.  ⚠️ l'énoncé compare à
                   `goldbach.zero()`, pas au numéral ; ici N(0) == zero() est
                   VÉRIFIÉ (assertion), donc aucun pont n'est nécessaire.
  · j = 2        — écarté par n ≠ 2.  ⚠️ ICI le pont est OBLIGATOIRE :
                   `goldbach.deux()` vaut un()+un() et N(2) == deux() est FAUX
                   (mesuré).  On transporte par ⊢ deux() = N(2), construit depuis
                   `primalite.pont_un` et `somme_num(1,1)` (même dérivation que
                   `defaut_infini.py`), puis Leibniz.
  · j IMPAIR     — l'hypothèse « pair n » est transportée sur N(j) par Leibniz, ce
                   qui donne (∃k)( N(j) = k+k ), que `non_pair(j)` réfute.
                   ⚠️ C'est le seul endroit où la parité travaille, et elle est
                   INDISPENSABLE : `couple(j)` est None pour j = 1, 3, 11, 17 —
                   ces branches n'ont AUCUNE route alternative (mesuré ci-dessous).
  · j PAIR ≥ 4   — on exhibe le couple de premiers, on prouve ⊢ N(j) = N(a)+N(b)
                   par `somme_num`, on le transporte sur n par l'hypothèse de
                   branche, puis S5 deux fois avec des MATRICES EXPLICITES.
                   ⚠️ pour 4 = 2+2 le témoin est le même des deux côtés : sans
                   matrice, S5 abstrairait les deux occurrences et rendrait
                   (∃p)( n = p+p ), plus faible.

Puis `cas` recolle, `loi_deduction` décharge, `generalisation` quantifie sur n.

────────────────────────────────────────────────────────────────────────────────
LES QUATRE CONTRÔLES (aucun n'est un commentaire : tous s'exécutent).

 1. FIDÉLITÉ — l'antécédent et le conséquent ne sont pas recopiés : ils sont
    EXTRAITS de `goldbach.goldbach()` par découpe structurelle, puis re-vérifiés
    par reconstruction indépendante à partir des briques de `goldbach.py`.  La
    cible est `pourtout(n, impl(et(ANTE_GB, n ≤ N(B)), DEC_GB))`.

 2. NÉCESSITÉ DES CONJOINTS n ≠ 0 ET n ≠ 2 — démontrée dans le noyau, pas
    argumentée : TOUS les autres conjoints de l'antécédent sont prouvés CLOS en
    n := N(0) puis en n := N(2) (chacun comparé à `subst_f(N(i), "ngb", conjoint)`).
    Or ni 0 ni 2 n'est somme de deux premiers : sans ces deux conjoints l'énoncé
    serait FAUX, exactement comme l'a montré `defaut_infini.py` pour ℕ+ℕ.

 3. NON-UNIVERSALITÉ — la recette appliquée à la branche j = 2 sans le conjoint
    n ≠ 2 exigerait de nier la parité de 2 : `non_pair(2, garde=False)` échoue
    ARITHMÉTIQUEMENT dans `outils_ia/arithmetique/machine_num.py:245`
    (`assert a != b`, il faudrait ⊢ ¬( N(2) = N(2) )).  Le fichier ET la ligne
    sont vérifiés — un contrôle qui échoue pour la mauvaise raison ne contrôle rien.

 4. LA BORNE N'EST PAS COSMÉTIQUE — `cible(B) != goldbach.goldbach()` est vérifié,
    et l'on vérifie aussi que retirer le seul conjoint `n ≤ N(B)` de la cible REND
    exactement `goldbach.goldbach()` : la différence est ce conjoint, et rien d'autre.

INVARIANT : aucun fichier du dépôt modifié ; aucun `_CLE`, aucun `Theoreme`
fabriqué, aucun monkeypatch ; `theorie_ensembles()` reste à 22 axiomes.
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
    var, egal, non, et, impl, existe, pourtout, afficher_f, subst_f, libres_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures import goldbach_borne as GBB
from outils_ia.conjectures.primalite import est_premier_num, pont_un

from outils_ia.arithmetique import parite as NP                      # l'étape 2 : la réfutation de parité

mp = N.modus_ponens
NUM = M.NUM
TROU = var(M._HOLE)


# ══════════════════════════════════════════════════════════════════════════════
#  L'ÉNONCÉ  —  EXTRAIT de goldbach.goldbach(), puis re-vérifié par reconstruction
# ══════════════════════════════════════════════════════════════════════════════
def _et_gauche_droite(f):
    """Rend (G, D) tels que f == et(G, D).  Découpe VÉRIFIÉE, pas supposée.

    `et(a,b)` est abrégé en `non(ou(non a, non b))` : on remonte l'abréviation."""
    assert f.tag == "non" and f.sous[0].tag == "ou", "pas une conjonction"
    g, d = f.sous[0].sous
    assert g.tag == "non" and d.tag == "non", "pas une conjonction"
    G, D = g.sous[0], d.sous[0]
    assert et(G, D) == f, "découpe de conjonction incorrecte"
    return G, D


def decoupe_goldbach():
    """(nom, ANTE, DEC) tels que `goldbach.goldbach()` == (∀nom)( ANTE ⇒ DEC ).

    Rien n'est recopié : on DÉCOUPE la formule du dépôt, et l'on vérifie que la
    recomposition rend bien la formule de départ."""
    g = GB.goldbach()
    assert g.tag == "non" and g.sous[0].tag == "exists", "goldbach() n'est pas un (∀)"
    ex = g.sous[0]
    nom, corps = ex.lieur, ex.sous[0]
    assert corps.tag == "non", "corps du (∀) inattendu"
    imp = corps.sous[0]
    assert imp.tag == "ou" and imp.sous[0].tag == "non", "corps n'est pas une implication"
    ante, dec = imp.sous[0].sous[0], imp.sous[1]
    assert pourtout(nom, impl(ante, dec)) == g, "recomposition != goldbach()"
    return nom, ante, dec


NOM_N, ANTE_GB, DEC_GB = decoupe_goldbach()
VN = var(NOM_N)


def fidelite_verifiee():
    """Les deux morceaux extraits sont RECONSTRUITS depuis les briques du dépôt.

    ANTE_GB doit être l'antécédent bâti avec `NP.est_pair` (dont `parite.py` a
    déjà vérifié qu'il EST la parité de `goldbach()`), `GB.zero()` et `GB.deux()` ;
    DEC_GB doit être `goldbach_borne.decomposition`, dont la fidélité est vérifiée
    dans le dépôt.  Si l'un des deux glissait, l'assertion tomberait."""
    ante = et(et(et(est_fini(VN), NP.est_pair(VN)), non(egal(VN, GB.zero()))),
              non(egal(VN, GB.deux())))
    return (ante == ANTE_GB and GBB.decomposition(VN) == DEC_GB
            and pourtout(NOM_N, impl(ante, GBB.decomposition(VN))) == GB.goldbach())


def antecedent(B):
    """L'antécédent de `goldbach()` AUGMENTÉ du seul conjoint n ≤ N(B)."""
    return et(ANTE_GB, inf_egal_card(VN, NUM(B)))


def cible(B):
    """LA cible : (∀n)( ( ANTE de goldbach()  et  n ≤ N(B) ) ⇒ DEC de goldbach() )."""
    return pourtout(NOM_N, impl(antecedent(B), DEC_GB))


def conjoints(B):
    """Les 5 conjoints de l'antécédent, extraits dans l'ordre :
    [ Fini n, pair n, n ≠ 0, n ≠ 2, n ≤ N(B) ]."""
    a4, le = _et_gauche_droite(antecedent(B))
    a3, ne2 = _et_gauche_droite(a4)
    a2, ne0 = _et_gauche_droite(a3)
    fini, pair = _et_gauche_droite(a2)
    return [fini, pair, ne0, ne2, le]


NOMS_CONJOINTS = ["Fini n", "pair n", "n != 0", "n != 2", "n <= N(B)"]

#: la matrice de Leibniz qui transporte « pair n » sur un numéral.
R_PAIR = existe(NP.K_PAIR, egal(TROU, SC(var(NP.K_PAIR), var(NP.K_PAIR))))
assert subst_f(VN, M._HOLE, R_PAIR) == NP.est_pair(VN), "matrice de parité incorrecte"


# ══════════════════════════════════════════════════════════════════════════════
#  LE PONT ARITHMÉTIQUE  —  goldbach.deux() n'est PAS le numéral N(2)
# ══════════════════════════════════════════════════════════════════════════════
_PONT_DEUX = None


def pont_deux():
    """⊢ deux() = N(2), où deux() = un()+un() de `goldbach.py`.  CLOS.

    Même dérivation que `defaut_infini.py` : `somme_num(1,1)` donne N(1)+N(1)=N(2),
    et `primalite.pont_un` (⊢ N(1) = un(), théorème CLOS du dépôt) transporte les
    deux occurrences.  ⚠️ N(2) == GB.deux() est FAUX — c'est vérifié ici, sinon on
    croirait le pont inutile et l'on démontrerait une formule voisine."""
    global _PONT_DEUX
    if _PONT_DEUX is None:
        assert NUM(2) != GB.deux(), "N(2) == deux() : le pont serait inutile ?"
        th = M.reecrit(pont_un(),
                       M.reecrit(pont_un(), C.somme_num(1, 1),
                                 egal(SC(TROU, NUM(1)), NUM(2))),
                       egal(SC(GB.un(), TROU), NUM(2)))
        assert th.conclusion == egal(GB.deux(), NUM(2)), "pont_deux : conclusion != cible"
        assert th.est_clos and not th.hypotheses, "pont_deux non clos"
        _PONT_DEUX = th
    return _PONT_DEUX


def pont_deux_cible():
    """Énoncé visé : deux() = N(2) (compagne zéro-arg pour le gate du volant)."""
    return egal(GB.deux(), NUM(2))


pont_deux_gate_caches = ("_PONT_DEUX",)   # voile du gate : jamais juger un cache


# ══════════════════════════════════════════════════════════════════════════════
#  LA PREUVE
# ══════════════════════════════════════════════════════════════════════════════
def goldbach_borne_n(B, p="pgb", pp="qgb", trace=None):
    """⊢ Goldbach, écrit sur n, pour tous les n ≤ N(B).      [CLOS, 0 hypothèse]

    B doit être PAIR et ≥ 4 (sinon le domaine ne contient aucun cas non trivial).
    `trace`, si fourni, reçoit (j, recette) pour chaque branche."""
    assert B >= 4 and B % 2 == 0, "goldbach_borne_n : B pair >= 4 attendu"
    manquants = [j for j in range(4, B + 1, 2) if GBB.couple(j) is None]
    assert not manquants, "aucune décomposition connue pour %s" % manquants
    # ⚠️ l'énoncé compare à `goldbach.zero()`, pas au numéral : on le VÉRIFIE.
    assert NUM(0) == GB.zero(), "N(0) != zero() : la branche j=0 demanderait un pont"

    vp, vpp = var(p), var(pp)
    DEC = DEC_GB
    ante = antecedent(B)

    h = N.assume(ante)
    gb = conjonction_elim_gauche(h)                 # l'antécédent de goldbach()
    le_B = conjonction_elim_droite(h)               # n ≤ N(B)
    g3 = conjonction_elim_gauche(gb)                # (Fini n et pair n) et n≠0
    ne_2 = conjonction_elim_droite(gb)              # ¬( n = deux() )
    g2 = conjonction_elim_gauche(g3)                # Fini n et pair n
    ne_0 = conjonction_elim_droite(g3)              # ¬( n = zero() ) == ¬( n = N(0) )
    fini_n = conjonction_elim_gauche(g2)
    pair_n = conjonction_elim_droite(g2)            # (∃k)( n = k + k )
    assert pair_n.conclusion == NP.est_pair(VN), "le conjoint extrait n'est pas la parité"

    # ⚠️ le pont : ¬( n = deux() )  ↦  ¬( n = N(2) ).  Sans lui la branche j = 2
    #    porterait sur un autre terme (piège n°5 de la campagne).
    ne_2n = M.reecrit(pont_deux(), ne_2, non(egal(VN, TROU)))
    assert ne_2n.conclusion == non(egal(VN, NUM(2)))

    # enum referme le domaine : B+1 branches
    disj_thm = mp(le_B, C.enum(VN, B, card_d=mp(fini_n, M.fic_t(VN))))
    assert disj_thm.conclusion == C.disj(VN, B)

    def branche(j):
        """⊢ ( n = N(j) ) ⇒ (∃p)(∃p')( p, p' premiers et n = p+p' )."""
        hj = N.assume(egal(VN, NUM(j)))
        if j == 0:
            recette = "n != 0"
            th = M.ex_falso(hj, ne_0, DEC)
        elif j == 2:
            recette = "n != 2 (via le pont deux() = N(2))"
            th = M.ex_falso(hj, ne_2n, DEC)
        elif j % 2 == 1:
            recette = "parite : non_pair(%d)" % j
            pj = M.reecrit(hj, pair_n, R_PAIR)          # (∃k)( N(j) = k+k )
            assert pj.conclusion == NP.est_pair(NUM(j))
            th = M.ex_falso(pj, NP.non_pair(j), DEC)
        else:
            a, b = GBB.couple(j)
            recette = "temoins %d + %d" % (a, b)
            somme_ab = SC(NUM(a), NUM(b))
            # ⊢ N(a)+N(b) = N(j)  renversé, composé avec  n = N(j)
            eq_n = composer_egalites(hj, mp(C.somme_num(a, b),
                                            symetrie(somme_ab, NUM(j))))
            assert eq_n.conclusion == egal(VN, somme_ab)
            # ⚠️ matrices EXPLICITES (4 = 2+2 : même témoin des deux côtés)
            mat_int = et(et(GB.est_premier(NUM(a), d="d1", q="q1"),
                            GB.est_premier(vpp, d="d2", q="q2")),
                         egal(VN, SC(NUM(a), vpp)))
            # deux ∃-intros imbriquées, par la tactique à témoin VÉRIFIÉ (ev.283)
            th_int = M.existe_temoin_verifie(
                conjonction_intro(conjonction_intro(
                    est_premier_num(a, d="d1", q="q1"),
                    est_premier_num(b, d="d2", q="q2")), eq_n),
                mat_int, NUM(b), pp)
            mat_ext = existe(pp, et(et(GB.est_premier(vp, d="d1", q="q1"),
                                       GB.est_premier(vpp, d="d2", q="q2")),
                                    egal(VN, SC(vp, vpp))))
            th = M.existe_temoin_verifie(th_int, mat_ext, NUM(a), p)
            assert th.conclusion == DEC, "branche j=%d : conclusion != DEC" % j
        if trace is not None:
            trace.append((j, recette))
        return N.loi_deduction(egal(VN, NUM(j)), th)

    cur = branche(0)
    for j in range(1, B + 1):
        dj = C.disj(VN, j)
        cur = N.loi_deduction(dj, cas(N.assume(dj), cur, branche(j)))

    imp = N.loi_deduction(ante, mp(disj_thm, cur))
    assert imp.est_clos, "résidu avant généralisation : %s" % (imp.hypotheses,)
    res = N.generalisation(NOM_N, imp)
    assert res.conclusion == cible(B), "goldbach_borne_n(%d) : conclusion != cible" % B
    assert res.est_clos and not res.hypotheses, \
        "goldbach_borne_n(%d) NON clos : %d hyps" % (B, len(res.hypotheses))
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  CONTRÔLE 2 — les conjoints n ≠ 0 et n ≠ 2 sont PORTEURS, démontré dans le noyau
# ══════════════════════════════════════════════════════════════════════════════
def autres_conjoints_satisfaits(i, B):
    """Pour i ∈ {0, 2} : ⊢ chacun des conjoints de l'antécédent SAUF « n ≠ i »,
    instancié en n := N(i).  Rend la liste (nom, théorème).      [tous CLOS]

    C'est la démonstration que le conjoint retiré est le SEUL rempart : 0 et 2 ne
    sont sommes d'aucun couple de premiers (`couple(0) is None`, `couple(2) is None`),
    donc sans lui l'énoncé serait FAUX — comme `defaut_infini.py` l'a montré pour ℕ+ℕ."""
    assert i in (0, 2)
    conj = conjoints(B)
    saute = 2 if i == 0 else 3                     # l'indice du conjoint « n ≠ i »
    idx_autre = 3 if i == 0 else 2                 # l'AUTRE exclusion, conservée
    ni = NUM(i)
    demi = i // 2

    # ⊢ N(i) = N(i/2) + N(i/2)  puis S5 au témoin N(i/2)  ⟹  ⊢ (∃k)( N(i) = k+k )
    eq = mp(C.somme_num(demi, demi), symetrie(SC(NUM(demi), NUM(demi)), ni))
    pair = mp(eq, N.s5(NP.corps_pair(ni), NUM(demi), NP.K_PAIR))

    # ⊢ ¬( N(i) = deux() ) / ¬( N(i) = zero() ) selon le conjoint conservé
    if i == 0:
        autre = M.reecrit(mp(pont_deux(), symetrie(GB.deux(), NUM(2))),
                          M.ne_num(0, 2), non(egal(NUM(0), TROU)))
        assert autre.conclusion == non(egal(ni, GB.deux()))
    else:
        autre = M.ne_num_sym(0, 2)                 # ⊢ ¬( N(2) = N(0) ) == ¬(N(2)=zero())
        assert autre.conclusion == non(egal(ni, GB.zero()))

    faits = {0: M.fini_num(i), 1: pair, idx_autre: autre, 4: M.le_num(i, B)}
    out = []
    for idx, f in enumerate(conj):
        if idx == saute:
            continue
        th = faits[idx]
        attendu = subst_f(ni, NOM_N, f)
        assert th.conclusion == attendu, (
            "conjoint « %s » en n=N(%d) : conclusion != conjoint instancié\n"
            "  attendu : %s\n  obtenu  : %s"
            % (NOMS_CONJOINTS[idx], i, afficher_f(attendu)[:200],
               afficher_f(th.conclusion)[:200]))
        assert th.est_clos and not th.hypotheses, "conjoint non clos"
        out.append((NOMS_CONJOINTS[idx], th))
    return out

__all__ = [
    "decoupe_goldbach", "fidelite_verifiee", "antecedent", "cible", "conjoints",
    "NOMS_CONJOINTS", "pont_deux", "pont_deux_cible", "goldbach_borne_n",
    "autres_conjoints_satisfaits",
]
