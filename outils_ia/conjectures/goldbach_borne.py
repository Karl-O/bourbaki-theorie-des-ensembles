"""Goldbach borné — le premier énoncé Goldbach QUANTIFIÉ que le corpus ferme.

    ⊢ (∀k)( ( Fini k et k≠0 et k≠1 et k ≤ N(K) ) ⇒ (∃p)(∃p')( p, p' premiers
                                                       et k+k = p+p' ) )

────────────────────────────────────────────────────────────────────────────────
CE QUE C'EST, ET SURTOUT CE QUE CE N'EST PAS.

Ce n'est PAS la conjecture : celle-ci est sans borne et reste ouverte depuis 1742.
Ce n'est pas non plus une instance : n = 4 était clos depuis le 5 août 2026, mais
un théorème par nombre n'est pas un théorème sur les nombres.

C'est l'énoncé INTERMÉDIAIRE, et il est quantifié : UNE formule, un (∀k), qui
couvre tous les pairs de 4 à 2K.  La différence avec l'instance est exactement
celle qui sépare « j'ai vérifié » de « j'ai démontré que, pour tout k borné ».

────────────────────────────────────────────────────────────────────────────────
CE QUE LA BORNE COÛTE, ET CE QU'IL FAUDRAIT POUR L'ENLEVER.

La preuve tient parce que `enum` rend le domaine FINI : K+1 branches, chacune
fermée par un témoin exhibé.  Enlever la borne casse les deux piliers à la fois —
plus d'énumération, et plus de témoin, puisqu'aucune fonction connue ne rend le
couple de premiers à partir de n.  C'est précisément le contenu du problème
ouvert, et le corpus le rend ici mesurable : la borne n'est pas une commodité,
c'est la frontière.

────────────────────────────────────────────────────────────────────────────────
POURQUOI PARAMÉTRER PAR LA MOITIÉ k, ET NON PAR n.

Écrit sur n, l'énoncé demanderait « n pair », donc (∃m)(n = m+m), donc de savoir
ÉCARTER les impairs — c'est-à-dire démontrer ¬(∃m)( N(3) = m+m ), un calcul de
parité sans rapport avec Goldbach, et qui doublerait le travail.

Écrit sur la moitié, la parité est GRATUITE : k+k est pair par construction.  Un
chantier entier économisé par un changement de variable.  Les restrictions k ≠ 0
et k ≠ 1 disent exactement « n ≠ 0 et n ≠ 2 ».

────────────────────────────────────────────────────────────────────────────────
LA ROUTE.  `enum` referme le domaine, puis branche par branche :
  · j = 0, j = 1 : écartés par les antécédents k ≠ 0 et k ≠ 1 (ex falso) ;
  · j ≥ 2        : on exhibe (p, p') avec p + p' = 2j, on prouve
                   ⊢ N(j)+N(j) = N(p)+N(p') par `somme_num` des deux côtés, on le
                   transporte sur k+k par Leibniz, puis S5 deux fois.

⚠️ LE PIÈGE DE S5, ET POURQUOI LES MATRICES SONT DONNÉES EXPLICITEMENT.  Pour
4 = 2+2 le témoin est le MÊME des deux côtés.  Laisser deviner quelles occurrences
abstraire les prendrait TOUTES, et l'on obtiendrait (∃p)( k+k = p+p ) — plus
faible, et faux en général.  En fournissant la matrice on décide du trou soi-même,
et l'assertion finale vérifie que la formule obtenue est bien la cible.

────────────────────────────────────────────────────────────────────────────────
LES DEUX CONTRÔLES.

 · FIDÉLITÉ.  `fidelite_verifiee()` REBÂTIT `goldbach.goldbach()` à partir de la
   brique `decomposition` d'ici et exige l'égalité.  Sans quoi rien n'empêcherait
   de démontrer une variante commode du corps existentiel.
 · NON-UNIVERSALITÉ.  L'hypothèse k ≠ 1 n'est pas décorative : 2·1 = 2 n'est somme
   d'aucun couple de premiers.  Et la fermer en trichant — en prétendant 2 = 1+1 —
   exigerait ⊢ ¬( N(1) = 1 ), alors que ⊢ N(1) = 1 est un théorème CLOS du dépôt
   (`un_egale_card_singleton`).  Le refus est donc un fait du noyau : fermer cette
   branche rendrait le corpus incohérent.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
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
from outils_ia.conjectures.primalite import est_premier_num

mp = N.modus_ponens
NUM = M.NUM


# ══════════════════════════════════════════════════════════════════════════════
#  L'ÉNONCÉ  —  mêmes briques que goldbach.py, vérifiées égales
# ══════════════════════════════════════════════════════════════════════════════
def decomposition(tn, p="pgb", pp="qgb"):
    """(∃p)(∃p')( p premier et p' premier et TN = p + p' ).

    Reproduit le corps existentiel de `goldbach.goldbach()` — l'égalité est
    VÉRIFIÉE par `fidelite_verifiee()`, pas supposée."""
    vp, vpp = var(p), var(pp)
    return existe(p, existe(pp,
        et(et(GB.est_premier(vp, d="d1", q="q1"), GB.est_premier(vpp, d="d2", q="q2")),
           egal(tn, somme_cardinale_binaire(vp, vpp)))))


def fidelite_verifiee():
    """Rebâtit `goldbach.goldbach()` avec la brique d'ici et exige l'égalité."""
    vn, vk = var("ngb"), var("kgb")
    pair = existe("kgb", egal(vn, somme_cardinale_binaire(vk, vk)))
    ante = et(et(et(est_fini(vn), pair), non(egal(vn, GB.zero()))),
              non(egal(vn, GB.deux())))
    return pourtout("ngb", impl(ante, decomposition(vn))) == GB.goldbach()


def couple(n):
    """Le couple de premiers (p, p') avec p + p' = n, p minimal.  None si aucun.

    C'est la seule partie « calculée en Python » : elle CHERCHE le témoin, elle ne
    le certifie pas.  La certification est faite par `est_premier_num` et
    `somme_num`, dans le noyau."""
    def premier(m):
        return m >= 2 and all(m % i for i in range(2, int(m ** 0.5) + 1))
    for p in range(2, n // 2 + 1):
        if premier(p) and premier(n - p):
            return p, n - p
    return None


def antecedent(vk, K):
    """( Fini k et k≠0 et k≠1 ) et k ≤ N(K)  —  associé à gauche."""
    return et(et(et(est_fini(vk), non(egal(vk, NUM(0)))), non(egal(vk, NUM(1)))),
              inf_egal_card(vk, NUM(K)))


def cible(K, k="kgb", p="pgb", pp="qgb"):
    """La formule complète, construite — jamais recopiée à la main."""
    vk = var(k)
    return pourtout(k, impl(antecedent(vk, K),
                            decomposition(somme_cardinale_binaire(vk, vk), p=p, pp=pp)))


# ══════════════════════════════════════════════════════════════════════════════
#  LA PREUVE
# ══════════════════════════════════════════════════════════════════════════════
def goldbach_borne(K, k="kgb", p="pgb", pp="qgb"):
    """⊢ Goldbach pour tous les pairs de 4 à 2K.          [CLOS, 0 hypothèse]

    Mesuré le 6 août 2026 : K = 2 en 60 s à froid (l'essentiel est la première
    primalité), puis K = 3 en 0,4 s, K = 5 en 2,1 s, K = 10 en 13,4 s."""
    assert K >= 2, "goldbach_borne : K >= 2 attendu"
    manquants = [j for j in range(2, K + 1) if couple(2 * j) is None]
    assert not manquants, "aucune décomposition connue pour 2*%d" % manquants[0]

    vk, vp, vpp = var(k), var(p), var(pp)
    kk = somme_cardinale_binaire(vk, vk)
    concl = decomposition(kk, p=p, pp=pp)

    ante = antecedent(vk, K)
    h = N.assume(ante)
    g1 = conjonction_elim_gauche(h)                     # (Fini k et k≠0) et k≠1
    g2 = conjonction_elim_gauche(g1)                    # Fini k et k≠0
    fini_k = conjonction_elim_gauche(g2)
    ne_k0, ne_k1 = conjonction_elim_droite(g2), conjonction_elim_droite(g1)
    disj_thm = mp(conjonction_elim_droite(h),
                  C.enum(vk, K, card_d=mp(fini_k, M.fic_t(vk))))

    def branche(j):
        """⊢ ( k = N(j) ) ⇒ (∃p)(∃p')( … )."""
        hj = N.assume(egal(vk, NUM(j)))
        if j in (0, 1):
            th = M.ex_falso(hj, ne_k0 if j == 0 else ne_k1, concl)
        else:
            a, b = couple(2 * j)
            somme_ab = somme_cardinale_binaire(NUM(a), NUM(b))
            # ⊢ N(j)+N(j) = N(2j)  et  ⊢ N(a)+N(b) = N(2j)  ⟹  N(j)+N(j) = N(a)+N(b)
            eq = composer_egalites(C.somme_num(j, j),
                                   mp(C.somme_num(a, b), symetrie(somme_ab, NUM(2 * j))))
            assert eq.conclusion == egal(somme_cardinale_binaire(NUM(j), NUM(j)), somme_ab)
            # transport sur k+k : les DEUX occurrences du trou sont voulues ici
            eq_k = M.reecrit(mp(hj, symetrie(vk, NUM(j))), eq,
                             egal(somme_cardinale_binaire(var(M._HOLE), var(M._HOLE)),
                                  somme_ab))
            assert eq_k.conclusion == egal(kk, somme_ab)
            # ⚠️ matrices EXPLICITES (cf. l'en-tête : 4 = 2+2 a le même témoin deux fois)
            mat_int = et(et(GB.est_premier(NUM(a), d="d1", q="q1"),
                            GB.est_premier(vpp, d="d2", q="q2")),
                         egal(kk, somme_cardinale_binaire(NUM(a), vpp)))
            # deux ∃-intros imbriquées, par la tactique à témoin VÉRIFIÉ (ev.283) :
            # le garde-fou attrape une matrice mal formée AVANT le noyau.
            th_int = M.existe_temoin_verifie(
                conjonction_intro(conjonction_intro(
                    est_premier_num(a, d="d1", q="q1"),
                    est_premier_num(b, d="d2", q="q2")), eq_k),
                mat_int, NUM(b), pp)
            mat_ext = existe(pp, et(et(GB.est_premier(vp, d="d1", q="q1"),
                                       GB.est_premier(vpp, d="d2", q="q2")),
                                    egal(kk, somme_cardinale_binaire(vp, vpp))))
            th = M.existe_temoin_verifie(th_int, mat_ext, NUM(a), p)
            assert th.conclusion == concl, "branche j=%d : ≠ conclusion" % j
        return N.loi_deduction(egal(vk, NUM(j)), th)

    cur = branche(0)
    for j in range(1, K + 1):
        dj = C.disj(vk, j)
        cur = N.loi_deduction(dj, cas(N.assume(dj), cur, branche(j)))

    imp = N.loi_deduction(ante, mp(disj_thm, cur))
    assert imp.est_clos, "résidu avant généralisation : %s" % (imp.hypotheses,)
    res = N.generalisation(k, imp)
    assert res.conclusion == cible(K, k, p, pp), "goldbach_borne(%d) : ≠ cible" % K
    assert res.est_clos and not res.hypotheses, "goldbach_borne(%d) non clos" % K
    return res


__all__ = ["decomposition", "fidelite_verifiee", "couple", "antecedent", "cible",
           "goldbach_borne"]
