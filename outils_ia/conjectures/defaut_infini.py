"""Le second défaut de `goldbach()`, DÉMONTRÉ — et non plus seulement argumenté.

    ⊢  pair( n )  et  ¬( n = 0 )  et  ¬( n = 2 )        pour  n := ℕ + ℕ

et cette conjonction EST, au caractère près, l'antécédent de `goldbach()` d'avant
le 6 août 2026, instancié en n.  Comme n est infini, il n'est somme d'aucun couple
de nombres premiers : **l'énoncé affirmait donc que ℕ+ℕ est somme de deux premiers**.

────────────────────────────────────────────────────────────────────────────────
POURQUOI CE MODULE EXISTE.  Le conjoint `est_fini(n)` a d'abord été ajouté à
`goldbach()` sur un ARGUMENT — « pour tout cardinal infini a, a + a = a, donc a
est pair au sens de l'énoncé ».  L'argument était juste, mais c'était une dette :
le projet ne se paie pas en raisonnements de marge.  Ce module la solde.

────────────────────────────────────────────────────────────────────────────────
DEUX RACCOURCIS QUI ONT DIVISÉ LE TRAVAIL, ET QU'IL FAUT RETENIR.

(1) PAS BESOIN DE a + a = a.  L'annonce initiale prévoyait de démontrer
    l'idempotence de la somme sur les cardinaux infinis, via Hessenberg (a² = a).
    Inutile : en posant n := a + a, « n est pair » devient vrai PAR CONSTRUCTION,
    avec a pour témoin.  Il ne reste qu'à écarter 0 et 2.
    ⚠️ Chercher le bon témoin AVANT d'attaquer le lemme général.

(2) LE TÉMOIN ENSEMBLISTE, PAS LE CARDINAL.  `inf_egal_somme_gauche_binaire(X,X)`
    rend ⊢ Card(X) ≤ X+X.  Avec X := ℕ on obtient ℵ₀ ≤ n immédiatement, alors
    qu'avec X := ℵ₀ il aurait fallu Card(ℵ₀) = ℵ₀ — qui n'est pas au dépôt.

🔴 PIÈGE MESURÉ : LE DÉPÔT PORTE DEUX ℕ.  `ensembles_infinis.NN = app("N")` est un
symbole OPAQUE ; le ℕ concret est `ensemble_NN()`, et ℵ₀ := Card(ensemble_NN()).
Mesuré : `aleph_0() != cardinal(ensembles_infinis.NN)`.  Prendre le mauvais fait
échouer la majoration sans rien dire d'utile.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE.
  (1) PAIR        ⊢ n = ℕ+ℕ est la réflexivité ; S5 au témoin ℕ donne (∃k)(n=k+k).
  (2) MAJORATION  ⊢ ℵ₀ ≤ n  (borne gauche de la somme, inconditionnelle).
  (3) n ≠ 0       si n = 0 alors ℵ₀ ≤ 0 donc ℵ₀ = 0, donc Fini(ℵ₀) — interdit.
  (4) n ≠ 2       si n = N(2) alors ℵ₀ ≤ N(2) ; `enum` referme le domaine et les
                  trois valeurs sont finies : même contradiction.
  (5) PONT        l'énoncé parle de `zero()` et `deux()`, PAS des numéraux ; on
                  transporte, sinon on démontrerait une formule voisine.

⚠️ COÛT : ℵ₀ demande ~235 s à construire (le ℕ concret).  Le test qui exerce ce
module porte donc le marqueur `slow`.

FRONTIÈRE.  Rien de fabriqué, rien de postulé, dépôt non modifié, invariant 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, existe, subst_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, cas, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as S,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    b_le_0_implique_egal_0,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
    inf_egal_somme_gauche_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import (
    aleph_0, aleph0_infini,
)
#: ⚠️ LE BON ℕ — le concret, celui sur lequel ℵ₀ est bâti (cf. l'en-tête).
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures.primalite import pont_un

mp = N.modus_ponens
NUM = M.NUM


def temoin_pair_infini():
    """Le terme n := ℕ + ℕ — un cardinal infini, pair par construction."""
    return S(ensemble_NN(), ensemble_NN())


def ancien_antecedent(vn):
    """L'antécédent de `goldbach()` AVANT la réparation du 6 août 2026.

    Conservé ici et NULLE PART ailleurs : c'est la formule dont ce module montre
    qu'elle est satisfaite par un infini.  Ne pas la réintroduire dans l'énoncé."""
    vk = var("kgb")
    return et(et(existe("kgb", egal(vn, S(vk, vk))), non(egal(vn, GB.zero()))),
              non(egal(vn, GB.deux())))


def _instancie_terme(build, nom, terme):
    """Généralise un lemme du dépôt sur `nom`, puis l'instancie au TERME donné."""
    base = build(nom)
    assert base.est_clos, "%s : générique non clos" % nom
    return instancie(N.generalisation(nom, base), terme)


def antecedent_satisfait_par_un_infini():
    """⊢ ( pair(n) et n ≠ 0 et n ≠ 2 )  pour n := ℕ+ℕ.      [CLOS, 0 hypothèse]

    La conclusion est comparée — égalité de formules — à `ancien_antecedent`
    instancié en n.  C'est cette comparaison qui fait la démonstration : sans
    elle on prouverait une formule voisine, et l'on n'aurait rien montré."""
    NNs, A = ensemble_NN(), aleph_0()
    n = temoin_pair_infini()
    inf_A = aleph0_infini()                                   # ⊢ ¬Fini(ℵ₀)
    assert inf_A.est_clos and inf_A.conclusion == non(est_fini(A))

    # ── (1) n est PAIR, par construction ─────────────────────────────────────
    vk = var("kgb")
    pair_n = mp(N.reflexivite(n), N.s5(egal(n, S(vk, vk)), NNs, "kgb"))
    assert pair_n.conclusion == existe("kgb", egal(n, S(vk, vk)))

    # ── (2) ℵ₀ ≤ n ───────────────────────────────────────────────────────────
    le_A = inf_egal_somme_gauche_binaire(NNs, NNs)
    assert le_A.conclusion == inf_egal_card(A, n), "la borne ne porte pas sur ℵ₀"

    trou = var(M._HOLE)

    def _fini_A_depuis(eq_A_Nj, j):
        """De ⊢ ℵ₀ = N(j), tirer ⊢ Fini(ℵ₀) — ce que `inf_A` contredit."""
        return M.reecrit(mp(eq_A_Nj, symetrie(A, NUM(j))),
                         M.fini_num(j), est_fini(trou))

    # ── (3) n ≠ 0 ────────────────────────────────────────────────────────────
    but0 = non(egal(n, NUM(0)))
    le0 = M.reecrit(N.assume(egal(n, NUM(0))), le_A, inf_egal_card(A, trou))
    eq_A0 = mp(le0, _instancie_terme(b_le_0_implique_egal_0, "bl0z", A))
    ne_n0 = M.neg_intro(egal(n, NUM(0)),
                        M.ex_falso(_fini_A_depuis(eq_A0, 0), inf_A, but0))
    assert ne_n0.est_clos and ne_n0.conclusion == non(egal(n, GB.zero()))

    # ── (4) n ≠ N(2) ─────────────────────────────────────────────────────────
    # ⚠️ le lieur DOIT être celui qu'attend `successeur_ordre` (défaut « X ») :
    #    avec un nom frais, l'antécédent d'`enum` ne se reconnaît plus.
    card_A = mp(N.reflexivite(A), N.s5(egal(A, cardinal(var("X"))), NNs, "X"))
    assert card_A.conclusion == est_cardinal(A)
    but2 = non(egal(n, NUM(2)))
    le2 = M.reecrit(N.assume(egal(n, NUM(2))), le_A, inf_egal_card(A, trou))
    disj = mp(le2, C.enum(A, 2, card_d=card_A))

    def branche(j):
        return N.loi_deduction(egal(A, NUM(j)), M.ex_falso(
            _fini_A_depuis(N.assume(egal(A, NUM(j))), j), inf_A, but2))

    cur = branche(0)
    for j in (1, 2):
        dj = C.disj(A, j)
        cur = N.loi_deduction(dj, cas(N.assume(dj), cur, branche(j)))
    ne_n2 = M.neg_intro(egal(n, NUM(2)), mp(disj, cur))

    # ── (5) PONT vers les constantes DE L'ÉNONCÉ ─────────────────────────────
    #     `deux()` vaut un()+un(), pas N(2) : sans transport on démontrerait
    #     une formule voisine de l'antécédent, et non l'antécédent.
    d_eq = M.reecrit(pont_un(),
                     M.reecrit(pont_un(), C.somme_num(1, 1),
                               egal(S(trou, NUM(1)), NUM(2))),
                     egal(S(GB.un(), trou), NUM(2)))
    assert d_eq.conclusion == egal(GB.deux(), NUM(2))
    ne_n2 = M.reecrit(mp(d_eq, symetrie(GB.deux(), NUM(2))), ne_n2,
                      non(egal(n, trou)))
    assert ne_n2.conclusion == non(egal(n, GB.deux()))

    res = conjonction_intro(conjonction_intro(pair_n, ne_n0), ne_n2)
    # ⚠️ `subst_f` suit l'ordre de Bourbaki (T|x)R : subst_f(TERME, var, FORMULE).
    #    Inverser les arguments rend un « False » silencieux — mesuré le 6 août.
    assert res.conclusion == subst_f(n, "ngb", ancien_antecedent(var("ngb"))), (
        "ce qui est démontré n'est PAS l'ancien antécédent instancié en n")
    assert res.est_clos and not res.hypotheses
    return res


def antecedent_satisfait_par_un_infini_cible():
    """Énoncé visé : l'ancien antécédent instancié au témoin infini ℕ+ℕ
    (compagne zéro-arg pour le gate du volant — même subst_f que l'assert final)."""
    return subst_f(temoin_pair_infini(), "ngb", ancien_antecedent(var("ngb")))


__all__ = ["temoin_pair_infini", "ancien_antecedent",
           "antecedent_satisfait_par_un_infini",
           "antecedent_satisfait_par_un_infini_cible"]
