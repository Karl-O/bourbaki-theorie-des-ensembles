"""Goldbach borné — le premier énoncé Goldbach quantifié, et ses deux gardes.

Le test central n'est pas « c'est clos » : c'est que la formule close est bien
celle de `goldbach.py`, et que l'hypothèse k ≠ 1 n'est pas décorative.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur, ZERO,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique.calcul_num import somme_num
from outils_ia.arithmetique.machine_num import ne_num
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures.goldbach_borne import (
    couple, decomposition, fidelite_verifiee, goldbach_borne,
)
from outils_ia.conjectures.primalite import est_premier_num, pont_un

mp = N.modus_ponens


def _numeral_a_la_main(k):
    """successeur^k(Card ∅), rebâti sans le cache : on ne croit pas le producteur."""
    t = ZERO
    for _ in range(k):
        t = successeur(t)
    return t


def test_sans_le_conjoint_n_non_nul_l_enonce_serait_faux():
    """🔴 RÉGRESSION — le défaut mesuré dans le noyau le 6 août 2026.

    `goldbach()` disait « n pair et n ≠ 2 », et cet antécédent est SATISFAIT en
    n = 0 : on le démontre ici, clos et sans hypothèse.  L'énoncé affirmait donc
    que 0 est somme de deux nombres premiers.  Ce n'était pas une difficulté de
    preuve — c'était une conjecture qui disait autre chose que la conjecture.

    Si ce test tombe, c'est que le conjoint `n ≠ 0` a été retiré."""
    z = _numeral_a_la_main(0)
    zz = somme_cardinale_binaire(z, z)
    # ⊢ 0 = 0 + 0, puis S5 : ⊢ (∃k)( 0 = k + k )
    eq = mp(somme_num(0, 0), symetrie(zz, z))
    pair0 = mp(eq, N.s5(egal(z, somme_cardinale_binaire(var("kgb"), var("kgb"))),
                        z, "kgb"))
    assert pair0.est_clos and not pair0.hypotheses
    assert pair0.conclusion == existe("kgb", egal(
        z, somme_cardinale_binaire(var("kgb"), var("kgb"))))

    # et le second conjoint de l'ANCIENNE rédaction est lui aussi vrai en 0.
    # Il faut d'abord ⊢ deux() = N(2) : deux() vaut un()+un(), et le pont donne
    # N(1) = un(), donc deux réécritures sur ⊢ N(1)+N(1) = N(2).
    un_, deux_ = GB.un(), GB.deux()
    n1, n2 = _numeral_a_la_main(1), _numeral_a_la_main(2)
    trou = var(M._HOLE)
    d_eq = M.reecrit(pont_un(),
                     M.reecrit(pont_un(), somme_num(1, 1),
                               egal(somme_cardinale_binaire(trou, n1), n2)),
                     egal(somme_cardinale_binaire(un_, trou), n2))
    assert d_eq.conclusion == egal(deux_, n2) and d_eq.est_clos
    grand0 = M.reecrit(mp(d_eq, symetrie(deux_, n2)), ne_num(0, 2),
                       non(egal(z, trou)))
    assert grand0.est_clos and grand0.conclusion == non(egal(z, deux_))

    # donc le conjoint réparateur est indispensable — et il est bien là :
    assert GB.zero() == z
    assert fidelite_verifiee(), "le conjoint n ≠ 0 a disparu de l'énoncé"


def test_le_quantificateur_doit_etre_garde_par_est_fini():
    """🔴 LE MÊME DÉFAUT, EN PLUS PROFOND — et commis DEUX FOIS.

    `pair(n)` force n à être un CARDINAL (n = Card(k⊔k)) mais nullement un
    ENTIER.  Or tout cardinal infini a vérifie a + a = a : il est donc « pair »
    au sens de cet énoncé, et a ≠ 0, a ≠ 2.  Sans `est_fini(n)`, la conjecture
    affirmait aussi que tout cardinal infini est somme de deux premiers.

    Ce défaut a d'abord été ARGUMENTÉ, puis DÉMONTRÉ : voir
    `test_defaut_infini.py` (⊢ l'ancien antécédent, satisfait par n := ℕ+ℕ, clos
    et sans hypothèse).  Il n'a fallu ni Hessenberg ni a + a = a — poser n := a+a
    rend la parité vraie par construction.  Le présent test reste la garde BON
    MARCHÉ : il fige la présence du conjoint sans payer les 235 s de ℵ₀.

    C'est exactement la faute corrigée le 5 août sur `est_premier` (garde
    `est_fini(d)`) : un (∀) posé sur les ensembles quand on le croyait posé sur
    les entiers.  Deux fois — donc à chercher sur TOUT quantificateur d'un
    énoncé arithmétique."""
    vn = var("ngb")
    sans_garde = pourtout("ngb", impl(
        et(et(existe("kgb", egal(vn, somme_cardinale_binaire(
                var("kgb"), var("kgb")))),
              non(egal(vn, GB.zero()))),
           non(egal(vn, GB.deux()))),
        decomposition(vn)))
    assert GB.goldbach() != sans_garde, "la garde est_fini(n) a disparu"
    assert fidelite_verifiee()


def test_le_corps_existentiel_est_celui_de_goldbach():
    """🔴 GARDE DE FIDÉLITÉ — sinon on démontrerait une variante commode.

    On REBÂTIT la conjecture entière avec la brique locale et on exige l'égalité
    avec ce que produit `goldbach.py`."""
    assert fidelite_verifiee()


def test_la_cible_est_reconstruite_independamment():
    """La conclusion est comparée à une formule bâtie ici, sans `cible()`."""
    th = goldbach_borne(2)
    vk = var("kgb")
    ante = et(et(et(est_fini(vk), non(egal(vk, _numeral_a_la_main(0)))),
                 non(egal(vk, _numeral_a_la_main(1)))),
              inf_egal_card(vk, _numeral_a_la_main(2)))
    attendu = pourtout("kgb", impl(ante, decomposition(
        somme_cardinale_binaire(vk, vk))))
    assert th.conclusion == attendu
    assert th.est_clos and not th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_goldbach_quantifie_jusqu_a_vingt():
    """UNE formule, un (∀k), tous les pairs de 4 à 2K."""
    for K in (2, 3, 5, 10):
        th = goldbach_borne(K)
        assert th.est_clos and not th.hypotheses


def test_les_decompositions_choisies_sont_correctes():
    """Le témoin est cherché en Python mais certifié par le noyau ; on vérifie
    au moins que la recherche ne ment pas."""
    for j in range(2, 11):
        a, b = couple(2 * j)
        assert a + b == 2 * j
        assert est_premier_num(a).est_clos and est_premier_num(b).est_clos
    assert couple(2) is None, "2 n'est somme d'aucun couple de premiers"


def test_l_hypothese_k_different_de_un_n_est_pas_decorative():
    """🔴 LE CONTRÔLE QUI COMPTE — pourquoi la branche k = 1 ne peut PAS se fermer.

    2·1 = 2 n'est somme d'aucun couple de premiers : `couple(2)` est None.  La
    seule façon de tricher serait de faire passer 1 pour premier — or
    `est_premier(N(1))` exige ¬( N(1) = 1 ), alors que ⊢ N(1) = 1 est un théorème
    CLOS du dépôt.  Le refus est donc un fait du NOYAU, pas de notre code Python :
    fermer cette branche rendrait le corpus incohérent."""
    assert couple(2) is None
    pont = pont_un()
    assert pont.est_clos and pont.conclusion == egal(_numeral_a_la_main(1), GB.un())

    # est_premier(N(1)) est hors du domaine de la machine, et pour une raison de
    # fond : son conjoint gauche est la négation d'un théorème clos.
    with pytest.raises(AssertionError):
        est_premier_num(1)

    # et l'on nomme la formule qu'il faudrait, pour qu'on voie qu'elle est niée :
    gauche_requise = non(egal(_numeral_a_la_main(1), GB.un()))
    assert gauche_requise == non(pont.conclusion)


def test_le_temoin_repete_ne_collapse_pas():
    """⚠️ PIÈGE DE S5 — pour 4 = 2+2 le témoin est le même des deux côtés.

    Si les matrices n'étaient pas explicites, S5 abstrairait les deux occurrences
    et l'on obtiendrait (∃p)( k+k = p+p ), strictement plus faible.  Deux gardes :
    le corps garde bien DEUX lieurs distincts, et la forme collapsée n'est PAS ce
    que la machine rend."""
    assert couple(4) == (2, 2)
    vk = var("kgb")
    kk = somme_cardinale_binaire(vk, vk)
    corps = decomposition(kk)
    assert corps.lieur == "pgb" and corps.sous[0].lieur == "qgb"

    vp = var("pgb")
    collapse = existe("pgb", et(et(GB.est_premier(vp, d="d1", q="q1"),
                                   GB.est_premier(vp, d="d2", q="q2")),
                                egal(kk, somme_cardinale_binaire(vp, vp))))
    assert corps != collapse, "le corps existentiel a collapsé sur un seul témoin"
    # Que la machine rende bien le corps NON collapsé est établi par
    # `test_la_cible_est_reconstruite_independamment`, qui compare la conclusion
    # ENTIÈRE à une formule bâtie sans passer par le producteur.
