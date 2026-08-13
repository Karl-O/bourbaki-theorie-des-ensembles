# -*- coding: utf-8 -*-
"""LA RÉCIPROQUE, ET L'ÉQUIVALENCE — goldbach() ⇔ la forme « moitiés », sur TOUT n.

    ⊢  goldbach() ⇒ H          (ce script)
    ⊢  ( H ⇒ goldbach() )  et  ( goldbach() ⇒ H )        (l'ÉQUIVALENCE, assemblée ici)

où H = (∀k)( ( Fini k et k≠0 et k≠1 ) ⇒ (∃p)(∃p')( p,p' premiers et k+k = p+p' ) )
— la même H que goldbach_reduction, prélevée de goldbach_borne, binder « kgb ».

────────────────────────────────────────────────────────────────────────────────
CE QUE L'ÉQUIVALENCE ÉTABLIT.  La conjecture de Goldbach EST la forme « moitiés » :
les deux énoncés sont interdérivables dans le noyau, sans borne, sans cas sur n.
Travailler sur l'une, c'est travailler sur l'autre — démontré, plus seulement dit.

────────────────────────────────────────────────────────────────────────────────
HONNÊTETÉ SUR LES CAS.  La preuve directe (goldbach_reduction) n'a AUCUNE analyse de cas.
Celle-ci en a UNE : le lemme « k+k = 2 ⇒ contradiction avec k≠0, k≠1 » énumère
k ∈ {0, 1, 2} — trois branches, taille FIXE, sur la CONSTANTE 2 de l'énoncé
(le conjoint n ≠ 2).  Ce n'est pas un cas sur n : la taille ne dépend d'aucune
borne, et la constante vient de l'énoncé lui-même, comme 0+0=0 dans goldbach_reduction.

────────────────────────────────────────────────────────────────────────────────
LA ROUTE (sous G := goldbach(), sous ( Fini k et k≠0 ) et k≠1, variable k) :

  1. G instancié en n := k+k.  ⚠️ CAPTURE CONTOURNÉE PAR PRÉLÈVEMENT DYNAMIQUE :
     le corps de goldbach() LIE « kgb » (le témoin de parité) qui est aussi notre
     variable de travail — l'instanciation α-renomme donc ce lieur.  On ne devine
     JAMAIS le nom frais : on PRÉLÈVE la formule instanciée (antécédent, conjoint
     de parité, lieur) sur le théorème lui-même, et l'on construit la preuve de
     parité avec CE lieur-là.
  2. Fini(k+k) : Proposition 1 §III.5.1 (somme_binaire_entier, CLOSE au dépôt).
  3. pair(k+k) : témoin k, réflexivité puis S5 (sur le lieur prélevé).
  4. Card k = k (sous est_cardinal k, tiré de Fini k) : idempotence de Card
     (_cardinal_idempotent_t) + congruence + élimination du témoin de est_cardinal.
     C'est LA charnière : elle transforme la borne « Card k ≤ k+k » en « k ≤ k+k ».
  5. k+k ≠ 0 : sinon k ≤ 0 donc k = 0 (b_le_0), contre k≠0.
     k+k ≠ 2 : sinon k ≤ N(2) (via le pont deux() = N(2)) ; énumération FIXE
     k ∈ {0,1,2} : 0 et 1 contredisent k≠0/k≠1, 2 donne k+k = N(4) = N(2), absurde.
  6. Modus ponens, décharges, généralisation sur k : la conclusion recompose H
     à l'identique ; décharge de G.

FRONTIÈRE : primitives du noyau uniquement ; aucun fichier du dépôt modifié ;
theorie_ensembles() = 22 vérifié en fin de script.
"""
from __future__ import annotations


from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, existe, subst_f,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie, congruence_terme,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import (
    theorie_ensembles,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
    inf_egal_somme_gauche_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_binaire_entier,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_cardinaux_props_restantes import (
    _cardinal_idempotent_t,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures import goldbach_borne as GBB
from outils_ia.conjectures.primalite import pont_un

from outils_ia.conjectures.goldbach_reduction import (
    preleve_goldbach, hypothese_moities, reduction_moities,
)

mp = N.modus_ponens
NUM = M.NUM
TROU = var(M._HOLE)
W = 78


def _et_g(f):
    """Conjoint GAUCHE d'une formule et(a,b) = ¬(¬a ∨ ¬b)."""
    return f.sous[0].sous[0].sous[0]


def _et_d(f):
    """Conjoint DROIT d'une formule et(a,b)."""
    return f.sous[0].sous[1].sous[0]


def card_egal_soi(vk, est_card_thm):
    """{est_cardinal k} ⊢ Card k = k  —  LA charnière de la réciproque.

    Par témoin : k = Card X ⇒ Card k = Card(Card X) (congruence) = Card X
    (idempotence) = k (symétrie de l'hypothèse) ; puis élimination du témoin.
    Le lieur « X » est PRÉLEVÉ sur le théorème est_cardinal, jamais deviné."""
    lieur = est_card_thm.conclusion.lieur
    vX = var(lieur)
    hX = N.assume(egal(vk, cardinal(vX)))              # k = Card X
    congr = mp(hX, congruence_terme(vk, cardinal(vX), cardinal(TROU), w=M._HOLE))
    carda = composer_egalites(composer_egalites(congr, _cardinal_idempotent_t(vX)),
                              mp(hX, symetrie(vk, cardinal(vX))))     # Card k = k
    imp = N.loi_deduction(egal(vk, cardinal(vX)), carda)
    r = mp(est_card_thm, existe_elimination(imp, lieur))
    assert r.conclusion == egal(cardinal(vk), vk)
    return r


def reciproque_moities(k="kgb"):
    """⊢ goldbach() ⇒ H.                                  [CLOS, 0 hypothèse]"""
    G = GB.goldbach()
    H = hypothese_moities(k)
    vk = var(k)
    kk = SC(vk, vk)

    h_G = N.assume(G)

    # ── l'antécédent de H, projeté ───────────────────────────────────────────
    sans_borne = GBB.antecedent(vk, 2).sous[0].sous[0].sous[0]   # (Fini k et k≠0) et k≠1
    h_ante = N.assume(sans_borne)
    g2 = conjonction_elim_gauche(h_ante)               # Fini k et k≠0
    ne_k1 = conjonction_elim_droite(h_ante)            # ¬( k = N(1) )
    fini_k = conjonction_elim_gauche(g2)               # Fini k
    ne_k0 = conjonction_elim_droite(g2)                # ¬( k = N(0) )

    # ── (1) G instancié en n := k+k, formules PRÉLEVÉES sur le théorème ──────
    G_kk = instancie(h_G, kk)
    # ⚠️ instancie a déjà dépouillé le pourtout : la conclusion EST le « ou » de
    #    l'implication abrégée (défaut mesuré à la 1re passe — IndexError sinon).
    ou_ = G_kk.conclusion
    ANTE_kk, DEC_kk = ou_.sous[0].sous[0], ou_.sous[1]
    assert impl(ANTE_kk, DEC_kk) == G_kk.conclusion
    assert DEC_kk == GBB.decomposition(kk), "le conséquent instancié a été α-renommé ?"

    # ── (2) Fini(k+k) : Prop. 1 §III.5.1, close au dépôt ─────────────────────
    fini_kk = mp(conjonction_intro(fini_k, fini_k), somme_binaire_entier(k, k))
    assert fini_kk.conclusion == est_fini(kk)

    # ── (3) pair(k+k) : témoin k, sur le LIEUR PRÉLEVÉ (α-renommage possible) ─
    pair_f = _et_d(_et_g(_et_g(ANTE_kk)))              # (∃?)( k+k = ?+? )
    assert pair_f.tag == "exists"
    lieur_pair, matrice = pair_f.lieur, pair_f.sous[0]
    assert subst_f(vk, lieur_pair, matrice) == egal(kk, kk), (
        "la matrice de parité instanciée au témoin k n'est pas la réflexivité")
    pair_kk = mp(N.reflexivite(kk), N.s5(matrice, vk, lieur_pair))
    assert pair_kk.conclusion == pair_f

    # ── (4) Card k = k, puis k ≤ k+k ─────────────────────────────────────────
    card_eq_k = card_egal_soi(vk, mp(fini_k, M.fic_t(vk)))
    le_brut = inf_egal_somme_gauche_binaire(k, k)      # Card k ≤ k+k  (inconditionnel)
    assert le_brut.conclusion == inf_egal_card(cardinal(vk), kk)
    le_k_kk = M.reecrit(card_eq_k, le_brut, inf_egal_card(TROU, kk))
    assert le_k_kk.conclusion == inf_egal_card(vk, kk)

    # ── (5a) k+k ≠ 0 ─────────────────────────────────────────────────────────
    assert GB.zero() == NUM(0)
    but0 = non(egal(kk, GB.zero()))
    h0 = N.assume(egal(kk, NUM(0)))
    le_k0 = M.reecrit(h0, le_k_kk, inf_egal_card(vk, TROU))       # k ≤ 0
    eq_k0 = mp(le_k0, M._ble0_t(vk))                              # k = 0
    ne_kk0 = M.neg_intro(egal(kk, NUM(0)), M.ex_falso(eq_k0, ne_k0, but0))
    assert ne_kk0.conclusion == but0

    # ── (5b) k+k ≠ 2 — l'UNIQUE analyse de cas, FIXE, sur la constante 2 ─────
    d_eq = M.reecrit(pont_un(),
                     M.reecrit(pont_un(), C.somme_num(1, 1),
                               egal(SC(TROU, NUM(1)), NUM(2))),
                     egal(SC(GB.un(), TROU), NUM(2)))
    assert d_eq.conclusion == egal(GB.deux(), NUM(2))             # deux() = N(2)
    but2 = non(egal(kk, GB.deux()))
    h2 = N.assume(egal(kk, GB.deux()))
    eq_kk_n2 = composer_egalites(h2, d_eq)                        # k+k = N(2)
    le_k2 = M.reecrit(eq_kk_n2, le_k_kk, inf_egal_card(vk, TROU))  # k ≤ N(2)
    disj = mp(le_k2, C.enum(vk, 2, card_d=mp(fini_k, M.fic_t(vk))))

    def branche(j):
        hj = N.assume(egal(vk, NUM(j)))
        if j in (0, 1):
            th = M.ex_falso(hj, ne_k0 if j == 0 else ne_k1, but2)
        else:                                          # k = 2 ⇒ k+k = N(4) = N(2)
            eq_kk4 = composer_egalites(
                M.reecrit(hj, N.reflexivite(kk), egal(kk, SC(TROU, TROU))),
                C.somme_num(2, 2))                     # k+k = N(4)
            eq_24 = composer_egalites(mp(eq_kk_n2, symetrie(kk, NUM(2))), eq_kk4)
            th = M.ex_falso(eq_24, M.ne_num(2, 4), but2)          # N(2) = N(4) : absurde
        return N.loi_deduction(egal(vk, NUM(j)), th)

    cur = branche(0)
    for j in (1, 2):
        dj = C.disj(vk, j)
        cur = N.loi_deduction(dj, cas(N.assume(dj), cur, branche(j)))
    ne_kk2 = M.neg_intro(egal(kk, GB.deux()), mp(disj, cur))
    assert ne_kk2.conclusion == but2

    # ── (6) assemblage, modus ponens, décharges ──────────────────────────────
    ante_thm = conjonction_intro(conjonction_intro(conjonction_intro(
        fini_kk, pair_kk), ne_kk0), ne_kk2)
    assert ante_thm.conclusion == ANTE_kk, "l'antécédent assemblé n'est pas celui de G[k+k]"
    dec_kk = mp(ante_thm, G_kk)
    assert dec_kk.conclusion == GBB.decomposition(kk)

    ded = N.loi_deduction(sans_borne, dec_kk)          # ante_H ⇒ decomposition(k+k)  [G]
    gen = N.generalisation(k, ded)
    assert gen.conclusion == H, "la recomposition n'est pas H"
    res = N.loi_deduction(G, gen)
    assert res.conclusion == impl(G, H)
    assert res.est_clos and not res.hypotheses, "résidu : %s" % (res.hypotheses,)
    return res


def equivalence_moities(k="kgb"):
    """⊢ ( H ⇒ goldbach() ) et ( goldbach() ⇒ H )  —  L'ÉQUIVALENCE, close."""
    r = conjonction_intro(reduction_moities(k), reciproque_moities(k))
    H = hypothese_moities(k)
    assert r.conclusion == et(impl(H, GB.goldbach()), impl(GB.goldbach(), H))
    assert r.est_clos and not r.hypotheses
    return r


# ══════════════════════════════════════════════════════════════════════════════
#  PILOTE
# ══════════════════════════════════════════════════════════════════════════════
