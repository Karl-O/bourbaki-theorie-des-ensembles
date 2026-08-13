# -*- coding: utf-8 -*-
"""LA RÉDUCTION SANS BORNE — le premier théorème Goldbach du corpus SUR TOUT n.

    ⊢   ( (∀k)( ( Fini k et k≠0 et k≠1 ) ⇒ (∃p)(∃p')( p,p' premiers et k+k = p+p' ) ) )
        ⇒   goldbach()

────────────────────────────────────────────────────────────────────────────────
CE QUE CE THÉORÈME DIT, ET CE QU'IL NE DIT PAS.

Il ne démontre PAS la conjecture : l'hypothèse H (la forme « moitiés », sans
borne) est exactement aussi ouverte qu'elle.  Il démontre que H l'IMPLIQUE —
c'est-à-dire que le passage aux moitiés ne perd RIEN, pour TOUT n, sans borne,
sans énumération, sans cas sur n.  La conjecture entière est ainsi ramenée à un
seul énoncé sur les moitiés, et ce qui manque est isolé en un point unique :
la décomposition elle-même.

AUCUN sous-cas sur n.  Les seules constantes qui apparaissent (0, 1, 2) sont
celles DE L'ÉNONCÉ (n≠0, n≠2, k≠0, k≠1) — pas une énumération.

────────────────────────────────────────────────────────────────────────────────
LES DEUX FORMULES SONT PRÉLEVÉES, PAS RECONSTRUITES.

  · goldbach() est DÉCOUPÉ (ANTE, DEC extraits par .sous, puis RECOMPOSÉ et
    comparé à l'original — le prélèvement est vérifié avant d'être utilisé) ;
  · H est l'antécédent de goldbach_borne.antecedent PRIVÉ de son conjoint de
    borne (là encore : prélevé par .sous[0] et vérifié par recomposition).

────────────────────────────────────────────────────────────────────────────────
LA ROUTE (sous H, sous ANTE en une variable libre n) :

  1. « n pair » = (∃k)( n = k+k ) : on élimine l'existentielle ; le témoin m
     est un ENSEMBLE QUELCONQUE, pas un cardinal.
  2. PONT : m+m = Card m + Card m (pont_cardinal, clos, terme arbitraire),
     donc n = c+c avec c := Card m — et c EST un cardinal.
  3. Fini c : c ≤ n (borne gauche de la somme, inconditionnelle, réécrite par
     n = m+m) puis « un minorant d'un fini est fini » — fini_downward_garde_thm,
     dont les DEUX résidus se déchargent : predecesseur_fini_universel est CLOS
     (Prop. 2 §III.5, ensembles_predecesseur_prop2) et est_cardinal(a) se
     décharge par loi de déduction avant généralisation.
  4. c ≠ 0 : sinon n = 0+0 = 0 (somme_num(0,0)), contre n≠0.
     c ≠ 1 : sinon n = 1+1 = N(2) = deux() (somme_num(1,1) + le pont
     un_egale_card_singleton), contre n≠2.
  5. H instancié en c donne la décomposition de c+c ; Leibniz (n = c+c
     retournée) la transporte sur n : c'est DEC.
  6. Décharge de l'existentielle (existe_elimination : le témoin n'est libre ni
     dans DEC ni dans les autres hypothèses), décharge de ANTE, généralisation
     sur n — la conclusion recompose goldbach() À L'IDENTIQUE — décharge de H.

FRONTIÈRE : primitives du noyau uniquement, aucun fichier du dépôt modifié,
theorie_ensembles() = 22 vérifié en fin de script.
"""
from __future__ import annotations


from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, et, impl, existe, pourtout, libres_f, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites, symetrie,
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
    cardinal, est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_calcul_entiers_props import (
    inf_egal_somme_gauche_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_vraie import (
    fini_downward_garde_thm,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)

from outils_ia.arithmetique import machine_num as M
from outils_ia.arithmetique import calcul_num as C
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures import goldbach_borne as GBB
from outils_ia.conjectures.primalite import pont_un

from outils_ia.arithmetique import pont_cardinal as PC

mp = N.modus_ponens
NUM = M.NUM
TROU = var(M._HOLE)
W = 78


# ══════════════════════════════════════════════════════════════════════════════
#  PRÉLÈVEMENTS — les deux formules viennent du dépôt, vérifiées par recomposition
# ══════════════════════════════════════════════════════════════════════════════
def preleve_goldbach():
    """(ANTE, DEC) extraits de goldbach() ; le prélèvement est VÉRIFIÉ."""
    ou_ = GB.goldbach().sous[0].sous[0].sous[0]        # ou( non ANTE , DEC )
    ante, dec = ou_.sous[0].sous[0], ou_.sous[1]
    assert pourtout("ngb", impl(ante, dec)) == GB.goldbach(), (
        "le prélèvement ne recompose pas goldbach()")
    return ante, dec


def hypothese_moities(k="kgb"):
    """H : la forme « moitiés » SANS borne — l'antécédent de goldbach_borne privé
    de son conjoint de borne, prélevé et vérifié par recomposition."""
    vk = var(k)
    borne = GBB.antecedent(vk, 2)                      # ((Fini k et k≠0) et k≠1) et k≤N(2)
    # ⚠️ et(a,b) est ABRÉGÉ en ¬(¬a ∨ ¬b) : le conjoint gauche est trois niveaux
    #    plus bas — .sous[0] serait le « ou », pas lui (défaut mesuré à la 1re passe).
    sans_borne = borne.sous[0].sous[0].sous[0]         # (Fini k et k≠0) et k≠1
    assert et(sans_borne, inf_egal_card(vk, NUM(2))) == borne, (
        "le prélèvement de l'antécédent sans borne ne recompose pas l'antécédent borné")
    return pourtout(k, impl(sans_borne, GBB.decomposition(SC(vk, vk))))


# ══════════════════════════════════════════════════════════════════════════════
#  FINI DESCENDANT, CLOS — { } ⊢ (∀a)( est_cardinal a ⇒ (∀x)( (a≤x et Fini x) ⇒ Fini a ) )
# ══════════════════════════════════════════════════════════════════════════════
_FD = None


def fini_downward_clos():
    """Le « minorant d'un fini est fini », SANS résidu.

    fini_downward_garde_thm laisse deux hypothèses : predecesseur_fini_universel
    (déchargée par sa preuve CLOSE, Prop. 2 §III.5) et est_cardinal(a) (déchargée
    par loi de déduction, PUIS généralisée — l'ordre compte : on ne généralise
    jamais une variable libre dans une hypothèse)."""
    global _FD
    if _FD is None:
        fdg = fini_downward_garde_thm()                # {est_cardinal(a), pfu} ⊢ (∀x) fd(a,x)
        garde = est_cardinal(var("a"))
        assert garde in fdg.hypotheses, "la garde est_cardinal(a) n'est pas une hypothèse"
        autres = [h for h in fdg.hypotheses if h != garde]
        assert len(autres) == 1, "résidus inattendus : %d" % len(autres)
        pfu = autres[0]
        preuve = predecesseur_fini_universel_preuve()
        assert preuve.est_clos and not preuve.hypotheses
        assert preuve.conclusion == pfu, (
            "la preuve de la Prop. 2 ne conclut pas le résidu de fini_downward "
            "(α-variantes ? noms de lieurs ?)")
        decharge_pfu = mp(preuve, N.loi_deduction(pfu, fdg))
        ded = N.loi_deduction(garde, decharge_pfu)     # est_cardinal(a) ⇒ (∀x) fd(a,x)
        assert ded.est_clos, "résidu après décharges : %s" % (ded.hypotheses,)
        _FD = N.generalisation("a", ded)
        assert _FD.est_clos
    return _FD


def _est_cardinal_card(t, temoin):
    """⊢ est_cardinal( Card(T) )  —  gratuit : témoin X := T, par réflexivité.

    ⚠️ Le lieur est « X », celui de la définition (est_cardinal(a, x="X")) : un
    nom « frais » casserait la reconnaissance de l'antécédent (piège mesuré)."""
    ct = cardinal(t)
    r = mp(N.reflexivite(ct), N.s5(egal(ct, cardinal(var("X"))), temoin, "X"))
    assert r.conclusion == est_cardinal(ct) and r.est_clos
    return r


# ══════════════════════════════════════════════════════════════════════════════
#  LE THÉORÈME
# ══════════════════════════════════════════════════════════════════════════════
def reduction_moities(k="kgb"):
    """⊢ H ⇒ goldbach().                                  [CLOS, 0 hypothèse]

    H = la forme « moitiés » sans borne (hypothese_moities).  Aucun cas sur n."""
    ANTE, DEC = preleve_goldbach()
    H = hypothese_moities(k)
    vn, vk = var("ngb"), var(k)

    h_H = N.assume(H)

    # ── ANTE, projeté conjoint par conjoint ──────────────────────────────────
    gb_h = N.assume(ANTE)
    g3 = conjonction_elim_gauche(gb_h)                 # (Fini n et pair n) et n≠0
    ne_2 = conjonction_elim_droite(gb_h)               # ¬( n = deux() )
    g2 = conjonction_elim_gauche(g3)                   # Fini n et pair n
    ne_0 = conjonction_elim_droite(g3)                 # ¬( n = zero() )
    fini_n = conjonction_elim_gauche(g2)               # Fini n
    pair_n = conjonction_elim_droite(g2)               # (∃k)( n = k+k )
    assert fini_n.conclusion == est_fini(vn)

    # ── sous le corps de l'existentielle : n = m+m, m ENSEMBLE quelconque ────
    corps = egal(vn, SC(vk, vk))
    assert existe(k, corps) == pair_n.conclusion, "le corps ne recompose pas « pair n »"
    h_corps = N.assume(corps)

    c = cardinal(vk)                                   # c := Card m — LE cardinal

    # (2) le pont : n = c + c
    eq_cc = composer_egalites(h_corps, PC.pont_card(vk))
    assert eq_cc.conclusion == egal(vn, SC(c, c))

    # (3) Fini c : c ≤ n puis fini-descendant
    le_brut = inf_egal_somme_gauche_binaire(k, k)      # Card m ≤ m+m   (inconditionnel)
    assert le_brut.conclusion == inf_egal_card(c, SC(vk, vk)) and le_brut.est_clos
    le_cn = M.reecrit(mp(h_corps, symetrie(vn, SC(vk, vk))), le_brut,
                      inf_egal_card(c, TROU))          # Card m ≤ n
    assert le_cn.conclusion == inf_egal_card(c, vn)

    fd_c = instancie(fini_downward_clos(), c)          # est_cardinal(c) ⇒ (∀x) fd(c,x)
    tous_x = mp(_est_cardinal_card(vk, vk), fd_c)      # (∀x) fd(c, x)
    fd_n = instancie(tous_x, vn)                       # (c≤n et Fini n) ⇒ Fini c
    fini_c = mp(conjonction_intro(le_cn, fini_n), fd_n)
    assert fini_c.conclusion == est_fini(c)

    # (4) c ≠ 0  — sinon n = 0+0 = 0, contre n ≠ 0
    R2 = egal(vn, SC(TROU, TROU))                      # les DEUX occurrences, voulues
    assert GB.zero() == NUM(0), "zero() n'est plus N(0) ?"
    eq_n0 = composer_egalites(
        M.reecrit(N.assume(egal(c, NUM(0))), eq_cc, R2), C.somme_num(0, 0))
    assert eq_n0.conclusion == egal(vn, GB.zero())
    ne_c0 = M.neg_intro(egal(c, NUM(0)), M.ex_falso(eq_n0, ne_0, non(egal(c, NUM(0)))))

    #     c ≠ 1  — sinon n = 1+1 = N(2) = deux(), contre n ≠ 2
    d_eq = M.reecrit(pont_un(),
                     M.reecrit(pont_un(), C.somme_num(1, 1),
                               egal(SC(TROU, NUM(1)), NUM(2))),
                     egal(SC(GB.un(), TROU), NUM(2)))
    assert d_eq.conclusion == egal(GB.deux(), NUM(2))  # le pont deux() = N(2)
    eq_n2 = composer_egalites(
        composer_egalites(M.reecrit(N.assume(egal(c, NUM(1))), eq_cc, R2),
                          C.somme_num(1, 1)),
        mp(d_eq, symetrie(GB.deux(), NUM(2))))
    assert eq_n2.conclusion == egal(vn, GB.deux())
    ne_c1 = M.neg_intro(egal(c, NUM(1)), M.ex_falso(eq_n2, ne_2, non(egal(c, NUM(1)))))

    # (5) H instancié en c, puis Leibniz vers n
    inst_H = instancie(h_H, c)
    ante_c = conjonction_intro(conjonction_intro(fini_c, ne_c0), ne_c1)
    dec_cc = mp(ante_c, inst_H)
    assert dec_cc.conclusion == GBB.decomposition(SC(c, c))
    R_dec = GBB.decomposition(TROU)
    dec_n = M.reecrit(mp(eq_cc, symetrie(vn, SC(c, c))), dec_cc, R_dec)
    assert dec_n.conclusion == DEC, "la décomposition transportée n'est pas DEC"

    # (6) décharges : l'existentielle, ANTE, la généralisation, H
    imp_corps = N.loi_deduction(corps, dec_n)          # corps ⇒ DEC
    assert k not in libres_f(DEC), "le témoin fuit dans DEC"
    for hyp in imp_corps.hypotheses:
        assert k not in libres_f(hyp), "le témoin fuit dans une hypothèse : %s" % (hyp,)
    dec_thm = mp(pair_n, existe_elimination(imp_corps, k))
    assert dec_thm.conclusion == DEC

    ded = N.loi_deduction(ANTE, dec_thm)               # ANTE ⇒ DEC   [H]
    gen = N.generalisation("ngb", ded)
    assert gen.conclusion == GB.goldbach(), "la recomposition n'est pas goldbach()"
    res = N.loi_deduction(H, gen)
    assert res.conclusion == impl(H, GB.goldbach())
    assert res.est_clos and not res.hypotheses, "résidu : %s" % (res.hypotheses,)
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  PILOTE
# ══════════════════════════════════════════════════════════════════════════════
