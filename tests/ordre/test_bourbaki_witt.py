"""Tests de ensembles_bourbaki_witt.py — LEMME 3 §III.2 (Bourbaki–Witt) vers Zorn.

On vérifie :
  • les DÉFINITIONS fidèles (inflationnaire, chaîne-complet, tour, M, axiome_M) ;
  • les LEMMES DIRECTS sur M (M⊂E, M_inclus, a∈M, M close par p, close par sup) ;
  • le CŒUR point fixe (p(s)≤s ; p(s)=s sous les hyps de clôture + antisymétrie) ;
  • les ÉNONCÉS (Bourbaki–Witt, M chaîne [verrou], Zorn via BW) — DÉFINITIONS
    d'énoncés, non prouvés ;
  • theorie_ensembles() reste = 22 axiomes (axiome_M vit dans une théorie DÉDIÉE).
"""
from bourbaki.logique.formule import (
    var, egal, et, impl, appartient, pourtout, inclus,
)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_relation as O
from bourbaki.ordre.ensembles_zorn import chaine, zorn
from bourbaki.ordre import ensembles_bourbaki_witt as BW


G, Es, P, A = var("G"), var("E"), var("p"), var("a")
s, x, u, C = var("s"), var("x"), var("u"), var("C")


def Mt():
    return BW.M(G, Es, P, A)


# ── theorie_ensembles INTANGIBLE = 22 ─────────────────────────────────────────
def test_theorie_ensembles_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── DÉFINITIONS fidèles §III.2 (Lemme 3) ──────────────────────────────────────
def test_inflationnaire_definition():
    f = BW.inflationnaire(G, Es, P)
    cible = pourtout("x", impl(appartient(x, Es),
                               appartient(E.couple(x, BW.pval(P, x)), G)))
    assert f == cible


def test_application_dans_definition():
    f = BW.application_dans(Es, P)
    cible = pourtout("x", impl(appartient(x, Es), appartient(BW.pval(P, x), Es)))
    assert f == cible


def test_chaine_complet_definition():
    f = BW.chaine_complet(G, Es)
    corps = impl(chaine(G, Es, C),
                 __import__("bourbaki.logique.formule", fromlist=["existe"]).existe(
                     "s", O.borne_superieure(G, C, s, Es)))
    cible = et(O.est_ordre(G, Es), pourtout("C", corps))
    assert f == cible


def test_est_tour_construit():
    f = BW.est_tour(G, Es, P, A, var("S"))
    assert f is not None  # conjonction (S⊂E et a∈S et clos_p et clos_sup)


def test_pval_terme():
    assert BW.pval(P, x) == E.app("bw_p", P, x)


# ── M : terme + axiome dédié + caractérisation membre ─────────────────────────
def test_M_terme():
    assert Mt() == E.app("bw_M", G, Es, P, A)


def test_axiome_M_dans_theorie_dediee():
    th = BW.theorie_M()
    assert th.nom == "M-Bourbaki-Witt"
    assert len(th.axiomes) == 1
    # et l'axiome de M n'est PAS dans theorie_ensembles
    assert BW.axiome_M() not in E.theorie_ensembles().axiomes


def test_M_membre_close():
    t = BW.M_membre()
    assert t.est_clos


# ── LEMMES DIRECTS sur M ──────────────────────────────────────────────────────
def test_M_inclus_E():
    t = BW.M_inclus_E()
    assert t.conclusion == inclus(Mt(), Es)
    assert t.est_clos


def test_M_inclus():
    t = BW.M_inclus()
    # (S tour admissible) ⇒ (M ⊂ S)
    tour = BW.est_tour(G, Es, P, A, var("S"))
    assert t.conclusion == impl(tour, inclus(Mt(), var("S")))
    assert t.est_clos


def test_a_dans_M():
    t = BW.a_dans_M()
    assert t.conclusion == appartient(A, Mt())
    assert t.hypotheses == {appartient(A, Es)}


def test_M_clos_p():
    t = BW.M_clos_p()
    # (u∈M) ⇒ (p(u)∈M)  sous l'hypothèse résiduelle p(u)∈E
    assert t.conclusion == impl(appartient(u, Mt()), appartient(BW.pval(P, u), Mt()))
    assert t.hypotheses == {appartient(BW.pval(P, u), Es)}


def test_M_clos_sup():
    t = BW.M_clos_sup()
    hyp = et(et(inclus(C, Mt()), chaine(G, Es, C)),
             O.borne_superieure(G, C, s, Es))
    assert t.conclusion == impl(hyp, appartient(s, Mt()))
    assert t.est_clos


# ── CŒUR : p(s) ≤ s puis point fixe p(s)=s ────────────────────────────────────
def test_p_de_sup_inferieur():
    t = BW.p_de_sup_inferieur()
    ps = BW.pval(P, s)
    # conclusion : (p(s), s)∈G   (i.e. p(s) ≤ s)
    assert t.conclusion == appartient(E.couple(ps, s), G)
    assert t.hypotheses == {appartient(ps, Mt()),
                            O.plus_grand_element(G, Mt(), s)}


def test_point_fixe_de_sup():
    t = BW.point_fixe_de_sup()
    ps = BW.pval(P, s)
    # conclusion : p(s) = s  (POINT FIXE de Bourbaki–Witt, étage final)
    assert t.conclusion == egal(ps, s)
    assert t.hypotheses == {
        O.antisymetrie(G),
        BW.inflationnaire(G, Es, P),
        appartient(s, Es),
        appartient(ps, Mt()),
        O.plus_grand_element(G, Mt(), s),
    }
    # JAMAIS clos sans ces hypothèses (rien n'est postulé)
    assert not t.est_clos


# ── ÉNONCÉS (définitions d'énoncés ; non prouvés) ─────────────────────────────
def test_bourbaki_witt_enonce():
    from bourbaki.logique.formule import existe
    f = BW.bourbaki_witt(G, Es, P, A)
    # ⇒ (∃s)(p(s)=s)
    hyp = et(et(et(et(O.est_ordre(G, Es),
                      BW.chaine_complet(G, Es)),
                   BW.application_dans(Es, P)),
                BW.inflationnaire(G, Es, P)),
             O.plus_petit_element(G, Es, A))
    cible = impl(hyp, existe("s", egal(BW.pval(P, s), s)))
    assert f == cible


def test_M_est_une_chaine_enonce_verrou():
    f = BW.M_est_une_chaine(G, Es, P, A)
    # énoncé du VERROU : M totalement ordonné
    assert f == O.totalement_ordonne(G, Mt())


def test_bourbaki_witt_si_M_chaine_enonce():
    f = BW.bourbaki_witt_si_M_chaine(G, Es, P, A)
    cible = impl(BW.M_est_une_chaine(G, Es, P, A),
                 BW.bourbaki_witt(G, Es, P, A))
    assert f == cible


def test_zorn_via_bw_enonce():
    f = BW.zorn_via_bw(G, Es)
    # redite fidèle de l'énoncé de Zorn (réduction Zorn ⇐ Bourbaki–Witt)
    assert f == zorn(G, Es)
