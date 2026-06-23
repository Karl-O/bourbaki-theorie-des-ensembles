"""Tests §III.3.2 — ensemble des cardinaux ≤ a, borne supérieure d'une famille de
cardinaux (notions auparavant ABSENTES).   Définitions fidèles + 2 lemmes directs
cheap clos.   theorie=22 ; collectivisation/existence (Th.1, Prop 2) reportées."""
from bourbaki.logique.i_1_termes_relations.formule import (var, app, egal, et, impl, equiv, pourtout,
                                       appartient)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux import ensembles_cardinaux_borne_sup as BS


# ── §III.3.2 (Remarque) — ENSEMBLE DES CARDINAUX ≤ a ──────────────────────────
def test_relation_cardinal_inf_egal_forme():
    vx, va = var("x"), var("A")
    assert BS.relation_cardinal_inf_egal(vx, va) == \
        et(est_cardinal(vx), inf_egal_card(vx, va))


def test_ensemble_cardinaux_inf_egal_terme():
    va = var("A")
    assert BS.ensemble_cardinaux_inf_egal(va) == app("cardinaux_inf_egal", va)


def test_membre_cardinaux_inf_egal_forme():
    vx, va = var("x"), var("A")
    assert BS.membre_cardinaux_inf_egal(vx, va) == \
        equiv(appartient(vx, BS.ensemble_cardinaux_inf_egal(va)),
              BS.relation_cardinal_inf_egal(vx, va))


def test_a_dans_cardinaux_inf_egal_close():
    va = var("A")
    thm = BS.a_dans_cardinaux_inf_egal("A")
    assert thm.est_clos
    # est_cardinal(a) ⇒ (a cardinal et a ≤ a)
    assert thm.conclusion == impl(est_cardinal(va),
                                  et(est_cardinal(va), inf_egal_card(va, va)))


# ── §III.3.2 (après Prop 2) — BORNE SUPÉRIEURE d'une famille de cardinaux ──────
def test_majore_famille_cardinaux_forme():
    vb, vf, vI, viota = var("B"), var("f"), var("I"), var("iota")
    out = BS.majore_famille_cardinaux(vb, vf, vI)
    a_iota = E.valeur_famille(vf, viota)
    assert out == pourtout("iota", impl(appartient(viota, vI),
                                        inf_egal_card(a_iota, vb)))


def test_plus_petit_majorant_forme():
    vb, vf, vI, vc = var("B"), var("f"), var("I"), var("c")
    out = BS.plus_petit_majorant_cardinaux(vb, vf, vI)
    hyp = et(est_cardinal(vc), BS.majore_famille_cardinaux(vb, vf, vI))
    assert out == pourtout("c", impl(hyp, inf_egal_card(vb, vc)))


def test_est_borne_superieure_cardinaux_forme():
    vb, vf, vI = var("B"), var("f"), var("I")
    out = BS.est_borne_superieure_cardinaux(vb, vf, vI)
    assert out == et(et(est_cardinal(vb), BS.majore_famille_cardinaux(vb, vf, vI)),
                     BS.plus_petit_majorant_cardinaux(vb, vf, vI))


def test_borne_sup_majore_close():
    vb, vf, vI = var("B"), var("f"), var("I")
    thm = BS.borne_sup_majore("B", "f", "I")
    assert thm.est_clos
    # est_borne_superieure(b,f,I) ⇒ majore(b,f,I)  (projection NON vacuux)
    assert thm.conclusion == impl(BS.est_borne_superieure_cardinaux(vb, vf, vI),
                                  BS.majore_famille_cardinaux(vb, vf, vI))


# ── garde-fou theorie ─────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
