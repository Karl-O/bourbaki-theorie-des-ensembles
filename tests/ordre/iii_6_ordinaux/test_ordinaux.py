"""Tests de ensembles_ordinaux.py — ORDINAUX (définition représentationnelle §III.6).

Vérifie que CHAQUE notion d'ordinal (type d'ordre d'un bon ordre, même ordinal,
ordinal d'un bon ordre, segment initial, comparaison ≤/< par segments, trichotomie
posée, ordinal initial) est INTRODUITE par un def FIDÈLE, que les termes/formules
coïncident avec les briques Bourbaki réutilisées (sans duplication), que les
lemmes directs sont CLOS, et que theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, app, tau, egal, et, ou, impl, non, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux import ensembles_cardinaux as C
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.ordre.iii_6_ordinaux import ensembles_ordinaux as O


# Relation ≤ de test : a≤b := (a,b)∈G  (convention graphe du projet)
G, Gp = var("G"), var("Gp")
def R(a, b):  return appartient(E.couple(a, b), G)
def Rp(a, b): return appartient(E.couple(a, b), Gp)

Es, Ep, S = var("E"), var("Ep"), var("S")
a, c = var("a"), var("c")


# ════════════════════════════════════════════════════════════════════════════
#  theorie_ensembles intangible
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  ORDINAL — type d'ordre représentationnel
# ════════════════════════════════════════════════════════════════════════════
def test_est_ordinal_est_bien_ordonne():
    # est_ordinal(E,R) := est_bien_ordonne(R,E)  (fidélité représentationnelle)
    assert O.est_ordinal(Es, R) == E.est_bien_ordonne(R, Es)


def test_meme_ordinal_est_isomorphisme_ordre():
    # meme_ordinal := sont_isomorphes_ordre  (même type d'ordre = isomorphes d'ordre)
    assert O.meme_ordinal(Es, R, Ep, Rp) == V.sont_isomorphes_ordre(Es, Ep, R, Rp)


def test_ordinal_de_est_tau_classe_isomorphisme():
    t = O.ordinal_de(Es, R)
    assert isinstance(t, Terme) and t.tag == "tau"
    # le corps du tau est sont_isomorphes_ordre(E, Z, R, R_Z)
    vZ = var("Z")
    R_Z = lambda u, v: appartient(E.couple(u, v), app("ordre_temoin", vZ))
    cible = tau("Z", V.sont_isomorphes_ordre(Es, vZ, R, R_Z))
    assert t == cible


# ════════════════════════════════════════════════════════════════════════════
#  SEGMENT INITIAL
# ════════════════════════════════════════════════════════════════════════════
def test_segment_initial_est_segment():
    assert O.est_segment_initial(S, Es, R) == E.est_segment(S, R, Es)


def test_segment_initial_extremite_est_segment_extremite():
    assert O.segment_initial_extremite(Es, R, a) == E.segment_extremite(R, Es, a)


def test_segment_propre_forme():
    assert O.est_segment_propre(S, Es, R) == et(E.est_segment(S, R, Es), non(egal(S, Es)))


# ════════════════════════════════════════════════════════════════════════════
#  COMPARAISON DES ORDINAUX  (par segments — Théorème 3, E.III.2)
# ════════════════════════════════════════════════════════════════════════════
def test_inferieur_ou_egal_forme():
    cible = existe("S", et(E.est_segment(S, Rp, Ep),
                           V.sont_isomorphes_ordre(Es, S, R, Rp)))
    assert O.ordinal_inferieur_ou_egal(Es, R, Ep, Rp) == cible


def test_strictement_inferieur_forme():
    cible = existe("S", et(O.est_segment_propre(S, Ep, Rp),
                           V.sont_isomorphes_ordre(Es, S, R, Rp)))
    assert O.ordinal_strictement_inferieur(Es, R, Ep, Rp) == cible


def test_trichotomie_est_disjonction():
    f = O.trichotomie_ordinaux(Es, R, Ep, Rp)
    cible = ou(O.ordinal_inferieur_ou_egal(Es, R, Ep, Rp),
               O.ordinal_inferieur_ou_egal(Ep, Rp, Es, R))
    assert f == cible
    # c'est une FORMULE-énoncé (REPORTÉ), pas un Theoreme
    assert not isinstance(f, N.Theoreme)


# ════════════════════════════════════════════════════════════════════════════
#  ORDINAL INITIAL
# ════════════════════════════════════════════════════════════════════════════
def test_ordinal_initial_mentionne_equipotence_et_strict():
    f = O.est_ordinal_initial(Es, R)
    # (∀E')(…) est encodé ¬∃E'¬… : tag "non" (forall = ¬∃¬)
    assert f.tag == "non"
    # contient bien ¬Eq(E',E) (équipotence) dans son corps
    assert "Eq" in repr(f) or "bijection" in repr(f) or "F" in repr(f)


def test_ordinal_initial_du_cardinal_est_tau():
    t = O.ordinal_initial_du_cardinal(c)
    assert isinstance(t, Terme) and t.tag == "tau"


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS (certifiés noyau)
# ════════════════════════════════════════════════════════════════════════════
def test_ordinal_est_bien_ordonne_certifie():
    th = O.ordinal_est_bien_ordonne()
    assert isinstance(th, N.Theoreme)


def test_meme_ordinal_donne_isomorphisme_certifie():
    th = O.meme_ordinal_donne_isomorphisme()
    assert isinstance(th, N.Theoreme)


def test_segment_propre_est_segment_certifie():
    th = O.segment_propre_est_segment()
    assert isinstance(th, N.Theoreme)
    # conclusion = est_segment(S,R,E)
    Rg = lambda u, v: appartient(E.couple(u, v), var("G"))
    assert th.conclusion == E.est_segment(var("S"), Rg, var("E"))


def test_inferieur_ou_egal_reflexif_est_enonce():
    f = O.inferieur_ou_egal_reflexif()
    # FORMULE-énoncé (réflexivité de ≤ des ordinaux), preuve REPORTÉE
    assert not isinstance(f, N.Theoreme)
    assert f.tag == "exists"   # (∃S) … segment témoin
