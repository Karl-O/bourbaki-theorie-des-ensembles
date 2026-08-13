"""Tests de ensembles_ordre_vocab.py — vocabulaire d'ordre manquant §III.1-2.

Vérifie que CHAQUE notion de mes sections (intervalles manquants, isomorphisme
d'ensembles ordonnés, ordre produit, adjonction d'un plus grand élément, ordre
lexicographique) est INTRODUITE par un def FIDÈLE, que les termes/formules se
construisent et coïncident avec l'énoncé Bourbaki, et que les lemmes directs
sont CLOS (ou gardent exactement les hypothèses attendues).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, app, egal, et, ou, impl, non, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V


# Relation ≤ de test : a≤b := (a,b)∈G  (convention graphe, comme le reste du projet)
G, Gp = var("G"), var("Gp")
def R(a, b):  return appartient(E.couple(a, b), G)
def Rp(a, b): return appartient(E.couple(a, b), Gp)

Es, Ep, I = var("E"), var("Ep"), var("I")
a, b, f = var("a"), var("b"), var("f")
x_pt, y_pt = var("xx"), var("yy")


# ════════════════════════════════════════════════════════════════════════════
#  INTERVALLES manquants (E.III.1.13) : termes + axiomes de membership
# ════════════════════════════════════════════════════════════════════════════
def test_intervalle_semi_ouvert_droite_terme():
    t = V.intervalle_semi_ouvert_droite(R, Es, a, b)
    assert t == app("interv_fo", Es, a, b)


def test_intervalle_semi_ouvert_gauche_terme():
    t = V.intervalle_semi_ouvert_gauche(R, Es, a, b)
    assert t == app("interv_of", Es, a, b)


def test_intervalle_illimite_gauche_ouvert_terme():
    t = V.intervalle_illimite_gauche_ouvert(R, Es, a)
    assert t == app("interv_igo", Es, a)


def test_intervalle_illimite_droite_ouvert_terme():
    t = V.intervalle_illimite_droite_ouvert(R, Es, a)
    assert t == app("interv_ido", Es, a)


def test_intervalle_total_est_E():
    # ]←,→[ = E
    assert V.intervalle_total(R, Es) == Es


def test_axiome_intervalle_semi_ouvert_droite_forme():
    ax = V.axiome_intervalle_semi_ouvert_droite(R)
    vE, va, vb, vx = var("E"), var("a"), var("b"), var("x")
    lt = lambda u, v: et(R(u, v), non(egal(u, v)))
    cible = pourtout("E", pourtout("a", pourtout("b", pourtout("x",
        equiv(appartient(vx, V.intervalle_semi_ouvert_droite(R, vE, va, vb)),
              et(et(appartient(vx, vE), R(va, vx)), lt(vx, vb)))))))
    assert ax == cible


def test_axiome_intervalle_illimite_droite_ouvert_forme():
    ax = V.axiome_intervalle_illimite_droite_ouvert(R)
    vE, va, vx = var("E"), var("a"), var("x")
    lt = lambda u, v: et(R(u, v), non(egal(u, v)))
    cible = pourtout("E", pourtout("a", pourtout("x",
        equiv(appartient(vx, V.intervalle_illimite_droite_ouvert(R, vE, va)),
              et(appartient(vx, vE), lt(va, vx))))))
    assert ax == cible


def test_theorie_intervalles_quatre_axiomes():
    th = V.theorie_intervalles(R)
    # 4 axiomes de membership, et theorie_ensembles INCHANGÉE (22 axiomes)
    assert len(th.axiomes) == 4
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  ISOMORPHISME d'ensembles ordonnés (E.III.1.3)
# ════════════════════════════════════════════════════════════════════════════
def test_compatible_ordre_forme():
    g = V.compatible_ordre(f, Es, R, Rp)
    vx, vy = var("x"), var("y")
    fx, fy = E.valeur(f, vx, b='j'), E.valeur(f, vy, b='j')
    cible = pourtout("x", pourtout("y",
        impl(et(appartient(vx, Es), appartient(vy, Es)),
             equiv(R(vx, vy), Rp(fx, fy)))))
    assert g == cible


def test_est_isomorphisme_ordre_forme():
    g = V.est_isomorphisme_ordre(f, Es, Ep, R, Rp)
    cible = et(E.est_bijective(f, Es, Ep), V.compatible_ordre(f, Es, R, Rp))
    assert g == cible


def test_sont_isomorphes_ordre_forme():
    g = V.sont_isomorphes_ordre(Es, Ep, R, Rp)
    cible = existe("f", V.est_isomorphisme_ordre(var("f"), Es, Ep, R, Rp))
    assert g == cible


def test_isomorphisme_ordre_est_bijection():
    t = V.isomorphisme_ordre_est_bijection("f", "E", "Ep", R, Rp)
    assert t.conclusion == E.est_bijective(f, Es, Ep)
    assert t.hypotheses == {V.est_isomorphisme_ordre(f, Es, Ep, R, Rp)}


def test_isomorphisme_ordre_compatible():
    t = V.isomorphisme_ordre_compatible("f", "E", "Ep", R, Rp)
    assert t.conclusion == V.compatible_ordre(f, Es, R, Rp)
    assert t.hypotheses == {V.est_isomorphisme_ordre(f, Es, Ep, R, Rp)}


# ════════════════════════════════════════════════════════════════════════════
#  ORDRE PRODUIT (E.III.1.4)
# ════════════════════════════════════════════════════════════════════════════
def test_ordre_produit_forme():
    Rfam = lambda ind: (lambda u, v: appartient(E.couple(u, v), E.valeur(var("Gfam"), ind)))
    g = V.ordre_produit(Rfam, I, x_pt, y_pt)
    vi = var("i")
    prx = E.projection_indice(x_pt, vi)
    pry = E.projection_indice(y_pt, vi)
    cible = pourtout("i", impl(appartient(vi, I), Rfam(vi)(prx, pry)))
    assert g == cible


def test_relation_ordre_produit_appel():
    Rfam = lambda ind: (lambda u, v: appartient(E.couple(u, v), E.valeur(var("Gfam"), ind)))
    Rprod = V.relation_ordre_produit(Rfam, I)
    # Rprod est une RELATION (fonction) ; appliquée elle redonne ordre_produit
    assert Rprod(x_pt, y_pt) == V.ordre_produit(Rfam, I, x_pt, y_pt)


# ════════════════════════════════════════════════════════════════════════════
#  ADJONCTION d'un plus grand élément (E.III.1.8, Proposition 3)
# ════════════════════════════════════════════════════════════════════════════
def test_ensemble_adjoint_forme():
    t = V.ensemble_adjoint(Es, a)
    assert t == E.reunion(Es, E.singleton(a))


def test_relation_adjoint_forme():
    Radj = V.relation_adjoint(R, Es, a)
    Ep_set = V.ensemble_adjoint(Es, a)
    # x≤'y := (x≤y) ou (y=a et x∈E')
    assert Radj(var("u"), var("v")) == ou(
        R(var("u"), var("v")),
        et(egal(var("v"), a), appartient(var("u"), Ep_set)))


def test_est_adjonction_plus_grand_forme():
    Radj = V.relation_adjoint(R, Es, a)
    g = V.est_adjonction_plus_grand(R, Radj, Es, a)
    Ep_set = V.ensemble_adjoint(Es, a)
    vx, vy = var("x"), var("y")
    induit = pourtout("x", pourtout("y",
        impl(et(appartient(vx, Es), appartient(vy, Es)),
             equiv(R(vx, vy), Radj(vx, vy)))))
    cible = et(et(E.est_relation_ordre_dans(Radj, Ep_set), induit),
               E.est_plus_grand_element(Radj, Ep_set, a))
    assert g == cible


def test_adjoint_a_est_plus_grand_lemme():
    t = V.adjoint_a_est_plus_grand(R, "E", "a")
    Radj = V.relation_adjoint(R, Es, a)
    Ep_set = V.ensemble_adjoint(Es, a)
    assert t.conclusion == E.est_plus_grand_element(Radj, Ep_set, a)
    assert t.hypotheses == {V.est_adjonction_plus_grand(R, Radj, Es, a)}


# ════════════════════════════════════════════════════════════════════════════
#  ORDRE LEXICOGRAPHIQUE (E.III.2)
# ════════════════════════════════════════════════════════════════════════════
def test_ordre_lexicographique_forme():
    Rfam = lambda ind: (lambda u, v: appartient(E.couple(u, v), E.valeur(var("Gfam"), ind)))
    RI = lambda u, v: appartient(E.couple(u, v), var("GI"))   # bon ordre des INDICES I
    g = V.ordre_lexicographique(Rfam, I, RI, x_pt, y_pt)
    vi0, vj = var("i0"), var("j")
    lt_comp = lambda u, v: et(Rfam(vi0)(u, v), non(egal(u, v)))   # <_{ι₀} sur le facteur
    lt_I = lambda u, v: et(RI(u, v), non(egal(u, v)))             # <_I sur les indices
    prx0 = E.projection_indice(x_pt, vi0)
    pry0 = E.projection_indice(y_pt, vi0)
    avant = pourtout("j", impl(et(appartient(vj, I), lt_I(vj, vi0)),
                               egal(E.projection_indice(x_pt, vj),
                                    E.projection_indice(y_pt, vj))))
    temoin = existe("i0", et(et(appartient(vi0, I), lt_comp(prx0, pry0)), avant))
    cible = ou(egal(x_pt, y_pt), temoin)
    assert g == cible


def test_relation_ordre_lexicographique_appel():
    Rfam = lambda ind: (lambda u, v: appartient(E.couple(u, v), E.valeur(var("Gfam"), ind)))
    RI = lambda u, v: appartient(E.couple(u, v), var("GI"))
    Rlex = V.relation_ordre_lexicographique(Rfam, I, RI)
    assert Rlex(x_pt, y_pt) == V.ordre_lexicographique(Rfam, I, RI, x_pt, y_pt)


# ════════════════════════════════════════════════════════════════════════════
#  LEMMES DIRECTS CLOS (.est_clos) — preuves certifiées par le noyau
# ════════════════════════════════════════════════════════════════════════════
def test_intervalle_total_est_E_clos():
    t = V.intervalle_total_est_E(R, "E")
    assert t.est_clos
    assert t.conclusion == egal(Es, Es)


def test_lexicographique_reflexive_clos():
    t = V.lexicographique_reflexive(I="I", a="a")
    assert t.est_clos
    # conclusion = ordre_lexicographique(...)(a,a) = ou(a=a, témoin)
    assert t.conclusion.tag == "ou"
    assert t.conclusion.sous[0] == egal(a, a)
