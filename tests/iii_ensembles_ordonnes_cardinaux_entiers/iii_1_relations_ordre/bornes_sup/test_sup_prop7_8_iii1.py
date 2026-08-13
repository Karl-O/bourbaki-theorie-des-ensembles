"""Tests — PROPOSITION 7 (sup par recouvrement, cœur binaire) §III.1 (E.III.11)."""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import borne_superieure, majorant
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.bornes_sup.ensembles_sup_prop7_8_iii1 import (
    borne_sup_reunion_iff,
    sup_reunion_est_borne_sup_majorants_communs,
)


def test_theorie_intangible():
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
    assert len(theorie_ensembles().axiomes) == 22


def test_borne_sup_reunion_iff_clos():
    th = borne_sup_reunion_iff()
    assert th.est_clos, f"hyps résiduelles: {th.hypotheses}"


def test_borne_sup_reunion_iff_conclusion():
    """La conclusion est bien l'équivalence
    borne_superieure(A∪B,m) ⟺ (plus petit majorant commun)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv, et, impl, pourtout, appartient as _app
    th = borne_sup_reunion_iff()
    G, A, B, Es, m = var("G"), var("A"), var("B"), var("E"), var("m")
    AuB = E.reunion(A, B)
    gauche = borne_superieure(G, AuB, m, Es, "x", "y")
    # côté droit : (maj(A,m) et maj(B,m)) et (∀y)((maj(A,y) et maj(B,y))⇒(m,y)∈G)
    vy = var("y")
    maj_comm_m = et(majorant(G, A, m, Es, "x"), majorant(G, B, m, Es, "x"))
    pp = pourtout("y", impl(
        et(majorant(G, A, vy, Es, "x"), majorant(G, B, vy, Es, "x")),
        _app(E.couple(m, vy), G)))
    droite = et(maj_comm_m, pp)
    attendu = equiv(gauche, droite)
    assert th.conclusion == attendu, f"\nattendu={attendu}\nobtenu ={th.conclusion}"


def test_alias_clos():
    th = sup_reunion_est_borne_sup_majorants_communs()
    assert th.est_clos
    assert th.conclusion == borne_sup_reunion_iff().conclusion
