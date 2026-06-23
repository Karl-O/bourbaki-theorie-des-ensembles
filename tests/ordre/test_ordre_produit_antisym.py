"""Tests §III.1.4 — L'ordre PRODUIT est une relation d'ORDRE (antisymétrie via
extensionnalite_produit).  Vérifie que ordre_produit_est_ordre est CLOS (0 hyp),
que la clause d'antisymétrie est EXACTEMENT antisymetrie_sur_produit (relativisée à
∏, honnête, non vacuous), et que les clauses transitivité/réflexivité-implicite
reproduisent celles du préordre.  theorie_ensembles() reste à 22.
"""
from bourbaki.logique.formule import var, egal, et, impl, appartient, pourtout
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_produit_antisym as A


def _Rfam():
    return lambda i: (lambda a, b: appartient(E.couple(a, b), E.app("Rg", i)))


def _conj_parts(f):
    """f = non(ou(non a, non b)) = (a et b) ; renvoie (a, b)."""
    inner = f.sous[0]
    return inner.sous[0].sous[0], inner.sous[1].sous[0]


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_ordre_produit_est_ordre_close():
    th = A.ordre_produit_est_ordre(_Rfam(), "fam", "I")
    assert th.est_clos
    assert len(th.hypotheses) == 0


def test_antisymetrie_clause_exacte():
    Rfam = _Rfam()
    th = A.ordre_produit_est_ordre(Rfam, "fam", "I")
    concl = th.conclusion.sous[1]                 # impl(ante, concl) = ou(non ante, concl)
    outer_l, _refl = _conj_parts(concl)
    _trans, antisym = _conj_parts(outer_l)
    P = V.relation_ordre_produit(Rfam, "I", "i")
    assert antisym == A.antisymetrie_sur_produit(P, "fam", "I")


def test_antisymetrie_non_vacuous():
    # x=y ne figure PAS dans l'antécédent de la clause d'antisymétrie
    Rfam = _Rfam()
    P = V.relation_ordre_produit(Rfam, "I", "i")
    clause = A.antisymetrie_sur_produit(P, "fam", "I")
    # clause = (∀xp)(∀yp)(ante ⇒ xp=yp) ; l'antécédent ne contient pas xp=yp
    vx, vy = var("xp"), var("yp")
    prod = E.produit_famille(var("fam"), var("I"))
    ante = et(et(et(et(et(
        appartient(vx, prod), appartient(vy, prod)),
        E.est_un_graphe(vx)), E.est_un_graphe(vy)),
        P(vx, vy)), P(vy, vx))
    expected = pourtout("xp", pourtout("yp", impl(ante, egal(vx, vy))))
    assert clause == expected


def test_antecedent_honnete():
    # l'antécédent global = per-factor (transitivité, antisymétrie, réflexivité-implicite)
    Rfam = _Rfam()
    th = A.ordre_produit_est_ordre(Rfam, "fam", "I")
    ante = th.conclusion.sous[0].sous[0]          # ou(non ante, concl) ; non ante = sous[0]
    vi = var("i")
    R_i = Rfam(vi)
    htr = pourtout("i", impl(appartient(vi, var("I")), E.ordre_transitif(R_i, "a", "b", "c")))
    hanti = pourtout("i", impl(appartient(vi, var("I")), E.ordre_antisymetrique(R_i, "a", "b")))
    href = pourtout("i", impl(appartient(vi, var("I")), E.ordre_reflexif_implicite(R_i, "a", "b")))
    assert ante == et(et(htr, hanti), href)
