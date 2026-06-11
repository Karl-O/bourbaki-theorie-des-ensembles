"""Tests §III.2 — Proposition 1 : segment PROPRE d'un bon ordre = ]←, min(E∖D)[.

Certifie que `prop1_segment_propre` établit RÉELLEMENT, sous les SEULES hypothèses
{ est_bien_ordonne(R,E), est_segment(D,R,E), D≠E } :

    (∃x)( est_plus_petit_element(R, E∖D, x)  et  D = seg(R,E,x) ),

que la forme close décharge les 3 hypothèses, et que rien n'est tautologie/postulé.
theorie=22.
"""
from bourbaki.logique.formule import non, egal, var, impl, et
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_trichotomie_prop1 as P


def _R_de(R="R"):
    from bourbaki.logique.formule import appartient
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


def test_prop1_conditionnelle():
    """{ bo, est_segment, D≠E } ⊢ (∃x)(min(E∖D)=x et D=seg(R,E,x))."""
    thm = P.prop1_segment_propre()
    assert not thm.est_clos
    # conclusion = la cible littérale
    assert thm.conclusion == P.cible_prop1()
    # non dégénéré : la conclusion n'est PAS une hypothèse
    assert thm.conclusion not in thm.hypotheses


def test_prop1_trois_hypotheses_exactes():
    """Exactement les 3 hypothèses canoniques, rien d'autre postulé."""
    thm = P.prop1_segment_propre()
    Rf = _R_de("R")
    vE, vD = var("E"), var("D")
    bo = E.est_bien_ordonne(Rf, vE)
    seg_h = E.est_segment(vD, Rf, vE)
    neq = non(egal(vD, vE))
    hyps = set(thm.hypotheses)
    assert bo in hyps, "bon ordre manquant"
    assert seg_h in hyps, "est_segment manquant"
    assert neq in hyps, "D≠E manquant"
    assert hyps == {bo, seg_h, neq}, f"hypotheses parasites: {hyps - {bo, seg_h, neq}}"


def test_prop1_close():
    """Forme CLOSE (0 hypothèse) : les 3 hypothèses sont déchargées."""
    clos = P.prop1_segment_propre_clos()
    assert clos.est_clos
    assert not clos.hypotheses
    # 3 implications imbriquées (neq ⇒ (seg ⇒ (bo ⇒ cible))) ; cible = conséquent le + interne
    c = clos.conclusion
    for _ in range(3):
        assert c.tag == "ou"   # impl encodé en ¬A ∨ B
        c = c.sous[1]
    assert c == P.cible_prop1()


def test_prop1_non_vacueux():
    """La cible n'est aucune des 3 hypothèses (non tautologique)."""
    thm = P.prop1_segment_propre()
    cible = P.cible_prop1()
    for h in thm.hypotheses:
        assert cible != h


def test_prop1_parametrable():
    """Fonctionne sur d'autres noms (R',F,S)."""
    thm = P.prop1_segment_propre("Rp", "F", "S")
    assert thm.conclusion == P.cible_prop1("Rp", "F", "S")


def test_theorie_intacte():
    """theorie_ensembles() = 22 : aucun axiome ajouté."""
    assert len(E.theorie_ensembles().axiomes) == 22
