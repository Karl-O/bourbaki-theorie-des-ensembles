"""Test §III.1.3 / §III.2 — la COMPOSÉE de deux isomorphismes d'ordre est un iso.

KEYSTONE de la trichotomie des ordinaux (la « glue » composition au niveau graphe).

  composee_isomorphisme_ordre :
    { iso(g,T,U,R',R''), iso(f,S,T,R,R'), f fonctionnel, dom f=S, g fonctionnel, dom g=T }
      ⊢ est_isomorphisme_ordre(g∘f, S, U, R, R'')
  composee_isomorphisme_ordre_implication :
    ⊢ (conjonction des 6 prémisses) ⇒ est_isomorphisme_ordre(g∘f, S, U, R, R'')   [CLOS]

Vérifie : conclusion == cible (anti-tautologie/anti-affaiblissement), hypothèses ==
EXACTEMENT les 6 prémisses structurelles, forme implicative CLOSE, theorie = 22 axiomes.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import (est_isomorphisme_ordre,
                                                  compatible_ordre)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.iso_ordre.ensembles_iso_ordre_composee import (
    composee_isomorphisme_ordre, composee_isomorphisme_ordre_implication,
    valeur_dans_but_surjectif)


def _relations():
    R = lambda a, b: appartient(E.couple(a, b), var("Rg"))
    Rp = lambda a, b: appartient(E.couple(a, b), var("Rpg"))
    Rpp = lambda a, b: appartient(E.couple(a, b), var("Rppg"))
    return R, Rp, Rpp


def test_valeur_dans_but_surjectif():
    """{dom f=S, image(f,S)=T, pt∈S} ⊢ f(pt)∈T — pour pt=x ET pt=w (slots frais)."""
    vf, vS, vT = var("f"), var("S"), var("T")
    for nom in ("x", "w"):
        vpt = var(nom)
        t = valeur_dans_but_surjectif(vf, vS, vT, vpt)
        assert t.conclusion == appartient(E.valeur(vf, vpt), vT)
        assert t.hypotheses == {egal(E.dom(vf), vS),
                                egal(E.image(vf, vS), vT),
                                appartient(vpt, vS)}


def test_composee_isomorphisme_ordre_conclusion_et_hyps():
    """Conclusion == est_isomorphisme_ordre(g∘f,S,U,R,R'') ; hyps == les 6 prémisses."""
    R, Rp, Rpp = _relations()
    vf, vg, vS, vT, vU = var("f"), var("g"), var("S"), var("T"), var("U")
    t = composee_isomorphisme_ordre()
    comp = E.composee(vg, vf)

    # CONCLUSION exacte (cible construite indépendamment, binders x, x2)
    cible = est_isomorphisme_ordre(comp, vS, vU, R, Rpp, "x", "x2")
    assert t.conclusion == cible

    # la conclusion EST réellement « bijective ET compatible_ordre » (pas une tautologie)
    co_cible = compatible_ordre(comp, vS, R, Rpp, "x", "x2")
    assert t.conclusion == et(E.est_bijective(comp, vS, vU), co_cible)

    # HYPOTHÈSES == EXACTEMENT les 6 prémisses structurelles
    attendu = {
        est_isomorphisme_ordre(vg, vT, vU, Rp, Rpp, "x", "x2"),
        est_isomorphisme_ordre(vf, vS, vT, R, Rp, "x", "x2"),
        E.est_fonctionnel(vf),
        egal(E.dom(vf), vS),
        E.est_fonctionnel(vg),
        egal(E.dom(vg), vT),
    }
    assert t.hypotheses == attendu
    assert len(t.hypotheses) == 6

    # anti-tautologie : la conclusion n'est aucune des hypothèses
    assert t.conclusion not in t.hypotheses


def test_composee_isomorphisme_ordre_implication_close():
    """Forme implicative : THÉORÈME CLOS, consequent == iso de la composée."""
    R, Rp, Rpp = _relations()
    vf, vg, vS, vT, vU = var("f"), var("g"), var("S"), var("T"), var("U")
    t = composee_isomorphisme_ordre_implication()
    assert t.est_clos
    # A⇒B encodé ou(non A, B) : le conséquent B doit être l'iso de la composée
    consequent = t.conclusion.sous[1]
    comp = E.composee(vg, vf)
    assert consequent == est_isomorphisme_ordre(comp, vS, vU, R, Rpp, "x", "x2")


def test_theorie_inchangee_22():
    """theorie_ensembles reste à 22 axiomes (aucun axiome postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22
