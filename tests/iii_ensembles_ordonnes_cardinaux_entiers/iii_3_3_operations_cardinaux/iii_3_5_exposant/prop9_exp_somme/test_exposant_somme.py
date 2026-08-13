"""Tests §III.3.5 — a^(b+c) = a^b · a^c  (Proposition 9, E.III.3.5).

PALIERS SÛRS (caractérisation membership + formes), DÉRIVÉS des axiomes de
DÉFINITION (rien postulé) ; la bijection restriction Φ (cœur) est REPORTÉE.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient, existe, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop9_exp_somme import ensembles_exposant_somme as S


# ── PALIER 0 : DÉFINITIONS / FORMES ──────────────────────────────────────────
def test_exposant_somme_cardinal_forme():
    """a^(b+c) := Card(𝓕(B⊔C; A))  (membre de gauche, forme exacte)."""
    vA, vB, vC = var("A"), var("B"), var("C")
    t = S.exposant_somme_cardinal("A", "B", "C")
    assert t == exposant_cardinal_binaire(vA, somme_disjointe(vB, vC))
    assert t == cardinal(E.applications(somme_disjointe(vB, vC), vA))


def test_produit_exposants_cardinal_forme():
    """a^b · a^c := Card(𝓕(B;A) × 𝓕(C;A))  (membre de droite, forme exacte)."""
    vA, vB, vC = var("A"), var("B"), var("C")
    t = S.produit_exposants_cardinal("A", "B", "C")
    assert t == cardinal(E.produit(E.applications(vB, vA), E.applications(vC, vA)))


# ── PALIER 1 : CARACTÉRISATION MEMBERSHIP ────────────────────────────────────
def test_membre_exposant_somme():
    """⊢ G∈A^(B⊔C) ⇔ (G⊂(B⊔C)×A et G fonct et dom G=B⊔C), CLOS."""
    vA, vB, vC, vG = var("A"), var("B"), var("C"), var("G")
    BC = somme_disjointe(vB, vC)
    t = S.membre_exposant_somme("A", "B", "C", "G")
    corps = et(et(inclus(vG, E.produit(BC, vA)), E.est_fonctionnel(vG)),
               egal(E.dom(vG), BC))
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    assert t.conclusion == equiv(appartient(vG, E.exposant(BC, vA)), corps)
    assert t.est_clos


def test_membre_applications_somme():
    """⊢ t∈𝓕(B⊔C;A) ⇔ (∃G)(t=((G,B⊔C),A) et G∈A^(B⊔C)), CLOS."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    vA, vB, vC, vt, vG = var("A"), var("B"), var("C"), var("t"), var("G")
    BC = somme_disjointe(vB, vC)
    t = S.membre_applications_somme("A", "B", "C", "t")
    triple = E.couple(E.couple(vG, BC), vA)
    corps = existe("G", et(egal(vt, triple), appartient(vG, E.exposant(BC, vA))))
    assert t.conclusion == equiv(appartient(vt, E.applications(BC, vA)), corps)
    assert t.est_clos


def test_membre_applications_b():
    """⊢ t∈𝓕(B;A) ⇔ (∃G)(t=((G,B),A) et G∈A^B), CLOS."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    vA, vB, vt, vG = var("A"), var("B"), var("t"), var("G")
    t = S.membre_applications_b("A", "B", "t")
    triple = E.couple(E.couple(vG, vB), vA)
    corps = existe("G", et(egal(vt, triple), appartient(vG, E.exposant(vB, vA))))
    assert t.conclusion == equiv(appartient(vt, E.applications(vB, vA)), corps)
    assert t.est_clos


def test_membre_produit_applications():
    """⊢ t∈𝓕(B;A)×𝓕(C;A) ⇔ (∃p)(∃q)(t=(p,q) et p∈𝓕(B;A) et q∈𝓕(C;A)), CLOS."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import equiv
    vA, vB, vC, vt, vp, vq = (var("A"), var("B"), var("C"),
                              var("t"), var("p"), var("q"))
    FB = E.applications(vB, vA)
    FC = E.applications(vC, vA)
    t = S.membre_produit_applications("A", "B", "C", "t")
    corps = existe("p", existe("q",
        et(et(egal(vt, E.couple(vp, vq)), appartient(vp, FB)), appartient(vq, FC))))
    assert t.conclusion == equiv(appartient(vt, E.produit(FB, FC)), corps)
    assert t.est_clos


# ── PALIER 2 : DÉCOMPOSITION STRUCTURELLE (sens facile) ──────────────────────
def test_applications_somme_donne_graphe():
    """⊢ t∈𝓕(B⊔C;A) ⇒ (∃G)(t=((G,B⊔C),A) et (G⊂(B⊔C)×A et G fonct et domG=B⊔C)), CLOS."""
    vA, vB, vC, vt, vG = (var("A"), var("B"), var("C"), var("t"), var("G"))
    BC = somme_disjointe(vB, vC)
    t = S.applications_somme_donne_graphe("A", "B", "C", "t")
    triple = E.couple(E.couple(vG, BC), vA)
    corps_exp = et(et(inclus(vG, E.produit(BC, vA)), E.est_fonctionnel(vG)),
                   egal(E.dom(vG), BC))
    cible = existe("G", et(egal(vt, triple), corps_exp))
    assert t.conclusion == impl(appartient(vt, E.applications(BC, vA)), cible)
    assert t.est_clos
