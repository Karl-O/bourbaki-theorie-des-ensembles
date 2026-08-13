"""Tests — De Morgan des familles (§II.4 Prop. 5) et identités de composition-valeur."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl, existe, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_demorgan import ensembles_familles_demorgan as M
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections import ensembles_composee_valeurs as CV


# ── (A) De Morgan des familles ───────────────────────────────────────────────
def test_de_morgan_inter_famille():
    """{(∃ι)(ι∈I)} ⊢ E∖(⋂_{ι∈I} X_ι) = ⋃_{ι∈I}(E∖X_ι)   (direction B, conditionnel I≠∅).

    ÉNONCÉ RENFORCÉ. Ce test assertait auparavant `not th.hypotheses`. Cette forme
    inconditionnelle était FAUSSE pour I=∅ : elle ne tenait que par l'ancien
    AXIOME_INTER_FAM, qui peuplait ⋂_{ι∈∅} X_ι de tout objet (théorie
    contradictoire). Depuis « ⋂ = sélection dans ⋃ » on a ⋂_{ι∈∅} X_ι = ∅, donc
    E∖(⋂_{ι∈∅}X_ι) = E ≠ ∅ = ⋃_{ι∈∅}(E∖X_ι). Le test suit l'énoncé, pas l'inverse."""
    th = M.de_morgan_inter_famille()
    target = egal(E.difference(var("E"), E.inter_famille(var("f"), var("I"))),
                  E.reunion_famille(E.complement_famille(var("E"), var("f")), var("I")))
    assert th.conclusion == target
    # hypothèse exacte : I non vide  (∃i)(i∈I) — celle de la Déf. 2 (E II.22)
    assert list(th.hypotheses) == [existe("i", appartient(var("i"), var("I")))]


def test_de_morgan_reunion_famille():
    """{(∃ι)(ι∈I)} ⊢ E∖(⋃_{ι∈I} X_ι) = ⋂_{ι∈I}(E∖X_ι)   (direction A, conditionnel I≠∅)."""
    th = M.de_morgan_reunion_famille()
    target = egal(E.difference(var("E"), E.reunion_famille(var("f"), var("I"))),
                  E.inter_famille(E.complement_famille(var("E"), var("f")), var("I")))
    assert th.conclusion == target
    # hypothèse exacte : I non vide  (∃i)(i∈I)
    assert list(th.hypotheses) == [existe("i", appartient(var("i"), var("I")))]


def test_axiome_compl_fam_clos():
    """L'axiome de la famille des complémentaires est clos et dans la théorie."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f
    assert not libres_f(E.AXIOME_COMPL_FAM)
    assert E.AXIOME_COMPL_FAM in E.theorie_ensembles().axiomes


# ── (B) identités de composition au niveau des valeurs ───────────────────────
def test_composition_valeur_t_simple():
    """⊢ (G∘F)(x) = G(F(x))   (version termes, point simple)."""
    th = CV.composition_valeur_t(var("G"), var("F"), var("x"))
    target = egal(E.valeur(E.composee(var("G"), var("F")), var("x")),
                  E.valeur(var("G"), E.valeur(var("F"), var("x"))))
    assert th.conclusion == target


def test_composition_valeur_t_compose():
    """⊢ ((H∘G)∘F)(x) = (H∘G)(F(x))   (facteur composé H∘G, point simple)."""
    HG = E.composee(var("H"), var("G"))
    th = CV.composition_valeur_t(HG, var("F"), var("x"))
    target = egal(E.valeur(E.composee(HG, var("F")), var("x")),
                  E.valeur(HG, E.valeur(var("F"), var("x"))))
    assert th.conclusion == target


def test_composee_associee_droite_valeur():
    """⊢ (H∘(G∘F))(x) = H(G(F(x)))   (demi-associativité, à droite)."""
    th = CV.composee_associee_droite_valeur()
    GF = E.composee(var("G"), var("F"))
    target = egal(E.valeur(E.composee(var("H"), GF), var("x")),
                  E.valeur(var("H"), E.valeur(var("G"), E.valeur(var("F"), var("x")))))
    assert th.conclusion == target


def test_retraction_compose_valeur():
    """{est_retraction(R,F,A), …} ⊢ (x∈A) ⇒ (R∘F)(x) = x   (r∘f = Id_A sur les valeurs)."""
    th = CV.retraction_compose_valeur()
    comp = E.composee(var("R"), var("F"))
    target = impl(appartient(var("x"), var("A")),
                  egal(E.valeur(comp, var("x")), var("x")))
    assert th.conclusion == target
    # est_retraction figure bien parmi les hypothèses
    assert E.est_retraction(var("R"), var("F"), var("A")) in th.hypotheses
