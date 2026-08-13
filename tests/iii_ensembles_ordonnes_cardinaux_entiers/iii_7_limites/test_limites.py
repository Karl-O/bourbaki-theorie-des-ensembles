"""Tests §III.7 — Limites projectives et inductives (théorèmes DIRECTS).

Chaque test vérifie que la conclusion certifiée par le noyau est EXACTEMENT la
cible attendue (et le statut des hypothèses résiduelles), et non une devinette.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient, et, impl, pourtout, equiv
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import ensembles_limites as L


def _leq():
    return lambda u, v: appartient(E.couple(u, v), var("Gleq"))


def _fab(a, b):  # f_{ab} projectif
    return L.appl_proj(var("f"), var(a), var(b))


def _val(t, x="x"):
    return E.valeur(t, var(x))


# ── (LP_I) cocycle au niveau des valeurs : f_{αγ}(x)=f_{αβ}(f_{βγ}(x)) ────────
def test_cocycle_valeur_projectif():
    th = L.cocycle_valeur_projectif("f", _leq(), "I")
    fag, fab, fbg = _fab("a", "g"), _fab("a", "b"), _fab("b", "g")
    attendu = egal(_val(fag), E.valeur(fab, _val(fbg)))
    assert th.conclusion == attendu
    # LP_I figure bien parmi les hypothèses résiduelles
    assert L.cocycle_projectif(var("f"), _leq(), var("I")) in th.hypotheses


def test_identite_valeur_projectif():
    th = L.identite_valeur_projectif("f", _leq(), "I")
    attendu = egal(_val(_fab("a", "a")), var("x"))
    assert th.conclusion == attendu
    assert L.identite_projectif(var("f"), _leq(), var("I")) in th.hypotheses
    assert appartient(var("a"), var("I")) in th.hypotheses


# ── duals inductifs (LI_I, LI_II) ────────────────────────────────────────────
def test_cocycle_valeur_inductif():
    th = L.cocycle_valeur_inductif("f", _leq(), "I")
    fga = L.appl_ind(var("f"), var("g"), var("a"))
    fgb = L.appl_ind(var("f"), var("g"), var("b"))
    fba = L.appl_ind(var("f"), var("b"), var("a"))
    attendu = egal(E.valeur(fga, var("x")), E.valeur(fgb, E.valeur(fba, var("x"))))
    assert th.conclusion == attendu


def test_identite_valeur_inductif():
    th = L.identite_valeur_inductif("f", _leq(), "I")
    faa = L.appl_ind(var("f"), var("a"), var("a"))
    assert th.conclusion == egal(E.valeur(faa, var("x")), var("x"))


# ── appartenance à la limite projective (instance de l'axiome, théorème clos) ─
def test_appartient_limite_projective_close():
    th = L.appartient_limite_projective("E", "f", _leq(), "I", "z")
    # théorème CLOS (aucune hypothèse) = équivalence caractérisante
    assert th.hypotheses == frozenset() or len(th.hypotheses) == 0
    vz = var("z")
    gauche = appartient(vz, L.lim_proj(var("E"), var("f")))
    # la conclusion est l'équivalence (z∈lim ⇔ (z∈∏ et condition(1)))
    droite = et(appartient(vz, E.produit_famille(var("E"), var("I"))),
                L._condition_1(var("f"), _leq(), var("I"), vz))
    assert th.conclusion == equiv(gauche, droite)


def test_limite_projective_relation_1():
    th = L.limite_projective_relation_1("E", "f", _leq(), "I", "z", "a", "b")
    va, vb, vz = var("a"), var("b"), var("z")
    prem = et(et(appartient(va, var("I")), appartient(vb, var("I"))),
              _leq()(va, vb))
    pra = E.projection_indice(vz, va)
    prb = E.projection_indice(vz, vb)
    concl = egal(pra, L.transition_valeur(L.appl_proj(var("f"), va, vb), prb))
    assert th.conclusion == impl(prem, concl)
    assert appartient(vz, L.lim_proj(var("E"), var("f"))) in th.hypotheses


def test_limite_projective_dans_produit():
    th = L.limite_projective_dans_produit("E", "f", _leq(), "I", "z")
    vz = var("z")
    assert th.conclusion == appartient(vz, E.produit_famille(var("E"), var("I")))
    assert appartient(vz, L.lim_proj(var("E"), var("f"))) in th.hypotheses


# ── les définitions se construisent (prédicats clos bien formés) ──────────────
def test_definitions_se_construisent():
    sp = L.est_systeme_projectif(var("E"), var("f"), _leq(), var("I"))
    si = L.est_systeme_inductif(var("f"), _leq(), var("I"))
    # ce sont des conjonctions (LP_I et LP_II) / (filtrant et LI_I et LI_II)
    assert sp is not None and si is not None
    # axiome de la limite : (∀z)(...) bien formé
    ax = L.axiome_lim_proj(var("E"), var("f"), _leq(), var("I"))
    assert ax is not None


def test_definition_systeme_projectif_est_fidele_au_livre():
    """✅ ÉCART DE FIDÉLITÉ COMBLÉ (2026-08-05) — le test est INVERSÉ.

    Bourbaki type les transitions AVANT (LP_I)/(LP_II) : « soit f_{αβ} une
    application de E_β dans E_α ».  L'encodage ne gardait que les deux conditions
    NUMÉROTÉES ; il porte désormais les TROIS.  Ce test épinglait l'absence du
    typage — il épingle maintenant sa présence, et c'est le même test qui
    garantit qu'on ne le reperdra pas.  Voir docs/journal/ANOMALIES.md.

    La signature a gagné `Efam` en tête : on ne peut pas typer les transitions
    sans nommer la famille.  Le manque était inscrit dans le TYPE, pas seulement
    dans le corps — c'est pourquoi il avait pu passer inaperçu."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, libres_f,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites import (
        est_systeme_projectif, transitions_typees, cocycle_projectif,
        identite_projectif,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _gleq,
    )
    leq = _gleq()
    typage = transitions_typees(var("E"), var("f"), leq, var("I"), "a", "b", "zt")
    systeme = est_systeme_projectif(var("E"), var("f"), leq, var("I"))
    assert libres_f(typage) == {"E", "f", "I", "Gleq"}

    def _contient(f, cible):
        return f == cible or any(_contient(s, cible) for s in getattr(f, "sous", ()))

    # LES TROIS conditions du livre sont présentes — typage inclus
    assert _contient(systeme, typage)
    assert _contient(systeme, cocycle_projectif(var("f"), leq, var("I")))
    assert _contient(systeme, identite_projectif(var("f"), leq, var("I")))
    # la famille apparaît : c'est elle qui rend le typage énonçable
    assert "E" in libres_f(systeme)


def test_transitions_applications_est_plus_fort_que_le_typage():
    """🔴 Le premier comblement de l'écart de fidélité était PARTIEL.

    « f_{αβ} une APPLICATION de E_β dans E_α » dit TROIS choses : graphe
    fonctionnel, défini sur tout E_β, à valeurs dans E_α.  `transitions_typees`
    n'en capturait qu'une — les valeurs.  Découvert le 5 août en butant sur
    l'inclusion réciproque de la Prop. 3 : ce sont les conditions de DOMAINE
    (« (∃y)((t,y) ∈ f_{αβ}) ») qui restaient indémontrables.

    ⚠️ ENCODAGE : l'EXPOSANT (E_α)^(E_β) — les GRAPHES fonctionnels — et non
    𝓕(E_β;E_α), qui est l'ensemble des TRIPLETS.  Les transitions du dépôt sont
    manipulées comme des graphes (`valeur(f_{αβ}, t)` sans `graphe_de`) : se
    tromper des deux donne un terme qui ne se raccorde à rien."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, libres_f,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites import (
        transitions_applications, transitions_typees,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _gleq,
    )
    leq = _gleq()
    ta = transitions_applications(var("E"), var("f"), leq, var("I"))
    tt = transitions_typees(var("E"), var("f"), leq, var("I"))
    assert libres_f(ta) == {"E", "f", "I", "Gleq"}
    # ce sont bien DEUX énoncés distincts : le second ne dit pas le premier
    assert ta != tt
    assert len(E.theorie_ensembles().axiomes) == 22


def test_transitions_fonctionnelles_et_totales():
    """👑 Ce que le typage COMPLET donne, et que l'ancien ne donnait pas :
    fonctionnalité et domaine des transitions — lecture de `axiome_exposant`."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites import (
        transitions_fonctionnelles_et_totales, appl_proj,
    )
    func, dom = transitions_fonctionnelles_et_totales()
    fab = appl_proj(var("f"), var("a"), var("b"))
    assert func.conclusion == E.est_fonctionnel(fab)
    assert dom.conclusion == egal(E.dom(fab), E.valeur_famille(var("E"), var("b")))
    assert len(func.hypotheses) == 2 and len(dom.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_transition_definie_en_tue_les_conditions_de_domaine():
    """👑 La conséquence OPÉRATOIRE du typage complet, mesurée sur le blocage réel.

    Les hypothèses qui bloquaient l'inclusion réciproque de la Prop. 3 ont
    toutes la forme « (∃y)((t,y) ∈ f_{αβ}) » — f_{αβ} est définie en t.  Ce
    test fige la forme de la brique (existentielle de liant `y`, 3 hypothèses
    honnêtes) ET le fait qu'elle s'apparie littéralement à ce que la machinerie
    du prolongement réclame : l'hypothèse « t ∈ E_β » doit y figurer telle
    quelle, sinon la coupe n'aurait rien à couper.

    ⚠️ Le liant `y` vient d'AXIOME_DOM : deux α-variants sont DISTINCTS pour le
    noyau, donc la cible doit être produite par l'axiome, jamais réécrite."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, appartient,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites import (
        transition_definie_en,
    )
    th = transition_definie_en(var("tpt"))
    assert th.conclusion.tag == "exists" and th.conclusion.lieur == "y"
    assert len(th.hypotheses) == 3
    # l'hypothèse de point : c'est elle que le contexte de la Prop. 3 fournira
    assert appartient(var("tpt"),
                      E.valeur_famille(var("E"), var("b"))) in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_les_deux_moities_du_typage_sont_chacune_porteuse():
    """👑 LA justification chiffrée du comblement complet de l'écart de fidélité.

    « f_{αβ} est une application de E_β dans E_α » a deux moitiés opératoires,
    et les hypothèses qui bloquaient l'inclusion réciproque de la Prop. 3 se
    partagent entre elles — mesuré sur les instances réelles :
      · le DOMAINE (`transitions_applications` → `transition_definie_en`)
        couvre 6 hypothèses « (∃y)((t,y) ∈ f_{αβ}) » ;
      · les VALEURS (`transitions_typees` → `transition_valeur_dans_E`)
        couvre 3 hypothèses « f_{αβ}(t) ∈ E_α ».
    Aucune des deux ne rend l'autre superflue.  C'est pourquoi le typage partiel
    du 4-5 août ne pouvait pas suffire : il ne couvrait qu'un des deux besoins,
    et l'autre restait invisible tant que le premier bloquait.

    Ce test fige les DEUX briques côte à côte, mêmes 3 hypothèses honnêtes,
    conclusions distinctes."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, appartient,
    )
    import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites import (
        transition_definie_en, transition_valeur_dans_E, appl_proj,
        transition_valeur,
    )
    dom = transition_definie_en(var("tpt"))
    val = transition_valeur_dans_E(var("tpt"))
    fab = appl_proj(var("f"), var("a"), var("b"))
    assert val.conclusion == appartient(
        transition_valeur(fab, var("tpt")), E.valeur_famille(var("E"), var("a")))
    assert len(dom.hypotheses) == 3 and len(val.hypotheses) == 3
    # même hypothèse de point, conclusions différentes : deux moitiés distinctes
    point = appartient(var("tpt"), E.valeur_famille(var("E"), var("b")))
    assert point in dom.hypotheses and point in val.hypotheses
    assert dom.conclusion != val.conclusion
    assert len(E.theorie_ensembles().axiomes) == 22
