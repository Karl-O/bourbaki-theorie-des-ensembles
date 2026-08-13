"""§III.7.2 — la SURJECTIVITÉ de g : G⟨lim←_I⟩ ⊂ lim←_J, et ce qu'il reste.

────────────────────────────────────────────────────────────────────────────────
`g_bijection_sous_surjectivite` (module `ensembles_g_construite`) démontre la
Proposition 3 en vocabulaire du dépôt sous UNE prémisse : la surjectivité
ensembliste G⟨lim←_I⟩ = lim←_J.  Ce module en établit une MOITIÉ ENTIÈRE.

👑 `image_incluse_dans_limite ⊢ G⟨lim←_I⟩ ⊂ lim←_J`, avec **une seule
hypothèse** : la cofinalité de J — l'hypothèse même de la Proposition.

La route, en deux temps.  D'abord ponctuellement
(`valeur_dans_limite_restreinte`) : la caractérisation (1) de la limite réclame
l'appartenance au produit du système restreint (module
`ensembles_restriction_systeme`) et la condition (1) restreinte à J, quantifiée
sur les deux indices (`condition_1_de_la_valeur`).  Puis on passe à l'inclusion :
AXIOME_IMAGE fournit un témoin, `membre_graphe_terme` le traduit en
« y = (f_α(x))_{α∈J} », deux transports par S6 recollent, et l'on élimine le
témoin.

⚠️ TROIS PIÈGES, tous mesurés ici :
   • la relation (2) porte ((α∈I et β∈I) et α≤β) comme UNE prémisse COMPOSITE :
     couper ses trois conjoints séparément ne l'enlève pas, il faut la
     reconstruire par conjonction et la couper telle quelle (déjà vu ev. 170) ;
   • `alpha_existe` AVANT `existe_elimination` — le liant de l'existentielle
     doit coïncider avec le nom du témoin ;
   • `inclus` lie « z », et évaluer G en son propre nom de liant libre est
     dégénéré : démontrer sous un nom sûr, puis α-renommer.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.outil_portage import (
    porter_aux_termes,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, graphe_terme_est_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    membre_produit_famille,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    pivot_inclusion_produit, hypothese_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites_canoniques as C,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
    famille_coordonnees,
)



from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_restriction_systeme import (
    restriction_construite, valeur_dans_produit_restreint,
)

_PT, _IDX = "s", "t"


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        if p.conclusion in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(p.conclusion, thm))
    return thm


def _alpha(thm, ancien, neuf):
    """Renomme en α le liant de tête d'un ⊢ (∀ancien)R en (∀neuf)R.

    ⚠️ (∀x)R est encodé ¬(∃x)(¬R) : TROIS niveaux à dépiler pour atteindre R."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_avant,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        alpha_pour_tout,
    )
    if ancien == neuf:
        return thm
    return N.modus_ponens(thm, equivalence_avant(alpha_pour_tout(
        ancien, neuf, thm.conclusion.sous[0].sous[0].sous[0])))

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (la condition (1) restreinte à J, QUANTIFIÉE sur les deux indices, pour la valeur g(x))
def condition_1_de_la_valeur(Efam="E", f="f", J="J", i="I", pt=_PT, idx=_IDX,
                             a="a", b="b", leq=None, point="d"):
    """{ x ∈ lim←_I, J cofinale } ⊢ (∀α)(∀β)( (α,β∈J et α≤β)
                                     ⇒ pr_α(G(x)) = f_{αβ}(pr_β(G(x))) ).  [2 hyps].

    Le « sens facile » (`cofinal_canonique_compatible`) quantifié sur les deux
    indices.  Motif de quantification éprouvé : décharger ce qui porte α et β,
    généraliser, puis TESTER qu'aucune hypothèse ne les contient plus.
    Les deux gardes α∈I, β∈I se coupent par J ⊂ I (cofinalité) ; restent α∈J,
    β∈J et α≤β, que l'on décharge sous forme de la CONJONCTION exacte attendue
    par la condition (1)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite, instancie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cofinal import (
        cofinale_dans_inclusion,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _gleq,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_limites_props2 import (
        cofinal_canonique_compatible,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
        graphe_g, g_formule_3_quantifiee,
    )
    if leq is None:
        leq = _gleq()
    vJ, va, vb = _t(J), var(a), var(b)
    th = cofinal_canonique_compatible(
        Efam, f, leq, i, J, point, a, b,
        gterme=graphe_g(Efam, f, J, pt, idx),
        formule_3=g_formule_3_quantifiee(Efam, f, J, pt=pt, idx=idx))
    incl = cofinale_dans_inclusion(leq, J, i)
    dans_I = {v.nom: N.modus_ponens(N.assume(appartient(v, vJ)),
                                    instancie(incl, v)) for v in (va, vb)}
    prem = et(et(appartient(va, vJ), appartient(vb, vJ)), leq(va, vb))
    h = N.assume(prem)
    gauche = conjonction_elim_gauche(h)
    h_leq = conjonction_elim_droite(h)
    # ⚠️ PRÉMISSE COMPOSITE : la relation (2) porte ((α∈I et β∈I) et α≤β) comme UNE
    # hypothèse, pas trois — la couper conjoint par conjoint ne suffit pas, il faut
    # la RECONSTRUIRE et la couper telle quelle (piège déjà rencontré ev. 170).
    composite = conjonction_intro(
        conjonction_intro(dans_I[va.nom], dans_I[vb.nom]), h_leq)
    th = _cut(th, composite, dans_I[va.nom], dans_I[vb.nom],
              conjonction_elim_gauche(gauche), conjonction_elim_droite(gauche),
              h_leq)
    res = N.generalisation(a, N.generalisation(b, N.loi_deduction(prem, th)))
    assert all(a not in libres_f(x) and b not in libres_f(x)
               for x in res.hypotheses), \
        "condition_1_de_la_valeur : un indice reste libre dans une hypothèse"
    assert len(res.hypotheses) == 2, \
        f"condition_1_de_la_valeur : hyps ≠ 2 ({len(res.hypotheses)})"
    return res

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (👑 g(x) ∈ lim←_J : l'inclusion DIRECTE de la surjectivité, ponctuelle)
def valeur_dans_limite_restreinte(Efam="E", f="f", J="J", i="I", pt=_PT,
                                  idx=_IDX, ind="i", c="c", a="a", b="b",
                                  point="d", leq=None):
    """{ x ∈ lim←_I, J cofinale } ⊢ G(x) ∈ lim←_J.                    [2 hyps].

    👑 L'INCLUSION DIRECTE de la surjectivité, sous forme ponctuelle : la valeur
    de g en un point de lim←_I tombe bien dans lim←_J.  La caractérisation de la
    limite (formule (1)) demande exactement deux choses, toutes deux acquises :
      • l'appartenance au produit du système restreint
        (`valeur_dans_produit_restreint`) ;
      • la condition (1) restreinte à J, quantifiée sur les deux indices
        (`condition_1_de_la_valeur`).
    Le tout sur le système restreint CONSTRUIT — d'où l'énoncé porte sur un
    lim←_J dont on peut parler, contrairement au terme opaque du dépôt.

    ⚠️ Le point d'évaluation (`point`) doit être un nom DISTINCT du « liant »
    libre de g (`pt`) : évaluer G en son propre nom de liant est dégénéré et le
    kit le refuse (« 's' libre dans C »)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_arriere, equivalence_avant, instancie,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites as L,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _gleq,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
        graphe_g,
    )
    if leq is None:
        leq = _gleq()
    vE, vf, vJ = _t(Efam), _t(f), _t(J)
    G = graphe_g(Efam, f, J, pt, idx)
    restr = restriction_construite(Efam, J, c)
    gx = E.valeur(G, var(point))
    fam_d = famille_coordonnees(Efam, f, J, point, idx)

    # G(x) = (f_α(x))_{α∈J} : la valeur du graphe-terme extérieur, au point choisi
    eq = graphe_terme_valeur(L.lim_proj(vE, vf),
                             famille_coordonnees(Efam, f, J, pt, idx),
                             point, pt, "y")
    prod = valeur_dans_produit_restreint(Efam, f, J, i, point, idx, ind, c, leq)
    # transporter l'appartenance de la famille vers la VALEUR (S6, position élément)
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    eq_sym = N.modus_ponens(eq, symetrie(gx, fam_d))          # fam_d = G(x)
    prod_gx = N.modus_ponens(prod, equivalence_avant(N.modus_ponens(
        eq_sym, N.s6(fam_d, gx, "hpt",
                     appartient(var("hpt"), E.produit_famille(restr, vJ))))))
    cond = condition_1_de_la_valeur(Efam, f, J, i, pt, idx, a, b, leq, point)
    ax = N.axiome(L.theorie_lim_proj(restr, vf, leq, vJ),
                  L.axiome_lim_proj(restr, vf, leq, vJ))
    res = N.modus_ponens(conjonction_intro(prod_gx, cond),
                         equivalence_arriere(instancie(ax, gx)))
    assert res.conclusion == appartient(gx, L.lim_proj(restr, vf)), \
        "valeur_dans_limite_restreinte : ≠ (G(x) ∈ lim←_J)"
    assert len(res.hypotheses) == 2, \
        f"valeur_dans_limite_restreinte : hyps ≠ 2 ({len(res.hypotheses)})"
    return res

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (👑👑 l'INCLUSION D'IMAGES G⟨lim←_I⟩ ⊂ lim←_J : une moitié entière de la surjectivité)
def image_incluse_dans_limite(Efam="E", f="f", J="J", i="I", pt=_PT, idx=_IDX,
                              ind="i", c="c", a="a", b="b", point="d",
                              y="yy", leq=None):
    """{ J cofinale dans I } ⊢ G⟨lim←_I⟩ ⊂ lim←_J.                    [1 hyp].

    👑👑 UNE MOITIÉ ENTIÈRE de la surjectivité ensembliste, et sous forme
    d'INCLUSION — plus ponctuelle.  Il ne reste plus qu'une hypothèse : la
    cofinalité de J, c'est-à-dire l'hypothèse même de la Proposition 3.

    Preuve.  Soit y ∈ G⟨lim←_I⟩.  AXIOME_IMAGE fournit un témoin x avec
    x ∈ lim←_I et (x,y) ∈ G ; `membre_graphe_terme` traduit le second en
    « y = (f_α(x))_{α∈J} », qui n'est autre que G(x) ; et
    `valeur_dans_limite_restreinte` place G(x) dans lim←_J.  Deux transports par
    S6 recollent, puis on élimine le témoin.

    ⚠️ Le témoin est éliminé sous le nom `point` (« d »), alors que
    AXIOME_IMAGE lie « x » : il faut donc α-renommer l'existentielle AVANT
    l'élimination, sinon `existe_elimination` ne s'applique pas."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
        syllogisme,
    )
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        alpha_existe, existe_elimination,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
        membre_graphe_terme,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_algebre_binaire_ii4 import (
        membre_image,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites as L,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_g_construite import (
        graphe_g,
    )
    vE, vf, vJ = _t(Efam), _t(f), _t(J)
    G = graphe_g(Efam, f, J, pt, idx)
    lim_i = L.lim_proj(vE, vf)
    lim_j = L.lim_proj(restriction_construite(Efam, J, c), vf)
    vy, vd = var(y), var(point)
    fam_pt = famille_coordonnees(Efam, f, J, pt, idx)
    fam_d = famille_coordonnees(Efam, f, J, point, idx)
    gd = E.valeur(G, vd)

    # G(d) ∈ lim←_J, puis transport vers la famille : fam_d ∈ lim←_J
    gd_in = valeur_dans_limite_restreinte(Efam, f, J, i, pt, idx, ind, c,
                                          a, b, point, leq)
    eq_gd = graphe_terme_valeur(lim_i, fam_pt, point, pt, "y")   # G(d) = fam_d
    fam_in = N.modus_ponens(gd_in, equivalence_avant(N.modus_ponens(
        eq_gd, N.s6(gd, fam_d, "him", appartient(var("him"), lim_j)))))

    # sous le témoin : (d ∈ lim←_I et (d,y) ∈ G) ⇒ y ∈ lim←_J
    corps = et(appartient(vd, lim_i), appartient(E.couple(vd, vy), G))
    h = N.assume(corps)
    y_eq = conjonction_elim_droite(N.modus_ponens(
        conjonction_elim_droite(h),
        equivalence_avant(membre_graphe_terme(lim_i, fam_pt, point, y, pt, "y"))))
    y_in = N.modus_ponens(fam_in, equivalence_avant(N.modus_ponens(
        N.modus_ponens(y_eq, symetrie(vy, fam_d)),
        N.s6(fam_d, vy, "him2", appartient(var("him2"), lim_j)))))
    # « d ∈ lim←_I » vient du conjoint GAUCHE du témoin : on la coupe par là, sinon
    # elle reste libre en d et bloque l'élimination du témoin.
    imp = N.loi_deduction(corps, _cut(y_in, conjonction_elim_gauche(h)))

    # éliminer le témoin : l'existentielle d'AXIOME_IMAGE lie « x », on la renomme
    img = membre_image(G, lim_i, vy)
    corps_x = et(appartient(var("x"), lim_i),
                 appartient(E.couple(var("x"), vy), G))
    ren = alpha_existe("x", point, corps_x)
    res_y = N.modus_ponens(N.modus_ponens(N.assume(appartient(vy, E.image(G, lim_i))),
                                          equivalence_avant(img)),
                           syllogisme(equivalence_avant(ren),
                                      existe_elimination(imp, point)))
    # `inclus` lie « z » : on démontre sous un nom sûr puis on α-renomme.
    res = _alpha(N.generalisation(y, N.loi_deduction(
        appartient(vy, E.image(G, lim_i)), res_y)), y, "z")
    assert res.conclusion == E.inclus(E.image(G, lim_i), lim_j), \
        "image_incluse_dans_limite : ≠ (G⟨lim←_I⟩ ⊂ lim←_J)"
    assert len(res.hypotheses) == 1, \
        f"image_incluse_dans_limite : hyps ≠ 1 ({len(res.hypotheses)})"
    return res


REPORTES = [
    "🔴 BLOCAGE DE FOND, trouvé le 4 août 2026 — `restriction_systeme_indices` "
    "est un terme OPAQUE *sans aucun axiome* : app('restr_indices', E, f, J).  "
    "Or c'est LUI qui dénote le système restreint, donc "
    "lim←_J := lim_proj(restr_indices(E,f,J), f).  CONSÉQUENCE : aucun énoncé "
    "portant sur lim←_J n'est démontrable — non par manque d'effort, mais parce "
    "que le terme n'est caractérisé par RIEN.  C'est pourquoi "
    "`valeur_dans_produit` conclut dans `produit_famille(E, J)` et NON dans le "
    "produit du système restreint : les deux termes ne sont reliés par rien.  "
    "MÊME DIAGNOSTIC que pour `application_canonique_g`, en pire (là il y avait "
    "au moins un axiome).  ROUTE — PREMIER PAS FAIT : `restriction_construite` "
    "(graphe_terme(J, E_α)) et `restriction_valeur` ((restr)_ι = E_ι sous ι∈J) "
    "sont écrits et testés.  RESTE : (1) l'égalité des deux produits "
    "∏_{α∈J}(restr) = ∏_{α∈J}(E) par `egalite_par_extension` — les quatre "
    "clauses coïncident sous ι∈J, mais il faut aussi traiter le conjoint "
    "d'inclusion, dont le ⋃X_ι diffère ; (2) l'égalité des deux limites, qui en "
    "découle par la caractérisation (1) ; (3) migrer les consommateurs de "
    "`restriction_systeme_indices` (limites_prop4plus_iii7:135) vers la version "
    "construite.  Cela débloque la surjectivité ensembliste ET la Prop. 4.",
    "INCLUSION RÉCIPROQUE ⊇ (lim←_J ⊂ G⟨lim←_I⟩) — LA SEULE PIÈCE ENCORE "
    "MANQUANTE de toute la Proposition 3.  L'inclusion DIRECTE est faite "
    "(`image_incluse_dans_limite`, 1 hypothèse).  Pour la réciproque, le "
    "témoin est le prolongement x̃ : il faut (i) en faire un TERME — la "
    "famille (x̃_α)_{α∈I}, soit graphe_terme(I, x_tilde(f,y,J,α)) ; (ii) le "
    "placer dans lim←_I, ce qui redemande la clause des valeurs (x̃_α ∈ E_α, "
    "via les transitions f_{αβ} : E_β → E_α) plus "
    "`prolongement_coherent_universel` pour la condition (1) ; (iii) montrer "
    "G(x̃) = y par extensionnalité, les coordonnées coïncidant grâce à "
    "`prolongement_restitue`.  Puis `extensionnalite_appliquee` sur les deux "
    "inclusions donne l'égalité, et décharger la prémisse de "
    "`g_bijection_sous_surjectivite` CLÔT la Prop. 3 en vocabulaire du dépôt.",
]


__all__ = ["condition_1_de_la_valeur", "valeur_dans_limite_restreinte",
           "image_incluse_dans_limite", "REPORTES"]
