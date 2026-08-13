"""§III.7.1-7.2 — le SYSTÈME RESTREINT à J, construit, et le produit sur J.

────────────────────────────────────────────────────────────────────────────────
Ce module fournit les briques « côté produit » dont dépend la surjectivité de g
(`ensembles_g_surjection`).  Deux apports.

1. LE SYSTÈME RESTREINT, CONSTRUIT.  `restriction_systeme_indices` (dépôt) est un
   terme OPAQUE **sans aucun axiome** : `app("restr_indices", E, f, J)`.  Comme
   c'est lui qui dénote le système restreint — lim←_J := lim_proj(restr_indices,
   f) — aucun énoncé mentionnant lim←_J n'est démontrable.  Ce n'est pas une
   difficulté, c'est une impasse par construction, et elle ne se révèle qu'au
   moment du raccord.  `restriction_construite` le remplace par un `graphe_terme`
   (la famille α ↦ E_α indexée par J) et `restriction_valeur` démontre le pont
   qui manquait : (restr)_ι = E_ι sous ι∈J.  Un détail d'encodage le rend
   immédiat — dans le dépôt, `valeur_famille(E, ι)` EST `valeur(E, ι)`.

2. LA VALEUR DE g DANS LE PRODUIT.  La famille (f_α(x))_{α∈J} étant CONSTRUITE,
   trois des quatre clauses de l'appartenance au produit sont CLOSES (graphe,
   fonctionnel, domaine — `faits_clos_famille`).  La quatrième, la clause des
   VALEURS, est DÉMONTRÉE (`clause_valeurs`) : G(x)(ι) = f_ι(x) = pr_ι(x) ∈ E_ι,
   la réécriture se faisant par S6.

LE RACCOURCI.  Une fois la restriction construite, le réflexe est de démontrer
l'égalité des deux produits ∏(restr,J) = ∏(E,J).  C'est INUTILE : on refait la
construction DANS le système restreint (`clause_valeurs_restreinte`,
`valeur_dans_produit_restreint`), et comme le pivot est paramétré par la
famille, le ⋃ de l'inclusion s'aligne tout seul.  Chercher le raccourci que la
construction rend possible avant d'entreprendre l'égalité de deux objets.

⚠️ Noms FRAIS obligatoires (« s » le point, « t » l'indice) : un `graphe_terme`
   porte ses « liants » LIBRES — voir le piège en tête de `ensembles_g_construite`.
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



_PT, _IDX = "s", "t"


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        if p.conclusion in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(p.conclusion, thm))
    return thm


def faits_clos_famille(Efam="E", f="f", J="J", pt=_PT, idx=_IDX):
    """Les TROIS faits CLOS sur la famille (f_α(x))_{α∈J}, vue comme graphe-terme :
    (est_un_graphe, est_fonctionnel, dom = J).  Aucune hypothèse.

    Ils sont clos parce que la famille est CONSTRUITE : c'est le même dividende
    que pour g elle-même.  Sur une famille opaque, les trois seraient des
    hypothèses."""
    vJ = _t(J)
    interne = C.application_canonique_proj_valeur(
        _t(Efam), _t(f), var(idx), var(pt))
    fam = famille_coordonnees(Efam, f, J, pt, idx)
    gr = graphe_terme_est_graphe(vJ, interne, idx, "y")
    fn = graphe_terme_fonctionnel(vJ, interne, idx, "y")
    dm = graphe_terme_domaine(vJ, interne, idx, "y", "z")
    assert gr.conclusion == E.est_un_graphe(fam), "faits_clos_famille : graphe"
    assert fn.conclusion == E.est_fonctionnel(fam), "faits_clos_famille : fonctionnel"
    assert dm.conclusion == egal(E.dom(fam), vJ), "faits_clos_famille : domaine"
    assert gr.est_clos and fn.est_clos and dm.est_clos, \
        "faits_clos_famille : l'un des trois n'est pas clos"
    return gr, fn, dm

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (la clause des valeurs, DÉMONTRÉE : f_ι(x) ∈ E_ι découle de lim←_I ⊂ ∏_I)
def clause_valeurs(Efam="E", f="f", J="J", i="I", pt=_PT, idx=_IDX, ind="i",
                   leq=None):
    """{ x ∈ lim←_I,  J cofinale dans I } ⊢ (∀ι)( ι∈J ⇒ G(x)(ι) ∈ E_ι ).  [2 hyps].

    La quatrième clause de l'appartenance au produit, DÉMONTRÉE au lieu d'être
    supposée.  Trois briques, puis une réécriture :
      1. G(x)(ι) = f_ι(x)     [valeur du graphe-terme, sous ι∈J] ;
      2. f_ι(x)  = pr_ι(x)    [axiome canonique (2), sous x∈lim←_I et ι∈I] ;
      3. pr_ι(x) ∈ E_ι        [4ᵉ clause de `membre_produit_famille` en x, sous
                               x ∈ ∏_I et ι∈I] ;
      4. S6 transporte l'appartenance le long de l'égalité 1-2.
    Les deux gardes intermédiaires se coupent : x ∈ ∏_I vient de lim←_I ⊂ ∏_I
    (`_lim_dans_produit`), et ι∈I de ι∈J avec J ⊂ I (`cofinale_dans_inclusion`,
    que porte la cofinalité).  Ne restent que les deux hypothèses de contexte.

    Le résultat est ASSERTÉ égal à `hypothese_valeurs(E, J, ind, G(x))` : c'est
    littéralement la clause que réclame le pivot, pas une formule ressemblante."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_droite, equivalence_avant, instancie,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
        ensembles_limites as L,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
        _lim_dans_produit, _gleq,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cofinal import (
        cofinale_dans_inclusion,
    )
    if leq is None:
        leq = _gleq()
    vE, vJ, vI = _t(Efam), _t(J), _t(i)
    vx, vind = var(pt), var(ind)
    interne = C.application_canonique_proj_valeur(vE, _t(f), var(idx), vx)
    fam = famille_coordonnees(Efam, f, J, pt, idx)
    Eind = E.valeur_famille(vE, vind)

    val = graphe_terme_valeur(vJ, interne, ind, idx, "y")      # G(x)(ι)=f_ι(x)
    h_x = N.assume(appartient(vx, L.lim_proj(vE, _t(f))))
    h_ind = N.assume(appartient(vind, vI))
    canon = N.modus_ponens(conjonction_intro(h_x, h_ind), instancie(instancie(
        N.axiome(C.theorie_canonique_proj(vE, _t(f), leq, vI),
                 C.axiome_canonique_proj(vE, _t(f), leq, vI)), vind), vx))
    chaine = composer_egalites(val, canon)                     # G(x)(ι)=pr_ι(x)

    carac = porter_aux_termes(membre_produit_famille(
        Efam if isinstance(Efam, str) else "E",
        i if isinstance(i, str) else "I", "Fpv"), {"Fpv": vx})
    quatre = conjonction_elim_droite(N.modus_ponens(
        N.assume(appartient(vx, E.produit_famille(vE, vI))),
        equivalence_avant(carac)))
    val_in = N.modus_ponens(h_ind, instancie(quatre, vind))    # pr_ι(x) ∈ E_ι

    pr_x = E.projection_indice(vx, vind)
    sym = N.modus_ponens(chaine, symetrie(E.valeur(fam, vind), pr_x))
    fam_in = N.modus_ponens(val_in, equivalence_avant(N.modus_ponens(
        sym, N.s6(pr_x, E.valeur(fam, vind), "htrou",
                  appartient(var("htrou"), Eind)))))

    fam_c = _cut(fam_in,
                 _lim_dans_produit(Efam, f, leq, i, vx, h_x),       # x ∈ ∏_I
                 N.modus_ponens(N.assume(appartient(vind, vJ)),     # ι ∈ I
                                instancie(cofinale_dans_inclusion(leq, J, i), vind)))
    res = N.generalisation(ind, N.loi_deduction(appartient(vind, vJ), fam_c))
    assert res.conclusion == hypothese_valeurs(vE, vJ, ind, fam), \
        "clause_valeurs : ≠ hypothese_valeurs(E, J, ι, G(x))"
    assert len(res.hypotheses) == 2, \
        f"clause_valeurs : hyps ≠ 2 ({len(res.hypotheses)})"
    return res

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (la valeur g(x) appartient au produit ∏_{α∈J} E_α — les QUATRE clauses acquises)
def famille_dans_produit(Efam="E", f="f", J="J", pt=_PT, idx=_IDX, i="i"):
    """{ (∀ι)(ι∈J ⇒ G(x)(ι) ∈ E_ι) } ⊢ G(x) ∈ ∏_{α∈J} E_α.          [1 hyp].

    L'appartenance au produit se caractérise par QUATRE clauses
    (`membre_produit_famille`) : inclusion dans J×⋃E_α, fonctionnalité, domaine,
    et valeurs.  Ici :
      • les trois premières sont CLOSES — la famille est un `graphe_terme`
        (`faits_clos_famille`), et l'inclusion s'en déduit par le PIVOT
        `pivot_inclusion_produit`, dont on coupe les trois hypothèses ;
      • la quatrième, la clause des VALEURS, reste la SEULE hypothèse.

    C'est le bon découpage : il isole exactement ce qui n'est pas gratuit.  La
    clause des valeurs dit que f_ι(x) ∈ E_ι, ce qui découle de lim←_I ⊂ ∏_I —
    vrai, mais non encore écrit (REPORTES)."""
    vE, vJ = _t(Efam), _t(J)
    fam = famille_coordonnees(Efam, f, J, pt, idx)
    gr, fn, dm = faits_clos_famille(Efam, f, J, pt, idx)
    h_vals = N.assume(hypothese_valeurs(vE, vJ, i, fam))

    incl = _cut(pivot_inclusion_produit(fam, vE, vJ, i), gr, fn, dm)
    carac = porter_aux_termes(membre_produit_famille(
        Efam if isinstance(Efam, str) else "E",
        J if isinstance(J, str) else "J", "Fprod"), {"Fprod": fam})
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(incl, fn), dm), h_vals), equivalence_arriere(carac))
    assert res.conclusion == appartient(fam, E.produit_famille(vE, vJ)), \
        "famille_dans_produit : conclusion ≠ (G(x) ∈ ∏_{α∈J} E_α)"
    assert res.hypotheses == frozenset({hypothese_valeurs(vE, vJ, i, fam)}), \
        f"famille_dans_produit : hypothèses ≠ {{clause des valeurs}} ({len(res.hypotheses)})"
    return res

# @livre Ch.III §7.1 Def.- | E III.52 L.27-32 | PDF p.155  (le système restreint à J, CONSTRUIT au lieu d'être un terme opaque sans axiome)
def restriction_construite(Efam="E", J="J", ind="c"):
    """Le système (E_α)_{α∈J} CONSTRUIT : la famille α ↦ E_α indexée par J.

    Remplace le terme opaque `restriction_systeme_indices`, qui n'est
    caractérisé par AUCUN axiome et rend donc indémontrable tout énoncé
    mentionnant lim←_J.  Ici c'est un simple `graphe_terme`, donc on peut en
    parler."""
    return E.graphe_terme(_t(J), E.valeur_famille(_t(Efam), var(ind)), ind)

# @livre Ch.III §7.1 Def.- | E III.52 L.27-32 | PDF p.155  (le pont : la restriction construite a bien les mêmes termes que la famille de départ sur J)
def restriction_valeur(Efam="E", J="J", ind="c", i="i"):
    """{ ι ∈ J } ⊢ (restr)_ι = E_ι.                                    [1 hyp].

    LE PONT qui manquait.  Il dit que la famille restreinte prend, en chaque
    indice de J, la même valeur que la famille de départ — ce qui est la
    définition même d'une restriction, et ce que le terme opaque ne permettait
    pas d'énoncer.

    Un détail d'encodage rend le pont immédiat : dans le dépôt,
    `valeur_famille(E, ι)` EST `valeur(E, ι)` (même terme).  La valeur du
    graphe-terme donne donc directement le résultat, sans conversion.

    Avec ce pont, les quatre clauses de l'appartenance à ∏_{α∈J} sont les mêmes
    pour les deux familles sous ι∈J, et `egalite_par_extension` conclut à
    l'égalité des deux produits — c'est la suite du chantier."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
        graphe_terme_valeur,
    )
    vE, vJ, vi = _t(Efam), _t(J), var(i)
    res = graphe_terme_valeur(vJ, E.valeur_famille(vE, var(ind)), i, ind, "y")
    assert res.conclusion == egal(
        E.valeur_famille(restriction_construite(Efam, J, ind), vi),
        E.valeur_famille(vE, vi)), \
        "restriction_valeur : conclusion ≠ ((restr)_ι = E_ι)"
    assert res.hypotheses == frozenset({appartient(vi, vJ)}), \
        "restriction_valeur : hypothèse ≠ {ι ∈ J}"
    return res

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (la clause des valeurs TRANSPORTÉE sur le système restreint construit)
def clause_valeurs_restreinte(Efam="E", f="f", J="J", i="I", pt=_PT, idx=_IDX,
                              ind="i", c="c", leq=None):
    """{ x ∈ lim←_I, J cofinale } ⊢ (∀ι)( ι∈J ⇒ G(x)(ι) ∈ (restr)_ι ).  [2 hyps].

    La même clause que `clause_valeurs`, mais visant les ensembles du système
    RESTREINT CONSTRUIT au lieu de ceux de la famille de départ.  C'est ce
    transport qui évite d'avoir à démontrer l'égalité des deux produits : on
    travaille directement dans le bon système.

    Une seule étape s'ajoute — S6 le long du pont (restr)_ι = E_ι, appliqué
    cette fois à la position ENSEMBLE de l'appartenance (et non à la position
    élément comme dans `clause_valeurs`)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_avant, instancie,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    vE, vJ = _t(Efam), _t(J)
    vind = var(ind)
    fam = famille_coordonnees(Efam, f, J, pt, idx)
    restr = restriction_construite(Efam, J, c)
    Eind, Rind = E.valeur_famille(vE, vind), E.valeur_famille(restr, vind)

    base = clause_valeurs(Efam, f, J, i, pt, idx, ind, leq)      # ∈ E_ι, quantifié
    h_ind = N.assume(appartient(vind, vJ))
    en_E = N.modus_ponens(h_ind, instancie(base, vind))          # G(x)(ι) ∈ E_ι
    pont = restriction_valeur(Efam, J, c, ind)                   # (restr)_ι = E_ι
    pont_sym = N.modus_ponens(pont, symetrie(Rind, Eind))        # E_ι = (restr)_ι
    en_R = N.modus_ponens(en_E, equivalence_avant(N.modus_ponens(
        pont_sym, N.s6(Eind, Rind, "hset",
                       appartient(E.valeur(fam, vind), var("hset"))))))
    res = N.generalisation(ind, N.loi_deduction(appartient(vind, vJ), en_R))
    assert res.conclusion == hypothese_valeurs(restr, vJ, ind, fam), \
        "clause_valeurs_restreinte : ≠ hypothese_valeurs(restr, J, ι, G(x))"
    assert len(res.hypotheses) == 2, \
        f"clause_valeurs_restreinte : hyps ≠ 2 ({len(res.hypotheses)})"
    return res

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (g(x) appartient au produit du système RESTREINT — le bon produit, celui de lim←_J)
def valeur_dans_produit_restreint(Efam="E", f="f", J="J", i="I", pt=_PT,
                                  idx=_IDX, ind="i", c="c", leq=None):
    """{ x ∈ lim←_I, J cofinale } ⊢ G(x) ∈ ∏_{α∈J} (restr)_α.        [2 hyps].

    LA BONNE CIBLE.  `valeur_dans_produit` concluait dans `produit_famille(E, J)`,
    que rien ne relie au produit du système restreint — donc rien ne permettait
    d'enchaîner vers lim←_J.  Ici on travaille d'emblée dans le système restreint
    CONSTRUIT, et l'obstacle disparaît sans qu'il faille démontrer l'égalité des
    deux produits : c'est le raccourci que la construction rend possible.

    Les trois clauses de bonne formation restent CLOSES (elles ne parlent que du
    graphe-terme G(x), pas du système), et le pivot est instancié sur la famille
    restreinte, ce qui aligne aussi le ⋃ de l'inclusion."""
    fam = famille_coordonnees(Efam, f, J, pt, idx)
    restr = restriction_construite(Efam, J, c)
    vJ = _t(J)
    gr, fn, dm = faits_clos_famille(Efam, f, J, pt, idx)
    incl = _cut(pivot_inclusion_produit(fam, restr, vJ, ind), gr, fn, dm)
    carac = porter_aux_termes(
        membre_produit_famille("Erst", J if isinstance(J, str) else "J", "Fprd"),
        {"Erst": restr, "Fprd": fam})
    res = N.modus_ponens(conjonction_intro(conjonction_intro(conjonction_intro(
        incl, fn), dm), N.assume(hypothese_valeurs(restr, vJ, ind, fam))),
        equivalence_arriere(carac))
    res = _cut(res, clause_valeurs_restreinte(Efam, f, J, i, pt, idx, ind, c, leq))
    assert res.conclusion == appartient(fam, E.produit_famille(restr, vJ)), \
        "valeur_dans_produit_restreint : ≠ (G(x) ∈ ∏_{α∈J}(restr)_α)"
    assert len(res.hypotheses) == 2, \
        f"valeur_dans_produit_restreint : hyps ≠ 2 ({len(res.hypotheses)})"
    return res

# @livre Ch.III §7.2 Prop.3 | E III.55 L.3-11 | PDF p.158  (g(x) ∈ ∏_{α∈J} E_α sous les seules hypothèses de contexte : la clause des valeurs est déchargée)
def valeur_dans_produit(Efam="E", f="f", J="J", i="I", pt=_PT, idx=_IDX,
                        ind="i", leq=None):
    """{ x ∈ lim←_I,  J cofinale dans I } ⊢ G(x) ∈ ∏_{α∈J} E_α.      [2 hyps].

    `famille_dans_produit` moins sa dernière hypothèse, déchargée par
    `clause_valeurs`.  C'est la moitié (a) de l'inclusion directe : la valeur de
    g tombe dans le produit sur J.  La moitié (b) — la condition (1) restreinte
    à J — est `cofinal_canonique_compatible`, déjà démontrée ; leur conjonction
    donnera « G(x) ∈ lim←_J » via `appartient_limite_projective`."""
    base = famille_dans_produit(Efam, f, J, pt, idx, ind)
    res = _cut(base, clause_valeurs(Efam, f, J, i, pt, idx, ind, leq))
    assert len(res.hypotheses) == 2, \
        f"valeur_dans_produit : hyps ≠ 2 ({len(res.hypotheses)})"
    return res


__all__ = ["faits_clos_famille", "clause_valeurs", "famille_dans_produit",
           "valeur_dans_produit", "restriction_construite",
           "restriction_valeur", "clause_valeurs_restreinte",
           "valeur_dans_produit_restreint"]
