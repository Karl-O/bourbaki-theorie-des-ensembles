"""§III.7.2 — le PROLONGEMENT x̃ comme TERME, et ses valeurs.

────────────────────────────────────────────────────────────────────────────────
Pour l'inclusion RÉCIPROQUE de la surjectivité (lim←_J ⊂ G⟨lim←_I⟩), il faut
exhiber un antécédent : étant donné y ∈ lim←_J, le point x̃ de lim←_I tel que
G(x̃) = y.  Bourbaki le construit coordonnée par coordonnée,
    x̃_α := f_{α, β(α)}( y_{β(α)} )
où β(α) est un majorant de α dans J — ici le témoin CANONIQUE τ, sans axiome du
choix (`ensembles_temoin_cofinal`).  `x_tilde` (module
`ensembles_prolongement_cofinal`) donne cette coordonnée ; ce module en fait une
FAMILLE, c'est-à-dire un terme unique dont on peut dire « il appartient à
lim←_I ».

Le dividende de la construction est le même qu'ailleurs : la famille est un
`graphe_terme`, donc trois des quatre clauses de l'appartenance au produit sont
CLOSES (`faits_clos_prolongement`).  Reste la clause des VALEURS, x̃_α ∈ E_α.

📌 C'est là que sert le TYPAGE des transitions : x̃_α est une VALEUR DE
TRANSITION, donc y être dans E_α exige de savoir que f_{αβ} envoie E_β dans E_α.
Cette condition manquait à `est_systeme_projectif` — écart de fidélité trouvé le
4 août et COMBLÉ le 5 (`docs/journal/ANOMALIES.md`).  On la porte ici sous son
nom propre, `transitions_typees`, plutôt que de supposer tout le système : c'est
la seule des trois conditions dont cette preuve ait besoin.

⚠️ Le point d'évaluation doit être un nom DISTINCT du liant de la famille :
   évaluer un `graphe_terme` en son propre liant est dégénéré (le kit lève
   « 'n' libre dans C »).  D'où le couple (liant « n », évaluation « i »).
⚠️ Le nom du point d'évaluation n'est PAS libre non plus : il devient le
   liant de la clause des valeurs, qui doit être CELUI DE L'AXIOME du
   produit — « i ».  Un autre nom fait échouer le modus ponens final.
INVARIANT : theorie_ensembles()=22 ; rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel, graphe_terme_est_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    hypothese_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_domaine, graphe_terme_valeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cofinal import (
    cofinale_dans_inclusion,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.ensembles_cone_unicite import (
    _gleq,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prolongement_cofinal import (
    x_tilde,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_temoin_cofinal import (
    beta_cofinal, temoin_cofinal,
)

#: liant de la famille, et nom du point d'évaluation — DISTINCTS obligatoirement.
_LIANT, _IND = "n", "i"


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, *preuves):
    for p in preuves:
        if p.conclusion in thm.hypotheses:
            thm = N.modus_ponens(p, N.loi_deduction(p.conclusion, thm))
    return thm


# @livre Ch.III §7.2 Prop.3 | E III.55 L.14-20 | PDF p.158  (le prolongement x̃=(x̃_α)_{α∈I} comme FAMILLE, c.-à-d. comme terme unique)
def prolongement_famille(f="f", y="yp", J="J", i="I", liant=_LIANT):
    """Le terme x̃ = ( f_{α,β(α)}(y_{β(α)}) )_{α∈I} — la famille prolongée.

    `x_tilde` donne la coordonnée ; ici on en fait un `graphe_terme` indexé par
    I, donc un objet dont on peut dire « il appartient à lim←_I »."""
    return E.graphe_terme(_t(i), x_tilde(_t(f), _t(y), _t(J), var(liant)), liant)


def faits_clos_prolongement(f="f", y="yp", J="J", i="I", liant=_LIANT):
    """Les TROIS faits CLOS sur x̃ : (est_un_graphe, est_fonctionnel, dom = I).

    Gratuits parce que x̃ est CONSTRUIT — même dividende que pour g et pour la
    famille des coordonnées."""
    vI = _t(i)
    interne = x_tilde(_t(f), _t(y), _t(J), var(liant))
    xt = prolongement_famille(f, y, J, i, liant)
    gr = graphe_terme_est_graphe(vI, interne, liant, "y")
    fn = graphe_terme_fonctionnel(vI, interne, liant, "y")
    dm = graphe_terme_domaine(vI, interne, liant, "y", "z")
    assert gr.conclusion == E.est_un_graphe(xt), "faits_clos_prolongement : graphe"
    assert fn.conclusion == E.est_fonctionnel(xt), "faits_clos_prolongement : fonctionnel"
    assert dm.conclusion == egal(E.dom(xt), vI), "faits_clos_prolongement : domaine"
    assert gr.est_clos and fn.est_clos and dm.est_clos, \
        "faits_clos_prolongement : l'un des trois n'est pas clos"
    return gr, fn, dm


# @livre Ch.III §7.2 Prop.3 | E III.55 L.14-20 | PDF p.158  (la clause des valeurs du prolongement — c'est ici que sert le TYPAGE des transitions)
def valeur_prolongement_dans_E(f="f", Efam="E", y="yp", J="J", i="I",
                               liant=_LIANT, ind=_IND, leq=None):
    """{ transitions typées, J cofinale, m ∈ I, y_{β(m)} ∈ E_{β(m)} }
        ⊢ x̃(m) ∈ E_m.                                                [4 hyps].

    La coordonnée du prolongement tombe dans le bon ensemble.  Deux pas :
      1. x̃(m) = f_{m,β(m)}(y_{β(m)})  — valeur du graphe-terme, sous m ∈ I ;
      2. `transitions_typees` en (m, β(m)) appliquée à y_{β(m)}.

    📌 Le pas 2 est exactement le TYPAGE des transitions — la condition qui
    manquait à `est_systeme_projectif` jusqu'au 5 août 2026.  On la porte sous
    son nom propre plutôt que de supposer tout le système : c'est la seule des
    trois dont cette preuve ait besoin.
    La garde composite ((m∈I et β(m)∈I) et m≤β(m)) est reconstruite depuis
    `temoin_cofinal` et l'inclusion J ⊂ I — c'est la prémisse composite, qu'il
    faut couper d'un bloc et non conjoint par conjoint."""
    if leq is None:
        leq = _gleq()
    vE, vf, vJ, vI, vy = _t(Efam), _t(f), _t(J), _t(i), _t(y)
    vm = var(ind)
    bm = beta_cofinal(vJ, vm)
    xt = prolongement_famille(f, y, J, i, liant)

    val = graphe_terme_valeur(vI, x_tilde(vf, vy, vJ, var(liant)), ind, liant, "y")
    typage = N.assume(L.transitions_typees(vE, vf, leq, vI, "a", "b", "zt"))
    corps = N.modus_ponens(
        N.assume(et(et(appartient(vm, vI), appartient(bm, vI)), leq(vm, bm))),
        instancie(instancie(typage, vm), bm))
    ycoord = E.valeur(vy, bm)
    dans_E = N.modus_ponens(
        N.assume(appartient(ycoord, E.valeur_famille(vE, bm))),
        instancie(corps, ycoord))                     # f_{m,β(m)}(y_{β(m)}) ∈ E_m

    # transporter le long de x̃(m) = f_{m,β(m)}(y_{β(m)})
    res = N.modus_ponens(dans_E, equivalence_avant(N.modus_ponens(
        N.modus_ponens(val, _symetrie(E.valeur(xt, vm),
                                      x_tilde(vf, vy, vJ, vm))),
        N.s6(x_tilde(vf, vy, vJ, vm), E.valeur(xt, vm), "hxt",
             appartient(var("hxt"), E.valeur_famille(vE, vm))))))
    # fournir la garde composite depuis le témoin canonique
    tc = temoin_cofinal(J, i, ind)
    b_in_J, m_leq_b = conjonction_elim_gauche(tc), conjonction_elim_droite(tc)
    b_in_I = N.modus_ponens(b_in_J, instancie(
        cofinale_dans_inclusion(leq, J, i), bm))
    res = _cut(res, conjonction_intro(conjonction_intro(
        N.assume(appartient(vm, vI)), b_in_I), m_leq_b), b_in_I, b_in_J, m_leq_b, tc)
    assert res.conclusion == appartient(E.valeur(xt, vm),
                                        E.valeur_famille(vE, vm)), \
        "valeur_prolongement_dans_E : conclusion ≠ (x̃(m) ∈ E_m)"
    return res


def _symetrie(u, v):
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie,
    )
    return symetrie(u, v)


# @livre Ch.III §7.2 Prop.3 | E III.55 L.14-20 | PDF p.158  (la coordonnée du point de départ tombe dans E_{β(m)} : lue sur y ∈ lim←_J via le pont du système restreint)
def coordonnee_de_y_dans_E(f="f", Efam="E", y="yp", J="J", i="I", ind=_IND,
                           c="c", leq=None):
    """{ y ∈ lim←_J, J cofinale, m ∈ I } ⊢ y_{β(m)} ∈ E_{β(m)}.        [3 hyps].

    L'ingrédient qui manquait à `valeur_prolongement_dans_E`.  Quatre pas :
    y ∈ lim←_J donne y ∈ ∏(restr, J) (conjoint de tête de la caractérisation),
    d'où la 4ᵉ clause (∀ι)(ι∈J ⇒ y(ι) ∈ (restr)_ι), instanciée en β(m) sous
    β(m) ∈ J que fournit `temoin_cofinal` ; puis le pont
    `restriction_valeur` ((restr)_ι = E_ι) transporte par S6 sur la position
    ENSEMBLE de l'appartenance."""
    if leq is None:
        leq = _gleq()
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.outil_portage import (
        porter_aux_termes,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
        membre_produit_famille,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.prop3_surj.ensembles_restriction_systeme import (
        restriction_construite, restriction_valeur,
    )
    vE, vf, vJ, vy = _t(Efam), _t(f), _t(J), _t(y)
    vm = var(ind)
    bm = beta_cofinal(vJ, vm)
    restr = restriction_construite(Efam, J, c)

    ax = N.axiome(L.theorie_lim_proj(restr, vf, leq, vJ),
                  L.axiome_lim_proj(restr, vf, leq, vJ))
    y_prod = conjonction_elim_gauche(N.modus_ponens(
        N.assume(appartient(vy, L.lim_proj(restr, vf))),
        equivalence_avant(instancie(ax, vy))))
    carac = porter_aux_termes(membre_produit_famille(
        "Erst", J if isinstance(J, str) else "J", "Fy"),
        {"Erst": restr, "Fy": vy})
    clause = conjonction_elim_droite(N.modus_ponens(
        y_prod, equivalence_avant(carac)))
    tc = temoin_cofinal(J, i, ind)
    b_in_J = conjonction_elim_gauche(tc)
    y_in_restr = N.modus_ponens(b_in_J, instancie(clause, bm))

    pont = porter_aux_termes(restriction_valeur(Efam, J, c), {"i": bm})
    res = N.modus_ponens(y_in_restr, equivalence_avant(N.modus_ponens(
        pont, N.s6(E.valeur_famille(restr, bm), E.valeur_famille(vE, bm), "hs",
                   appartient(E.valeur(vy, bm), var("hs"))))))
    res = _cut(res, b_in_J)              # la garde du pont, β(m) ∈ J
    assert res.conclusion == appartient(E.valeur(vy, bm),
                                        E.valeur_famille(vE, bm)), \
        "coordonnee_de_y_dans_E : conclusion ≠ (y_{β(m)} ∈ E_{β(m)})"
    assert len(res.hypotheses) == 3, \
        f"coordonnee_de_y_dans_E : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.14-20 | PDF p.158  (la clause des valeurs du prolongement, QUANTIFIÉE : x̃ a bien ses coordonnées dans les E_α)
def clause_valeurs_prolongement(f="f", Efam="E", y="yp", J="J", i="I",
                                liant=_LIANT, ind=_IND, c="c", leq=None):
    """{ transitions typées, J cofinale, y ∈ lim←_J }
        ⊢ (∀m)( m ∈ I ⇒ x̃(m) ∈ E_m ).                                [3 hyps].

    `valeur_prolongement_dans_E` moins son hypothèse de coordonnée, déchargée
    par `coordonnee_de_y_dans_E`, puis quantifiée sur l'indice.  Motif de
    quantification : décharger ce qui porte m, généraliser, TESTER qu'aucune
    hypothèse ne le contient plus.

    Le résultat est ASSERTÉ égal à `hypothese_valeurs(E, I, m, x̃)` — la clause
    exacte qu'attend le pivot, pas une formule ressemblante."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        libres_f,
    )
    vI = _t(i)
    vm = var(ind)
    base = valeur_prolongement_dans_E(f, Efam, y, J, i, liant, ind, leq)
    base = _cut(base, coordonnee_de_y_dans_E(f, Efam, y, J, i, ind, c, leq))
    res = N.generalisation(ind, N.loi_deduction(appartient(vm, vI), base))
    assert all(ind not in libres_f(h) for h in res.hypotheses), \
        "clause_valeurs_prolongement : m encore libre dans une hypothèse"
    assert res.conclusion == hypothese_valeurs(
        _t(Efam), vI, ind, prolongement_famille(f, y, J, i, liant)), \
        "clause_valeurs_prolongement : ≠ hypothese_valeurs(E, I, m, x̃)"
    assert len(res.hypotheses) == 3, \
        f"clause_valeurs_prolongement : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


# @livre Ch.III §7.2 Prop.3 | E III.55 L.14-20 | PDF p.158  (x̃ appartient au produit ∏_{α∈I} E_α — les quatre clauses réunies)
def prolongement_dans_produit(f="f", Efam="E", y="yp", J="J", i="I",
                              liant=_LIANT, ind=_IND, c="c", leq=None):
    """{ transitions typées, J cofinale, y ∈ lim←_J } ⊢ x̃ ∈ ∏_{α∈I} E_α.  [3 hyps].

    Les quatre clauses de l'appartenance au produit : les trois de bonne
    formation sont CLOSES (`faits_clos_prolongement`, x̃ est un `graphe_terme`),
    la quatrième est `clause_valeurs_prolongement`.  Le PIVOT
    `pivot_inclusion_produit` en tire l'inclusion x̃ ⊂ I×⋃E_α, et la
    caractérisation conclut.

    Il ne reste que les trois hypothèses de contexte — aucune n'est propre à x̃."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_intro, equivalence_arriere,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.outil_portage import (
        porter_aux_termes,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
        membre_produit_famille,
    )
    from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
        pivot_inclusion_produit,
    )
    vE, vI = _t(Efam), _t(i)
    xt = prolongement_famille(f, y, J, i, liant)
    gr, fn, dm = faits_clos_prolongement(f, y, J, i, liant)
    vals = clause_valeurs_prolongement(f, Efam, y, J, i, liant, ind, c, leq)

    # le pivot porte les QUATRE clauses en hypothèses : on coupe les trois
    # closes ET la clause des valeurs (sinon elle ressort dans le résultat).
    incl = _cut(pivot_inclusion_produit(xt, vE, vI, ind), gr, fn, dm, vals)
    carac = porter_aux_termes(membre_produit_famille(
        Efam if isinstance(Efam, str) else "E",
        i if isinstance(i, str) else "I", "Fxt"), {"Fxt": xt})
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        conjonction_intro(incl, fn), dm), vals), equivalence_arriere(carac))
    assert res.conclusion == appartient(xt, E.produit_famille(vE, vI)), \
        "prolongement_dans_produit : conclusion ≠ (x̃ ∈ ∏_{α∈I} E_α)"
    assert len(res.hypotheses) == 3, \
        f"prolongement_dans_produit : hyps ≠ 3 ({len(res.hypotheses)})"
    return res


REPORTES = [
    "x̃ ∈ lim←_I — DERNIÈRE PIÈCE avant l'inclusion réciproque.  "
    "`prolongement_dans_produit` donne la moitié PRODUIT (3 hypothèses de "
    "contexte : transitions typées, J cofinale, y ∈ lim←_J).  Reste la "
    "condition (1) sur I.  Le contenu mathématique EXISTE — "
    "`prolongement_coherent` conclut x̃_α = f_{αα'}(x̃_{α'}).  Deux écarts : "
    "(a) FORME — il parle de `x_tilde(f,y,J,α)` alors que la condition (1) "
    "parle de pr_α(x̃) = valeur(x̃, α) : deux transports S6 le long de "
    "`graphe_terme_valeur`, mécanique ; (b) FOND — sa prémisse est une cascade "
    "de QUATORZE hypothèses portant les indices, et ⚠️ CE NE SONT PAS DE "
    "SIMPLES GARDES : mesurées, ce sont 6 existentielles de témoin (∃y), "
    "3 conditions universelles et 5 cascades — c.-à-d. les propriétés du témoin "
    "canonique et la relation (1) sur y aux couples d'indices concernés.  Les "
    "fournir depuis le contexte, c'est les DÉMONTRER, pas les réarranger.  "
    "(Une première estimation annonçait « aucune difficulté mathématique, "
    "seulement de la forme » : elle était FAUSSE, corrigée après mesure.)  "
    "🔓 MAJ 5 août : les 6 existentielles SONT DÉSORMAIS FOURNIES.  Elles "
    "disaient toutes « f_{αβ} est définie au point t » et se dérivent du typage "
    "COMPLET par `ensembles_limites.transition_definie_en` — apparié 6/6 sur les "
    "instances réelles (sonde : conclusion == hypothèse, pas une ressemblance).  "
    "ÉTAT MESURÉ APRÈS COUPE : 18 → 22 hypothèses, dont 16 non fournies par le "
    "contexte = **5 hypothèses de POINT** (« pr_β(y') ∈ E'_β », à tirer de la "
    "clause des valeurs de y' ∈ ∏_{β∈J} E'_β, donc de `hypothese_valeurs` "
    "instanciée en β — attention, β y parcourt J, alors que certains indices "
    "utilisés sont des témoins τ de I : c'est LÀ qu'est la vraie question) et "
    "**11 conditions universelles** qui sont les conditions du système "
    "projectif lui-même, donc des hypothèses HONNÊTES de la proposition, à "
    "laisser telles quelles.  Le prochain pas est donc les 5 points, pas les 11.",
    "PUIS : G(x̃) = y par extensionnalité du produit — les coordonnées "
    "coïncident par `prolongement_restitue` (x̃_α = y_α pour α∈J) — d'où "
    "y ∈ G⟨lim←_I⟩ par AXIOME_IMAGE avec le témoin x̃, puis l'inclusion "
    "lim←_J ⊂ G⟨lim←_I⟩, puis `extensionnalite_appliquee` sur les deux "
    "inclusions, puis décharge de la prémisse de "
    "`g_bijection_sous_surjectivite` ⇒ **Prop. 3 CLOSE en vocabulaire du "
    "dépôt**, sous la seule hypothèse du système projectif.",
]

__all__ = ["prolongement_famille", "faits_clos_prolongement",
           "valeur_prolongement_dans_E", "coordonnee_de_y_dans_E",
           "clause_valeurs_prolongement", "prolongement_dans_produit",
           "REPORTES"]
