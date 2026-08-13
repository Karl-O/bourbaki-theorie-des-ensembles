# -*- coding: utf-8 -*-
"""§II.5.3 — LE PRODUIT D'INDEX VIDE :  ∏_{ι∈∅} X_ι = {∅}.                [CLOS]

Le livre, E II.32 L.22-23 : « Si I = ∅, l'ensemble ∏_{ι∈I} X_ι ne possède qu'un
seul élément, savoir l'ensemble vide (II, p. 14, Exemple 1). »  C'est CETTE phrase
que E III.41 L.30 invoque — « On a 0! = 1 (II, p. 32) » — pour le cas de base de
la Définition 2 de la factorielle.  Ce module la démontre, sans résidu.

  • `produit_famille_vide_est_singleton_vide(u)`  ⊢ ∏(u, ∅) = {∅}     [CLOS, 0 hyp]

────────────────────────────────────────────────────────────────────────────────
POURQUOI CE THÉORÈME N'ÉTAIT PAS DÉMONTRABLE AVANT LE 2026-07-26.

Le sens ⊂ (« tout élément du produit est vide ») repose sur le corollaire E II.10
« si pr₁G = ∅ alors G = ∅ », dont l'hypothèse est *G est un ensemble de couples*.
Or `AXIOME_PRODUIT_FAM` avait perdu à la transcription son conjoint de TÊTE
« F ⊂ I × ⋃_{ι∈I} X_ι » ; les trois conjoints restants (fonctionnel, dom, valeurs)
ne LISENT que les couples de F et ne disent RIEN de ses autres éléments.  « F est
un graphe » devait donc être PORTÉ COMME HYPOTHÈSE — et cette hypothèse était, pour
I = ∅, RÉFUTABLE (témoin {∅}, cf. `ensembles_produit_famille_graphe`) : tout
théorème qui la portait était VACUEUX.  Le conjoint rétabli en fait un théorème
(`produit_graphe`, via les briques B1/B2) ; l'hypothèse est ici DÉCHARGÉE, pas
supposée, et le résultat est clos sous les 22 axiomes seuls.

⚠️ PIÈGE DE LECTURE (à ne pas confondre avec une contradiction).  Ce module et
`singleton_vide_hors_produit_vide` disent des choses COMPATIBLES :
      ∏(u,∅) = {∅}          (l'unique élément du produit est ∅, la FONCTION VIDE)
      ¬( {∅} ∈ ∏(u,∅) )     (le SINGLETON {∅}, lui, n'est pas dans le produit)
Ensemble elles donnent ¬({∅} ∈ {∅}) — vrai, et nullement absurde.  C'est ∅ qui est
élément du produit, pas {∅}.

⚠️ PIÈGE α, mesuré.  `E.est_un_graphe` (abrégé, liants « x,y ») et `est_graphe`
(§II.3.1, liants « a,b ») sont α-variantes et le noyau NE les identifie PAS : le
passage se fait par `alpha_bridge`, jamais en supposant les deux formes.

FRONTIÈRE.  Aucun axiome ajouté, aucun `Theoreme` fabriqué : tout passe par les
primitives `N.*` et par la recette d'écriture `ensembles_produit_ecriture`.
`theorie_ensembles()` vaut 22 avant comme après (asserté en test).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, non, appartient, inclus, libres_t,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    antecedent_consequent,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    alpha_pour_tout,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    vide_inclus_partout,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_graphe_inclus_produit import (
    est_graphe, projection_vide_implique_graphe_vide,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    instance_membre, composants_membre, graphe_du_point, corps_membre,
)

#: Liant du point courant du produit (exotique : les dépendances imposent z/x/y/a/b).
_LIANT_F = "Fpv"
#: Trou des congruences de Leibniz de ce module (exotique, vérifié absent).
_TROU = "wpv"
#: Liants et trous qu'un `u` LIBRE ne doit pas heurter (capture silencieuse).
_NOMS_RESERVES = frozenset({_LIANT_F, _TROU, "z", "i", "x", "y", "a", "b",
                            "p", "q", "u", "v", "w"})


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _garde(vu):
    """Refuse un `u` dont un nom LIBRE heurterait un liant/trou des dépendances."""
    heurts = _NOMS_RESERVES & libres_t(vu)
    assert not heurts, \
        "produit d'index vide : nom libre de u heurtant un liant réservé %s" % sorted(heurts)


def _dech(premisse, but):
    """Décharge la conclusion de `premisse` de `but`, puis coupe (MP)."""
    return N.modus_ponens(premisse, N.loi_deduction(premisse.conclusion, but))


def _leibniz(thm_eq, gabarit):
    """De Γ ⊢ F = ∅ et d'un gabarit R{_TROU}, rendre Γ ⊢ ( R{F} ⇔ R{∅} )."""
    gauche, droite = thm_eq.conclusion.termes
    return N.modus_ponens(thm_eq, N.s6(gauche, droite, _TROU, gabarit))


def _sens_direct(vu, vF):
    """⊢ ( F ∈ ∏(u,∅) ⇒ F ∈ {∅} ).   [CLOS] — un élément du produit EST vide.

    C'est la moitié qui a coûté la réparation de l'axiome.  Le conjoint de TÊTE
    donne F ⊂ ∅ × ⋃X_ι, donc (B1) « F est un graphe » ; avec dom F = ∅, le
    corollaire E II.10 conclut F = ∅.  Les deux hypothèses du corollaire sont
    DÉCHARGÉES par ces théorèmes-là : rien n'est supposé."""
    membre = appartient(vF, E.produit_famille(vu, E.VIDE))
    h = N.assume(membre)
    incl, _func, dom_eq, _vals = composants_membre(h, vu, E.VIDE, vF)
    graphe = graphe_du_point(incl, vF, E.VIDE, vu)          # est_un_graphe(F), abrégé
    graphe = alpha_bridge(graphe, est_graphe(vF))           # → forme §II.3.1 « a,b »
    cor = projection_vide_implique_graphe_vide(_LIANT_F)    # {graphe, dom=∅} ⊢ F = ∅
    F_vide = _dech(dom_eq, _dech(graphe, cor))
    dans_sgl = N.modus_ponens(F_vide, equivalence_arriere(singleton_membre(vF, E.VIDE)))
    res = N.loi_deduction(membre, dans_sgl)
    assert res.est_clos, "sens ⊂ : devrait être CLOS depuis la réparation de l'axiome"
    return res


def _conjoints_du_vide(vu, vF, F_vide):
    """Les QUATRE conjoints de la Déf. 1 pour le point F = ∅, sous { F ∈ {∅} }.

    (1) tête : ∅ ⊂ ∅ × ⋃X_ι — le vide est inclus dans tout (E II.6) ;
    (2) fonctionnel et (3) domaine : les faits sur le graphe vide, transportés à F
        par Leibniz le long de F = ∅ ;
    (4) valeurs : VACUEUSEMENT, rien n'appartenant à ∅ (AXIOME_VIDE).  Le liant
        est « i », celui de `AXIOME_PRODUIT_FAM` — il est lu sur l'axiome, non deviné."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux \
        .iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
            vide_est_fonctionnel, dom_vide_egale_vide)
    vw = var(_TROU)
    prod_ambiant = E.produit(E.VIDE, E.reunion_famille(vu, E.VIDE))
    tete = N.modus_ponens(vide_inclus_partout(prod_ambiant),
                          equivalence_arriere(_leibniz(F_vide, inclus(vw, prod_ambiant))))
    func = N.modus_ponens(vide_est_fonctionnel(),
                          equivalence_arriere(_leibniz(F_vide, E.est_fonctionnel(vw))))
    dom_v = N.modus_ponens(dom_vide_egale_vide(),
                           equivalence_arriere(_leibniz(F_vide, egal(E.dom(vw), E.VIDE))))
    vi = var("i")
    rien = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vi)      # ¬(i ∈ ∅)
    vals = N.generalisation("i", N.modus_ponens(rien, N.s2(
        non(appartient(vi, E.VIDE)),
        appartient(E.valeur(vF, vi), E.valeur_famille(vu, vi)))))
    return tete, func, dom_v, vals


def _sens_reciproque(vu, vF):
    """⊢ ( F ∈ {∅} ⇒ F ∈ ∏(u,∅) ).   [CLOS] — ∅ EST dans le produit, et il est CONSTRUIT.

    Aucune hypothèse de non-vacuité : le témoin ∅ existe par AXIOME_VIDE.  Le corps
    reconstruit est comparé PAR ÉGALITÉ EXACTE au corps de l'axiome — si l'ordre
    des quatre conjoints rebougeait, ce site casserait au lieu de dériver."""
    eq_ax = instance_membre(vu, E.VIDE, vF)
    dans_sgl = appartient(vF, E.singleton(E.VIDE))
    h_sgl = N.assume(dans_sgl)
    F_vide = N.modus_ponens(h_sgl, equivalence_avant(singleton_membre(vF, E.VIDE)))
    corps = corps_membre(*_conjoints_du_vide(vu, vF, F_vide))
    _, corps_cible = antecedent_consequent(equivalence_avant(eq_ax).conclusion)
    assert corps.conclusion == corps_cible, \
        "sens ⊃ : corps reconstruit ≠ corps de AXIOME_PRODUIT_FAM"
    res = N.loi_deduction(dans_sgl, N.modus_ponens(corps, equivalence_arriere(eq_ax)))
    assert res.est_clos, "sens ⊃ : devrait être CLOS (le témoin ∅ est construit)"
    return res


def produit_famille_vide_enonce(u="upv"):
    """Formule cible :  ∏_{ι∈∅} X_ι = {∅}   — pour vérification stricte hors module."""
    vu = _t(u)
    return egal(E.produit_famille(vu, E.VIDE), E.singleton(E.VIDE))


# @livre Ch.II §5.3 Rem.- | E II.32 L.22-23 | PDF p.83
#   (« Si I = ∅, l'ensemble ∏_{ι∈I} X_ι ne possède qu'un seul élément, savoir
#    l'ensemble vide (II, p. 14, Exemple 1). » — c'est le renvoi que E III.41 L.30
#    invoque pour « On a 0! = 1 (II, p. 32) ».)
def produit_famille_vide_est_singleton_vide(u="upv"):
    """🎯 ⊢ ∏_{ι∈∅} X_ι = {∅}.        [CLOS, 0 hypothèse, pour u QUELCONQUE]

    Double inclusion puis extensionnalité (A1) :
      ⊂  un élément du produit est un graphe (conjoint de tête + B1) de domaine ∅,
         donc vide (E II.10) ;
      ⊃  ∅ vérifie les quatre conjoints de la Déf. 1 pour I = ∅.
    ⚠️ A1 écrit ses inclusions au liant « z » : les deux ∀-clôtures sont
    α-converties de `_LIANT_F` vers « z » AVANT le modus ponens."""
    vu = _t(u)
    _garde(vu)
    vF = var(_LIANT_F)
    direct, recip = _sens_direct(vu, vF), _sens_reciproque(vu, vF)
    prod, sgl = E.produit_famille(vu, E.VIDE), E.singleton(E.VIDE)
    incl1 = N.modus_ponens(N.generalisation(_LIANT_F, direct),
                           equivalence_avant(alpha_pour_tout(_LIANT_F, "z", direct.conclusion)))
    incl2 = N.modus_ponens(N.generalisation(_LIANT_F, recip),
                           equivalence_avant(alpha_pour_tout(_LIANT_F, "z", recip.conclusion)))
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), prod), sgl)
    res = N.modus_ponens(conjonction_intro(incl1, incl2), a1)
    assert res.conclusion == produit_famille_vide_enonce(vu), \
        "produit_famille_vide_est_singleton_vide : conclusion ≠ ∏(u,∅) = {∅}"
    assert res.est_clos and res.hypotheses == frozenset(), \
        "produit_famille_vide_est_singleton_vide : hypothèses résiduelles %r" % (res.hypotheses,)
    return res


__all__ = ["produit_famille_vide_enonce", "produit_famille_vide_est_singleton_vide"]
