"""§II.5.5 / §III.3.3 — ADJONCTION D'INDICE au produit d'une famille (T1b-(2)) : Φ.

Sous j∉I, ∏_{ι∈I∪{j}} u_ι se décompose en (∏_{ι∈I} u_ι) × u_j (Rem. 1 de la
Prop. 7, E II.35 : partition (I, {j}), facteur singleton identifié à u_j).  La
bijection-témoin est l'ADJONCTION  Φ : F ↦ (F|I, F(j)),  de graphe (C54)

    Φ := graphe_terme( ∏_{ι∈I∪{j}} u_ι ,  (Fq|I, valeur(Fq, j, b="c")) ,  "Fq" ).

LIANTS (levée du verrou liant valeur, motif prop2_conjugaison_surjective) : liant
de graphe « Fq » (exotique), τ-liant de la valeur F(j) DANS le terme « c » (frais,
≠ « y » de la machinerie graphe_terme/AXIOME_DOM) ; le pont valeur_y_egal_c
(alpha_tau/CS1) recolle les deux écritures de F(j).

Ce module : les TERMES de l'énoncé, les 3 HYPOTHÈSES HONNÊTES (H1 j∉I ; H2/H3
« les points du produit sont des graphes » — AXIOME_PRODUIT_FAM n'expose que
fonctionnel ∧ dom ∧ valeurs, PAS « tout élément est un couple », vrai dans la
théorie complète mais hors de l'axiome encodé, cf. extensionnalite_produit), le
membership de I∪{j} et du produit, et les paliers :
  P1 adjonction_fonctionnelle   ⊢ est_fonctionnel(Φ)                      [CLOS]
  P2 adjonction_valeur          {G ∈ ∏_{I∪{j}}} ⊢ Φ(G) = (G|I, G(j)[τc])  [1 hyp]
  P3 adjonction_domaine         ⊢ dom Φ = ∏_{I∪{j}}                       [CLOS]
Suite : ..._adjonction_briques (restriction/prolongement), ..._adjonction_bij
(P4-P7 : image, injectivité, bijection, Eq, Card).  Rien postulé ; noyau/subst
intouchés ; theorie_ensembles() = 22 (asserté en test).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout, inclus, subst_t)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, equivalence_avant,
    equivalence_arriere, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur, graphe_terme_domaine)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_ecriture import (
    composants_membre, conjoint_de_tete, corps_membre, graphe_du_point, instance_membre)

XB = "Fq"      # liant (C54) du graphe-terme de l'adjonction — exotique
VC = "c"       # τ-liant de la valeur F(j) DANS le terme (frais ≠ y ; lettre simple)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _dech(res, *premisses):
    """Décharge en chaîne : pour chaque prémisse-théorème p (dont la conclusion est
    une hypothèse ASSUMÉE de res), loi de déduction puis modus ponens."""
    for p in premisses:
        res = N.modus_ponens(p, N.loi_deduction(p.conclusion, res))
    return res


# ── Termes de l'énoncé ────────────────────────────────────────────────────────
def indices_adjoints(i="Iq", j="jq"):
    """I∪{j}  (l'ensemble d'indices après adjonction du nouvel indice j)."""
    return E.reunion(_t(i), E.singleton(_t(j)))


def produit_total(u="uq", i="Iq", j="jq"):
    """∏_{ι∈I∪{j}} u_ι  (le produit sur les indices adjoints — la SOURCE de Φ)."""
    return E.produit_famille(_t(u), indices_adjoints(i, j))


def produit_cible(u="uq", i="Iq", j="jq"):
    """(∏_{ι∈I} u_ι) × u_j  (le produit binaire — le BUT de Φ)."""
    vu = _t(u)
    return E.produit(E.produit_famille(vu, _t(i)), E.valeur_famille(vu, _t(j)))


def terme_adjonction(i="Iq", j="jq"):
    """T := (Fq|I, valeur(Fq, j, b="c"))  — le terme C54 de F ↦ (F|I, F(j))."""
    return E.couple(E.restriction(var(XB), _t(i)), E.valeur(var(XB), _t(j), b=VC))


# @livre Ch.II §5.5 Rem.1 | E II.35 L.15-22 | PDF p.86
#   (la bijection canonique ∏_{ι∈I∪{j}} → ∏_I × u_j de la Rem. 1 — partition (I,{j}),
#    facteur singleton identifié à u_j : c'est l'application F ↦ (F|I, F(j)).)
def graphe_adjonction(u="uq", i="Iq", j="jq"):
    """Φ := graphe_terme(∏_{I∪{j}}, T, "Fq")  (le graphe de l'adjonction, C54)."""
    return E.graphe_terme(produit_total(u, i, j), terme_adjonction(i, j), XB)


def valeur_y_egal_c(f, x):
    """⊢ valeur(f, x) = valeur(f, x, b="c")   (pont α-τ y→c, CS1 ; f, x termes)."""
    return N.alpha_tau(appartient(E.couple(_t(x), var("y")), _t(f)), "y", VC)


# ── Les trois hypothèses honnêtes de la bijection ─────────────────────────────
def hypothese_indice_neuf(i="Iq", j="jq"):
    """H1 := ¬(j ∈ I)   (le nouvel indice n'est pas déjà dans I)."""
    return non(appartient(_t(j), _t(i)))


def hypothese_graphes_total(u="uq", i="Iq", j="jq"):
    """H2 := (∀G)(G ∈ ∏_{I∪{j}} ⇒ est_un_graphe(G))   (points = graphes).

    ⚠️ N'EST PLUS UNE HYPOTHÈSE NÉCESSAIRE depuis le 26 juil. 2026 : le conjoint de
    tête « F ⊂ I×⋃X_ι » rétabli dans `AXIOME_PRODUIT_FAM` la DÉMONTRE (cf.
    `ii_5_definitions.ensembles_produit_famille.produit_graphe`, CLOS).  Elle est
    conservée telle quelle pour ne pas changer, dans la même passe, l'énoncé des
    théorèmes de `..._adjonction_bij` qui la portent ; son DÉCHARGEMENT est un
    chantier suivant, mécanique (instancier `produit_graphe` sur ∏_{I∪{j}}).
    Rappel : sous l'ANCIEN encodage, cette forme d'hypothèse était RÉFUTABLE pour
    I = ∅ — tout ce qui s'en déduisait y était vacueux."""
    return pourtout("G", impl(appartient(var("G"), produit_total(u, i, j)),
                              E.est_un_graphe(var("G"))))


def hypothese_graphes_partiel(u="uq", i="Iq", j="jq"):
    """H3 := (∀G)(G ∈ ∏_I ⇒ est_un_graphe(G))   (idem pour le produit partiel).

    Même statut que H2 ci-dessus : DÉMONTRABLE depuis la réparation de l'axiome."""
    return pourtout("G", impl(appartient(var("G"), E.produit_famille(_t(u), _t(i))),
                              E.est_un_graphe(var("G"))))


# ── Membership de I∪{j} ───────────────────────────────────────────────────────
def _car_union(i, j, tt):
    """⊢ (t ∈ I∪{j}) ⇔ ((t∈I) ou (t∈{j}))   (AXIOME_REUNION instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    return instancie(instancie(instancie(ax, _t(i)), E.singleton(_t(j))), _t(tt))


def i_dans_union(i="Iq", j="jq", tt="i"):
    """{t ∈ I} ⊢ t ∈ I∪{j}.   (facteur gauche de la réunion.)"""
    vt = _t(tt)
    h = N.assume(appartient(vt, _t(i)))
    disj = N.modus_ponens(h, N.s2(appartient(vt, _t(i)), appartient(vt, E.singleton(_t(j)))))
    return N.modus_ponens(disj, equivalence_arriere(_car_union(i, j, vt)))


def j_dans_union(i="Iq", j="jq"):
    """⊢ j ∈ I∪{j}.   (le nouvel indice est dans la réunion ; CLOS.)"""
    vj = _t(j)
    j_in_s = N.modus_ponens(N.reflexivite(vj), equivalence_arriere(singleton_membre(vj, vj)))
    inS, inI = appartient(vj, E.singleton(vj)), appartient(vj, _t(i))
    disj = N.modus_ponens(N.modus_ponens(j_in_s, N.s2(inS, inI)), N.s3(inS, inI))
    res = N.modus_ponens(disj, equivalence_arriere(_car_union(i, j, vj)))
    assert res.est_clos, "j_dans_union : non clos"
    return res


def inclusion_I_union(i="Iq", j="jq"):
    """⊢ I ⊂ I∪{j}.   (liant « z », forme exacte de inclus ; CLOS.)"""
    vz = var("z")
    res = N.generalisation("z", N.loi_deduction(appartient(vz, _t(i)),
                                                i_dans_union(i, j, vz)))
    assert res.conclusion == inclus(_t(i), indices_adjoints(i, j)), "inclusion_I_union : forme"
    return res


# ── Membership du produit (AXIOME_PRODUIT_FAM, term-safe) ─────────────────────
def _inst_fam(fam, idx, ff):
    """⊢ (F ∈ ∏_{ι∈idx}) ⇔ (F ⊂ idx×⋃u_ι ∧ func F ∧ dom F = idx ∧ (∀i)(i∈idx ⇒ F(i)∈u_i)).

    Alias term-safe de `ii_5_definitions.ensembles_produit_ecriture.instance_membre`
    (le corps a QUATRE conjoints depuis la réparation du 26 juil. 2026)."""
    return instance_membre(fam, idx, ff)


def _corps_membre(h, fam, idx, ff):
    """De Γ ⊢ F∈∏, extraire (Γ⊢F⊂idx×⋃u_ι, Γ⊢func F, Γ⊢dom F=idx, Γ⊢∀i-valeurs).

    ⚠️ Rend QUATRE composants depuis le 26 juil. 2026 (le conjoint de TÊTE de la
    Déf. 1 a été rétabli).  Les chemins d'accès ne sont PAS écrits ici : ils le
    sont une seule fois, dans `ensembles_produit_ecriture.composants_membre`."""
    return composants_membre(h, fam, idx, ff)


def _leibniz_membre(thm_x_in_a, eq_a_b, x):
    """Γ ⊢ x∈A, Δ ⊢ A=B  ⟹  Γ∪Δ ⊢ x∈B   (Leibniz S6 sur le 2ᵉ argument de ∈)."""
    a, b = eq_a_b.conclusion.termes
    leib = N.modus_ponens(eq_a_b, N.s6(a, b, "w", appartient(_t(x), var("w"))))
    return N.modus_ponens(thm_x_in_a, equivalence_avant(leib))


def _leibniz_membre_arriere(thm_x_in_b, eq_a_b, x):
    """Γ ⊢ x∈B, Δ ⊢ A=B  ⟹  Γ∪Δ ⊢ x∈A   (sens ⇐ du même Leibniz)."""
    a, b = eq_a_b.conclusion.termes
    leib = N.modus_ponens(eq_a_b, N.s6(a, b, "w", appartient(_t(x), var("w"))))
    return N.modus_ponens(thm_x_in_b, equivalence_arriere(leib))


# ── P1 / P3 / P2 : le graphe Φ est une fonction sur tout ∏_{I∪{j}} ────────────
def adjonction_fonctionnelle(u="uq", i="Iq", j="jq"):
    """P1 ⊢ est_fonctionnel(Φ).   (C54, graphe_terme_fonctionnel ; CLOS.)"""
    res = graphe_terme_fonctionnel(produit_total(u, i, j), terme_adjonction(i, j), XB, "y")
    assert res.conclusion == E.est_fonctionnel(graphe_adjonction(u, i, j)), "P1 : forme"
    assert res.est_clos, "P1 : non clos"
    return res


def adjonction_domaine(u="uq", i="Iq", j="jq"):
    """P3 ⊢ dom Φ = ∏_{I∪{j}}.   (graphe_terme_domaine ; CLOS.)"""
    res = graphe_terme_domaine(produit_total(u, i, j), terme_adjonction(i, j), XB, "y", "z")
    assert res.conclusion == egal(E.dom(graphe_adjonction(u, i, j)),
                                  produit_total(u, i, j)), "P3 : forme"
    assert res.est_clos, "P3 : non clos"
    return res


def adjonction_valeur(g="Gq", u="uq", i="Iq", j="jq"):
    """P2 {G ∈ ∏_{I∪{j}}} ⊢ Φ(G) = (G|I, valeur(G, j, b="c")).   (g : NOM.)

    Hypothèse honnête : G est dans le domaine du graphe.  Le τ-liant de la
    2ᵉ composante est « c » (celui du terme T — pont valeur_y_egal_c au besoin)."""
    res = graphe_terme_valeur(produit_total(u, i, j), terme_adjonction(i, j), g, XB, "y")
    vg = var(g)
    cible = egal(E.valeur(graphe_adjonction(u, i, j), vg),
                 subst_t(vg, XB, terme_adjonction(i, j)))
    assert res.conclusion == cible, "P2 : forme"
    assert res.hypotheses == frozenset({appartient(vg, produit_total(u, i, j))}), "P2 : hyps"
    return res


__all__ = ["XB", "VC", "indices_adjoints", "produit_total", "produit_cible",
           "terme_adjonction", "graphe_adjonction", "valeur_y_egal_c",
           "hypothese_indice_neuf", "hypothese_graphes_total", "hypothese_graphes_partiel",
           "i_dans_union", "j_dans_union", "inclusion_I_union",
           "adjonction_fonctionnelle", "adjonction_domaine", "adjonction_valeur"]
