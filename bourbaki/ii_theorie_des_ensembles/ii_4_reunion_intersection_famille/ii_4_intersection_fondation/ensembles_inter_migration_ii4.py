# -*- coding: utf-8 -*-
"""§II.4.1 Déf. 2 — PONT DE MIGRATION : l'ancien axiome récupéré, la pathologie morte.

Deux livrables, tous deux CLOS (0 hypothèse), au-dessus de la fondation
`ensembles_inter_selection_ii4` (⋂ = sélection dans ⋃, route Grimm B5).

────────────────────────────────────────────────────────────────────────────────
A. LE PONT.  `caracterisation_inter_famille_non_vide` :

      ⊢ (∃i)(i∈I) ⇒ (∀z)( z ∈ ⋂_{ι∈I} X_ι ⇔ (∀i)((i∈I) ⇒ z∈X_i) )

C'est EXACTEMENT l'ancien `AXIOME_INTER_FAM`, mais DÉMONTRÉ, et sous l'hypothèse
que Bourbaki écrit noir sur blanc (E II.22, PDF p.73, Déf. 2 : « … dont l'ensemble
d'indices I n'est pas vide »).  Tout site d'usage qui dispose d'un indice retrouve
son énoncé par ce lemme ; ceux qui n'utilisent que l'élimination n'ont même pas
besoin de lui (`inter_donne_membres` est inconditionnel).

STRATÉGIE.  Sous H := (∃i)(i∈I), `N.existe_temoin` livre le témoin canonique
T₀ := τi(i∈I) avec T₀ ∈ I.  `inter_par_membres_si_temoin_terme` — dont c'est la
raison d'être d'accepter un TERME — fournit alors la direction d'introduction ;
l'élimination est inconditionnelle ; `conjonction_intro` recolle l'équivalence ;
généralisation sur z (licite : H ne contient pas z libre), puis C14 décharge H.

`caracterisation_inter_famille_indices_non_vide` en donne la forme LITTÉRALE du
livre, « I n'est pas vide » :

      ⊢ ¬(I = ∅) ⇒ (∀z)( z ∈ ⋂_{ι∈I} X_ι ⇔ (∀i)((i∈I) ⇒ z∈X_i) )

La brique reliant ¬(I=∅) à (∃i)(i∈I) EXISTE déjà : `ensembles_vide.non_vide_ssi_element`
(⊢ ¬(A=∅) ⇔ (∃z)(z∈A)).  Son liant est « z » et le nôtre « i » ; les α-variants ne
sont PAS identifiés par le noyau, d'où le passage par `alpha_bridge` (pont α certifié,
jamais un renommage de liant τ externe).

────────────────────────────────────────────────────────────────────────────────
B. LA PATHOLOGIE EST MORTE.  `inter_famille_vide_est_vide` :

      ⊢ (∀z) ¬( z ∈ ⋂_{ι∈∅} X_ι )       et      ⊢ ⋂_{ι∈∅} X_ι = ∅

Route : ⋂_{ι∈∅} ⊂ ⋃_{ι∈∅} (projection GAUCHE de la sélection, `inter_inclus_reunion`
instancié à I:=∅) ; or ⋃_{ι∈∅} X_ι = ∅ est déjà certifié (`ensembles_familles.
reunion_famille_vide`, note de la Déf. 1) ; contraposition.  Avec l'ANCIEN axiome
ce même ⋂_{ι∈∅} X_ι contenait TOUT objet, ce qui contredisait
`ensembles_pas_ensemble_universel` (E II.6, Remarque) — la contradiction machine de
`outils_ia/audit/preuve_incoherence_inter_vide.py`.

INVARIANTS
  • `theorie_ensembles()` reste à 22 axiomes ; le seul postulat neuf est
    AXIOME_INTER_FAM_SEL, porté par sa théorie dédiée.  Aucun fichier existant touché.
  • Liants « i » (indice) et « z » (élément) imposés ; « z » est aussi celui de
    `vide_ssi_sans_element` / `inclus` / A1, d'où la compatibilité directe.
  • Les quatre résultats sont CLOS — vérifié par assertion à chaque appel.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, Formule, var, egal, non, impl, equiv, appartient, existe, pourtout, tau)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, contraposition, equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    vide_ssi_sans_element, non_vide_ssi_element)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import (
    reunion_famille_vide)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    corps_membres_famille, inter_donne_membres, inter_inclus_reunion,
    inter_par_membres_si_temoin_terme)

_IDX = var("i")


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def indices_non_vides(i_set="I", i: str = "i") -> Formule:
    """(∃i)(i ∈ I)  — « l'ensemble d'indices I n'est pas vide », forme utilisable."""
    return existe(i, appartient(var(i), _t(i_set)))


# ── A. Le pont de migration ───────────────────────────────────────────────────
def enonce_caracterisation_inter_famille(f="f", i_set="I", z="z") -> Formule:
    """(∀z)( z ∈ ⋂_{ι∈I} X_ι ⇔ (∀i)((i∈I) ⇒ z∈X_i) )  — l'ANCIEN AXIOME_INTER_FAM."""
    vf, vI, vz = _t(f), _t(i_set), var(z)
    return pourtout(z, equiv(appartient(vz, E.inter_famille(vf, vI)),
                             corps_membres_famille(vf, vI, vz)))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (LE lemme de migration : la Déf. 2 récupérée sous son hypothèse « I n'est pas vide »)
def caracterisation_inter_famille_non_vide(f="f", i_set="I", z="z"):
    """⊢ (∃i)(i∈I) ⇒ (∀z)( z ∈ ⋂_{ι∈I} X_ι ⇔ (∀i)((i∈I) ⇒ z∈X_i) ).   CLOS.

    L'ancien AXIOME_INTER_FAM, désormais DÉMONTRÉ sous l'hypothèse de la Déf. 2.
    Témoin canonique T₀ := τi(i∈I) fourni par `N.existe_temoin` (identité-τ)."""
    vf, vI, vz = _t(f), _t(i_set), var(z)
    H = indices_non_vides(vI)
    T0 = tau("i", appartient(_IDX, vI))                       # τi(i∈I)

    h = N.assume(H)
    t_in_I = N.modus_ponens(h, N.existe_temoin(appartient(_IDX, vI), "i"))   # T₀ ∈ I
    bwd = N.modus_ponens(t_in_I,                              # corps ⇒ z∈⋂
                         inter_par_membres_si_temoin_terme(vf, vI, T0, vz))
    fwd = instancie(inter_donne_membres(vf, vI, z), vz)       # z∈⋂ ⇒ corps
    res = N.loi_deduction(H, N.generalisation(z, conjonction_intro(fwd, bwd)))

    assert res.conclusion == impl(H, enonce_caracterisation_inter_famille(vf, vI, z)), \
        "caracterisation_inter_famille_non_vide : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), \
        "caracterisation_inter_famille_non_vide : doit être CLOS (0 hypothèse)"
    return res


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (forme LITTÉRALE du livre : « dont l'ensemble d'indices I n'est pas vide »)
def caracterisation_inter_famille_indices_non_vide(f="f", i_set="I", z="z"):
    """⊢ ¬(I = ∅) ⇒ (∀z)( z ∈ ⋂_{ι∈I} X_ι ⇔ (∀i)((i∈I) ⇒ z∈X_i) ).   CLOS.

    Corollaire du pont, mis sous la forme que Bourbaki écrit.  Le maillon
    ¬(I=∅) ⇔ (∃z)(z∈I) est `ensembles_vide.non_vide_ssi_element` (il EXISTE, il
    n'a pas fallu le bricoler) ; `alpha_bridge` rend le liant « i » attendu."""
    vf, vI, vz = _t(f), _t(i_set), var(z)
    hyp = non(egal(vI, E.VIDE))
    h = N.assume(hyp)
    ez = N.modus_ponens(h, equivalence_avant(non_vide_ssi_element(vI)))  # (∃z)(z∈I)
    ei = alpha_bridge(ez, indices_non_vides(vI))                         # (∃i)(i∈I)
    core = N.modus_ponens(ei, caracterisation_inter_famille_non_vide(vf, vI, z))
    res = N.loi_deduction(hyp, core)

    assert res.conclusion == impl(hyp, enonce_caracterisation_inter_famille(vf, vI, z)), \
        "caracterisation_inter_famille_indices_non_vide : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), \
        "caracterisation_inter_famille_indices_non_vide : doit être CLOS"
    return res


# ── B. La pathologie est morte ────────────────────────────────────────────────
def enonce_inter_famille_vide_est_vide(f="f", z="z") -> Formule:
    return pourtout(z, non(appartient(var(z), E.inter_famille(_t(f), E.VIDE))))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (la note en petits caractères de la Déf. 2 : le cas I=∅, qui n'est PLUS une pathologie)
def inter_famille_vide_est_vide(f="f", z="z"):
    """⊢ (∀z) ¬( z ∈ ⋂_{ι∈∅} X_ι ).   CLOS — l'ensemble universel a disparu.

    ⋂_{ι∈∅} ⊂ ⋃_{ι∈∅} (projection gauche de la sélection) et ⋃_{ι∈∅} X_ι = ∅
    (`reunion_famille_vide`, note de la Déf. 1) ; contraposition sur z.
    `f` est un NOM de variable (contrat de `reunion_famille_vide`, que l'on réutilise)."""
    assert isinstance(f, str), "inter_famille_vide_est_vide : f doit être un NOM de variable"
    vf, vz = var(f), var(z)
    U = E.reunion_famille(vf, E.VIDE)
    sans_U = N.modus_ponens(reunion_famille_vide(f),           # (∀z)¬(z∈⋃_{ι∈∅})
                            equivalence_avant(vide_ssi_sans_element(U)))
    imp = instancie(inter_inclus_reunion(vf, E.VIDE, z), vz)   # z∈⋂_∅ ⇒ z∈⋃_∅
    nz = N.modus_ponens(instancie(sans_U, vz), contraposition(imp))
    res = N.generalisation(z, nz)

    assert res.conclusion == enonce_inter_famille_vide_est_vide(vf, z), \
        "inter_famille_vide_est_vide : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), "inter_famille_vide_est_vide : doit être CLOS"
    return res


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (⋂ sur l'ensemble d'indices vide = ∅ — le CHOIX de Grimm, cf. RR-6999-v7 p.35 §2.7)
def inter_famille_vide_egale_vide(f="f"):
    """⊢ ⋂_{ι∈∅} X_ι = ∅.   CLOS — la forme ensembliste de la mort de la pathologie.

    Bourbaki laisse ⋂_{ι∈∅} INDÉFINIE (Déf. 2 exige I≠∅) et le Résumé E.R.19 la
    fixe à E dans le monde des familles de PARTIES de E ; la sélection dans ⋃ la
    fixe à ∅, sans dépendre d'un E de contexte — c'est précisément l'argument de
    Grimm (« We do not like this definition, since it depends on the context »)."""
    vf = var(f)
    res = N.modus_ponens(inter_famille_vide_est_vide(f),
                         equivalence_arriere(vide_ssi_sans_element(
                             E.inter_famille(vf, E.VIDE))))
    assert res.conclusion == egal(E.inter_famille(vf, E.VIDE), E.VIDE), \
        "inter_famille_vide_egale_vide : conclusion ≠ (⋂_{ι∈∅} X_ι = ∅)"
    assert res.hypotheses == frozenset(), "inter_famille_vide_egale_vide : doit être CLOS"
    return res


__all__ = ["indices_non_vides", "enonce_caracterisation_inter_famille",
           "caracterisation_inter_famille_non_vide",
           "caracterisation_inter_famille_indices_non_vide",
           "enonce_inter_famille_vide_est_vide", "inter_famille_vide_est_vide",
           "inter_famille_vide_egale_vide"]
