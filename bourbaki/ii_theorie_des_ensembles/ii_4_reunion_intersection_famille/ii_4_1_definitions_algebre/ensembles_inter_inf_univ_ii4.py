# -*- coding: utf-8 -*-
"""§II.4 — PROPRIÉTÉ UNIVERSELLE de l'intersection d'une famille (caractérisation inf).

DUAL de `ensembles_reunion_sup_univ_ii4`.  ⋂_{ι∈I} X_ι est le PLUS GRAND MINORANT
(au sens de ⊂) de la famille (X_ι)_{ι∈I} :

        ( A ⊂ ⋂_{ι∈I} X_ι )  ⟺  ( (∀k)(k∈I ⇒ A ⊂ X_k) )

════════════════════════════════════════════════════════════════════════════════
RENFORCEMENT D'ÉNONCÉ (migration Déf. 2 « ⋂ par sélection dans ⋃ », 2026-07)
════════════════════════════════════════════════════════════════════════════════
L'ancienne version de ce module démontrait l'équivalence ci-dessus SANS AUCUNE
HYPOTHÈSE.  Cet énoncé était **FAUX** : il reposait sur l'ancien AXIOME_INTER_FAM,
posé sans la restriction « I ≠ ∅ » qu'exige la Déf. 2 de Bourbaki (E II.22), et
cet axiome rendait `theorie_ensembles()` CONTRADICTOIRE (⋂_{ι∈∅} X_ι contenait
tout objet — cf. `outils_ia/audit/preuve_incoherence_inter_vide.py`).

Contre-modèle explicite de l'ancien énoncé, avec la Déf. 2 réparée (⋂_{ι∈∅} = ∅,
certifié par `ensembles_inter_migration_ii4.inter_famille_vide_egale_vide`) :

    I = ∅  et  A ≠ ∅   ⟹   le membre DROIT (∀k)(k∈∅ ⇒ …) est vide-vrai,
                            le membre GAUCHE A ⊂ ⋂_{ι∈∅} X_ι = ∅ est FAUX.

Le sens « ⇐ » est donc réellement conditionné par « I n'est pas vide », exactement
comme l'écrit Bourbaki.  Ce module livre en conséquence DEUX résultats, et sépare
scrupuleusement ce qui survit inconditionnellement de ce qui ne survit pas :

  • `inter_inf_minorante`   — INCONDITIONNEL, énoncé INCHANGÉ (issue A) :
        ⊢ ( A ⊂ ⋂_{ι∈I} X_ι ) ⇒ ( (∀k)(k∈I ⇒ A ⊂ X_k) )
    (⋂ est bien un minorant de la famille ; pure ÉLIMINATION, elle passe par
     `inter_donne_membres` qui est la projection droite de la sélection.)

  • `inter_inf_universelle` — HYPOTHÈSE AJOUTÉE (issue B) :
        ⊢ (∃i)(i∈I) ⇒ ( ( A ⊂ ⋂_{ι∈I} X_ι ) ⟺ ( (∀k)(k∈I ⇒ A ⊂ X_k) ) )
    L'hypothèse (∃i)(i∈I) — `indices_non_vides` — est celle de la Déf. 2.  Le
    théorème reste CLOS (0 hypothèse non déchargée) : l'hypothèse est portée par
    l'énoncé, en antécédent, et non laissée au compteur.

STRATÉGIE.  Sens « ⇒ » : `inter_donne_membres` (inconditionnel).  Sens « ⇐ » :
sous H := (∃i)(i∈I), `caracterisation_inter_famille_non_vide` restitue l'ANCIENNE
équivalence d'appartenance (∀z)( z∈⋂ ⇔ (∀i)(i∈I ⇒ z∈X_i) ) — démontrée, plus
postulée — dont `equivalence_arriere` fournit l'introduction.  Point courant nommé
« z » (binder de ⊂ / A1), capture-safe vis-à-vis du liant « i » des axiomes de
famille et du liant « k » du ∀ externe.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, impl, appartient, pourtout, inclus, equiv)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    inter_donne_membres)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides, caracterisation_inter_famille_non_vide)


def _membres(vf, vI, vA):
    """(A ⊂ ⋂X_ι ,  (∀k)(k∈I ⇒ A ⊂ X_k))  — les deux membres de la caractérisation."""
    vk = var("k")
    gauche = inclus(vA, E.inter_famille(vf, vI))
    droite = pourtout("k", impl(appartient(vk, vI),
                                inclus(vA, E.valeur_famille(vf, vk))))
    return gauche, droite


def cible_inter_inf_minorante(f="X", i="I", a="A"):
    """A ⊂ ⋂X_ι  ⇒  (∀k)(k∈I ⇒ A ⊂ X_k)   — la moitié INCONDITIONNELLE."""
    gauche, droite = _membres(var(f), var(i), var(a))
    return impl(gauche, droite)


def cible_inter_inf_universelle(f="X", i="I", a="A"):
    """(∃i)(i∈I) ⇒ ( A ⊂ ⋂X_ι ⟺ (∀k)(k∈I ⇒ A ⊂ X_k) ).

    ⚠️ L'HYPOTHÈSE (∃i)(i∈I) est NEUVE (migration Déf. 2) : la forme sans
    hypothèse, que ce module affirmait auparavant, est FAUSSE pour I = ∅."""
    gauche, droite = _membres(var(f), var(i), var(a))
    return impl(indices_non_vides(var(i)), equiv(gauche, droite))


# @livre Ch.II §4.1 Prop.- | E II.23 L.13-20 | PDF p.74
# @livre Ch.R §4 Prop.- | E.R.19 item 8 (⋂X_ι ⊂ X_κ) | PDF p.322
def inter_inf_minorante(f="X", i="I", a="A"):
    """⊢ ( A ⊂ ⋂_{ι∈I} X_ι ) ⇒ ( (∀k)(k∈I ⇒ A ⊂ X_k) ).   CLOS — 0 hypothèse.

    INCONDITIONNEL, énoncé INCHANGÉ par la migration (issue A) : c'est la
    direction d'ÉLIMINATION, qui ne consomme que la projection droite de la
    conjonction de sélection (`inter_donne_membres`).  Dit autrement : ⋂ est
    toujours un minorant de la famille, y compris pour I = ∅ (où ⋂ = ∅)."""
    vf, vI, vA = var(f), var(i), var(a)
    vz, vk = var("z"), var("k")
    gauche, _droite = _membres(vf, vI, vA)

    hG = N.assume(gauche)                                   # A ⊂ ⋂
    hk = N.assume(appartient(vk, vI))                       # k ∈ I
    hz = N.assume(appartient(vz, vA))                       # z ∈ A
    z_inter = N.modus_ponens(hz, instancie(hG, vz))         # z ∈ ⋂
    # ÉLIMINATION : z ∈ ⋂ ⇒ (∀i)(i∈I ⇒ z ∈ X_i)  —  inconditionnel.
    forall_i = N.modus_ponens(z_inter,
                              instancie(inter_donne_membres(vf, vI, "z"), vz))
    z_Xk = N.modus_ponens(hk, instancie(forall_i, vk))      # z ∈ X_k
    Xk_sup = N.generalisation("z", N.loi_deduction(appartient(vz, vA), z_Xk))
    imp_k = N.loi_deduction(appartient(vk, vI), Xk_sup)     # k∈I ⇒ A ⊂ X_k
    res = N.loi_deduction(gauche, N.generalisation("k", imp_k))

    assert res.conclusion == cible_inter_inf_minorante(f, i, a), \
        "inter_inf_minorante : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), "inter_inf_minorante : doit être CLOS"
    return res


# @livre Ch.II §4.1 Prop.- | E II.23 L.13-20 | PDF p.74
# @livre Ch.R §4 Prop.- | E.R.19 item 8 (Y⊂X_ι qq soit ι ⇒ Y⊂⋂X_ι) | PDF p.322
def inter_inf_universelle(f="X", i="I", a="A"):
    """⊢ (∃i)(i∈I) ⇒ ( ( A ⊂ ⋂_{ι∈I} X_ι ) ⟺ ( (∀k)(k∈I ⇒ A ⊂ X_k) ) ).   CLOS.

    ⚠️ RENFORCEMENT D'ÉNONCÉ (issue B).  L'hypothèse « I n'est pas vide » de la
    Déf. 2 (E II.22) est désormais EXPLICITE.  L'ancienne forme inconditionnelle
    était FAUSSE : pour I = ∅ on a ⋂_{ι∈∅} X_ι = ∅ tandis que le membre droit est
    vide-vrai, donc n'importe quel A ≠ ∅ la réfute.  Elle ne « tenait » que parce
    que l'ancien AXIOME_INTER_FAM rendait la théorie contradictoire.

    Le théorème reste CLOS : l'hypothèse est portée en antécédent, pas au compteur.
    La moitié « ⇒ » survit sans hypothèse — c'est `inter_inf_minorante`, réutilisée
    telle quelle ici."""
    vf, vI, vA = var(f), var(i), var(a)
    vz, vi = var("z"), var("i")
    gauche, droite = _membres(vf, vI, vA)
    H = indices_non_vides(vI)                               # (∃i)(i ∈ I)

    # ── sens « ⇒ » : inconditionnel ────────────────────────────────────────
    sens_avant = inter_inf_minorante(f, i, a)

    # ── sens « ⇐ » : sous H, on retrouve l'ANCIENNE équivalence d'appartenance ──
    hH = N.assume(H)
    eq_z = instancie(                                       # z∈⋂ ⇔ (∀i)(i∈I ⇒ z∈X_i)
        N.modus_ponens(hH, caracterisation_inter_famille_non_vide(vf, vI, "z")), vz)

    hD = N.assume(droite)                                   # (∀k)(k∈I ⇒ A ⊂ X_k)
    hz = N.assume(appartient(vz, vA))                       # z ∈ A
    hi = N.assume(appartient(vi, vI))                       # i ∈ I
    A_Xi = N.modus_ponens(hi, instancie(hD, vi))            # A ⊂ X_i
    z_Xi = N.modus_ponens(hz, instancie(A_Xi, vz))          # z ∈ X_i
    imp_i = N.loi_deduction(appartient(vi, vI), z_Xi)       # i∈I ⇒ z∈X_i
    corps = N.generalisation("i", imp_i)                    # (∀i)(i∈I ⇒ z∈X_i)
    z_inter = N.modus_ponens(corps, equivalence_arriere(eq_z))          # z ∈ ⋂
    inclusion = N.generalisation("z", N.loi_deduction(appartient(vz, vA), z_inter))
    sens_arriere = N.loi_deduction(droite, inclusion)       # {H} ⊢ droite ⇒ gauche

    res = N.loi_deduction(H, conjonction_intro(sens_avant, sens_arriere))

    assert res.conclusion == cible_inter_inf_universelle(f, i, a), \
        "inter_inf_universelle : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), "inter_inf_universelle : doit être CLOS"
    return res


__all__ = ["cible_inter_inf_minorante", "inter_inf_minorante",
           "cible_inter_inf_universelle", "inter_inf_universelle"]
