# -*- coding: utf-8 -*-
"""§II.4.1 Déf. 2 — ⋂_{ι∈I} X_ι défini par SÉLECTION dans ⋃_{ι∈I} X_ι (route Grimm B5).

ÉNONCÉ DE L'AXIOME (le seul postulat de ce dossier) :

    (∀f)(∀I)(∀z)( z ∈ ⋂_{ι∈I} X_ι  ⇔  ( z ∈ ⋃_{ι∈I} X_ι
                                          ∧ (∀i)((i∈I) ⇒ (z ∈ X_i)) ) )

LÉGITIMITÉ.  S8 (schéma de sélection-réunion, E II.4) + A1 (extensionnalité, unicité).
La réunion ⋃_{ι∈I} X_ι EXISTE inconditionnellement (Déf. 1, E II.22 : la relation
(∃ι)(ι∈I et x∈X_ι) est collectivisante en x, sans hypothèse sur I) ; sélectionner
dedans est donc toujours licite.  C'est le mécanisme déjà employé par
AXIOME_QUOTIENT (sélection dans P(E)) et AXIOME_PRODUIT_FAM (sélection dans P(I×A)).
Bourbaki fait la même sélection mais dans X_α pour un α ∈ I quelconque (E II.22,
juste avant la Déf. 2 : « Si α est un élément de I, la relation (∀ι)((ι∈I) ⇒ (x∈X_ι))
entraîne x ∈ X_α, donc, en vertu de C52, cette relation est collectivisante en x ») —
d'où son hypothèse I ≠ ∅.  Grimm remplace X_α par ⋃_{ι∈I} X_ι, qui existe toujours ;
l'hypothèse tombe et ⋂_{ι∈∅} X_ι = ∅ au lieu d'un ensemble universel.

STRATÉGIE DES TROIS RÉSULTATS
  1. `inter_donne_membres` — ÉLIMINATION : projection DROITE de la conjonction.
     C'est la direction que consomment la plupart des sites d'usage, et elle est
     INCHANGÉE par la réparation (même énoncé qu'avec l'ancien AXIOME_INTER_FAM).
  2. `inter_inclus_reunion` — projection GAUCHE : ⋂ ⊂ ⋃ (l'ensemble-borne).
  3. `inter_par_membres_si_temoin` — INTRODUCTION, qui exige désormais un témoin
     d'indice : de (∀i)(i∈I ⇒ z∈X_i) et a∈I on tire z∈X_a, puis (a∈I et z∈X_a)
     donne z∈⋃ par S5 (témoin a) + AXIOME_REUNION_FAM ; la conjonction avec le
     membre (∀i) referme l'équivalence de sélection par `equivalence_arriere`.

INVARIANTS
  • Liant d'indice « i » IMPOSÉ (c'est celui d'AXIOME_REUNION_FAM / AXIOME_INTER_FAM) ;
    liant d'élément « z » (cohérent avec inclus/A1).  Aucun α-renommage ici.
  • Rien de postulé hors AXIOME_INTER_FAM_SEL, porté par `theorie_inter_selection()` ;
    `theorie_ensembles()` reste à 22 axiomes et AUCUN fichier existant n'est touché.
  • Les trois résultats sont CLOS (0 hypothèse) — vérifié par assertion à chaque appel.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, Formule, var, et, non, impl, equiv, appartient, pourtout, inclus, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie,
    projection_gauche, projection_droite)

_F, _I, _Z, _IDX = var("f"), var("I"), var("z"), var("i")


def _t(v):
    """Nom de variable ou Terme → Terme (les paramètres f, I acceptent les deux)."""
    return v if isinstance(v, Terme) else var(v)


# ── La formule « z appartient à tous les X_ι » ────────────────────────────────
# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  ({x | (∀ι)((ι∈I) ⇒ (x∈X_ι))} — le membre droit de la Déf. 2)
def corps_membres_famille(f, i_set, z, i: str = "i") -> Formule:
    """(∀i)((i∈I) ⇒ (z ∈ X_i))   — le corps de la Déf. 2 (X_i = valeur_famille(f,i)).

    Liant d'indice « i » IMPOSÉ par les axiomes de famille ; f, I, z sont des Termes."""
    vi = var(i)
    return pourtout(i, impl(appartient(vi, _t(i_set)),
                            appartient(_t(z), E.valeur_famille(_t(f), vi))))


# ── L'AXIOME de sélection ─────────────────────────────────────────────────────
# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (Déf. 2 RÉALISÉE par sélection S8 dans ⋃ ; @source sources/grimm_gaia/RR-6999-v7.pdf p.35 §2.7)
AXIOME_INTER_FAM_SEL = pourtout("f", pourtout("I", pourtout("z",
    equiv(appartient(_Z, E.inter_famille(_F, _I)),
          et(appartient(_Z, E.reunion_famille(_F, _I)),
             corps_membres_famille(_F, _I, _Z))))))


def theorie_inter_selection() -> N.Theorie:
    """Théorie DÉDIÉE ne contenant que l'axiome de sélection de ⋂ (motif du projet).

    `theorie_ensembles()` n'est PAS touchée : elle reste à 22 axiomes."""
    return N.Theorie("Inter-selection", [AXIOME_INTER_FAM_SEL])


# ── Instances ─────────────────────────────────────────────────────────────────
def membre_inter_selection(f="f", i_set="I", z="z"):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ ( z ∈ ⋃_{ι∈I} X_ι  et  (∀i)((i∈I) ⇒ z∈X_i) ).

    Instance DIRECTE d'AXIOME_INTER_FAM_SEL (∀f, ∀I, ∀z éliminés)."""
    ax = N.axiome(theorie_inter_selection(), AXIOME_INTER_FAM_SEL)
    return instancie(instancie(instancie(ax, _t(f)), _t(i_set)), _t(z))


def _inst_reunion(f, i_set, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i).   (AXIOME_REUNION_FAM, 22 axiomes.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i_set), z)


def _projections(f, i_set, z):
    """(⊢ z∈⋂ ⇒ z∈⋃ , ⊢ z∈⋂ ⇒ (∀i)(…)) — les deux projections de la sélection."""
    vf, vI, vz = _t(f), _t(i_set), _t(z)
    gauche = appartient(vz, E.reunion_famille(vf, vI))
    droite = corps_membres_famille(vf, vI, vz)
    fwd = equivalence_avant(membre_inter_selection(vf, vI, vz))
    return (syllogisme(fwd, projection_gauche(gauche, droite)),
            syllogisme(fwd, projection_droite(gauche, droite)))


# ── 1. ÉLIMINATION — la direction gratuite pour la migration ──────────────────
def enonce_inter_donne_membres(f="f", i_set="I", z="z") -> Formule:
    vf, vI, vz = _t(f), _t(i_set), var(z)
    return pourtout(z, impl(appartient(vz, E.inter_famille(vf, vI)),
                            corps_membres_famille(vf, vI, vz)))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (élimination : ⋂ ⊂ chaque X_ι — direction INCHANGÉE par la réparation)
def inter_donne_membres(f="f", i_set="I", z="z"):
    """⊢ (∀z)( z ∈ ⋂_{ι∈I} X_ι ⇒ (∀i)((i∈I) ⇒ z∈X_i) ).   CLOS — 0 hypothèse.

    Simple projection DROITE de la conjonction de sélection, généralisée sur z.
    C'est l'énoncé que produisait l'ANCIEN AXIOME_INTER_FAM dans ce sens : les
    sites d'usage qui n'utilisent que l'élimination migrent SANS RIEN CHANGER."""
    res = N.generalisation(z, _projections(f, i_set, var(z))[1])
    assert res.conclusion == enonce_inter_donne_membres(f, i_set, z), \
        "inter_donne_membres : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), "inter_donne_membres : doit être CLOS"
    return res


# ── 2. ⋂ ⊂ ⋃ — l'autre projection ─────────────────────────────────────────────
def enonce_inter_inclus_reunion(f="f", i_set="I", z="z") -> Formule:
    """(∀z)(z∈⋂ ⇒ z∈⋃).  Pour z="z" (défaut) c'est LITTÉRALEMENT `inclus(⋂, ⋃)`."""
    vf, vI, vz = _t(f), _t(i_set), var(z)
    return pourtout(z, impl(appartient(vz, E.inter_famille(vf, vI)),
                            appartient(vz, E.reunion_famille(vf, vI))))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (⋂ ⊂ ⋃ : l'ensemble-borne de la sélection S8 — c'est CE membre qui tue le cas I=∅)
def inter_inclus_reunion(f="f", i_set="I", z="z"):
    """⊢ (∀z)( z ∈ ⋂_{ι∈I} X_ι ⇒ z ∈ ⋃_{ι∈I} X_ι ),  i.e. ⊢ ⋂ ⊂ ⋃.   CLOS.

    Projection GAUCHE de la conjonction.  Nouveau par rapport à l'ancien axiome —
    et c'est LUI qui fait mourir la pathologie : pour I=∅ la réunion est vide,
    donc l'intersection l'est aussi (cf. `ensembles_inter_migration_ii4`)."""
    res = N.generalisation(z, _projections(f, i_set, var(z))[0])
    assert res.conclusion == enonce_inter_inclus_reunion(f, i_set, z), \
        "inter_inclus_reunion : conclusion ≠ (⋂ ⊂ ⋃)"
    assert res.hypotheses == frozenset(), "inter_inclus_reunion : doit être CLOS"
    return res


# ── Réunion : introduction par un témoin d'indice TERME quelconque ────────────
# @livre Ch.II §4.1 Def.1 | E II.22 L.31-36 | PDF p.73  (⋃ par S5, témoin d'indice : version TERME de `ensembles_familles.reunion_famille_intro`)
def reunion_intro_terme(f, i_set, temoin, z):
    """⊢ ( (T∈I) et (z∈X_T) ) ⇒ z ∈ ⋃_{ι∈I} X_ι,  pour un TERME T quelconque.

    Variante de `ensembles_familles.reunion_famille_intro` acceptant un témoin
    TERME (et pas seulement un nom de variable) — indispensable au pont de
    migration, dont le témoin est le τ-terme τi(i∈I) livré par `existe_temoin`."""
    vf, vI, vz, vT = _t(f), _t(i_set), _t(z), _t(temoin)
    inner = et(appartient(_IDX, vI), appartient(vz, E.valeur_famille(vf, _IDX)))
    body = subst_f(vT, "i", inner)                       # (T∈I et z∈X_T)
    h = N.assume(body)
    ex = N.modus_ponens(h, N.s5(inner, vT, "i"))         # (∃i)(i∈I et z∈X_i)
    zU = N.modus_ponens(ex, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    return N.loi_deduction(body, zU)


# ── 3. INTRODUCTION — nécessite un témoin d'indice ────────────────────────────
def enonce_inter_par_membres_si_temoin(f="f", i_set="I", a="a", z="z") -> Formule:
    vf, vI, va, vz = _t(f), _t(i_set), _t(a), _t(z)
    return impl(appartient(va, vI),
                impl(corps_membres_famille(vf, vI, vz),
                     appartient(vz, E.inter_famille(vf, vI))))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (introduction ; « Si α est un élément de I … » — le TÉMOIN d'indice exigé par le livre)
def inter_par_membres_si_temoin_terme(f, i_set, temoin, z):
    """⊢ (T∈I) ⇒ ( (∀i)((i∈I) ⇒ z∈X_i) ⇒ z ∈ ⋂_{ι∈I} X_ι ),  T terme quelconque.

    Route : de (∀i)(…) instancié en T et de T∈I on tire z∈X_T ; la conjonction
    (T∈I et z∈X_T) donne z∈⋃ par `reunion_intro_terme` ; conjuguée au membre
    (∀i)(…) elle referme l'équivalence de sélection (`equivalence_arriere`)."""
    vf, vI, vT, vz = _t(f), _t(i_set), _t(temoin), _t(z)
    hyp_a = appartient(vT, vI)
    corps = corps_membres_famille(vf, vI, vz)
    ha, hall = N.assume(hyp_a), N.assume(corps)
    zXt = N.modus_ponens(ha, instancie(hall, vT))                    # z ∈ X_T
    zU = N.modus_ponens(conjonction_intro(ha, zXt),                  # z ∈ ⋃
                        reunion_intro_terme(vf, vI, vT, vz))
    zInt = N.modus_ponens(conjonction_intro(zU, hall),               # z ∈ ⋂
                          equivalence_arriere(membre_inter_selection(vf, vI, vz)))
    return N.loi_deduction(hyp_a, N.loi_deduction(corps, zInt))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73  (introduction, témoin = variable a — « Si α est un élément de I »)
def inter_par_membres_si_temoin(f="f", i_set="I", a="a", z="z"):
    """⊢ (a∈I) ⇒ ( (∀i)((i∈I) ⇒ z∈X_i) ⇒ z ∈ ⋂_{ι∈I} X_ι ).   CLOS — 0 hypothèse.

    LA direction qui change : sans témoin d'indice on ne peut plus conclure, et
    c'est exactement ce qui interdit désormais de peupler ⋂_{ι∈∅} X_ι."""
    res = inter_par_membres_si_temoin_terme(f, i_set, a, z)
    assert res.conclusion == enonce_inter_par_membres_si_temoin(f, i_set, a, z), \
        "inter_par_membres_si_temoin : conclusion ≠ énoncé attendu"
    assert res.hypotheses == frozenset(), "inter_par_membres_si_temoin : doit être CLOS"
    return res


__all__ = ["AXIOME_INTER_FAM_SEL", "theorie_inter_selection",
           "corps_membres_famille", "membre_inter_selection", "reunion_intro_terme",
           "enonce_inter_donne_membres", "inter_donne_membres",
           "enonce_inter_inclus_reunion", "inter_inclus_reunion",
           "enonce_inter_par_membres_si_temoin", "inter_par_membres_si_temoin",
           "inter_par_membres_si_temoin_terme"]
