"""§II.4 — Réunion et intersection d'une famille d'ensembles.

Termes définis ⋃_{ι∈I} X_ι, ⋂_{ι∈I} X_ι (E.II.4.1, Déf. 1 et 2) avec axiomes
caractérisants (légitimés par S8 = sélection-réunion + extensionnalité A1, comme
produit/image). Une famille (X_ι)_{ι∈I} est une fonction ι↦X_ι ; X_ι est noté
par le terme valeur_famille(f, i).

Théorèmes certifiés : caractérisation de l'appartenance, introduction dans la
réunion, élimination de l'intersection, MONOTONIE de ⋃ et ⋂ (§II.4.2, demi-Prop.
de croissance), et ⋃_{ι∈∅} X_ι = ∅ (note de la Déf. 1).

MIGRATION « ⋂ = SÉLECTION DANS ⋃ » (cf. `ii_4_intersection_fondation`).
AXIOME_INTER_FAM caractérise désormais z∈⋂ par une CONJONCTION (z∈⋃ ET le membre
(∀ι)((ι∈I) ⇒ (z∈X_ι))), ce qui tue l'ensemble universel ⋂_{ι∈∅} X_ι.  Bilan sur ce
fichier :
  • `membre_inter_famille` — ÉNONCÉ RENFORCÉ : l'équivalence de la Déf. 2 n'est
    plus inconditionnelle, elle porte l'hypothèse (∃i)(i∈I) que Bourbaki écrit
    (E II.22).  L'ancienne forme sans hypothèse était FAUSSE pour I = ∅.
  • `inter_famille_elim`, `monotonie_inter_famille` — ÉNONCÉS INCHANGÉS : seules
    les preuves changent (projeter la conjonction ; transporter la borne z∈⋃).
  • les résultats de ⋃ (`membre_reunion_famille`, `reunion_famille_intro`,
    `monotonie_reunion_famille`, `reunion_famille_vide`) sont intacts.

Les Propositions 1-10 et Déf. 4-8 plus profondes (reparamétrage surjectif,
associativité, image directe/réciproque, De Morgan sur familles, recollement,
somme) sont REPORTÉES (cf. rapport) : elles exigent une infrastructure absente
(complémentaire ∁_E, recollement de fonctions, sommes, surjections) ou de très
longues preuves multi-étapes nouvelles.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient, existe, pourtout, inclus, tau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               equivalence_arriere, instancie, contraposition,
                               projection_gauche, projection_droite, dni)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import monotonie_existe, monotonie_pour_tout
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import vide_sans_element
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import vide_ssi_sans_element
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    reunion_intro_terme)


def _inst_reunion(f, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ ( z∈⋃_{ι∈I} X_ι  et  (∀i)(i∈I ⇒ z∈X_i) ).

    AXIOME_INTER_FAM est désormais la forme de SÉLECTION dans la réunion : son
    membre droit est une CONJONCTION (cf. `ii_4_intersection_fondation`)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _corps_membres(vf, vI, vz):
    """(∀i)((i∈I) ⇒ (z ∈ X_i))  — le membre droit de la Déf. 2 (liant « i » imposé)."""
    vi = var("i")
    return pourtout("i", impl(appartient(vi, vI),
                              appartient(vz, E.valeur_famille(vf, vi))))


def _projections_inter(vf, vI, vz):
    """(⊢ z∈⋂ ⇒ z∈⋃ ,  ⊢ z∈⋂ ⇒ (∀i)(i∈I ⇒ z∈X_i)) — les deux projections.

    Depuis la migration, le membre droit de l'axiome est une conjonction : on ne
    peut plus l'attaquer directement, il faut le PROJETER (même motif que
    `ensembles_inter_selection_ii4._projections`)."""
    gauche = appartient(vz, E.reunion_famille(vf, vI))
    droite = _corps_membres(vf, vI, vz)
    fwd = equivalence_avant(_inst_inter(vf, vI, vz))
    return (syllogisme(fwd, projection_gauche(gauche, droite)),
            syllogisme(fwd, projection_droite(gauche, droite)))


def indices_non_vides(i="I"):
    """(∃i)(i ∈ I)  — « l'ensemble d'indices I n'est pas vide » (hypothèse de la Déf. 2)."""
    return existe("i", appartient(var("i"), var(i)))


# @livre Ch.II §4.1 Def.1 | E II.22 L.31-36 | PDF p.73
def membre_reunion_famille(f="f", i="I", z="z"):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i).   (E.II.4.1, Déf. 1 — appartenance.)"""
    return _inst_reunion(var(f), var(i), var(z))


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73
def membre_inter_famille(f="f", i="I", z="z"):
    """⊢ (∃i)(i∈I) ⇒ ( (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i) ).   (Déf. 2.)

    ÉNONCÉ RENFORCÉ (issue B de la migration ⋂ = sélection dans ⋃).  L'ancienne
    forme, SANS hypothèse — « (z∈⋂) ⇔ (∀i)(i∈I ⇒ z∈X_i) » — était FAUSSE pour
    I = ∅ : le membre droit y est vide-vrai pour tout z alors que ⋂_{ι∈∅} X_ι = ∅
    (`ensembles_inter_migration_ii4.inter_famille_vide_egale_vide`).  C'est
    exactement l'incohérence prouvée par `outils_ia/audit/preuve_incoherence_inter_vide.py`.
    On restitue donc l'énoncé sous l'hypothèse que Bourbaki écrit noir sur blanc
    (E II.22, PDF p.73 : « … dont l'ensemble d'indices I n'est pas vide »).

    STRATÉGIE.  Sous H := (∃i)(i∈I), `N.existe_temoin` livre le témoin canonique
    T₀ := τi(i∈I) avec T₀ ∈ I.  ⇒ : projection DROITE de la conjonction de
    sélection (inconditionnelle).  ⇐ : de (∀i)(…) instancié en T₀ et de T₀∈I on
    tire z∈X_{T₀}, d'où z∈⋃ par `reunion_intro_terme` (S5, témoin T₀) ; conjuguée
    au membre (∀i)(…) elle referme l'équivalence de sélection.  C14 décharge H."""
    vf, vI, vz, vi = var(f), var(i), var(z), var("i")
    H = indices_non_vides(i)
    T0 = tau("i", appartient(vi, vI))                              # τi(i∈I)
    h = N.assume(H)
    t_in_I = N.modus_ponens(h, N.existe_temoin(appartient(vi, vI), "i"))   # T₀ ∈ I
    corps = _corps_membres(vf, vI, vz)
    hall = N.assume(corps)
    zXt = N.modus_ponens(t_in_I, instancie(hall, T0))              # z ∈ X_{T₀}
    zU = N.modus_ponens(conjonction_intro(t_in_I, zXt),            # z ∈ ⋃
                        reunion_intro_terme(vf, vI, T0, vz))
    zInt = N.modus_ponens(conjonction_intro(zU, hall),             # z ∈ ⋂
                          equivalence_arriere(_inst_inter(vf, vI, vz)))
    bwd = N.loi_deduction(corps, zInt)                             # {H} ⊢ corps ⇒ z∈⋂
    fwd = _projections_inter(vf, vI, vz)[1]                        # ⊢ z∈⋂ ⇒ corps
    return N.loi_deduction(H, conjonction_intro(fwd, bwd))


# @livre Ch.II §4.1 Def.1 | E II.22 L.31-36 | PDF p.73
def reunion_famille_intro(f="f", i="I", a="a", z="z"):
    """⊢ ((a∈I) et (z∈X_a)) ⇒ (z ∈ ⋃_{ι∈I} X_ι).   (un élément d'un X_a est dans ⋃.)"""
    vf, vI, va, vz = var(f), var(i), var(a), var(z)
    body = et(appartient(va, vI), appartient(vz, E.valeur_famille(vf, va)))
    h = N.assume(body)
    # (a∈I et z∈X_a) ⇒ (∃i)(i∈I et z∈X_i)   par S5 (témoin a)
    inner = et(appartient(var("i"), vI), appartient(vz, E.valeur_famille(vf, var("i"))))
    ex = N.modus_ponens(h, N.s5(inner, va, "i"))                  # (∃i)(i∈I et z∈X_i)
    zU = N.modus_ponens(ex, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    return N.loi_deduction(body, zU)


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73
def inter_famille_elim(f="f", i="I", a="a", z="z"):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇒ ((a∈I) ⇒ (z∈X_a)).   (l'intersection est incluse dans chaque X_a.)

    ÉNONCÉ INCHANGÉ par la migration ⋂ = sélection dans ⋃ : l'élimination est la
    direction gratuite, elle ne demande aucun témoin d'indice.  Seule la ROUTE
    change — le membre droit de l'axiome étant devenu une conjonction, on projette
    à DROITE (`_projections_inter`) au lieu d'attaquer le (∀i) directement."""
    vf, vI, va, vz = var(f), var(i), var(a), var(z)
    h = N.assume(appartient(vz, E.inter_famille(vf, vI)))
    forall = N.modus_ponens(h, _projections_inter(vf, vI, vz)[1])   # (∀i)(i∈I⇒z∈X_i)
    inst = instancie(forall, va)                       # (a∈I ⇒ z∈X_a)
    return N.loi_deduction(appartient(vz, E.inter_famille(vf, vI)), inst)


# @livre Ch.II §4.2 Prop.- | E II.24 L.1-4 | PDF p.75
# @livre Ch.R §4 Prop.- | E.R.17 item 3 (X_ι⊂Y_ι qq soit ι ⇒ ⋃X_ι⊂⋃Y_ι) | PDF p.320
def monotonie_reunion_famille(f="f", g="g", i="I"):
    """⊢ ((∀i)(X_i ⊂ Y_i)) ⇒ (⋃_{ι∈I} X_ι ⊂ ⋃_{ι∈I} Y_ι).   (§II.4.2, monotonie de ⋃.)

    X_i = valeur_famille(f,i), Y_i = valeur_famille(g,i)."""
    vf, vg, vI, vz, vi = var(f), var(g), var(i), var("z"), var("i")
    hyp = pourtout("i", inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))
    h = N.assume(hyp)
    incl_i = instancie(h, vi)                          # X_i ⊂ Y_i  = (∀z')(z'∈X_i ⇒ z'∈Y_i)
    zXi_zYi = instancie(incl_i, vz)                    # z∈X_i ⇒ z∈Y_i
    # (i∈I et z∈X_i) ⇒ (i∈I et z∈Y_i)
    inner = et(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    hi = N.assume(inner)
    conc = conjonction_intro(conjonction_elim_gauche(hi),
                             N.modus_ponens(conjonction_elim_droite(hi), zXi_zYi))
    step = N.loi_deduction(inner, conc)                # {hyp} ⊢ inner ⇒ inner'
    mono = monotonie_existe(step, "i")                 # (∃i …X) ⇒ (∃i …Y)
    z_imp = syllogisme(equivalence_avant(_inst_reunion(vf, vI, vz)),
                       syllogisme(mono, equivalence_arriere(_inst_reunion(vg, vI, vz))))
    gen = N.generalisation("z", z_imp)                 # {hyp} ⊢ ⋃X ⊂ ⋃Y
    return N.loi_deduction(hyp, gen)


# @livre Ch.II §4.2 Prop.- | E II.24 L.1-4 | PDF p.75
# @livre Ch.R §4 Prop.- | E.R.19 item 8 (X_ι⊂Y_ι qq soit ι ⇒ ⋂X_ι⊂⋂Y_ι) | PDF p.322
def monotonie_inter_famille(f="f", g="g", i="I"):
    """⊢ ((∀i)(X_i ⊂ Y_i)) ⇒ (⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈I} Y_ι).   (§II.4.2, monotonie de ⋂.)

    ÉNONCÉ INCHANGÉ par la migration ⋂ = sélection dans ⋃ : AUCUNE hypothèse
    « I ≠ ∅ » n'est requise (pour I = ∅ les deux membres valent ∅, l'inclusion
    tient trivialement).  La route, elle, change : il faut désormais fournir les
    DEUX conjonctions de la sélection côté Y.
      • le membre (∀i)(i∈I ⇒ z∈Y_i) vient, comme avant, de `monotonie_pour_tout` ;
      • le membre-BORNE z ∈ ⋃Y vient de z ∈ ⋃X (projection GAUCHE de la sélection
        côté X) et de la monotonie DÉJÀ certifiée de ⋃ (`monotonie_reunion_famille`).
    C'est le seul endroit du fichier où la borne de sélection doit être transportée."""
    vf, vg, vI, vz, vi = var(f), var(g), var(i), var("z"), var("i")
    hyp = pourtout("i", inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))
    h = N.assume(hyp)
    incl_i = instancie(h, vi)                          # X_i ⊂ Y_i
    zXi_zYi = instancie(incl_i, vz)                    # z∈X_i ⇒ z∈Y_i
    # (i∈I ⇒ z∈X_i) ⇒ (i∈I ⇒ z∈Y_i)
    inner = impl(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    hi = N.assume(inner)
    # construire (i∈I ⇒ z∈Y_i) à partir de (i∈I ⇒ z∈X_i)
    hii = N.assume(appartient(vi, vI))
    zYi = N.modus_ponens(N.modus_ponens(hii, hi), zXi_zYi)        # {inner, i∈I} ⊢ z∈Y_i
    inner_imp = N.loi_deduction(inner, N.loi_deduction(appartient(vi, vI), zYi))
    mono = monotonie_pour_tout(inner_imp, "i")         # (∀i …X) ⇒ (∀i …Y)
    # borne de sélection : z∈⋃X ⇒ z∈⋃Y  (monotonie de ⋃, déjà certifiée)
    reun = instancie(N.modus_ponens(h, monotonie_reunion_famille(f, g, i)), vz)
    zX = appartient(vz, E.inter_famille(vf, vI))
    hz = N.assume(zX)
    p_gauche, p_droite = _projections_inter(vf, vI, vz)
    zUY = N.modus_ponens(N.modus_ponens(hz, p_gauche), reun)      # z ∈ ⋃Y
    corpsY = N.modus_ponens(N.modus_ponens(hz, p_droite), mono)   # (∀i)(i∈I ⇒ z∈Y_i)
    zIntY = N.modus_ponens(conjonction_intro(zUY, corpsY),        # z ∈ ⋂Y
                           equivalence_arriere(_inst_inter(vg, vI, vz)))
    gen = N.generalisation("z", N.loi_deduction(zX, zIntY))
    return N.loi_deduction(hyp, gen)


# @livre Ch.II §4.1 Rem.- | E II.22 L.38-40 | PDF p.73
# @livre Ch.R §4 Prop.- | E.R.17 item 2 ((33) réunion sur l'ensemble d'indices vide = ∅) | PDF p.320
def reunion_famille_vide(f="f"):
    """⊢ ⋃_{ι∈∅} X_ι = ∅.   (note de la Déf. 1 : réunion sur l'ensemble d'indices vide.)"""
    vf, vz, vi = var(f), var("z"), var("i")
    # ¬(i∈∅ et z∈X_i) pour tout i, donc ¬(∃i)(…), donc ¬(z∈⋃)
    body = et(appartient(vi, E.VIDE), appartient(vz, E.valeur_famille(vf, vi)))
    n_body = N.modus_ponens(vide_sans_element("i"),
        contraposition(projection_gauche(appartient(vi, E.VIDE),
                                         appartient(vz, E.valeur_famille(vf, vi)))))  # ¬body
    n_ex = N.modus_ponens(N.generalisation("i", n_body),
                          contraposition(monotonie_existe(dni(body), "i")))
    nz = N.modus_ponens(n_ex, contraposition(equivalence_avant(
        _inst_reunion(vf, E.VIDE, vz))))                # ¬(z∈⋃_{∅})
    return N.modus_ponens(N.generalisation("z", nz),
        equivalence_arriere(vide_ssi_sans_element(E.reunion_famille(vf, E.VIDE))))


__all__ = ["indices_non_vides", "membre_reunion_famille", "membre_inter_famille",
           "reunion_famille_intro", "inter_famille_elim",
           "monotonie_reunion_famille", "monotonie_inter_famille",
           "reunion_famille_vide"]
