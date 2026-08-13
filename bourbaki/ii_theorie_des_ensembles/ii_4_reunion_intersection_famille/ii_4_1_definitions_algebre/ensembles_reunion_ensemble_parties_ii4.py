"""§II.4.1 — Réunion / intersection d'un ENSEMBLE de parties  ⋃𝔊, ⋂𝔊.

Brique d'infrastructure (partagée n°95 Cantor, n°140 Cor.2 Th.2, n°67 Résumé).

Bourbaki définit la réunion ⋃_{X∈𝔊} X d'un ensemble 𝔊 dont les éléments sont des
parties comme la réunion de la FAMILLE IDENTITÉ (X)_{X∈𝔊} — i.e. la famille dont
l'ensemble d'indices est 𝔊 lui-même et dont le ι-ème terme est ι.  On réutilise
donc telle quelle la machinerie ⋃_{ι∈I}/⋂_{ι∈I} (déjà axiomatisée dans les 22
axiomes : AXIOME_REUNION_FAM / AXIOME_INTER_FAM), SANS ajouter d'axiome et SANS
passer par graphe_terme (qui vit dans une théorie dédiée ≠ 22).

La propriété « f est la famille identité sur U » (valeur_famille(f,X)=X pour tout
X∈U) est portée en HYPOTHÈSE honnête (même procédé que le H de n°92) :

    est_famille_identite(f, U) := (∀X)(X∈U ⇒ valeur_famille(f,X) = X)

    reunion_ensemble(f, U) := ⋃_{ι∈U} X_ι      (= ⋃U quand f est l'identité sur U)
    inter_ensemble(f, U)   := ⋂_{ι∈U} X_ι      (= ⋂U quand f est l'identité sur U)

Résultat certifié de ce fichier :
    membre_reunion_ensemble  {est_famille_identite(f,U)} ⊢
        (z ∈ ⋃U) ⇔ (∃i)(i∈U et z∈i)

dérivé de membre_reunion_famille (instance d'AXIOME_REUNION_FAM) + réécriture
Leibniz S6 (valeur_famille(f,i)=i, valable sous i∈U) portée sous l'existentiel
par monotonie_existe (les deux sens).  theorie_ensembles() inchangée (22 axiomes).

MIGRATION Déf. 2 (⋂ = SÉLECTION dans ⋃, E II.22) — impact sur ce fichier :
  • `membre_reunion_ensemble`, `partie_incluse_reunion` : côté ⋃, INTACTS.
  • `inter_incluse_partie` : énoncé INCHANGÉ, preuve refaite sur la seule
    ÉLIMINATION (`inter_donne_membres`, inconditionnelle) — l'antécédent c∈U
    fournit lui-même le témoin d'indice.
  • `membre_inter_ensemble` : énoncé RENFORCÉ.  L'équivalence complète réclame
    désormais l'hypothèse de Bourbaki (∃i)(i∈U) (`indices_non_vides`), portée au
    compteur d'hypothèses.  Sans elle l'énoncé est FAUX pour U=∅ (⋂∅=∅ mais
    (∀i)(i∈∅⇒z∈i) vaut pour tout z) ; il n'était dérivable que de l'ancien
    AXIOME_INTER_FAM, qui rendait la théorie contradictoire.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, impl, appartient, existe, pourtout, equiv, inclus)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import monotonie_existe, monotonie_pour_tout
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import membre_reunion_famille
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import inter_donne_membres
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides, caracterisation_inter_famille_non_vide)


# ── Définitions ──────────────────────────────────────────────────────────────
# @livre Ch.II §4.1 Def.- | E II.22 L.31-36 | PDF p.73  (⋃𝔊 = réunion de la famille identité sur 𝔊)
def est_famille_identite(f, u):
    """« f est la famille identité sur U » := (∀X)(X∈U ⇒ X_ι=ι), X_ι=valeur_famille(f,ι)."""
    vf, vu, vX = _t(f), _t(u), var("X")
    return pourtout("X", impl(appartient(vX, vu), egal(E.valeur_famille(vf, vX), vX)))


def reunion_ensemble(f, u):
    """⋃U := ⋃_{ι∈U} X_ι  (réunion de l'ensemble de parties U, via sa famille identité f)."""
    return E.reunion_famille(_t(f), _t(u))


def inter_ensemble(f, u):
    """⋂U := ⋂_{ι∈U} X_ι  (intersection de l'ensemble de parties U, via sa famille identité f)."""
    return E.inter_famille(_t(f), _t(u))


def _t(v):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme
    return v if isinstance(v, Terme) else var(v)


def enonce_membre_reunion_ensemble(f="f", u="U", z="z"):
    vf, vu, vz = var(f), var(u), var(z)
    vi = var("i")
    return equiv(appartient(vz, reunion_ensemble(vf, vu)),
                 existe("i", et(appartient(vi, vu), appartient(vz, vi))))


# @livre Ch.II §4.1 Def.- | E II.22 L.31-36 | PDF p.73  (appartenance à ⋃𝔊)
def membre_reunion_ensemble(f="f", u="U", z="z"):
    """⊢ {est_famille_identite(f,U)}  (z ∈ ⋃U) ⇔ (∃i)(i∈U et z∈i).

    ⋃U = ⋃_{ι∈U} X_ι ; sous l'hypothèse « f identité sur U » on a X_ι=ι, donc
    l'appartenance à la réunion de famille devient l'appartenance à ⋃U."""
    vf, vu, vz = var(f), var(u), var(z)
    vi = var("i")
    H = est_famille_identite(vf, vu)
    hH = N.assume(H)
    inst = instancie(hH, vi)                     # (i∈U) ⇒ (X_i = i)        [sous H]

    star = membre_reunion_famille(f, u, z)       # (z∈⋃_{ι∈U}) ⇔ (∃i)(i∈U et z∈X_i)
    inner1 = et(appartient(vi, vu), appartient(vz, E.valeur_famille(vf, vi)))  # i∈U et z∈X_i
    inner2 = et(appartient(vi, vu), appartient(vz, vi))                        # i∈U et z∈i
    # S6 : (X_i = i) ⇒ ((z∈X_i) ⇔ (z∈i))
    memb_bicond = lambda eqv, fwd: N.modus_ponens(
        eqv, N.s6(E.valeur_famille(vf, vi), vi, "w", appartient(vz, var("w"))))

    # sens → : inner1 ⇒ inner2
    h1 = N.assume(inner1)
    iU1 = conjonction_elim_gauche(h1)
    eq1 = N.modus_ponens(iU1, inst)              # X_i = i
    zi1 = N.modus_ponens(conjonction_elim_droite(h1),
                         equivalence_avant(memb_bicond(eq1, True)))            # z∈i
    imp_fwd = N.loi_deduction(inner1, conjonction_intro(iU1, zi1))             # {H} inner1⇒inner2

    # sens ← : inner2 ⇒ inner1
    h2 = N.assume(inner2)
    iU2 = conjonction_elim_gauche(h2)
    eq2 = N.modus_ponens(iU2, inst)              # X_i = i
    zXi2 = N.modus_ponens(conjonction_elim_droite(h2),
                          equivalence_arriere(memb_bicond(eq2, False)))        # z∈X_i
    imp_bwd = N.loi_deduction(inner2, conjonction_intro(iU2, zXi2))            # {H} inner2⇒inner1

    ex_fwd = monotonie_existe(imp_fwd, "i")      # (∃i inner1) ⇒ (∃i inner2)
    ex_bwd = monotonie_existe(imp_bwd, "i")      # (∃i inner2) ⇒ (∃i inner1)

    tot_fwd = syllogisme(equivalence_avant(star), ex_fwd)    # (z∈⋃U) ⇒ (∃i inner2)
    tot_bwd = syllogisme(ex_bwd, equivalence_arriere(star))  # (∃i inner2) ⇒ (z∈⋃U)
    res = conjonction_intro(tot_fwd, tot_bwd)                # {H} (z∈⋃U) ⇔ (∃i inner2)
    assert res.conclusion == enonce_membre_reunion_ensemble(f, u, z), \
        "membre_reunion_ensemble : conclusion ≠ énoncé attendu"
    return res


def enonce_membre_inter_ensemble(f="f", u="U", z="z"):
    vf, vu, vz = var(f), var(u), var(z)
    vi = var("i")
    return equiv(appartient(vz, inter_ensemble(vf, vu)),
                 pourtout("i", impl(appartient(vi, vu), appartient(vz, vi))))


# @livre Ch.II §4.1 Def.- | E II.22 L.49-53 | PDF p.73  (appartenance à ⋂𝔊)
def membre_inter_ensemble(f="f", u="U", z="z"):
    """⊢ {est_famille_identite(f,U), (∃i)(i∈U)}  (z ∈ ⋂U) ⇔ (∀i)(i∈U ⇒ z∈i).

    Dual de membre_reunion_ensemble : sous « f identité sur U » (X_ι=ι),
    l'appartenance à ⋂_{ι∈U} X_ι devient l'appartenance à ⋂U.

    ⚠️ RENFORCEMENT D'ÉNONCÉ (migration Déf. 2 par sélection dans ⋃, E II.22).
    L'ancienne forme — SANS l'hypothèse « U n'est pas vide » — était FAUSSE pour
    U = ∅ : le membre droit (∀i)(i∈∅ ⇒ z∈i) est vrai pour TOUT z alors que
    ⋂∅ = ∅ ne contient rien (`inter_famille_vide_egale_vide`).  Elle n'était
    dérivable que de l'ancien AXIOME_INTER_FAM, lequel rendait la théorie
    CONTRADICTOIRE (⋂ sur I=∅ = ensemble universel, cf.
    `outils_ia/audit/preuve_incoherence_inter_vide.py`).
    L'hypothèse `indices_non_vides(U)` = (∃i)(i∈U) est celle que Bourbaki écrit
    noir sur blanc dans la Déf. 2 ; elle est portée honnêtement au compteur
    d'hypothèses (comme `est_famille_identite`), pas cachée dans la preuve.
    Le sens ⇒ seul (élimination) reste, lui, INCONDITIONNEL : c'est exactement
    ce dont `inter_incluse_partie` se contente, et pourquoi ce dernier n'a PAS
    besoin du renforcement."""
    vf, vu, vz = var(f), var(u), var(z)
    vi = var("i")
    H = est_famille_identite(vf, vu)
    hH = N.assume(H)
    inst = instancie(hH, vi)                      # (i∈U) ⇒ (X_i = i)        [sous H]

    # L'ancien AXIOME_INTER_FAM, récupéré sous l'hypothèse de la Déf. 2 :
    #   (∃i)(i∈U) ⇒ (∀z)( z∈⋂_{ι∈U} X_ι ⇔ (∀i)(i∈U ⇒ z∈X_i) )
    h_ne = N.assume(indices_non_vides(vu))        # (∃i)(i∈U)   [hypothèse Bourbaki]
    star = instancie(N.modus_ponens(h_ne, caracterisation_inter_famille_non_vide(vf, vu, z)),
                     vz)                          # (z∈⋂_{ι∈U}) ⇔ (∀i)(i∈U ⇒ z∈X_i)
    inner1 = impl(appartient(vi, vu), appartient(vz, E.valeur_famille(vf, vi)))  # i∈U ⇒ z∈X_i
    inner2 = impl(appartient(vi, vu), appartient(vz, vi))                        # i∈U ⇒ z∈i
    s6 = N.s6(E.valeur_famille(vf, vi), vi, "w", appartient(vz, var("w")))       # (X_i=i)⇒((z∈X_i)⇔(z∈i))

    # sens → : inner1 ⇒ inner2
    h1 = N.assume(inner1)
    hiU1 = N.assume(appartient(vi, vu))
    zi1 = N.modus_ponens(N.modus_ponens(hiU1, h1),
                         equivalence_avant(N.modus_ponens(N.modus_ponens(hiU1, inst), s6)))   # z∈i
    imp_fwd = N.loi_deduction(inner1, N.loi_deduction(appartient(vi, vu), zi1))               # {H} inner1⇒inner2

    # sens ← : inner2 ⇒ inner1
    h2 = N.assume(inner2)
    hiU2 = N.assume(appartient(vi, vu))
    zXi2 = N.modus_ponens(N.modus_ponens(hiU2, h2),
                          equivalence_arriere(N.modus_ponens(N.modus_ponens(hiU2, inst), s6)))  # z∈X_i
    imp_bwd = N.loi_deduction(inner2, N.loi_deduction(appartient(vi, vu), zXi2))                # {H} inner2⇒inner1

    fa_fwd = monotonie_pour_tout(imp_fwd, "i")    # (∀i inner1) ⇒ (∀i inner2)
    fa_bwd = monotonie_pour_tout(imp_bwd, "i")    # (∀i inner2) ⇒ (∀i inner1)

    tot_fwd = syllogisme(equivalence_avant(star), fa_fwd)    # (z∈⋂U) ⇒ (∀i inner2)
    tot_bwd = syllogisme(fa_bwd, equivalence_arriere(star))  # (∀i inner2) ⇒ (z∈⋂U)
    res = conjonction_intro(tot_fwd, tot_bwd)               # {H} (z∈⋂U) ⇔ (∀i inner2)
    assert res.conclusion == enonce_membre_inter_ensemble(f, u, z), \
        "membre_inter_ensemble : conclusion ≠ énoncé attendu"
    return res


# ── Inclusions caractéristiques (intro ⋃, élim ⋂) ────────────────────────────
def enonce_partie_incluse_reunion(f="f", u="U", c="c"):
    vf, vu, vc = var(f), var(u), var(c)
    return impl(appartient(vc, vu), inclus(vc, reunion_ensemble(vf, vu)))


# @livre Ch.II §4.1 Prop.- | E II.22 L.31-36 | PDF p.73  (chaque partie de 𝔊 est incluse dans ⋃𝔊)
def partie_incluse_reunion(f="f", u="U", c="c"):
    """⊢ {est_famille_identite(f,U)}  (c∈U) ⇒ (c ⊂ ⋃U).   (chaque élément de U est ⊂ ⋃U.)"""
    vf, vu, vc, vz = var(f), var(u), var(c), var("z")
    hc = N.assume(appartient(vc, vu))                     # c∈U
    hz = N.assume(appartient(vz, vc))                     # z∈c
    inner = et(appartient(var("i"), vu), appartient(vz, var("i")))
    ex = N.modus_ponens(conjonction_intro(hc, hz), N.s5(inner, vc, "i"))   # (∃i)(i∈U et z∈i)
    zU = N.modus_ponens(ex, equivalence_arriere(membre_reunion_ensemble(f, u, "z")))  # z∈⋃U
    gen = N.generalisation("z", N.loi_deduction(appartient(vz, vc), zU))   # {H,c∈U} c⊂⋃U
    res = N.loi_deduction(appartient(vc, vu), gen)
    assert res.conclusion == enonce_partie_incluse_reunion(f, u, c), \
        "partie_incluse_reunion : conclusion ≠ énoncé attendu"
    return res


def enonce_inter_incluse_partie(f="f", u="U", c="c"):
    vf, vu, vc = var(f), var(u), var(c)
    return impl(appartient(vc, vu), inclus(inter_ensemble(vf, vu), vc))


# @livre Ch.II §4.1 Prop.- | E II.22 L.49-53 | PDF p.73  (⋂𝔊 est incluse dans chaque partie de 𝔊)
def inter_incluse_partie(f="f", u="U", c="c"):
    """⊢ {est_famille_identite(f,U)}  (c∈U) ⇒ (⋂U ⊂ c).   (⋂U est incluse dans chaque élément de U.)

    ÉNONCÉ INCHANGÉ par la migration Déf. 2 (⋂ = sélection dans ⋃) : seule la
    PREUVE change.  On ne passe plus par l'équivalence `membre_inter_ensemble`
    (qui, elle, réclame désormais (∃i)(i∈U)), mais par la seule ÉLIMINATION
    `inter_donne_membres`, qui est inconditionnelle.  Et c'est logiquement juste :
    l'antécédent c∈U FOURNIT DÉJÀ le témoin d'indice qui manquait — U n'est pas
    vide dès qu'on suppose c∈U.  D'où le réglage : z∈⋂U donne (∀i)(i∈U ⇒ z∈X_i),
    instancié en c puis réécrit par X_c = c (hypothèse « f identité sur U »)."""
    vf, vu, vc, vz = var(f), var(u), var(c), var("z")
    hc = N.assume(appartient(vc, vu))                     # c∈U
    hz = N.assume(appartient(vz, inter_ensemble(vf, vu)))  # z∈⋂U
    # Élimination INCONDITIONNELLE : (∀z)( z∈⋂_{ι∈U} X_ι ⇒ (∀i)(i∈U ⇒ z∈X_i) )
    elim = instancie(inter_donne_membres(vf, vu, "z"), vz)
    forall = N.modus_ponens(hz, elim)                     # (∀i)(i∈U ⇒ z∈X_i)
    zXc = N.modus_ponens(hc, instancie(forall, vc))       # z∈X_c
    hH = N.assume(est_famille_identite(vf, vu))
    eqc = N.modus_ponens(hc, instancie(hH, vc))           # X_c = c            [sous H]
    zc = N.modus_ponens(zXc, equivalence_avant(N.modus_ponens(   # z∈c   (S6 : X_c=c)
        eqc, N.s6(E.valeur_famille(vf, vc), vc, "w", appartient(vz, var("w"))))))
    gen = N.generalisation("z", N.loi_deduction(appartient(vz, inter_ensemble(vf, vu)), zc))  # {H,c∈U} ⋂U⊂c
    res = N.loi_deduction(appartient(vc, vu), gen)
    assert res.conclusion == enonce_inter_incluse_partie(f, u, c), \
        "inter_incluse_partie : conclusion ≠ énoncé attendu"
    return res


__all__ = ["est_famille_identite", "reunion_ensemble", "inter_ensemble",
           "enonce_membre_reunion_ensemble", "membre_reunion_ensemble",
           "enonce_membre_inter_ensemble", "membre_inter_ensemble",
           "enonce_partie_incluse_reunion", "partie_incluse_reunion",
           "enonce_inter_incluse_partie", "inter_incluse_partie"]
