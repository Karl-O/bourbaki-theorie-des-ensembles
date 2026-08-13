# -*- coding: utf-8 -*-
"""§II.4 — Proposition 1 (E.II.4.1), DUAL INTERSECTION du reparamétrage surjectif.

La version RÉUNION  ⋃_{κ∈K} X_{φ(κ)} = ⋃_{ι∈I} X_ι  (sous φ:K→I surjective) est
déjà close dans `ensembles_chap2_props_restantes` (`reparam_reunion_egal_si_surjectif`).
Ici on ferme son DUAL pour l'INTERSECTION :

    ⋂_{κ∈K} X_{φ(κ)} = ⋂_{ι∈I} X_ι        (E.II.4, Prop. 1, formule duale)

sous les deux hypothèses FIDÈLES :
  • domaine     :  (∀κ)(κ∈K ⇒ φ(κ)∈I)
  • surjectivité:  (∀ι)(ι∈I ⇒ (∃κ)(κ∈K et φ(κ)=ι))

────────────────────────────────────────────────────────────────────────────────
MIGRATION « ⋂ par SÉLECTION DANS ⋃ » (Déf. 2 réparée, cf. `ii_4_intersection_fondation`).
L'ancien AXIOME_INTER_FAM  (z∈⋂ ⇔ (∀i)(i∈I⇒z∈X_i))  était CONTRADICTOIRE pour I=∅.
Le nouvel axiome est une SÉLECTION :

    z ∈ ⋂_{ι∈I} X_ι   ⇔   ( z ∈ ⋃_{ι∈I} X_ι   et   (∀i)((i∈I) ⇒ z∈X_i) )

Conséquences sur CE fichier, chacune traitée explicitement :
  • ÉLIMINATION (z∈⋂ ⇒ (∀i)…) : INCHANGÉE, fournie par `inter_donne_membres`
    (projection droite de la conjonction).
  • INTRODUCTION ((∀i)… ⇒ z∈⋂) : exige désormais un TÉMOIN d'indice, fourni par
    `inter_par_membres_si_temoin_terme`.

STATUT HONNÊTE DES DEUX RÉSULTATS
  • `reparam_inter_incluse` — ÉNONCÉ RENFORCÉ (issue B).  L'ancienne forme, sans
    hypothèse, est FAUSSE : pour K=∅ et I≠∅ on a ⋂_{κ∈∅} X_{φ(κ)} = ∅ tandis que
    ⋂_{ι∈I} X_ι peut être non vide, et l'hypothèse de domaine est vacuément vraie.
    On ajoute donc l'hypothèse de Bourbaki (E II.22, Déf. 2 : « dont l'ensemble
    d'indices n'est pas vide ») sur l'ensemble d'indices CIBLE : (∃i)(i∈K).
  • `reparam_inter_egal_si_surjectif` — ÉNONCÉ INCHANGÉ (issue A).  Sous la
    SURJECTIVITÉ, K=∅ force I=∅, et les deux intersections valent alors ∅ : le cas
    dégénéré se démontre au lieu de s'exclure.  La preuve procède donc par CAS sur
    (∃i)(i∈K) — c'est la surjectivité qui paie l'hypothèse de non-vacuité.

theorie_ensembles() INCHANGÉE (22 ax.).  On réutilise l'infra `famille_reparam` /
`_val_reparam` du module union (mêmes familles reparamétrées, C54).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, tau)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    cas, conjonction_intro, conjonction_elim_gauche as cg,
    conjonction_elim_droite as cd, contraposition, equivalence_avant,
    equivalence_arriere, instancie, projection_gauche, tiers_exclu)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    alpha_existe, existe_elimination, monotonie_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee

from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ensembles_chap2_props_restantes import (
    famille_reparam, _val_reparam, _inst_reunion, _membre_eq)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    inter_donne_membres, inter_inclus_reunion, inter_par_membres_si_temoin_terme)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── outils de migration (motifs (a) élimination / (b) introduction) ───────────
def _membres_de_inter(fam, s, z):
    """⊢ (z ∈ ⋂_{ι∈S} Z_ι) ⇒ (∀i)((i∈S) ⇒ z∈Z_i).   [motif (a) : ÉLIMINATION]

    Remplace l'ancien `equivalence_avant(_inst_inter(...))`, devenu impossible
    puisque le membre droit de la Déf. 2 est maintenant une CONJONCTION."""
    return instancie(inter_donne_membres(fam, s, "z"), _t(z))


def _inter_par_temoin(fam, s, temoin, z):
    """⊢ (T∈S) ⇒ ( (∀i)((i∈S) ⇒ z∈Z_i) ⇒ z ∈ ⋂_{ι∈S} Z_ι ).  [motif (b) : INTRO]"""
    return inter_par_membres_si_temoin_terme(fam, s, temoin, _t(z))


def _indice_depuis_inter(fam, s, z):
    """⊢ (z ∈ ⋂_{ι∈S} Z_ι) ⇒ (∃i)(i∈S).   — la BORNE ⋃ de la sélection au travail.

    z∈⋂ ⇒ z∈⋃ (projection gauche) ⇒ (∃i)(i∈S et z∈Z_i) ⇒ (∃i)(i∈S).
    C'est CE lemme qui rend le cas dégénéré K=∅ démontrable au lieu d'être exclu."""
    vz, vi = _t(z), var("i")
    vers_reunion = instancie(inter_inclus_reunion(fam, s, "z"), vz)
    vers_existe = equivalence_avant(_inst_reunion(fam, s, vz))
    oublie = monotonie_existe(projection_gauche(appartient(vi, s),
                                                appartient(vz, E.valeur_famille(fam, vi))), "i")
    return syllogisme(syllogisme(vers_reunion, vers_existe), oublie)


def _ex_falso(thm_non_p, p, q):
    """De ⊢ ¬P déduire ⊢ (P ⇒ Q)   (impl(P,Q) = ou(¬P,Q), donc S2 suffit)."""
    return N.modus_ponens(thm_non_p, N.s2(non(p), q))


def _temoin_indice(s, i="i"):
    """(τ, ⊢ (∃i)(i∈S) ⇒ τ∈S) — le témoin canonique d'un ensemble d'indices non vide."""
    corps = appartient(var(i), _t(s))
    return tau(i, corps), N.existe_temoin(corps, i)


# ══════════════════════════════════════════════════════════════════════════════
# Sens ⊃ — ÉNONCÉ RENFORCÉ (issue B) : il faut K ≠ ∅.
# ══════════════════════════════════════════════════════════════════════════════
def _cible_incluse(f="X", phi="phi", i="I", k="K"):
    """(∃i)(i∈K) ⇒ ( (∀κ)(κ∈K⇒φ(κ)∈I) ⇒ ⋂_{ι∈I}X_ι ⊂ ⋂_{κ∈K}X_{φ(κ)} )."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    dom_hyp = pourtout("k", impl(appartient(var("k"), vK),
                                 appartient(E.valeur(vphi, var("k")), vI)))
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    return impl(indices_non_vides(vK),
                impl(dom_hyp, inclus(E.inter_famille(vf, vI),
                                     E.inter_famille(famille_reparam(vf, vphi), vK))))


# @livre Ch.II §4.1 Prop.1 | E II.23 L.28-50 | PDF p.74
def reparam_inter_incluse(f="X", phi="phi", i="I", k="K"):
    """⊢ (∃i)(i∈K) ⇒ ( (∀κ)(κ∈K⇒φ(κ)∈I) ⇒ ⋂_{ι∈I} X_ι ⊂ ⋂_{κ∈K} X_{φ(κ)} ).

    (E.II.4, Prop. 1 dual — sens « ⊃ ».)   [domaine + indices K non vides]

    ⚠ ÉNONCÉ RENFORCÉ PAR LA RÉPARATION DE LA DÉF. 2 (issue B).  L'énoncé
    ANTÉRIEUR — la même inclusion sous le SEUL domaine — est FAUX : prendre K=∅
    (le domaine est alors vacuément vrai) et I≠∅ avec ⋂_{ι∈I}X_ι non vide ; le
    membre de droite ⋂_{κ∈∅}X_{φ(κ)} vaut ∅ (`inter_famille_vide_egale_vide`).
    Il était « démontrable » sous l'ANCIEN AXIOME_INTER_FAM parce que celui-ci
    peuplait ⋂_{κ∈∅} de TOUT objet — la contradiction même qu'a tuée la migration.
    On ajoute donc l'hypothèse que Bourbaki écrit (E II.22, Déf. 2, « dont
    l'ensemble d'indices n'est pas vide »), portant sur l'ensemble d'indices CIBLE.

    Preuve.  z∈⋂X_ι donne (∀i)(i∈I⇒z∈X_i) par ÉLIMINATION (motif (a),
    `_membres_de_inter`).  À κ fixé avec κ∈K, le domaine donne φ(κ)∈I, donc
    z∈X_{φ(κ)} (instance), et Y_κ=X_{φ(κ)} (déf. famille reparam) donne z∈Y_κ ;
    d'où (∀κ)(κ∈K⇒z∈Y_κ).  L'INTRODUCTION dans ⋂Y_κ (motif (b)) consomme alors le
    témoin canonique τi(i∈K) livré par l'hypothèse de non-vacuité.
    Inclusion repliée sur le liant FRESH « z »."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vz, vi = var("z"), var("i")
    fam_r = famille_reparam(vf, vphi)
    phii = E.valeur(vphi, vi)
    Yi = E.valeur_famille(fam_r, vi)
    Xphii = E.valeur_famille(vf, phii)
    interX = E.inter_famille(vf, vI)

    ne_hyp = indices_non_vides(vK)                 # (∃i)(i∈K)
    dom_hyp = pourtout("k", impl(appartient(var("k"), vK),
                                 appartient(E.valeur(vphi, var("k")), vI)))
    hNE, hH = N.assume(ne_hyp), N.assume(dom_hyp)
    T0, temoin_th = _temoin_indice(vK)
    t_in_K = N.modus_ponens(hNE, temoin_th)                      # τi(i∈K) ∈ K

    hL = N.assume(appartient(vz, interX))
    forall_iX = N.modus_ponens(hL, _membres_de_inter(vf, vI, vz))  # (∀i)(i∈I⇒z∈X_i)
    # but : (∀i)(i∈K ⇒ z∈Y_i)   (binder « i » de l'axiome INTER sur ⋂Y_κ)
    hi = N.assume(appartient(vi, vK))                            # i∈K
    phii_in_I = N.modus_ponens(hi, instancie(hH, vi))            # φ(i)∈I
    z_Xphii = N.modus_ponens(phii_in_I, instancie(forall_iX, phii))  # z∈X_{φ(i)}
    # z∈X_{φ(i)} = z∈Y_i  (déf. famille reparam : Y_i=X_{φ(i)})
    z_Yi = N.modus_ponens(z_Xphii, equivalence_arriere(
        _membre_eq(Yi, Xphii, _val_reparam(vf, vphi, vi), vz)))   # z∈Y_i
    imp_i = N.loi_deduction(appartient(vi, vK), z_Yi)           # i∈K ⇒ z∈Y_i
    forall_kY = N.generalisation("i", imp_i)                    # (∀i)(i∈K⇒z∈Y_i)
    z_interY = N.modus_ponens(forall_kY,
                              N.modus_ponens(t_in_K, _inter_par_temoin(fam_r, vK, T0, vz)))
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, interX), z_interY))
    res = N.loi_deduction(ne_hyp, N.loi_deduction(dom_hyp, incl))
    assert res.conclusion == _cible_incluse(vf, vphi, vI, vK), \
        "reparam_inter_incluse : conclusion ≠ énoncé (renforcé) attendu"
    return res


def _cible(f="X", phi="phi", i="I", k="K"):
    """L'énoncé visé — INCHANGÉ par la migration (issue A) :
       (domaine et surjectivité) ⇒ ⋂_{κ∈K}X_{φ(κ)} = ⋂_{ι∈I}X_ι."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vk, vi = var("k"), var("i")
    phik = E.valeur(vphi, vk)
    fam_r = famille_reparam(vf, vphi)
    interY = E.inter_famille(fam_r, vK)
    interX = E.inter_famille(vf, vI)
    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    surj_hyp = pourtout("i", impl(appartient(vi, vI),
                                  existe("k", et(appartient(vk, vK), egal(phik, vi)))))
    return impl(et(dom_hyp, surj_hyp), egal(interY, interX))


# ══════════════════════════════════════════════════════════════════════════════
# Cas 1 — K ≠ ∅ : la preuve « normale », rendue au format sélection.
# ══════════════════════════════════════════════════════════════════════════════
def _cas_k_non_vide(vf, vphi, vI, vK, h_dom, h_surj):
    """{dom, surj} ⊢ (∃i)(i∈K) ⇒ ( ⋂_{κ∈K}Y_κ = ⋂_{ι∈I}X_ι ).

    ⊃ : `reparam_inter_incluse` (le domaine et la non-vacuité de K sont là).
    ⊂ : z∈⋂Y_κ ⇒ (∀k)(k∈K⇒z∈Y_k) (élimination) ; pour ι∈I, la surjectivité donne
        κ∈K avec φ(κ)=ι, d'où z∈Y_κ=X_{φ(κ)}=X_ι ; d'où (∀i)(i∈I⇒z∈X_i).
        L'INTRODUCTION dans ⋂X_ι réclame un témoin d'indice DANS I : c'est
        φ(τi(i∈K)), légitimé par l'hypothèse de domaine."""
    vz, vk, vi = var("z"), var("k"), var("i")
    fam_r = famille_reparam(vf, vphi)
    phik = E.valeur(vphi, vk)
    Yk = E.valeur_famille(fam_r, vk)
    Xphik = E.valeur_famille(vf, phik)
    interY, interX = E.inter_famille(fam_r, vK), E.inter_famille(vf, vI)

    ne_hyp = indices_non_vides(vK)
    hNE = N.assume(ne_hyp)
    T0, temoin_th = _temoin_indice(vK)
    t_in_K = N.modus_ponens(hNE, temoin_th)                      # τi(i∈K) ∈ K
    phiT0_in_I = N.modus_ponens(t_in_K, instancie(h_dom, T0))    # φ(τi(i∈K)) ∈ I

    # ── ⊃ : ⋂X_ι ⊂ ⋂Y_κ  (décharge non-vacuité PUIS domaine) ─────────────────
    incl_RL = N.modus_ponens(h_dom, N.modus_ponens(
        hNE, reparam_inter_incluse(vf, vphi, vI, vK)))

    # ── ⊂ : ⋂Y_κ ⊂ ⋂X_ι ─────────────────────────────────────────────────────
    hL = N.assume(appartient(vz, interY))
    forall_k = N.modus_ponens(hL, _membres_de_inter(fam_r, vK, vz))  # (∀i)(i∈K⇒z∈Y_i)
    hi = N.assume(appartient(vi, vI))                             # i∈I
    exk = N.modus_ponens(hi, instancie(h_surj, vi))             # (∃k)(k∈K et φ(k)=ι)
    bodyk = et(appartient(vk, vK), egal(phik, vi))
    hbk = N.assume(bodyk)
    z_Yk = N.modus_ponens(cg(hbk), instancie(forall_k, vk))      # z∈Y_κ
    z_Xphik = N.modus_ponens(z_Yk, equivalence_avant(
        _membre_eq(Yk, Xphik, _val_reparam(vf, vphi, vk), vz)))  # z∈X_{φ(κ)}
    # φ(κ)=ι  donne X_{φ(κ)}=X_ι  (Leibniz sur w ↦ z∈X_w)
    leibniz = N.modus_ponens(cd(hbk), N.s6(phik, vi, "w",
                     appartient(vz, E.valeur_famille(vf, var("w")))))
    z_Xi = N.modus_ponens(z_Xphik, equivalence_avant(leibniz))   # z∈X_ι
    # éliminer le témoin κ (k non libre dans z∈X_ι : terme clos en i)
    imp_k = existe_elimination(N.loi_deduction(bodyk, z_Xi), "k")
    z_Xi_final = N.modus_ponens(exk, imp_k)
    forall_i = N.generalisation("i", N.loi_deduction(appartient(vi, vI), z_Xi_final))
    z_interX = N.modus_ponens(forall_i, N.modus_ponens(
        phiT0_in_I, _inter_par_temoin(vf, vI, E.valeur(vphi, T0), vz)))
    incl_LR = N.generalisation("z", N.loi_deduction(appartient(vz, interY), z_interX))

    egal_th = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                             extensionnalite_appliquee(interY, interX))
    return N.loi_deduction(ne_hyp, egal_th)


# ══════════════════════════════════════════════════════════════════════════════
# Cas 2 — K = ∅ : la SURJECTIVITÉ force I = ∅, et les deux ⋂ valent ∅.
# ══════════════════════════════════════════════════════════════════════════════
def _cas_k_vide(vf, vphi, vI, vK, h_surj):
    """{surj} ⊢ ¬(∃i)(i∈K) ⇒ ( ⋂_{κ∈K}Y_κ = ⋂_{ι∈I}X_ι ).

    Sans la sélection, ce cas serait indémontrable (l'ancien ⋂_{κ∈∅} contenait
    tout).  Ici `_indice_depuis_inter` réfute l'appartenance aux DEUX côtés :
    z∈⋂Y_κ livre un indice de K (contradiction directe) ; z∈⋂X_ι livre un indice
    de I, que la surjectivité convertit en indice de K (même contradiction).
    Les deux inclusions suivent alors ex falso."""
    vz, vk, vi = var("z"), var("k"), var("i")
    fam_r = famille_reparam(vf, vphi)
    interY, interX = E.inter_famille(fam_r, vK), E.inter_famille(vf, vI)
    ne_K = indices_non_vides(vK)
    hV = N.assume(non(ne_K))

    # (∃i)(i∈I) ⇒ (∃i)(i∈K)  — c'est la SURJECTIVITÉ, dépouillée de l'égalité.
    oublie_eq = monotonie_existe(projection_gauche(appartient(vk, vK),
                                                   egal(E.valeur(vphi, vk), vi)), "k")
    vers_K = syllogisme(instancie(h_surj, vi), oublie_eq)        # i∈I ⇒ (∃k)(k∈K)
    align = equivalence_avant(alpha_existe("k", "i", appartient(vk, vK)))
    ex_I_vers_ex_K = existe_elimination(syllogisme(vers_K, align), "i")

    nz_Y = N.modus_ponens(hV, contraposition(_indice_depuis_inter(fam_r, vK, vz)))
    nz_X = N.modus_ponens(hV, contraposition(
        syllogisme(_indice_depuis_inter(vf, vI, vz), ex_I_vers_ex_K)))

    incl_LR = N.generalisation("z", _ex_falso(nz_Y, appartient(vz, interY),
                                              appartient(vz, interX)))
    incl_RL = N.generalisation("z", _ex_falso(nz_X, appartient(vz, interX),
                                              appartient(vz, interY)))
    egal_th = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                             extensionnalite_appliquee(interY, interX))
    return N.loi_deduction(non(ne_K), egal_th)


# @livre Ch.II §4.1 Prop.1 | E II.23 L.28-50 | PDF p.74
def reparam_inter_egal_si_surjectif(f="X", phi="phi", i="I", k="K"):
    """{φ : K→I (∀κ∈K φ(κ)∈I)  et  φ surjective sur I (∀ι∈I ∃κ∈K φ(κ)=ι)}
        ⊢  ⋂_{κ∈K} X_{φ(κ)} = ⋂_{ι∈I} X_ι.   (E.II.4, Prop. 1 dual VERBATIM.)

    ÉNONCÉ INCHANGÉ par la réparation de la Déf. 2 (issue A) — et c'est la
    surjectivité qui le permet : elle interdit « K vide, I non vide », le seul
    couple qui casse le dual.  Preuve par CAS sur (∃i)(i∈K) :
      • K ≠ ∅ (`_cas_k_non_vide`) : preuve usuelle, avec le témoin τi(i∈K) pour
        l'introduction dans ⋂Y_κ et φ(τi(i∈K)) pour celle dans ⋂X_ι ;
      • K = ∅ (`_cas_k_vide`) : la surjectivité vide I aussi, les deux ⋂ sont
        vides (borne ⋃ de la sélection), les inclusions sont ex falso.
    CONDITIONNÉ aux deux hypothèses FIDÈLES, jamais postulé.  Sans surjectivité
    l'égalité est FAUSSE."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vk, vi = var("k"), var("i")
    phik = E.valeur(vphi, vk)
    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    surj_hyp = pourtout("i", impl(appartient(vi, vI),
                                  existe("k", et(appartient(vk, vK), egal(phik, vi)))))
    hyp = et(dom_hyp, surj_hyp)
    hH = N.assume(hyp)
    h_dom, h_surj = cg(hH), cd(hH)

    egal_th = cas(tiers_exclu(indices_non_vides(vK)),
                  _cas_k_non_vide(vf, vphi, vI, vK, h_dom, h_surj),
                  _cas_k_vide(vf, vphi, vI, vK, h_surj))
    res = N.loi_deduction(hyp, egal_th)
    assert res.conclusion == _cible(vf, vphi, vI, vK), \
        "reparam_inter_egal_si_surjectif : conclusion ≠ énoncé (inchangé) attendu"
    return res


__all__ = ["reparam_inter_incluse", "reparam_inter_egal_si_surjectif",
           "_cible", "_cible_incluse"]
