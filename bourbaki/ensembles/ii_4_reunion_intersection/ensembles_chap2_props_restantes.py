"""§II.4 — PROPOSITIONS RESTANTES sur réunion/intersection d'une famille (preuves).

Module NEUF (campagne book-II-restant).  Ne MODIFIE AUCUN fichier existant ;
complète `ensembles_familles` (déf./monotonie/⋃_∅), `ensembles_familles_demorgan`
(Prop. 5) et `ensembles_familles_reunion_props` (Prop. 3/4/6) SANS les dupliquer.

On formalise ici, VERBATIM, des propositions de E.II.4 encore non prouvées et
LOGIQUEMENT DIRECTES :

  • Corollaire de la Prop. 1 (famille constante) — E.II.4.1 :
        si X_ι = X_κ pour tout couple (ι, κ), alors pour tout α∈I,
            ⋃_{ι∈I} X_ι = X_α     et (I ≠ ∅ via α∈I)   ⋂_{ι∈I} X_ι = X_α.
    Théorèmes : `reunion_constante`, `inter_constante` — CONDITIONNÉS aux deux
    hypothèses fidèles (famille constante + α∈I), jamais postulés.

  • Proposition 1 (invariance par reparamétrage surjectif) — E.II.4.1 :
        si f : K → I et Y_κ := X_{f(κ)}, alors
            ⋃_{κ∈K} X_{f(κ)} ⊂ ⋃_{ι∈I} X_ι        (INCONDITIONNEL)
        et, SI f est surjective de K sur I, l'inclusion inverse, d'où l'ÉGALITÉ
            ⋃_{κ∈K} X_{f(κ)} = ⋃_{ι∈I} X_ι.
    Théorèmes : `reparam_reunion_incluse` (incond.) et
    `reparam_reunion_egal_si_surjectif` (CONDITIONNÉ à « f surjective sur I »,
    énoncé verbatim de Bourbaki ; sans surjectivité l'égalité est FAUSSE).

La famille reparamétrée (X_{f(κ)})_{κ∈K} est une famille définie par un terme
(Critère C54) : sa κ-ème valeur est X_{f(κ)}.  On la caractérise par un AXIOME DE
VALEUR dédié, en THÉORIE SÉPARÉE (JAMAIS dans theorie_ensembles qui reste à 22
axiomes), exactement comme AXIOME_COMPL_FAM (De Morgan) ou les axiomes de valeur
de `ensembles_familles_reunion_props` (familles image/réciproque).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, impl,
                                       appartient, existe, pourtout, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg, conjonction_elim_droite as cd,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie as sym_eg
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── instances des axiomes de theorie_ensembles (22 ax., inchangée) ────────────
def _inst_reunion(f, i, z):
    """⊢ (z ∈ ⋃_{ι∈I} X_ι) ⇔ (∃i)(i∈I et z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _inst_inter(f, i, z):
    """⊢ (z ∈ ⋂_{ι∈I} X_ι) ⇔ (∀i)(i∈I ⇒ z∈X_i)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER_FAM)
    return instancie(instancie(instancie(ax, f), i), z)


def _membre_eq(t1, t2, eq_thm, z):
    """De ⊢ t1=t2 déduire ⊢ (z∈t1) ⇔ (z∈t2)   (Leibniz via S6)."""
    return N.modus_ponens(eq_thm, N.s6(t1, t2, "w", appartient(_t(z), var("w"))))


def _sym(eq_thm):
    """De ⊢ T=U déduire ⊢ U=T."""
    t, u = eq_thm.conclusion.termes
    return N.modus_ponens(eq_thm, sym_eg(t, u))


# ══════════════════════════════════════════════════════════════════════════════
# Corollaire de la Prop. 1 — FAMILLE CONSTANTE  (E.II.4.1).
#   si X_ι = X_κ pour tout (ι,κ), alors  ⋃_{ι∈I}X_ι = X_α  et  ⋂_{ι∈I}X_ι = X_α
#   pour tout α∈I.
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §4.1 Cor.- | E II.23 L.29-31 | PDF p.74
def reunion_constante(f="X", i="I", a="a"):
    """{(∀ι)(∀κ)(X_ι = X_κ) ,  α∈I} ⊢ ⋃_{ι∈I} X_ι = X_α.   (Cor. Prop. 1, E.II.4.1.)

    INCONDITIONNEL modulo les deux hypothèses FIDÈLES (famille constante + α∈I).
    ⊂ : z∈⋃X_ι ⇒ (∃ι)(ι∈I et z∈X_ι) ; pour le témoin ι, X_ι = X_α (constance),
        donc z∈X_α.
    ⊃ : z∈X_α avec α∈I donne (ι=α) le témoin de (∃ι)(ι∈I et z∈X_ι)."""
    vf, vI, va = _t(f), _t(i), _t(a)
    vz, vi = var("z"), var("i")
    Xi = E.valeur_famille(vf, vi)
    Xa = E.valeur_famille(vf, va)
    reun = E.reunion_famille(vf, vI)
    cst = pourtout("i", pourtout("k",
        egal(E.valeur_famille(vf, vi), E.valeur_famille(vf, var("k")))))
    a_in = appartient(va, vI)
    hyp = et(cst, a_in)
    hH = N.assume(hyp)
    h_cst = cg(hH)
    h_a = cd(hH)

    # ── ⊂ : ⋃X_ι ⊂ X_α ──────────────────────────────────────────────────────
    hL = N.assume(appartient(vz, reun))
    exi = N.modus_ponens(hL, equivalence_avant(_inst_reunion(vf, vI, vz)))  # (∃i)(i∈I et z∈X_i)
    body = et(appartient(vi, vI), appartient(vz, Xi))
    hb = N.assume(body)
    eq_ia = instancie(instancie(h_cst, vi), va)               # X_i = X_α
    z_in_Xa = N.modus_ponens(cd(hb), equivalence_avant(_membre_eq(Xi, Xa, eq_ia, vz)))
    imp_i = existe_elimination(N.loi_deduction(body, z_in_Xa), "i")
    z_Xa = N.modus_ponens(exi, imp_i)
    incl_LR = N.generalisation("z", N.loi_deduction(appartient(vz, reun), z_Xa))

    # ── ⊃ : X_α ⊂ ⋃X_ι ──────────────────────────────────────────────────────
    hR = N.assume(appartient(vz, Xa))
    # témoin ι = α : (α∈I et z∈X_α)
    bodyA = et(appartient(vi, vI), appartient(vz, Xi))
    ex_a = N.modus_ponens(conjonction_intro(h_a, hR), N.s5(bodyA, va, "i"))
    z_reun = N.modus_ponens(ex_a, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    incl_RL = N.generalisation("z", N.loi_deduction(appartient(vz, Xa), z_reun))

    egal_th = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                             extensionnalite_appliquee(reun, Xa))
    return N.loi_deduction(hyp, egal_th)


# @livre Ch.II §4.1 Cor.- | E II.23 L.29-31 | PDF p.74
def inter_constante(f="X", i="I", a="a"):
    """{(∀ι)(∀κ)(X_ι = X_κ) ,  α∈I} ⊢ ⋂_{ι∈I} X_ι = X_α.   (Cor. Prop. 1, E.II.4.1.)

    INCONDITIONNEL modulo les deux hypothèses FIDÈLES (la clause α∈I incarne « I ≠ ∅ »).
    ⊂ : z∈⋂X_ι ⇒ (∀ι)(ι∈I ⇒ z∈X_ι) ; en ι=α (α∈I) : z∈X_α.
    ⊃ : z∈X_α ⇒ pour tout ι∈I, X_ι = X_α (constance) donne z∈X_ι, d'où z∈⋂X_ι."""
    vf, vI, va = _t(f), _t(i), _t(a)
    vz, vi = var("z"), var("i")
    Xi = E.valeur_famille(vf, vi)
    Xa = E.valeur_famille(vf, va)
    inter = E.inter_famille(vf, vI)
    cst = pourtout("i", pourtout("k",
        egal(E.valeur_famille(vf, vi), E.valeur_famille(vf, var("k")))))
    a_in = appartient(va, vI)
    hyp = et(cst, a_in)
    hH = N.assume(hyp)
    h_cst = cg(hH)
    h_a = cd(hH)

    # ── ⊂ : ⋂X_ι ⊂ X_α ──────────────────────────────────────────────────────
    hL = N.assume(appartient(vz, inter))
    fa = N.modus_ponens(hL, equivalence_avant(_inst_inter(vf, vI, vz)))    # (∀i)(i∈I ⇒ z∈X_i)
    z_Xa = N.modus_ponens(h_a, instancie(fa, va))                         # z∈X_α
    incl_LR = N.generalisation("z", N.loi_deduction(appartient(vz, inter), z_Xa))

    # ── ⊃ : X_α ⊂ ⋂X_ι ──────────────────────────────────────────────────────
    hR = N.assume(appartient(vz, Xa))
    hI = N.assume(appartient(vi, vI))
    eq_ai = instancie(instancie(h_cst, va), vi)                           # X_α = X_i
    z_in_Xi = N.modus_ponens(hR, equivalence_avant(_membre_eq(Xa, Xi, eq_ai, vz)))
    forall_i = N.generalisation("i", N.loi_deduction(appartient(vi, vI), z_in_Xi))
    z_inter = N.modus_ponens(forall_i, equivalence_arriere(_inst_inter(vf, vI, vz)))
    incl_RL = N.generalisation("z", N.loi_deduction(appartient(vz, Xa), z_inter))

    egal_th = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                             extensionnalite_appliquee(inter, Xa))
    return N.loi_deduction(hyp, egal_th)


# ══════════════════════════════════════════════════════════════════════════════
# Proposition 1 — REPARAMÉTRAGE SURJECTIF  (E.II.4.1).
#   famille reparamétrée  Y := (X_{f(κ)})_{κ∈K}  ,  Y_κ = X_{f(κ)}.
# ══════════════════════════════════════════════════════════════════════════════
def famille_reparam(f, phi):
    """(X_{f(κ)})_{κ∈K} := la famille κ ↦ X_{f(κ)}  (reparamétrage par φ=phi).

    f = famille (X_ι), phi = graphe de l'application K → I.  La κ-ème valeur est
    X_{φ(κ)} = valeur_famille(f, φ(κ)).  Famille définie par un terme (C54)."""
    return app("fam_reparam", f, phi)


def axiome_valeur_reparam(f, phi, k="k"):
    """(∀κ)( Y_κ = X_{φ(κ)} ).   (C54 ; comme AXIOME_COMPL_FAM.)"""
    vk = var(k)
    return pourtout(k, egal(E.valeur_famille(famille_reparam(f, phi), vk),
                            E.valeur_famille(f, E.valeur(phi, vk))))


def theorie_valeur_reparam(f, phi, k="k"):
    """Théorie dédiée : axiome de valeur de Y_κ = X_{φ(κ)} (C54)."""
    return N.Theorie("Famille-reparam", [axiome_valeur_reparam(f, phi, k)])


def _val_reparam(f, phi, k):
    """⊢ Y_κ = X_{φ(κ)}   (instance de la theorie dédiée)."""
    ax = N.axiome(theorie_valeur_reparam(f, phi), axiome_valeur_reparam(f, phi))
    return instancie(ax, _t(k))


# @livre Ch.II §4.1 Prop.1 | E II.23 L.16-17 | PDF p.74
def reparam_reunion_incluse(f="X", phi="phi", i="I", k="K"):
    """⊢ ⋃_{κ∈K} X_{φ(κ)} ⊂ ⋃_{ι∈I} X_ι.   (E.II.4, Prop. 1 — sens facile.)

    INCONDITIONNEL.  z∈⋃Y_κ ⇒ (∃κ)(κ∈K et z∈Y_κ) ; pour ce témoin κ, Y_κ=X_{φ(κ)}
    donc z∈X_{φ(κ)} avec ι=φ(κ) un indice ; on N'A PAS BESOIN de φ(κ)∈I — l'axiome
    REUNION_FAM ne contraint pas l'indice témoin à I, mais ici l'énoncé fidèle
    suppose φ : K → I, donc φ(κ)∈I est légitime : on l'OBTIENT en chargeant
    l'hypothèse de domaine.  Ici on livre la version SANS hypothèse de domaine,
    qui exige seulement la définition de Y et la caractérisation de ⋃ : on pose
    ι := φ(κ) comme témoin direct.  (Bourbaki suppose φ application K→I ; l'indice
    φ(κ) est alors dans I, ce que la version `_egal` charge explicitement.)

    On charge ici l'hypothèse fidèle minimale  φ(κ)∈I  via (∀κ)(κ∈K ⇒ φ(κ)∈I).
    NB : l'axiome REUNION_FAM lie l'indice témoin par la lettre « i » ; on aligne
    donc le binder de la boucle-K sur « i » (les deux ∃ sont en portées disjointes)."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vz, vi = var("z"), var("i")
    fam_r = famille_reparam(vf, vphi)
    Yi = E.valeur_famille(fam_r, vi)
    phii = E.valeur(vphi, vi)
    Xphii = E.valeur_famille(vf, phii)
    reunY = E.reunion_famille(fam_r, vK)
    reunX = E.reunion_famille(vf, vI)

    # hypothèse de domaine fidèle :  (∀κ)(κ∈K ⇒ φ(κ)∈I)
    dom_hyp = pourtout("k", impl(appartient(var("k"), vK),
                                 appartient(E.valeur(vphi, var("k")), vI)))
    hH = N.assume(dom_hyp)

    hL = N.assume(appartient(vz, reunY))
    exk = N.modus_ponens(hL, equivalence_avant(_inst_reunion(fam_r, vK, vz)))  # (∃i)(i∈K et z∈Y_i)
    body = et(appartient(vi, vK), appartient(vz, Yi))
    hb = N.assume(body)
    k_in = cg(hb)
    z_Yi = cd(hb)
    phii_in_I = N.modus_ponens(k_in, instancie(hH, vi))         # φ(i)∈I
    # z∈Y_i = z∈X_{φ(i)}
    z_Xphii = N.modus_ponens(z_Yi, equivalence_avant(
        _membre_eq(Yi, Xphii, _val_reparam(vf, vphi, vi), vz)))
    # témoin ι=φ(i) : (φ(i)∈I et z∈X_{φ(i)})  ⇒  z∈⋃X_ι.  L'existentielle introduite
    # est exactement (∃i)(i∈I et z∈X_i) (binder « i » de l'axiome), donc se referme
    # directement par REUNION_FAM.  L'éigenvariable « i » de l'élimination-K
    # n'apparaît pas libre dans z∈⋃X_ι (terme clos), donc l'élimination est valide.
    bodyI = et(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    ex_j = N.modus_ponens(conjonction_intro(phii_in_I, z_Xphii), N.s5(bodyI, phii, "i"))
    z_reunX = N.modus_ponens(ex_j, equivalence_arriere(_inst_reunion(vf, vI, vz)))
    imp_k = existe_elimination(N.loi_deduction(body, z_reunX), "i")
    z_in = N.modus_ponens(exk, imp_k)
    incl = N.generalisation("z", N.loi_deduction(appartient(vz, reunY), z_in))
    return N.loi_deduction(dom_hyp, incl)


# @livre Ch.II §4.1 Prop.1 | E II.23 L.16-17 | PDF p.74
def reparam_reunion_egal_si_surjectif(f="X", phi="phi", i="I", k="K"):
    """{φ : K→I (∀κ∈K φ(κ)∈I)  et  φ surjective sur I (∀ι∈I ∃κ∈K φ(κ)=ι)}
        ⊢  ⋃_{κ∈K} X_{φ(κ)} = ⋃_{ι∈I} X_ι.   (E.II.4, Prop. 1 VERBATIM.)

    Le sens ⊂ est inconditionnel modulo le domaine (`reparam_reunion_incluse`).
    Le sens ⊃ exige la SURJECTIVITÉ : z∈⋃X_ι ⇒ (∃ι)(ι∈I et z∈X_ι) ; par
    surjectivité ι=φ(κ) pour un κ∈K, donc z∈X_{φ(κ)}=Y_κ, d'où z∈⋃Y_κ.
    CONDITIONNÉ aux deux hypothèses FIDÈLES (domaine + surjectivité), jamais postulé.
    Sans surjectivité l'égalité est FAUSSE (un X_ι, ι hors image, manquerait)."""
    vf, vphi, vI, vK = _t(f), _t(phi), _t(i), _t(k)
    vz, vk, vi = var("z"), var("k"), var("i")
    fam_r = famille_reparam(vf, vphi)
    phik = E.valeur(vphi, vk)
    Yk = E.valeur_famille(fam_r, vk)
    Xphik = E.valeur_famille(vf, phik)
    Xi = E.valeur_famille(vf, vi)
    reunY = E.reunion_famille(fam_r, vK)
    reunX = E.reunion_famille(vf, vI)

    dom_hyp = pourtout("k", impl(appartient(vk, vK), appartient(phik, vI)))
    surj_hyp = pourtout("i", impl(appartient(vi, vI),
                                  existe("k", et(appartient(vk, vK), egal(phik, vi)))))
    hyp = et(dom_hyp, surj_hyp)
    hH = N.assume(hyp)
    h_dom = cg(hH)
    h_surj = cd(hH)

    # ── ⊂ : ⋃Y_κ ⊂ ⋃X_ι  (décharge le domaine de reparam_reunion_incluse) ────
    incl_LR = N.modus_ponens(h_dom, reparam_reunion_incluse(vf, vphi, vI, vK))

    # ── ⊃ : ⋃X_ι ⊂ ⋃Y_κ ─────────────────────────────────────────────────────
    hR = N.assume(appartient(vz, reunX))
    exi = N.modus_ponens(hR, equivalence_avant(_inst_reunion(vf, vI, vz)))  # (∃i)(i∈I et z∈X_i)
    body = et(appartient(vi, vI), appartient(vz, Xi))
    hb = N.assume(body)
    i_in = cg(hb)
    z_Xi = cd(hb)
    exk = N.modus_ponens(i_in, instancie(h_surj, vi))          # (∃κ)(κ∈K et φ(κ)=ι)
    bodyk = et(appartient(vk, vK), egal(phik, vi))
    hbk = N.assume(bodyk)
    k_in = cg(hbk)
    phik_eq_i = cd(hbk)                                        # φ(κ)=ι
    # z∈X_i  et  φ(κ)=ι  donne z∈X_{φ(κ)}  (Leibniz sur le prédicat w ↦ z∈X_w)
    i_eq_phik = _sym(phik_eq_i)                               # ι=φ(κ)
    leibniz = N.modus_ponens(i_eq_phik, N.s6(vi, phik, "w",
                     appartient(vz, E.valeur_famille(vf, var("w")))))  # (z∈X_i)⇔(z∈X_{φ(κ)})
    z_Xphik = N.modus_ponens(z_Xi, equivalence_avant(leibniz))  # z∈X_{φ(κ)}
    z_Yk = N.modus_ponens(z_Xphik, equivalence_arriere(
        _membre_eq(Yk, Xphik, _val_reparam(vf, vphi, vk), vz)))  # z∈Y_κ
    # témoin κ : (κ∈K et z∈Y_κ) ⇒ z∈⋃Y_κ.  L'existentielle de ⋃Y est liée par
    # « i » (axiome REUNION_FAM) ; on introduit donc (∃i)(i∈K et z∈Y_i) avec le
    # témoin κ.  L'éigenvariable « k » de l'élimination-surjectivité n'apparaît
    # pas libre dans z∈⋃Y (terme clos).
    bodyY = et(appartient(vi, vK), appartient(vz, E.valeur_famille(fam_r, vi)))
    ex_kY = N.modus_ponens(conjonction_intro(k_in, z_Yk), N.s5(bodyY, vk, "i"))
    z_reunY = N.modus_ponens(ex_kY, equivalence_arriere(_inst_reunion(fam_r, vK, vz)))
    imp_k = existe_elimination(N.loi_deduction(bodyk, z_reunY), "k")
    z_reunY_k = N.modus_ponens(exk, imp_k)
    imp_i = existe_elimination(N.loi_deduction(body, z_reunY_k), "i")
    z_in = N.modus_ponens(exi, imp_i)
    incl_RL = N.generalisation("z", N.loi_deduction(appartient(vz, reunX), z_in))

    egal_th = N.modus_ponens(conjonction_intro(incl_LR, incl_RL),
                             extensionnalite_appliquee(reunY, reunX))
    return N.loi_deduction(hyp, egal_th)


__all__ = [
    # Cor. Prop. 1 — famille constante
    "reunion_constante", "inter_constante",
    # Prop. 1 — reparamétrage surjectif
    "famille_reparam", "axiome_valeur_reparam", "theorie_valeur_reparam",
    "reparam_reunion_incluse", "reparam_reunion_egal_si_surjectif",
]
