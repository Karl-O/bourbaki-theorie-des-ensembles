"""Chapitre III §2 — THÉORÈME DE ZORN (Théorème 2), via BOURBAKI–WITT.

Module NEUF.  Il PROUVE le Théorème de Zorn

    zorn_theoreme() :  ( est_ordre(G,E) ∧ est_inductif(G,E) ∧ E≠∅ )
                          ⇒ (∃m) element_maximal(G,E,m)

à partir du CŒUR LOGIQUE déjà certifié `bw_strict_contradiction`
(ensembles_bourbaki_witt_chaine.py, LU D'ABORD) : « les hypothèses de
Bourbaki–Witt + une application STRICTEMENT inflationnaire sont contradictoires ».

RECETTE (Zorn ⇐ Bourbaki–Witt par le poset des CHAÎNES) :
  1. P := { C∈𝔓(E) | chaine(G,E,C) }, ordonné par l'INCLUSION Γ_⊂.
     [terme opaque + axiome DÉFINITIONNEL ; motif `axiome_M`/`axiome_D`.]
  2. (Γ,P) est CHAÎNE-COMPLET : une Γ-chaîne 𝔇 a pour borne sup l'UNION ⋃𝔇 ∈ P.
     [le cœur ; ⋃𝔇 = terme opaque `Union` + axiome de membership.]
  3. ∅ ∈ P (chaîne vide) = plus petit élément de (P,⊂).
  4. SOUS « E sans élément maximal » : f(C) := C ∪ {τ(majorant strict de C)} est
     STRICTEMENT inflationnaire sur (P,⊂)  [signe τ, axiome du choix].
  5. bw_strict_contradiction(Γ,P,f,∅) ⇒ contradiction sous « E inductif sans
     maximal » ⇒ par l'absurde (∃m) element_maximal(G,E,m).

INVARIANT : theorie_ensembles() reste = 22 (axiomes de P/Γ/Union en théories
DÉDIÉES, motif Mc/Cext/M).  Rien n'est postulé : le maximal et le point fixe sont
DÉMONTRÉS (via bw_strict_contradiction), JAMAIS supposés.

NOTATIONS d'ordre :  x ≤ y := (x,y)∈G   [_le] ;   X ⊂ Y := inclus(X,Y).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme, a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite, contraposition, cas, tiers_exclu,
    equivalence_avant, equivalence_arriere, equivalence_symetrie, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    monotonie_existe, existe_elimination,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie as _sym
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, reflexivite_sur, antisymetrie, transitivite_rel, totalement_ordonne,
    majorant, borne_superieure, plus_grand_element, plus_petit_element,
    element_maximal,
)
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine, est_inductif, enonce_non_vide, zorn,
)
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt import (
    pval, inflationnaire, application_dans, chaine_complet, est_tour,
)
from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import (
    inflationnaire_strict, bw_strict_contradiction,
)


# Trou de substitution Leibniz GARANTI FRAIS.
_H = "hole_leibniz_zorn"


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _le(x, y, G):
    """Formule « x ≤ y » := (x,y)∈G."""
    return appartient(E.couple(_terme(x), _terme(y)), _terme(G))


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _incl_refl(t):
    """⊢ t⊂t  pour un TERME t."""
    from bourbaki.logique.tactiques.tactiques_abrege import inclusion_reflexive
    th = inclusion_reflexive("_r")
    return instancie(N.generalisation("_r", th), _terme(t))


def _incl_trans(a, b, c, ab, bc):
    """De ⊢ a⊂b [ab] et ⊢ b⊂c [bc] (TERMES) déduit ⊢ a⊂c.

    Réécriture DIRECTE de la transitivité de ⊂ avec le MÊME binder d'élément que
    la forme canonique `inclus(a,c)` (auto-freshening si x/y/z y est libre), pour
    que la conclusion soit STRUCTURELLEMENT identique à inclus(a,c) — cas du poset
    P où les chaînes portent les noms x/y/z."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    va, vb, vc = _terme(a), _terme(b), _terme(c)
    cible = inclus(va, vc)                               # (∀<bndr>)(<bndr>∈a ⇒ <bndr>∈c)
    bndr, _ = _peler_pourtout(cible)                     # le binder réel du ∀ (souvent @0)
    zt = var(bndr)
    hz = N.assume(appartient(zt, va))                    # z∈a
    z_in_b = N.modus_ponens(hz, instancie(ab, zt))       # z∈b
    z_in_c = N.modus_ponens(z_in_b, instancie(bc, zt))   # z∈c
    body = N.loi_deduction(appartient(zt, va), z_in_c)   # z∈a ⇒ z∈c
    return N.generalisation(bndr, body)                  # a⊂c


def _ou_gauche(thm_p, q):
    """De ⊢ P, déduit ⊢ (P OU Q)."""
    return N.modus_ponens(thm_p, N.s2(thm_p.conclusion, q))


def _ou_droite(thm_q, p):
    """De ⊢ Q, déduit ⊢ (P OU Q)."""
    q = thm_q.conclusion
    return N.modus_ponens(N.modus_ponens(thm_q, N.s2(q, p)), N.s3(q, p))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — le POSET DES CHAÎNES :  P := { C∈𝔓(E) | chaine(G,E,C) }
#  Terme opaque + axiome DÉFINITIONNEL (S8+A1, motif axiome_M/axiome_Mc).
#  theorie_ensembles() reste INCHANGÉE = 22.
# ════════════════════════════════════════════════════════════════════════════
def P(G, E_set):
    """P(G,E) := { C | chaine(G,E,C) }  (l'ensemble des chaînes de E)."""
    return E.app("zorn_P", _terme(G), _terme(E_set))


def axiome_P(G="G", E_set="E", C="C"):
    """⊢-schéma (∀G E C)( C∈P ⇔ chaine(G,E,C) ).

    Axiome DÉFINITIONNEL du poset des chaînes (sélection S8+A1, motif axiome_M).
    N'altère PAS theorie_ensembles()."""
    vG, vE, vC = var(G), var(E_set), var(C)
    return pourtout(G, pourtout(E_set, pourtout(C,
        equiv(appartient(vC, P(vG, vE)), chaine(vG, vE, vC)))))


def theorie_P(G="G", E_set="E", C="C"):
    """Théorie DÉDIÉE ne contenant que l'axiome de P (E.III.2, Zorn, ÉTAPE 1)."""
    return N.Theorie("P-Zorn", [axiome_P(G, E_set, C)])


def _inst_P(G, E_set, C):
    """⊢ ( C∈P ⇔ chaine(G,E,C) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_P(), axiome_P())
    for tm in (G, E_set, C):
        ax = instancie(ax, _terme(tm))
    return ax


def P_membre(G="G", E_set="E", C="C"):
    """⊢ ( C∈P ) ⇔ chaine(G,E,C)."""
    return _inst_P(var(G), var(E_set), var(C))


# ════════════════════════════════════════════════════════════════════════════
#  Le GRAPHE D'ORDRE Γ_⊂ sur P :  (C,D)∈Γ ⇔ (C∈P et D∈P et C⊂D)
#  Terme opaque + axiome DÉFINITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def Gamma(G, E_set):
    """Γ(G,E) := { (C,D) | C∈P et D∈P et C⊂D }  (graphe de l'inclusion sur P)."""
    return E.app("zorn_Gamma", _terme(G), _terme(E_set))


def _corps_Gamma(G, E_set, C, D):
    """Corps de Γ :  C∈P et D∈P et C⊂D."""
    vP = P(_terme(G), _terme(E_set))
    return et(et(appartient(_terme(C), vP), appartient(_terme(D), vP)),
              inclus(_terme(C), _terme(D)))


def axiome_Gamma(G="G", E_set="E", C="C", D="D"):
    """⊢-schéma (∀G E C D)( (C,D)∈Γ ⇔ (C∈P et D∈P et C⊂D) ).

    Axiome DÉFINITIONNEL du graphe d'inclusion sur P (S8+A1).  N'altère PAS
    theorie_ensembles()."""
    vG, vE, vC, vD = var(G), var(E_set), var(C), var(D)
    return pourtout(G, pourtout(E_set, pourtout(C, pourtout(D,
        equiv(appartient(E.couple(vC, vD), Gamma(vG, vE)),
              _corps_Gamma(vG, vE, vC, vD))))))


def theorie_Gamma(G="G", E_set="E", C="C", D="D"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Γ (E.III.2, Zorn, ÉTAPE 1)."""
    return N.Theorie("Gamma-Zorn", [axiome_Gamma(G, E_set, C, D)])


def _inst_Gamma(G, E_set, C, D):
    """⊢ ( (C,D)∈Γ ⇔ (C∈P et D∈P et C⊂D) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Gamma(), axiome_Gamma())
    for tm in (G, E_set, C, D):
        ax = instancie(ax, _terme(tm))
    return ax


def Gamma_membre(G="G", E_set="E", C="C", D="D"):
    """⊢ ( (C,D)∈Γ ) ⇔ ( C∈P et D∈P et C⊂D )."""
    return _inst_Gamma(var(G), var(E_set), var(C), var(D))


def _gle(C, D, G, E_set):
    """Formule « (C,D)∈Γ »  (l'ordre du poset P, i.e. C⊂D)."""
    return appartient(E.couple(_terme(C), _terme(D)), Gamma(_terme(G), _terme(E_set)))


def _Gamma_intro(G, E_set, C, D, hCP, hDP, hCD):
    """De ⊢ C∈P [hCP], ⊢ D∈P [hDP], ⊢ C⊂D [hCD], déduit ⊢ (C,D)∈Γ."""
    corps = conjonction_intro(conjonction_intro(hCP, hDP), hCD)
    return N.modus_ponens(corps, equivalence_arriere(_inst_Gamma(G, E_set, C, D)))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (suite) — Γ est un ORDRE sur P  (⊂ réflexive/antisym/transitive)
# ════════════════════════════════════════════════════════════════════════════
def Gamma_reflexive_sur(G="G", E_set="E", C="x"):
    """⊢ reflexivite_sur(Γ,P).   = (∀x)( x∈P ⇒ (x,x)∈Γ ).

    Si C∈P alors C⊂C (réflexivité de l'inclusion), donc (C,C)∈Γ.  Le binder par
    défaut est « x » pour matcher reflexivite_sur(Γ,P)."""
    vG, vE, vC = var(G), var(E_set), var(C)
    hCP = N.assume(appartient(vC, P(vG, vE)))             # C∈P
    CC = _incl_refl(vC)                                   # C⊂C
    CC_Gamma = _Gamma_intro(vG, vE, vC, vC, hCP, hCP, CC) # (C,C)∈Γ
    body = N.loi_deduction(appartient(vC, P(vG, vE)), CC_Gamma)
    return N.generalisation(C, body)                     # (∀C)(C∈P⇒(C,C)∈Γ)


def Gamma_antisymetrique(G="G", E_set="E", C="x", D="y"):
    """⊢ antisymetrie(Γ).   = (∀x∀y)( ((x,y)∈Γ et (y,x)∈Γ) ⇒ x=y ).

    (C,D)∈Γ ⇒ C⊂D ; (D,C)∈Γ ⇒ D⊂C ; l'antisymétrie de ⊂ (A1) donne C=D.  Binders
    par défaut « x,y » pour matcher antisymetrie(Γ)."""
    from bourbaki.ensembles.ensembles_theoremes import extensionnalite_appliquee
    vG, vE, vC, vD = var(G), var(E_set), var(C), var(D)
    hyp = et(_gle(vC, vD, vG, vE), _gle(vD, vC, vG, vE))
    h = N.assume(hyp)
    CD = conjonction_elim_droite(N.modus_ponens(conjonction_elim_gauche(h),
                                                equivalence_avant(_inst_Gamma(vG, vE, vC, vD))))  # C⊂D
    DC = conjonction_elim_droite(N.modus_ponens(conjonction_elim_droite(h),
                                                equivalence_avant(_inst_Gamma(vG, vE, vD, vC))))  # D⊂C
    a1 = extensionnalite_appliquee(vC, vD)               # (C⊂D et D⊂C)⇒C=D
    C_eq_D = N.modus_ponens(conjonction_intro(CD, DC), a1)  # C=D
    body = N.loi_deduction(hyp, C_eq_D)
    return N.generalisation(C, N.generalisation(D, body))


def Gamma_transitive(G="G", E_set="E", C="x", D="y", F="z"):
    """⊢ transitivite_rel(Γ).   = (∀x∀y∀z)( ((x,y)∈Γ et (y,z)∈Γ) ⇒ (x,z)∈Γ ).

    (C,D)∈Γ ⇒ C∈P, C⊂D ; (D,F)∈Γ ⇒ F∈P, D⊂F ; transitivité de ⊂ ⇒ C⊂F, et
    C∈P, F∈P ⇒ (C,F)∈Γ.  Binders par défaut « x,y,z » pour matcher
    transitivite_rel(Γ)."""
    vG, vE, vC, vD, vF = var(G), var(E_set), var(C), var(D), var(F)
    hyp = et(_gle(vC, vD, vG, vE), _gle(vD, vF, vG, vE))
    h = N.assume(hyp)
    cdcorps = N.modus_ponens(conjonction_elim_gauche(h),
                             equivalence_avant(_inst_Gamma(vG, vE, vC, vD)))  # C∈P et D∈P et C⊂D
    dfcorps = N.modus_ponens(conjonction_elim_droite(h),
                             equivalence_avant(_inst_Gamma(vG, vE, vD, vF)))  # D∈P et F∈P et D⊂F
    CP = conjonction_elim_gauche(conjonction_elim_gauche(cdcorps))  # C∈P
    FP = conjonction_elim_droite(conjonction_elim_gauche(dfcorps))  # F∈P
    CD = conjonction_elim_droite(cdcorps)                # C⊂D
    DF = conjonction_elim_droite(dfcorps)                # D⊂F
    CF = _incl_trans(vC, vD, vF, CD, DF)                 # C⊂F
    CF_Gamma = _Gamma_intro(vG, vE, vC, vF, CP, FP, CF)  # (C,F)∈Γ
    body = N.loi_deduction(hyp, CF_Gamma)
    return N.generalisation(C, N.generalisation(D, N.generalisation(F, body)))


def Gamma_est_ordre(G="G", E_set="E"):
    """⊢ est_ordre(Γ,P).   (L'inclusion Γ_⊂ est un ordre sur le poset des chaînes.)

    INCONDITIONNEL : réflexivité (Gamma_reflexive_sur), antisymétrie (A1),
    transitivité de ⊂ ; aucune hypothèse.  Binders « x,y,z » → matche l'énoncé
    canonique est_ordre(Γ,P)."""
    refl = Gamma_reflexive_sur(G, E_set, "x")
    antisym = Gamma_antisymetrique(G, E_set, "x", "y")
    trans = Gamma_transitive(G, E_set, "x", "y", "z")
    return conjonction_intro(conjonction_intro(refl, antisym), trans)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — ∅ ∈ P (chaîne vide) = PLUS PETIT élément de (P,⊂)
# ════════════════════════════════════════════════════════════════════════════
def _nz_vide(z):
    """⊢ ¬( z ∈ ∅ )  pour un TERME z  (axiome du vide instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    return instancie(ax, _terme(z))


def _exfalso_vide(z, phi):
    """De z TERME et une formule Φ, déduit ⊢ ( z∈∅ ⇒ Φ )  (vacuité)."""
    nz = _nz_vide(z)                                       # ¬(z∈∅)
    # ¬(z∈∅) ⇒ (¬(z∈∅) ∨ Φ) = (z∈∅ ⇒ Φ)
    return N.modus_ponens(nz, N.s2(non(appartient(_terme(z), E.VIDE)), phi))


def _vide_inclus(t, z="_zv"):
    """⊢ ∅ ⊂ t  pour un TERME t  (l'ensemble vide est inclus dans tout ensemble).

    Binder choisi pour matcher inclus(∅,t)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    vt = _terme(t)
    cible = inclus(E.VIDE, vt)
    bndr, _ = _peler_pourtout(cible)
    zt = var(bndr)
    imp = _exfalso_vide(zt, appartient(zt, vt))           # z∈∅ ⇒ z∈t
    return N.generalisation(bndr, imp)                    # ∅⊂t


def vide_est_chaine(G="G", E_set="E"):
    """⊢ { antisymetrie(G), transitivite_rel(G) } ⊢ chaine(G,E,∅).

    L'ensemble VIDE est une chaîne de E : ∅⊂E (vacuité) et totalement_ordonne(G,∅).
    totalement_ordonne(G,∅) = est_ordre(G,∅) et comparables(∅) ; réflexivité sur ∅
    et comparabilité sur ∅ sont VACUEMENT vraies ; antisymétrie/transitivité de G
    sont des propriétés GLOBALES de G (portées en hypothèse)."""
    vG, vE = var(G), var(E_set)
    Has = N.assume(antisymetrie(vG))                      # antisymetrie(G)
    Htr = N.assume(transitivite_rel(vG))                 # transitivite_rel(G)
    # ∅⊂E
    vide_E = _vide_inclus(vE)                             # ∅⊂E
    # reflexivite_sur(G,∅) = (∀x)(x∈∅ ⇒ (x,x)∈G)  — vacuité
    vx, vy = var("x"), var("y")
    refl_body = _exfalso_vide(vx, _le(vx, vx, vG))        # x∈∅ ⇒ (x,x)∈G
    refl_vide = N.generalisation("x", refl_body)          # reflexivite_sur(G,∅)
    ord_vide = conjonction_intro(conjonction_intro(refl_vide, Has), Htr)  # est_ordre(G,∅)
    # comparables : (∀x∀y)((x∈∅ et y∈∅) ⇒ ((x,y)∈G ou (y,x)∈G)) — vacuité
    cible_comp = ou(_le(vx, vy, vG), _le(vy, vx, vG))
    comp_body = _exfalso_vide_conj(vx, vy, cible_comp)    # (x∈∅ et y∈∅) ⇒ but
    comp_vide = N.generalisation("x", N.generalisation("y", comp_body))
    tot_vide = conjonction_intro(ord_vide, comp_vide)     # totalement_ordonne(G,∅)
    return conjonction_intro(vide_E, tot_vide)            # chaine(G,E,∅)


def _exfalso_vide_conj(x, y, phi):
    """De x,y TERMES et Φ, déduit ⊢ ( (x∈∅ et y∈∅) ⇒ Φ )  (vacuité via x∈∅)."""
    vx = _terme(x)
    H = N.assume(et(appartient(vx, E.VIDE), appartient(_terme(y), E.VIDE)))
    x_vide = conjonction_elim_gauche(H)                   # x∈∅
    falso = N.modus_ponens(x_vide, _exfalso_vide(vx, phi))  # Φ
    return N.loi_deduction(et(appartient(vx, E.VIDE), appartient(_terme(y), E.VIDE)), falso)


def vide_dans_P(G="G", E_set="E"):
    """⊢ { antisymetrie(G), transitivite_rel(G) } ⊢ ∅ ∈ P.

    ∅ est une chaîne (vide_est_chaine), donc ∅∈P par l'axiome de P."""
    vG, vE = var(G), var(E_set)
    chaine_vide = vide_est_chaine(G, E_set)               # chaine(G,E,∅)  [antisym,trans]
    return N.modus_ponens(chaine_vide,
                          equivalence_arriere(_inst_P(vG, vE, E.VIDE)))   # ∅∈P


def vide_plus_petit(G="G", E_set="E", C="x"):
    """⊢ { antisymetrie(G), transitivite_rel(G) } ⊢ plus_petit_element(Γ,P,∅).

    plus_petit_element(Γ,P,∅) = ∅∈P et (∀x)( x∈P ⇒ (∅,x)∈Γ ).  ∅∈P (vide_dans_P) ;
    et pour C∈P, ∅⊂C (vacuité) avec ∅∈P, C∈P donne (∅,C)∈Γ.  Binder « x » pour
    matcher plus_petit_element(Γ,P,∅)."""
    vG, vE, vC = var(G), var(E_set), var(C)
    vide_P = vide_dans_P(G, E_set)                        # ∅∈P
    hCP = N.assume(appartient(vC, P(vG, vE)))             # C∈P
    vide_C = _vide_inclus(vC)                             # ∅⊂C
    vide_C_Gamma = _Gamma_intro(vG, vE, E.VIDE, vC, vide_P, hCP, vide_C)  # (∅,C)∈Γ
    body = N.loi_deduction(appartient(vC, P(vG, vE)), vide_C_Gamma)
    allC = N.generalisation(C, body)                     # (∀C)(C∈P⇒(∅,C)∈Γ)
    return conjonction_intro(vide_P, allC)               # plus_petit_element(Γ,P,∅)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — (Γ,P) est CHAÎNE-COMPLET  (le CŒUR : la borne sup d'une Γ-chaîne
#  de chaînes 𝔇 est l'UNION ⋃𝔇).  Union(𝔇) = terme opaque + axiome de membership
#  (S8+A1, motif reunion_famille / axiome_M).  theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
def Union(G, E_set, D):
    """⋃𝔇 := { x | (∃C)(C∈𝔇 et x∈C) }  (réunion d'une famille 𝔇 d'ensembles)."""
    return E.app("zorn_Union", _terme(G), _terme(E_set), _terme(D))


def _corps_Union(G, E_set, D, x, C="C"):
    """Corps de ⋃𝔇 :  (∃C)( C∈𝔇 et x∈C )."""
    vC = var(C)
    return existe(C, et(appartient(vC, _terme(D)), appartient(_terme(x), vC)))


def axiome_Union(G="G", E_set="E", D="D", x="x", C="C"):
    """⊢-schéma (∀G E D x)( x∈⋃𝔇 ⇔ (∃C)(C∈𝔇 et x∈C) ).

    Axiome DÉFINITIONNEL de la réunion d'une famille (légitime S8+A1, motif
    reunion_famille).  N'altère PAS theorie_ensembles()."""
    vG, vE, vD, vx = var(G), var(E_set), var(D), var(x)
    return pourtout(G, pourtout(E_set, pourtout(D, pourtout(x,
        equiv(appartient(vx, Union(vG, vE, vD)),
              _corps_Union(vG, vE, vD, vx, C))))))


def theorie_Union(G="G", E_set="E", D="D", x="x", C="C"):
    """Théorie DÉDIÉE ne contenant que l'axiome de ⋃𝔇 (E.III.2, Zorn, ÉTAPE 2)."""
    return N.Theorie("Union-Zorn", [axiome_Union(G, E_set, D, x, C)])


def _inst_Union(G, E_set, D, x):
    """⊢ ( x∈⋃𝔇 ⇔ (∃C)(C∈𝔇 et x∈C) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Union(), axiome_Union())
    for tm in (G, E_set, D, x):
        ax = instancie(ax, _terme(tm))
    return ax


def Union_membre(G="G", E_set="E", D="D", x="x"):
    """⊢ ( x∈⋃𝔇 ) ⇔ ( (∃C)(C∈𝔇 et x∈C) )."""
    return _inst_Union(var(G), var(E_set), var(D), var(x))


# ── outillage d'ordre porté en hypothèses (antisym/trans GLOBALES de G) ───────
def _trans(G, x, y, z, hxy, hyz):
    """{ transitivite_rel(G), (x,y)∈G [hxy], (y,z)∈G [hyz] } ⊢ (x,z)∈G."""
    Ht = N.assume(transitivite_rel(_terme(G)))
    inst = instancie(instancie(instancie(Ht, _terme(x)), _terme(y)), _terme(z))
    return N.modus_ponens(conjonction_intro(hxy, hyz), inst)


def _disj_syll_g(thm_pq, thm_np):
    """De ⊢ (P∨Q) et ⊢ ¬P déduit ⊢ Q  (syllogisme disjonctif)."""
    p, q = thm_pq.conclusion.sous
    P_imp_Q = N.modus_ponens(thm_np, N.s2(non(p), q))     # (P⇒Q)  [¬P]
    Q_imp_Q = a_implique_a(q)
    return cas(thm_pq, P_imp_Q, Q_imp_Q)


# ── (A) ⋃𝔇 ⊂ E ──────────────────────────────────────────────────────────────
def Union_inclus_E(G="G", E_set="E", D="D", x="x", C="C"):
    """⊢ { 𝔇⊂P } ⊢ ⋃𝔇 ⊂ E.

    Si x∈⋃𝔇, témoin C∈𝔇⊂P donc C est une chaîne (C⊂E), et x∈C, d'où x∈E."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    vG, vE, vD = var(G), var(E_set), var(D)
    Ut = Union(vG, vE, vD)
    cible = inclus(Ut, vE)
    bndr, _ = _peler_pourtout(cible)
    vx = var(bndr)
    HDP = N.assume(inclus(vD, P(vG, vE)))                 # 𝔇⊂P
    hxU = N.assume(appartient(vx, Ut))                    # x∈⋃𝔇
    ex = N.modus_ponens(hxU, equivalence_avant(_inst_Union(vG, vE, vD, vx)))  # (∃C)(C∈𝔇 et x∈C)
    # per-témoin C : (C∈𝔇 et x∈C) ⇒ x∈E
    vC = var(C)
    Hw = N.assume(et(appartient(vC, vD), appartient(vx, vC)))
    CD = conjonction_elim_gauche(Hw)                      # C∈𝔇
    xC = conjonction_elim_droite(Hw)                      # x∈C
    CP = N.modus_ponens(CD, instancie(HDP, vC))           # C∈P
    chaineC = N.modus_ponens(CP, equivalence_avant(_inst_P(vG, vE, vC)))  # chaine(G,E,C)
    C_E = conjonction_elim_gauche(chaineC)                # C⊂E
    xE = N.modus_ponens(xC, instancie(C_E, vx))           # x∈E
    wit_imp = N.loi_deduction(et(appartient(vC, vD), appartient(vx, vC)), xE)
    ex_imp = existe_elimination(wit_imp, C)               # (∃C)(…) ⇒ x∈E
    xE_final = N.modus_ponens(ex, ex_imp)                 # x∈E  [x∈⋃𝔇, 𝔇⊂P]
    body = N.loi_deduction(appartient(vx, Ut), xE_final)
    return N.generalisation(bndr, body)                   # ⋃𝔇⊂E


# ── helper : (C,C')∈Γ ⇒ C⊂C'  (lecture de l'ordre Γ comme inclusion) ─────────
def _gamma_incl(G, E_set, C, Cp, hGamma):
    """De ⊢ (C,C')∈Γ [hGamma] déduit ⊢ C⊂C'  (projection du corps de Γ)."""
    vG, vE = _terme(G), _terme(E_set)
    corps = N.modus_ponens(hGamma, equivalence_avant(_inst_Gamma(vG, vE, C, Cp)))
    return conjonction_elim_droite(corps)                 # C⊂C'


def _comparable_dans_chaine(G, E_set, C, x, y, hxC, hyC, hchaineC):
    """{ chaine(G,E,C) [hchaineC], x∈C [hxC], y∈C [hyC] } ⊢ ((x,y)∈G ou (y,x)∈G).

    Une chaîne C de E est totalement ordonnée : deux éléments de C sont
    comparables."""
    vG = _terme(G)
    tot = conjonction_elim_droite(hchaineC)               # totalement_ordonne(G,C)
    comp = conjonction_elim_droite(tot)                   # (∀x∀y)((x∈C et y∈C)⇒(…ou…))
    inst = instancie(instancie(comp, _terme(x)), _terme(y))
    return N.modus_ponens(conjonction_intro(hxC, hyC), inst)   # (x,y)∈G ou (y,x)∈G


def _chaine_de_D(G, E_set, D, C, hCD, hDP):
    """{ 𝔇⊂P [hDP], C∈𝔇 [hCD] } ⊢ chaine(G,E,C)  (un élément de 𝔇 est une chaîne)."""
    vG, vE = _terme(G), _terme(E_set)
    CP = N.modus_ponens(hCD, instancie(hDP, _terme(C)))   # C∈P
    return N.modus_ponens(CP, equivalence_avant(_inst_P(vG, vE, _terme(C))))  # chaine(G,E,C)


def Union_totalement_ordonne(G="G", E_set="E", D="D", x="x", y="y", C="C", Cp="Cpw"):
    """⊢ { 𝔇⊂P, totalement_ordonne(Γ,𝔇), transitivite_rel(G) }
         ⊢ totalement_ordonne(G, ⋃𝔇).

    est_ordre(G,⋃𝔇) (réflexivité via ⋃𝔇⊂E + … en fait ici on n'a besoin que de
    est_ordre via les composantes globales) PLUS comparabilité : pour x,y∈⋃𝔇,
    témoins C,C′∈𝔇 ; 𝔇 Γ-totalement ordonné ⇒ C⊂C′ ou C′⊂C ; dans le 1er cas
    x∈C⊂C′ et y∈C′ sont dans la CHAÎNE C′, donc comparables (idem 2e cas)."""
    vG, vE, vD = var(G), var(E_set), var(D)
    vx, vy = var(x), var(y)
    Ut = Union(vG, vE, vD)
    HDP = N.assume(inclus(vD, P(vG, vE)))                 # 𝔇⊂P
    Htot = N.assume(totalement_ordonne(Gamma(vG, vE), vD))  # totalement_ordonne(Γ,𝔇)
    Hgas = N.assume(antisymetrie(vG))                    # antisymetrie(G)  (pour est_ordre(G,⋃𝔇))
    Hgtr = N.assume(transitivite_rel(vG))                # transitivite_rel(G)
    comp_D = conjonction_elim_droite(Htot)               # (∀C∀C′)((C∈𝔇 et C′∈𝔇)⇒((C,C′)∈Γ ou (C′,C)∈Γ))

    # ── est_ordre(G,⋃𝔇) : réflexivité sur ⋃𝔇 (via x∈⋃𝔇⊂E … en fait via chaîne C) ─
    # reflexivite_sur(G,⋃𝔇) = (∀x)(x∈⋃𝔇 ⇒ (x,x)∈G).  x∈⋃𝔇 ⇒ témoin C chaîne, x∈C⊂E,
    # et réflexivité de C ((x,x)∈G car C ordonné).
    hxU = N.assume(appartient(vx, Ut))                   # x∈⋃𝔇
    exx = N.modus_ponens(hxU, equivalence_avant(_inst_Union(vG, vE, vD, vx)))  # (∃C)(C∈𝔇 et x∈C)
    vC = var(C)
    Hwx = N.assume(et(appartient(vC, vD), appartient(vx, vC)))
    CDx = conjonction_elim_gauche(Hwx)                   # C∈𝔇
    xCx = conjonction_elim_droite(Hwx)                   # x∈C
    chaineCx = _chaine_de_D(vG, vE, vD, vC, CDx, HDP)    # chaine(G,E,C)
    # (x,x)∈G via comparabilité de x avec x dans la chaîne C : (x,x)∈G ou (x,x)∈G ⇒ (x,x)∈G
    comp_xx = _comparable_dans_chaine(vG, vE, vC, vx, vx, xCx, xCx, chaineCx)  # (x,x)∈G ou (x,x)∈G
    xx = N.modus_ponens(comp_xx, N.s1(_le(vx, vx, vG)))  # (x,x)∈G
    wit_refl = N.loi_deduction(et(appartient(vC, vD), appartient(vx, vC)), xx)
    refl_x = N.modus_ponens(exx, existe_elimination(wit_refl, C))  # (x,x)∈G  [x∈⋃𝔇,…]
    refl_body = N.loi_deduction(appartient(vx, Ut), refl_x)
    refl_U = N.generalisation(x, refl_body)              # reflexivite_sur(G,⋃𝔇)
    ord_U = conjonction_intro(conjonction_intro(refl_U, Hgas), Hgtr)  # est_ordre(G,⋃𝔇)

    # ── comparabilité sur ⋃𝔇 : (x∈⋃𝔇 et y∈⋃𝔇) ⇒ ((x,y)∈G ou (y,x)∈G) ───────────
    but = ou(_le(vx, vy, vG), _le(vy, vx, vG))
    Hxy = N.assume(et(appartient(vx, Ut), appartient(vy, Ut)))
    xU = conjonction_elim_gauche(Hxy)                    # x∈⋃𝔇
    yU = conjonction_elim_droite(Hxy)                    # y∈⋃𝔇
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    ex_x = N.modus_ponens(xU, equivalence_avant(_inst_Union(vG, vE, vD, vx)))  # (∃C)(C∈𝔇 et x∈C)
    ex_y_C = N.modus_ponens(yU, equivalence_avant(_inst_Union(vG, vE, vD, vy)))  # (∃C)(C∈𝔇 et y∈C)
    # α-renomme le ∃ de y vers C′ (=Cp) pour ne pas collisionner avec le ∃ de x
    R_yC = et(appartient(var(C), vD), appartient(vy, var(C)))
    ex_y = N.modus_ponens(ex_y_C, equivalence_avant(alpha_existe(C, Cp, R_yC)))  # (∃C′)(C′∈𝔇 et y∈C′)
    vCp = var(Cp)
    # per-témoins C (pour x) et C′ (pour y)
    HwC = N.assume(et(appartient(vC, vD), appartient(vx, vC)))    # C∈𝔇 et x∈C
    HwCp = N.assume(et(appartient(vCp, vD), appartient(vy, vCp))) # C′∈𝔇 et y∈C′
    CD = conjonction_elim_gauche(HwC)                    # C∈𝔇
    xC = conjonction_elim_droite(HwC)                    # x∈C
    CpD = conjonction_elim_gauche(HwCp)                  # C′∈𝔇
    yCp = conjonction_elim_droite(HwCp)                  # y∈C′
    chaineC = _chaine_de_D(vG, vE, vD, vC, CD, HDP)      # chaine(G,E,C)
    chaineCp = _chaine_de_D(vG, vE, vD, vCp, CpD, HDP)   # chaine(G,E,C′)
    # 𝔇 Γ-total : (C,C′)∈Γ ou (C′,C)∈Γ
    comp_CCp = N.modus_ponens(conjonction_intro(CD, CpD),
                              instancie(instancie(comp_D, vC), vCp))   # (C,C′)∈Γ ou (C′,C)∈Γ
    # BRANCHE (C,C′)∈Γ : C⊂C′ ⇒ x∈C′ ; x,y∈C′ chaîne ⇒ comparables
    HCCp = N.assume(_gle(vC, vCp, vG, vE))               # (C,C′)∈Γ
    C_Cp = _gamma_incl(vG, vE, vC, vCp, HCCp)            # C⊂C′
    xCp = N.modus_ponens(xC, instancie(C_Cp, vx))        # x∈C′
    comp1 = _comparable_dans_chaine(vG, vE, vCp, vx, vy, xCp, yCp, chaineCp)  # but
    b1 = N.loi_deduction(_gle(vC, vCp, vG, vE), comp1)
    # BRANCHE (C′,C)∈Γ : C′⊂C ⇒ y∈C ; x,y∈C chaîne ⇒ comparables
    HCpC = N.assume(_gle(vCp, vC, vG, vE))               # (C′,C)∈Γ
    Cp_C = _gamma_incl(vG, vE, vCp, vC, HCpC)            # C′⊂C
    yC = N.modus_ponens(yCp, instancie(Cp_C, vy))        # y∈C
    comp2 = _comparable_dans_chaine(vG, vE, vC, vx, vy, xC, yC, chaineC)  # but
    b2 = N.loi_deduction(_gle(vCp, vC, vG, vE), comp2)
    comp_wit = cas(comp_CCp, b1, b2)                     # but  [HwC, HwCp, …]
    # éliminer les deux ∃ : d'abord sur C′ (y non lié par le témoin C), puis sur C
    wit_imp_Cp = N.loi_deduction(et(appartient(vCp, vD), appartient(vy, vCp)), comp_wit)
    ex_imp_Cp = existe_elimination(wit_imp_Cp, Cp)       # (∃C′)(C′∈𝔇 et y∈C′) ⇒ but   [HwC,…]
    comp_after_y = N.modus_ponens(ex_y, ex_imp_Cp)       # but  [HwC, x∈⋃𝔇,…]
    wit_imp_C = N.loi_deduction(et(appartient(vC, vD), appartient(vx, vC)), comp_after_y)
    ex_imp_C = existe_elimination(wit_imp_C, C)          # (∃C)(C∈𝔇 et x∈C) ⇒ but
    comp_final = N.modus_ponens(ex_x, ex_imp_C)          # but  [x∈⋃𝔇, y∈⋃𝔇,…]
    comp_body = N.loi_deduction(et(appartient(vx, Ut), appartient(vy, Ut)), comp_final)
    comp_U = N.generalisation(x, N.generalisation(y, comp_body))  # comparabilité sur ⋃𝔇
    return conjonction_intro(ord_U, comp_U)              # totalement_ordonne(G,⋃𝔇)


def Union_dans_P(G="G", E_set="E", D="D"):
    """⊢ { 𝔇⊂P, totalement_ordonne(Γ,𝔇), antisymetrie(G), transitivite_rel(G) }
         ⊢ ⋃𝔇 ∈ P.

    ⋃𝔇 est une chaîne de E : ⋃𝔇⊂E (Union_inclus_E) et totalement_ordonne(G,⋃𝔇)
    (Union_totalement_ordonne), donc ⋃𝔇∈P par l'axiome de P."""
    vG, vE, vD = var(G), var(E_set), var(D)
    U_E = Union_inclus_E(G, E_set, D)                    # ⋃𝔇⊂E  [𝔇⊂P]
    tot_U = Union_totalement_ordonne(G, E_set, D)        # totalement_ordonne(G,⋃𝔇)  [hyps]
    chaine_U = conjonction_intro(U_E, tot_U)             # chaine(G,E,⋃𝔇)
    return N.modus_ponens(chaine_U,
                          equivalence_arriere(_inst_P(vG, vE, Union(vG, vE, vD))))  # ⋃𝔇∈P


# ── (B) ⋃𝔇 est la BORNE SUPÉRIEURE de 𝔇 dans P ──────────────────────────────
def _C_inclus_Union(G, E_set, D, C, hCD):
    """De ⊢ C∈𝔇 [hCD] déduit ⊢ C⊂⋃𝔇  (tout C∈𝔇 est inclus dans la réunion).

    Pour x∈C : (C∈𝔇 et x∈C) témoigne (∃C)(C∈𝔇 et x∈C), donc x∈⋃𝔇."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    vG, vE, vD, vC = _terme(G), _terme(E_set), _terme(D), _terme(C)
    Ut = Union(vG, vE, vD)
    cible = inclus(vC, Ut)
    bndr, _ = _peler_pourtout(cible)
    vx = var(bndr)
    hxC = N.assume(appartient(vx, vC))                    # x∈C
    # (∃W)(W∈𝔇 et x∈W) via témoin W=C  (binder du corps de l'axiome = "C")
    corps_temoin = conjonction_intro(hCD, hxC)            # C∈𝔇 et x∈C
    R = et(appartient(var("C"), vD), appartient(vx, var("C")))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vC, "C"))   # (∃C)(C∈𝔇 et x∈C)
    xU = N.modus_ponens(ex, equivalence_arriere(_inst_Union(vG, vE, vD, vx)))  # x∈⋃𝔇
    body = N.loi_deduction(appartient(vx, vC), xU)
    return N.generalisation(bndr, body)                   # C⊂⋃𝔇


def Union_majorant(G="G", E_set="E", D="D", C="x"):
    """⊢ { 𝔇⊂P, totalement_ordonne(Γ,𝔇), antisymetrie(G), transitivite_rel(G) }
         ⊢ majorant(Γ, 𝔇, ⋃𝔇, P).

    majorant(Γ,𝔇,⋃𝔇,P) = ⋃𝔇∈P et (∀C)(C∈𝔇 ⇒ (C,⋃𝔇)∈Γ).  ⋃𝔇∈P (Union_dans_P) ;
    et pour C∈𝔇 : C∈P (𝔇⊂P), ⋃𝔇∈P, C⊂⋃𝔇 ⇒ (C,⋃𝔇)∈Γ.  Binder « x » pour matcher
    majorant(Γ,𝔇,⋃𝔇,P)."""
    vG, vE, vD = var(G), var(E_set), var(D)
    Ut = Union(vG, vE, vD)
    HDP = N.assume(inclus(vD, P(vG, vE)))                 # 𝔇⊂P
    U_P = Union_dans_P(G, E_set, D)                       # ⋃𝔇∈P  [4 hyps]
    vC = var(C)
    hCD = N.assume(appartient(vC, vD))                    # C∈𝔇
    CP = N.modus_ponens(hCD, instancie(HDP, vC))          # C∈P
    C_U = _C_inclus_Union(vG, vE, vD, vC, hCD)            # C⊂⋃𝔇
    C_U_Gamma = _Gamma_intro(vG, vE, vC, Ut, CP, U_P, C_U)  # (C,⋃𝔇)∈Γ
    body = N.loi_deduction(appartient(vC, vD), C_U_Gamma)
    allC = N.generalisation(C, body)                     # (∀C)(C∈𝔇⇒(C,⋃𝔇)∈Γ)
    return conjonction_intro(U_P, allC)                  # majorant(Γ,𝔇,⋃𝔇,P)


def Union_borne_sup(G="G", E_set="E", D="D", m="m", C="x", y="y"):
    """⊢ { 𝔇⊂P, totalement_ordonne(Γ,𝔇), antisymetrie(G), transitivite_rel(G) }
         ⊢ borne_superieure(Γ, 𝔇, ⋃𝔇, P).

    ⋃𝔇 est un majorant (Union_majorant) et c'est le PLUS PETIT : pour tout
    majorant m de 𝔇 dans P, m∈P et (∀C)(C∈𝔇⇒C⊂m), donc ⋃𝔇⊂m (tout x∈⋃𝔇 a un
    témoin C∈𝔇 avec x∈C⊂m), d'où (⋃𝔇,m)∈Γ."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    vG, vE, vD, vm = var(G), var(E_set), var(D), var(m)
    Ut = Union(vG, vE, vD)
    maj_U = Union_majorant(G, E_set, D, C)               # majorant(Γ,𝔇,⋃𝔇,P)  [4 hyps]
    # least : (∀y)( majorant(Γ,𝔇,y,P) ⇒ (⋃𝔇,y)∈Γ )
    Hmaj = N.assume(majorant(Gamma(vG, vE), vD, vm, P(vG, vE)))  # majorant(Γ,𝔇,m,P)
    mP = conjonction_elim_gauche(Hmaj)                   # m∈P
    m_majfun = conjonction_elim_droite(Hmaj)             # (∀C)(C∈𝔇⇒(C,m)∈Γ)
    # ⋃𝔇⊂m : x∈⋃𝔇 ⇒ témoin C∈𝔇, x∈C, (C,m)∈Γ ⇒ C⊂m ⇒ x∈m
    cible = inclus(Ut, vm)
    bndr, _ = _peler_pourtout(cible)
    vx = var(bndr)
    hxU = N.assume(appartient(vx, Ut))                   # x∈⋃𝔇
    ex = N.modus_ponens(hxU, equivalence_avant(_inst_Union(vG, vE, vD, vx)))  # (∃C)(C∈𝔇 et x∈C)
    vCt = var("C")
    Hw = N.assume(et(appartient(vCt, vD), appartient(vx, vCt)))
    CD = conjonction_elim_gauche(Hw)                     # C∈𝔇
    xC = conjonction_elim_droite(Hw)                     # x∈C
    Cm_Gamma = N.modus_ponens(CD, instancie(m_majfun, vCt))  # (C,m)∈Γ
    C_m = _gamma_incl(vG, vE, vCt, vm, Cm_Gamma)         # C⊂m
    xm = N.modus_ponens(xC, instancie(C_m, vx))          # x∈m
    wit_imp = N.loi_deduction(et(appartient(vCt, vD), appartient(vx, vCt)), xm)
    ex_imp = existe_elimination(wit_imp, "C")            # (∃C)(…) ⇒ x∈m
    xm_final = N.modus_ponens(ex, ex_imp)                # x∈m  [x∈⋃𝔇,…]
    U_m_body = N.loi_deduction(appartient(vx, Ut), xm_final)
    U_m = N.generalisation(bndr, U_m_body)               # ⋃𝔇⊂m
    U_P = conjonction_elim_gauche(maj_U)                 # ⋃𝔇∈P
    U_m_Gamma = _Gamma_intro(vG, vE, Ut, vm, U_P, mP, U_m)  # (⋃𝔇,m)∈Γ
    least_body = N.loi_deduction(majorant(Gamma(vG, vE), vD, vm, P(vG, vE)), U_m_Gamma)
    least = N.generalisation(y, _rename_majorant_binder(least_body, m, y))
    return conjonction_intro(maj_U, least)              # borne_superieure(Γ,𝔇,⋃𝔇,P)


def _rename_majorant_binder(thm_m, m, y):
    """De ⊢ ( majorant(Γ,𝔇,m,P) ⇒ (⋃𝔇,m)∈Γ ) [m libre], renvoie le corps avec m↦y.

    Substitue la variable libre m par y dans la conclusion (pour matcher le liant
    « y » de borne_superieure).  Via Leibniz/instanciation : on généralise m puis
    on instancie en y."""
    # m n'apparaît plus dans les hypothèses de thm_m (toutes déchargées) → on peut
    # généraliser puis instancier.
    gen = N.generalisation(m, thm_m)                     # (∀m)( majorant(m) ⇒ (⋃𝔇,m)∈Γ )
    return instancie(gen, var(y))                        # majorant(y) ⇒ (⋃𝔇,y)∈Γ


# ── (C) ASSEMBLAGE : (Γ,P) est CHAÎNE-COMPLET ───────────────────────────────
def Gamma_chaine_complet(G="G", E_set="E", D="D", s="s", x="x", y="y", z="z"):
    """⊢ { antisymetrie(G), transitivite_rel(G) } ⊢ chaine_complet(Γ,P).

    chaine_complet(Γ,P) = est_ordre(Γ,P) et (∀𝔇)(chaine(Γ,P,𝔇) ⇒ (∃s)bsup(Γ,𝔇,s,P)).
    est_ordre(Γ,P) (Gamma_est_ordre, inconditionnel) ; et pour une Γ-chaîne 𝔇 (=
    chaine(Γ,P,𝔇) donne 𝔇⊂P et totalement_ordonne(Γ,𝔇)), la BORNE SUP est ⋃𝔇
    (Union_borne_sup) — témoin du (∃s).  Les seules hyps PORTÉES sont les faits
    GLOBAUX de G (antisym/trans), fournis par est_ordre(G,E) à l'assemblage final.

    🎯 LE CŒUR : la réunion d'une chaîne de chaînes est une chaîne, borne sup."""
    vG, vE, vD = var(G), var(E_set), var(D)
    Gam, Pp = Gamma(vG, vE), P(vG, vE)
    Ut = Union(vG, vE, vD)
    # est_ordre(Γ,P)  — inconditionnel
    ord_GP = Gamma_est_ordre(G, E_set)
    # corps : chaine(Γ,P,𝔇) ⇒ (∃s) bsup(Γ,𝔇,s,P)
    Hch = N.assume(chaine(Gam, Pp, vD, x, y, z))         # chaine(Γ,P,𝔇)
    D_P = conjonction_elim_gauche(Hch)                   # 𝔇⊂P
    tot_D = conjonction_elim_droite(Hch)                 # totalement_ordonne(Γ,𝔇)
    # borne_superieure(Γ,𝔇,⋃𝔇,P) — décharge les 4 hyps de Union_borne_sup
    bsup_U = Union_borne_sup(G, E_set, D)                # bsup(Γ,𝔇,⋃𝔇,P)  [4 hyps]
    bsup_U = _cut(bsup_U, inclus(vD, Pp), D_P)
    bsup_U = _cut(bsup_U, totalement_ordonne(Gam, vD), tot_D)
    # antisym/trans(G) restent en hyps (globales) → portées
    # (∃s) bsup(Γ,𝔇,s,P)  via S5, témoin s=⋃𝔇
    corps_s = borne_superieure(Gam, vD, var(s), Pp, x, y)
    s5 = N.s5(corps_s, Ut, s)                            # (⋃𝔇|s)corps ⇒ (∃s)corps
    ex_bsup = N.modus_ponens(bsup_U, s5)                 # (∃s)bsup(Γ,𝔇,s,P)
    body = N.loi_deduction(chaine(Gam, Pp, vD, x, y, z), ex_bsup)
    allD = N.generalisation(D, body)                     # (∀D)(chaine⇒(∃s)bsup)
    # α-renomme le liant D → C pour matcher chaine_complet(Γ,P) (binder canonique « C »)
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    _, corps_D = _peler_pourtout(allD.conclusion)
    if D != "C":
        from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
        ren = alpha_pour_tout(D, "C", corps_D)           # (∀D)corps ⇔ (∀C)corps'
        allD = N.modus_ponens(allD, equivalence_avant(ren))
    return conjonction_intro(ord_GP, allD)              # chaine_complet(Γ,P)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — sous « E SANS ÉLÉMENT MAXIMAL », toute chaîne C∈P admet une chaîne
#  STRICTEMENT plus grande dans P : C∪{m′} où m′ > (majorant de C).
#  C'est ce qui fabrique, par τ, l'application STRICTEMENT inflationnaire f.
# ════════════════════════════════════════════════════════════════════════════
def _ajoute(C, t):
    """C ∪ {t}  (la chaîne C augmentée d'un point t)."""
    return E.reunion(_terme(C), E.singleton(_terme(t)))


def _membre_ajoute(C, t, z):
    """⊢ ( z ∈ C∪{t} ) ⇔ ( z∈C ou z=t )   (axiome réunion + singleton)."""
    vC, vt, vz = _terme(C), _terme(t), _terme(z)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)   # (∀x∀y∀z)(z∈x∪y ⇔ (z∈x ou z∈y))
    inst = instancie(instancie(instancie(ax, vC), E.singleton(vt)), vz)  # z∈C∪{t} ⇔ (z∈C ou z∈{t})
    from bourbaki.ensembles.base.ensembles_couples import singleton_membre
    sm = singleton_membre(vz, vt)                            # z∈{t} ⇔ z=t
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        ou_congruence, equivalence_transitivite,
    )
    aa = a_implique_a(appartient(vz, vC))
    refl_zC = conjonction_intro(aa, aa)                      # (z∈C) ⇔ (z∈C)
    cong = ou_congruence(refl_zC, sm)                        # (z∈C ou z∈{t}) ⇔ (z∈C ou z=t)
    return equivalence_transitivite(inst, cong)              # z∈C∪{t} ⇔ (z∈C ou z=t)


def _ajoute_intro_C(C, t, z, hzC):
    """De ⊢ z∈C [hzC] déduit ⊢ z∈C∪{t}."""
    vz = _terme(z)
    disj = N.modus_ponens(hzC, N.s2(appartient(vz, _terme(C)), egal(vz, _terme(t))))
    return N.modus_ponens(disj, equivalence_arriere(_membre_ajoute(C, t, z)))


def _ajoute_intro_t(C, t):
    """⊢ t ∈ C∪{t}  (t appartient à C∪{t} par t=t)."""
    vt, vC = _terme(t), _terme(C)
    # (t=t) ⇒ (t=t ∨ t∈C) ⇒ (t∈C ∨ t=t)
    d1 = N.modus_ponens(N.reflexivite(vt), N.s2(egal(vt, vt), appartient(vt, vC)))   # t=t ∨ t∈C
    disj = N.modus_ponens(d1, N.s3(egal(vt, vt), appartient(vt, vC)))                # t∈C ∨ t=t
    return N.modus_ponens(disj, equivalence_arriere(_membre_ajoute(C, t, vt)))


def _refl_sur(G, E_set, t, htE):
    """{ reflexivite_sur(G,E), t∈E [htE] } ⊢ (t,t)∈G."""
    Hr = N.assume(reflexivite_sur(_terme(G), _terme(E_set)))
    return N.modus_ponens(htE, instancie(Hr, _terme(t)))


def _comp_chaine(G, C, x, y, hxC, hyC, hchaineC):
    """{ chaine(G,E,C) [hchaineC], x∈C [hxC], y∈C [hyC] } ⊢ ((x,y)∈G ou (y,x)∈G)."""
    return _comparable_dans_chaine(G, None, C, x, y, hxC, hyC, hchaineC)


def ajoute_est_chaine(G="G", E_set="E", C="C", t="t", x="x", y="y"):
    """⊢ { reflexivite_sur(G,E), antisymetrie(G), transitivite_rel(G),
           chaine(G,E,C), t∈E, (∀c)(c∈C ⇒ (c,t)∈G) } ⊢ chaine(G,E,C∪{t}).

    C∪{t} est une chaîne : tout z∈C∪{t} est dans C⊂E ou vaut t∈E (donc ⊂E) ; et
    deux éléments x,y de C∪{t} sont comparables — soit tous deux dans C (chaîne),
    soit l'un = t qui MAJORE C (hyp (∀c)(c∈C⇒(c,t)∈G)), soit x=y=t (réflexivité).

    C, t, G, E acceptent des TERMES (sans collision avec les binders x/y/c) ;
    seuls x, y restent des NOMS de binders."""
    vG, vE, vC, vt = _terme(G), _terme(E_set), _terme(C), _terme(t)
    vx, vy = var(x), var(y)
    A = _ajoute(vC, vt)                                   # C∪{t}
    Hch = N.assume(chaine(vG, vE, vC))                   # chaine(G,E,C)
    HtE = N.assume(appartient(vt, vE))                   # t∈E
    Hmaj = N.assume(pourtout("c", impl(appartient(var("c"), vC), _le("c", vt, vG))))  # ∀c∈C (c,t)∈G
    Hgas = N.assume(antisymetrie(vG))
    Hgtr = N.assume(transitivite_rel(vG))
    C_E = conjonction_elim_gauche(Hch)                   # C⊂E
    # (1) C∪{t}⊂E
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    cibleAE = inclus(A, vE)
    bAE, _ = _peler_pourtout(cibleAE)
    vz = var(bAE)
    hzA = N.assume(appartient(vz, A))                    # z∈C∪{t}
    disjz = N.modus_ponens(hzA, equivalence_avant(_membre_ajoute(vC, vt, vz)))  # z∈C ou z=t
    #   z∈C ⇒ z∈E
    bz1 = N.loi_deduction(appartient(vz, vC),
                          N.modus_ponens(N.assume(appartient(vz, vC)), instancie(C_E, vz)))
    #   z=t ⇒ z∈E  (Leibniz : z=t, t∈E ⇒ z∈E)
    Hzt = N.assume(egal(vz, vt))
    leibz = N.s6(vt, vz, _H, appartient(var(_H), vE))    # (t=z)⇒((t∈E)⇔(z∈E))
    t_eq_z = N.modus_ponens(Hzt, _sym(vz, vt))           # t=z
    z_in_E = N.modus_ponens(HtE, equivalence_avant(N.modus_ponens(t_eq_z, leibz)))  # z∈E
    bz2 = N.loi_deduction(egal(vz, vt), z_in_E)
    zE = cas(disjz, bz1, bz2)                            # z∈E
    AE_body = N.loi_deduction(appartient(vz, A), zE)
    A_E = N.generalisation(bAE, AE_body)                # C∪{t}⊂E
    # (2) est_ordre(G,C∪{t}) : réflexivité via comparabilité, antisym/trans globaux
    refl_A = _ajoute_refl(vG, vE, vC, vt, A, Hch, HtE, Hmaj, Hgas, Hgtr)  # reflexivite_sur(G,C∪{t})
    ord_A = conjonction_intro(conjonction_intro(refl_A, Hgas), Hgtr)
    # (3) comparabilité sur C∪{t}
    comp_A = _ajoute_comparables(vG, vE, vC, vt, A, Hch, HtE, Hmaj, x, y)
    tot_A = conjonction_intro(ord_A, comp_A)            # totalement_ordonne(G,C∪{t})
    return conjonction_intro(A_E, tot_A)               # chaine(G,E,C∪{t})


def _x_comparable_ajoute(G, E_set, C, t, A, Hch, HtE, Hmaj, x, y, hxA, hyA):
    """{…, x∈C∪{t} [hxA], y∈C∪{t} [hyA]} ⊢ ((x,y)∈G ou (y,x)∈G).

    Disjonction sur (x∈C ou x=t) et (y∈C ou y=t).  4 cas, tous comparables :
    (C,C) chaîne ; (C,t) majoration ; (t,C) majoration ; (t,t) réflexivité."""
    vG, vE, vC, vt = _terme(G), _terme(E_set), _terme(C), _terme(t)
    vx, vy = _terme(x), _terme(y)
    but = ou(_le(vx, vy, vG), _le(vy, vx, vG))
    C_E = conjonction_elim_gauche(Hch)
    refl_E = None  # not needed if x=t handled by maj for y∈C; t,t via reflexivite
    dx = N.modus_ponens(hxA, equivalence_avant(_membre_ajoute(vC, vt, vx)))  # x∈C ou x=t
    dy = N.modus_ponens(hyA, equivalence_avant(_membre_ajoute(vC, vt, vy)))  # y∈C ou y=t
    # branche x∈C
    HxC = N.assume(appartient(vx, vC))
    #   sous-branche y∈C : chaîne
    HyC = N.assume(appartient(vy, vC))
    cc = _comparable_dans_chaine(vG, vE, vC, vx, vy, HxC, HyC, Hch)         # but
    bxC_yC = N.loi_deduction(appartient(vy, vC), cc)
    #   sous-branche y=t : (x,t)∈G (maj) ⇒ (x,y)∈G via y=t
    Hyt = N.assume(egal(vy, vt))
    xt = N.modus_ponens(HxC, instancie(Hmaj, vx))                          # (x,t)∈G
    #   transporter (x,t)∈G en (x,y)∈G via t=y
    t_eq_y = N.modus_ponens(Hyt, _sym(vy, vt))                             # t=y
    leib_xy = N.s6(vt, vy, _H, _le(vx, var(_H), vG))                       # (t=y)⇒((x,t)∈G⇔(x,y)∈G)
    xy = N.modus_ponens(xt, equivalence_avant(N.modus_ponens(t_eq_y, leib_xy)))  # (x,y)∈G
    bxC_yt = N.loi_deduction(egal(vy, vt), _ou_gauche(xy, _le(vy, vx, vG)))
    bxC = N.loi_deduction(appartient(vx, vC), cas(dy, bxC_yC, bxC_yt))     # x∈C ⇒ but
    # branche x=t
    Hxt = N.assume(egal(vx, vt))
    #   sous-branche y∈C : (y,t)∈G (maj) ⇒ (y,x)∈G via t=x
    HyC2 = N.assume(appartient(vy, vC))
    yt = N.modus_ponens(HyC2, instancie(Hmaj, vy))                        # (y,t)∈G
    t_eq_x = N.modus_ponens(Hxt, _sym(vx, vt))                            # t=x
    leib_yx = N.s6(vt, vx, _H, _le(vy, var(_H), vG))                      # (t=x)⇒((y,t)∈G⇔(y,x)∈G)
    yx = N.modus_ponens(yt, equivalence_avant(N.modus_ponens(t_eq_x, leib_yx)))  # (y,x)∈G
    bxt_yC = N.loi_deduction(appartient(vy, vC), _ou_droite(yx, _le(vx, vy, vG)))
    #   sous-branche y=t : (t,t)∈G (réflexivité) ⇒ (x,y)∈G
    Hyt2 = N.assume(egal(vy, vt))
    tt = _refl_sur(vG, vE, vt, HtE)                                       # (t,t)∈G
    #   (x,y)∈G : x=t, y=t ⇒ transporter (t,t)→(x,y)
    leib_x = N.s6(vt, vx, _H, _le(var(_H), vt, vG))                       # (t=x)⇒((t,t)∈G⇔(x,t)∈G)
    xt2 = N.modus_ponens(tt, equivalence_avant(N.modus_ponens(t_eq_x, leib_x)))   # (x,t)∈G
    t_eq_y2 = N.modus_ponens(Hyt2, _sym(vy, vt))                          # t=y
    leib_y = N.s6(vt, vy, _H, _le(vx, var(_H), vG))                       # (t=y)⇒((x,t)∈G⇔(x,y)∈G)
    xy2 = N.modus_ponens(xt2, equivalence_avant(N.modus_ponens(t_eq_y2, leib_y)))  # (x,y)∈G
    bxt_yt = N.loi_deduction(egal(vy, vt), _ou_gauche(xy2, _le(vy, vx, vG)))
    bxt = N.loi_deduction(egal(vx, vt), cas(dy, bxt_yC, bxt_yt))          # x=t ⇒ but
    return cas(dx, bxC, bxt)                                              # but


def _ajoute_comparables(G, E_set, C, t, A, Hch, HtE, Hmaj, x="x", y="y"):
    """⊢ (∀x∀y)((x∈C∪{t} et y∈C∪{t}) ⇒ ((x,y)∈G ou (y,x)∈G))  (comparabilité)."""
    vG, vE, vC, vt = _terme(G), _terme(E_set), _terme(C), _terme(t)
    vx, vy = var(x), var(y)
    Hxy = N.assume(et(appartient(vx, A), appartient(vy, A)))
    hxA = conjonction_elim_gauche(Hxy)
    hyA = conjonction_elim_droite(Hxy)
    comp = _x_comparable_ajoute(vG, vE, vC, vt, A, Hch, HtE, Hmaj, vx, vy, hxA, hyA)
    body = N.loi_deduction(et(appartient(vx, A), appartient(vy, A)), comp)
    return N.generalisation(x, N.generalisation(y, body))


def _ajoute_refl(G, E_set, C, t, A, Hch, HtE, Hmaj, Hgas, Hgtr, x="x"):
    """⊢ reflexivite_sur(G,C∪{t}) = (∀x)(x∈C∪{t} ⇒ (x,x)∈G)  (via comparabilité x,x)."""
    vG, vE, vC, vt = _terme(G), _terme(E_set), _terme(C), _terme(t)
    vx = var(x)
    hxA = N.assume(appartient(vx, A))
    comp = _x_comparable_ajoute(vG, vE, vC, vt, A, Hch, HtE, Hmaj, vx, vx, hxA, hxA)  # (x,x)∈G ou (x,x)∈G
    xx = N.modus_ponens(comp, N.s1(_le(vx, vx, vG)))     # (x,x)∈G
    body = N.loi_deduction(appartient(vx, A), xx)
    return N.generalisation(x, body)


# ── « E sans élément maximal » et « m non maximal ⇒ ∃ strictement plus grand » ─
def sans_maximal(G, E_set, m="m", x="x"):
    """sans_maximal(G,E) := ¬(∃m) element_maximal(G,E,m).  « E n'a pas de maximal »."""
    return non(existe(m, element_maximal(_terme(G), _terme(E_set), var(m), x)))


def _non_maximal_donne_strict(G, E_set, m, hmE, hsans, x="x", t="t"):
    """{ sans_maximal(G,E) [hsans], m∈E [hmE] } ⊢ (∃t)( t∈E et ((m,t)∈G et t≠m) ).

    E sans maximal ⇒ m (∈E) n'est PAS maximal ⇒ ¬(∀x)((x∈E et (m,x)∈G)⇒x=m),
    donc (∃x)(x∈E et (m,x)∈G et x≠m), reformé en (∃t)(t∈E et ((m,t)∈G et t≠m))."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import dne, demorgan_et
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import (
        _neg_impl_equiv, _ex_falso, _refute_self,
    )
    vG, vE, vm = _terme(G), _terme(E_set), _terme(m)
    maxm = element_maximal(vG, vE, vm, x)
    # ── ¬maxm : assume maxm ⇒ (∃m)maximal ⇒ contredit hsans=¬(∃m)maximal ───────
    Hmax = N.assume(maxm)
    Rbind = element_maximal(vG, vE, var("m"), x)
    ex_max = N.modus_ponens(Hmax, N.s5(Rbind, vm, "m"))   # (∃m)maximal   [maxm]
    nP = _ex_falso(ex_max, hsans, non(maxm))             # ¬maxm   [maxm, hsans]
    not_maxm = _refute_self(N.loi_deduction(maxm, nP))   # ¬maxm   [hsans]
    # maxm = m∈E et quant ; ¬maxm ⇔ (¬(m∈E) ou ¬quant) ; m∈E ⇒ ¬quant
    quant = pourtout(x, impl(et(appartient(var(x), vE), _le(vm, var(x), vG)), egal(var(x), vm)))
    dm = demorgan_et(appartient(vm, vE), quant)          # ¬(m∈E et quant) ⇔ (¬(m∈E) ou ¬quant)
    disj_neg = N.modus_ponens(not_maxm, equivalence_avant(dm))   # ¬(m∈E) ou ¬quant
    not_quant = _disj_syll_g(disj_neg, _dni_local(hmE))  # ¬quant
    # ¬(∀x)Rx ⇒ (∃x)¬Rx
    Rx = impl(et(appartient(var(x), vE), _le(vm, var(x), vG)), egal(var(x), vm))
    ex_negRx = N.modus_ponens(not_quant, dne(existe(x, non(Rx))))  # (∃x)¬Rx
    # ¬(P⇒Q) ⇔ (P et ¬Q)
    P = et(appartient(var(x), vE), _le(vm, var(x), vG))
    Q = egal(var(x), vm)
    eqv = _neg_impl_equiv(P, Q)                          # ¬(P⇒Q) ⇔ (P et ¬Q)
    ex_conj = N.modus_ponens(ex_negRx, equivalence_avant(congruence_existe(eqv, x)))  # (∃x)((x∈E et (m,x)∈G) et x≠m)
    return _reformule_strict(vG, vE, vm, ex_conj, x, t)


def _dni_local(thm):
    """De ⊢ P déduit ⊢ ¬¬P."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import dni
    return N.modus_ponens(thm, dni(thm.conclusion))


def _reformule_strict(G, E_set, m, ex_conj, x, t):
    """De ⊢ (∃x)((x∈E et (m,x)∈G) et x≠m) déduit ⊢ (∃t)(t∈E et ((m,t)∈G et t≠m)).

    Réassocie ((P et Q) et R) en (P et (Q et R)) sous le ∃, puis α-renomme x→t."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import assoc_et
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import congruence_existe, alpha_existe
    vG, vE, vm = _terme(G), _terme(E_set), _terme(m)
    P = appartient(var(x), vE)
    Q = _le(vm, var(x), vG)
    R = non(egal(var(x), vm))
    # ((P et Q) et R) ⇔ (P et (Q et R))
    asse = assoc_et(P, Q, R)                             # (P et (Q et R)) ⇔ ((P et Q) et R)
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_symetrie
    asse_inv = equivalence_symetrie(asse)               # ((P et Q) et R) ⇔ (P et (Q et R))
    ex_assoc = N.modus_ponens(ex_conj, equivalence_avant(congruence_existe(asse_inv, x)))  # (∃x)(P et (Q et R))
    # α-renomme x → t
    body_x = et(P, et(Q, R))
    if x == t:
        return ex_assoc
    ren = alpha_existe(x, t, body_x)
    return N.modus_ponens(ex_assoc, equivalence_avant(ren))  # (∃t)(t∈E et ((m,t)∈G et t≠m))


# ── la chaîne strictement plus grande C∪{t} (sous E inductif sans maximal) ────
def _strict_chaine_temoin(G, E_set, C, m, t, refl_E, antisym, trans,
                          hCP, hchaineC, h_m_maj, h_tE, h_mt, h_tne):
    """Construit, pour un majorant m de C et un t>m, le couple
    ( D∈P et (C,D)∈Γ et C≠D ) avec D=C∪{t}, sous les hyps fournies en théorèmes.

    h_m_maj : (∀c)(c∈C⇒(c,m)∈G)  [m majore C] ;  h_tE : t∈E ;  h_mt : (m,t)∈G ;
    h_tne : t≠m.  Renvoie ⊢ (D∈P et ((C,D)∈Γ et C≠D))  [hyps des théorèmes passés]."""
    vG, vE, vC, vm, vt = _terme(G), _terme(E_set), _terme(C), _terme(m), _terme(t)
    D = _ajoute(vC, vt)
    # (a) t majore C : (∀c)(c∈C ⇒ (c,t)∈G)  via (c,m)∈G et (m,t)∈G ⇒ (c,t)∈G
    vc = var("c")
    hcC = N.assume(appartient(vc, vC))
    cm = N.modus_ponens(hcC, instancie(h_m_maj, vc))     # (c,m)∈G
    ct = _trans(vG, vc, vm, vt, cm, h_mt)                # (c,t)∈G  [transitivite_rel(G) assumé par _trans]
    ct = _cut(ct, transitivite_rel(vG), trans)           # décharge la transitivité (fournie par trans)
    t_maj = N.generalisation("c", N.loi_deduction(appartient(vc, vC), ct))  # (∀c)(c∈C⇒(c,t)∈G)
    # (b) chaine(G,E,C∪{t})  via ajoute_est_chaine (décharge ses 6 hyps)
    chaineD = ajoute_est_chaine(G, E_set, C, t)
    chaineD = _cut(chaineD, reflexivite_sur(vG, vE), refl_E)
    chaineD = _cut(chaineD, antisymetrie(vG), antisym)
    chaineD = _cut(chaineD, transitivite_rel(vG), trans)
    chaineD = _cut(chaineD, chaine(vG, vE, vC), hchaineC)
    chaineD = _cut(chaineD, appartient(vt, vE), h_tE)
    chaineD = _cut(chaineD, pourtout("c", impl(appartient(var("c"), vC), _le("c", vt, vG))), t_maj)
    DP = N.modus_ponens(chaineD, equivalence_arriere(_inst_P(vG, vE, D)))   # C∪{t}∈P
    # (c) (C, C∪{t})∈Γ : C⊂C∪{t}, C∈P, C∪{t}∈P
    C_D = _C_inclus_ajoute(vG, vC, vt)                   # C⊂C∪{t}
    C_D_Gamma = _Gamma_intro(vG, vE, vC, D, hCP, DP, C_D)  # (C,C∪{t})∈Γ
    # (d) C ≠ C∪{t} : t∈C∪{t} mais t∉C (sinon (t,m)∈G et (m,t)∈G ⇒ t=m, contredit t≠m)
    t_notin_C = _t_pas_dans_C(vG, vC, vm, vt, antisym, h_m_maj, h_mt, h_tne)  # ¬(t∈C)
    C_ne_D = _C_ne_ajoute(vG, vC, vt, t_notin_C)         # C≠C∪{t}
    return conjonction_intro(DP, conjonction_intro(C_D_Gamma, C_ne_D))


def _C_inclus_ajoute(G, C, t):
    """⊢ C ⊂ C∪{t}  (binder matché à inclus(C,C∪{t}))."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    vG, vC, vt = _terme(G), _terme(C), _terme(t)
    D = _ajoute(vC, vt)
    cible = inclus(vC, D)
    bndr, _ = _peler_pourtout(cible)
    vz = var(bndr)
    hzC = N.assume(appartient(vz, vC))
    zD = _ajoute_intro_C(vC, vt, vz, hzC)                # z∈C∪{t}
    return N.generalisation(bndr, N.loi_deduction(appartient(vz, vC), zD))


def _t_pas_dans_C(G, C, m, t, antisym, h_m_maj, h_mt, h_tne):
    """{ antisymetrie(G), (∀c)(c∈C⇒(c,m)∈G), (m,t)∈G, t≠m } ⊢ ¬(t∈C).

    Si t∈C : (t,m)∈G (m majore C) et (m,t)∈G ⇒ t=m (antisym), contredit t≠m."""
    vG, vC, vm, vt = _terme(G), _terme(C), _terme(m), _terme(t)
    HtC = N.assume(appartient(vt, vC))                   # t∈C
    tm = N.modus_ponens(HtC, instancie(h_m_maj, vt))     # (t,m)∈G
    antisym_inst = instancie(instancie(antisym, vt), vm) # ((t,m)∈G et (m,t)∈G)⇒t=m
    t_eq_m = N.modus_ponens(conjonction_intro(tm, h_mt), antisym_inst)  # t=m
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    falso = _ex_falso(t_eq_m, h_tne, non(appartient(vt, vC)))  # ¬(t∈C)  [t∈C,…]
    return _refute_self(N.loi_deduction(appartient(vt, vC), falso))   # ¬(t∈C)


def _C_ne_ajoute(G, C, t, t_notin_C):
    """{ ¬(t∈C) [t_notin_C] } ⊢ C ≠ C∪{t}.

    t∈C∪{t} ; si C=C∪{t} alors t∈C (Leibniz), contredisant ¬(t∈C)."""
    vG, vC, vt = _terme(G), _terme(C), _terme(t)
    D = _ajoute(vC, vt)
    Heq = N.assume(egal(vC, D))                          # C=C∪{t}
    t_in_D = _ajoute_intro_t(vC, vt)                     # t∈C∪{t}
    # Leibniz : (C∪{t}=C) ⇒ ((t∈C∪{t}) ⇔ (t∈C))
    D_eq_C = N.modus_ponens(Heq, _sym(vC, D))            # C∪{t}=C
    leib = N.s6(D, vC, _H, appartient(vt, var(_H)))      # (C∪{t}=C)⇒((t∈C∪{t})⇔(t∈C))
    t_in_C = N.modus_ponens(t_in_D, equivalence_avant(N.modus_ponens(D_eq_C, leib)))  # t∈C
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    falso = _ex_falso(t_in_C, t_notin_C, non(egal(vC, D)))   # ¬(C=C∪{t})  [C=C∪{t},…]
    return _refute_self(N.loi_deduction(egal(vC, D), falso))  # C≠C∪{t}


def _enonce_strict_D(G, E_set, C, D="D"):
    """(∃D)( D∈P et ((C,D)∈Γ et C≠D) )  — « C a une chaîne STRICTEMENT plus grande »."""
    vG, vE, vC = _terme(G), _terme(E_set), _terme(C)
    vD = var(D)
    corps = et(appartient(vD, P(vG, vE)),
               et(_gle(vC, vD, vG, vE), non(egal(vC, vD))))
    return existe(D, corps)


def strict_chaine_existe(G="G", E_set="E", C="C", m="m", t="t", x="x", D="D"):
    """⊢ { est_inductif(G,E), sans_maximal(G,E), C∈P }
         ⊢ (∃D)( D∈P et ((C,D)∈Γ et C≠D) ).

    C∈P ⇒ C chaîne ⇒ (inductif) majorant m de C dans E ; E sans maximal ⇒ ∃t>m ;
    D:=C∪{t} est une chaîne (t majore C par transitivité) STRICTEMENT plus grande
    (t∉C car (t,m) et (m,t) ⇒ t=m, contredit t≠m).  WITNESS D=C∪{t}."""
    vG, vE, vC, vm, vt = var(G), var(E_set), var(C), var(m), var(t)
    Hind = N.assume(est_inductif(vG, vE))                # est_inductif(G,E)
    Hsans = N.assume(sans_maximal(vG, vE))               # sans_maximal(G,E)
    HCP = N.assume(appartient(vC, P(vG, vE)))            # C∈P
    # structurels depuis est_ordre(G,E) ⊂ est_inductif
    ord_E = conjonction_elim_gauche(Hind)               # est_ordre(G,E)
    refl_E = conjonction_elim_gauche(conjonction_elim_gauche(ord_E))   # reflexivite_sur(G,E)
    antisym = conjonction_elim_droite(conjonction_elim_gauche(ord_E))  # antisymetrie(G)
    trans = conjonction_elim_droite(ord_E)              # transitivite_rel(G)
    # C chaîne
    chaineC = N.modus_ponens(HCP, equivalence_avant(_inst_P(vG, vE, vC)))  # chaine(G,E,C)
    # (inductif) ⇒ (∃m) majorant(G,C,m,E)
    ind_quant = conjonction_elim_droite(Hind)           # (∀C)(chaine⇒(∃m)majorant)
    ex_maj = N.modus_ponens(chaineC, instancie(ind_quant, vC))  # (∃m)majorant(G,C,m,E)
    cible = _enonce_strict_D(vG, vE, vC, D)
    # per-témoin m : majorant(G,C,m,E) ⇒ cible
    Hmaj = N.assume(majorant(vG, vC, vm, vE, x))         # majorant(G,C,m,E)
    mE = conjonction_elim_gauche(Hmaj)                  # m∈E
    m_majfun = conjonction_elim_droite(Hmaj)           # (∀x)(x∈C⇒(x,m)∈G)
    # E sans maximal ⇒ (∃t)(t∈E et ((m,t)∈G et t≠m))
    ex_strict = _non_maximal_donne_strict(vG, vE, vm, mE, Hsans, x, t)
    # per-témoin t : (t∈E et ((m,t)∈G et t≠m)) ⇒ cible
    Hw = N.assume(et(appartient(vt, vE), et(_le(vm, vt, vG), non(egal(vt, vm)))))
    tE = conjonction_elim_gauche(Hw)                   # t∈E
    mt_tne = conjonction_elim_droite(Hw)               # (m,t)∈G et t≠m
    mt = conjonction_elim_gauche(mt_tne)               # (m,t)∈G
    tne = conjonction_elim_droite(mt_tne)              # t≠m
    temoin = _strict_chaine_temoin(vG, vE, vC, vm, vt, refl_E, antisym, trans,
                                   HCP, chaineC, m_majfun, tE, mt, tne)  # (D∈P et ((C,D)∈Γ et C≠D))
    D_term = _ajoute(vC, vt)
    corps_D = et(appartient(var(D), P(vG, vE)),
                 et(_gle(vC, var(D), vG, vE), non(egal(vC, var(D)))))
    ex_D = N.modus_ponens(temoin, N.s5(corps_D, D_term, D))   # (∃D)(…)  [Hw,…]
    # éliminer ∃t
    wit_t = N.loi_deduction(et(appartient(vt, vE), et(_le(vm, vt, vG), non(egal(vt, vm)))), ex_D)
    ex_after_t = N.modus_ponens(ex_strict, existe_elimination(wit_t, t))   # (∃D)(…)  [Hmaj,…]
    # éliminer ∃m
    wit_m = N.loi_deduction(majorant(vG, vC, vm, vE, x), ex_after_t)
    ex_after_m = N.modus_ponens(ex_maj, existe_elimination(wit_m, m))      # (∃D)(…)  [Hind,Hsans,HCP]
    return ex_after_m


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 (suite) — l'application f STRICTEMENT INFLATIONNAIRE par le signe τ.
#  f(C) := τ_D( D∈P et ((C,D)∈Γ et C≠D) )  « une chaîne strictement plus grande »
#  (terme opaque + axiome DÉFINITIONNEL ; le τ EST l'opérateur de choix du noyau).
# ════════════════════════════════════════════════════════════════════════════
def zorn_f(G, E_set):
    """f := l'application C ↦ τ_D( D∈P et ((C,D)∈Γ et C≠D) )  (majorant STRICT par τ)."""
    return E.app("zorn_f", _terme(G), _terme(E_set))


def _corps_strict_D(G, E_set, C, D="D"):
    """Corps strict :  D∈P et ((C,D)∈Γ et C≠D)."""
    vG, vE, vC, vD = _terme(G), _terme(E_set), _terme(C), var(D)
    return et(appartient(vD, P(vG, vE)), et(_gle(vC, vD, vG, vE), non(egal(vC, vD))))


def _tau_strict(G, E_set, C, D="D"):
    """τ_D( D∈P et ((C,D)∈Γ et C≠D) )  (le témoin-τ de la chaîne strictement plus grande)."""
    return tau(D, _corps_strict_D(G, E_set, C, D))


def axiome_f(G="G", E_set="E", C="C", D="D"):
    """⊢-schéma (∀G E C)( f(C) = τ_D( D∈P et ((C,D)∈Γ et C≠D) ) ).

    Axiome DÉFINITIONNEL de f via le signe τ (opérateur de Hilbert du noyau,
    légitime — c'est l'AXIOME DU CHOIX du projet).  N'altère PAS theorie_ensembles()."""
    vG, vE, vC = var(G), var(E_set), var(C)
    return pourtout(G, pourtout(E_set, pourtout(C,
        egal(pval(zorn_f(vG, vE), vC), _tau_strict(vG, vE, vC, D)))))


def theorie_f(G="G", E_set="E", C="C", D="D"):
    """Théorie DÉDIÉE ne contenant que l'axiome de f (E.III.2, Zorn, ÉTAPE 4, τ)."""
    return N.Theorie("f-Zorn", [axiome_f(G, E_set, C, D)])


def _inst_f(G, E_set, C, D="D"):
    """⊢ ( f(C) = τ_D(corps strict) )   (axiome de f instancié aux TERMES)."""
    ax = N.axiome(theorie_f(), axiome_f(D=D))
    for tm in (G, E_set, C):
        ax = instancie(ax, _terme(tm))
    return ax


def _f_temoin(G, E_set, C, ex_strict, D="D"):
    """De ⊢ (∃D)( D∈P et ((C,D)∈Γ et C≠D) ) [ex_strict] déduit
       ⊢ ( f(C)∈P et ((C,f(C))∈Γ et C≠f(C)) ).

    existe_temoin : (∃D)corps ⇒ (τ_D corps | D)corps ; et f(C)=τ_D corps (axiome) ;
    Leibniz remplace τ_D corps par f(C).  C'est le CŒUR τ : f(C) EST le témoin."""
    vG, vE, vC = _terme(G), _terme(E_set), _terme(C)
    corps = _corps_strict_D(vG, vE, vC, D)
    tau_t = _tau_strict(vG, vE, vC, D)
    # (∃D)corps ⇒ (τ_D corps|D)corps
    temoin_brut = N.modus_ponens(ex_strict, N.existe_temoin(corps, D))  # (τ|D)corps = corps[D:=τ]
    # corps[D:=τ] = (τ∈P et ((C,τ)∈Γ et C≠τ))  ; remplacer τ par f(C) via f(C)=τ (Leibniz)
    f_eq_tau = _inst_f(vG, vE, vC, D)                   # f(C)=τ
    tau_eq_f = N.modus_ponens(f_eq_tau, _sym(pval(zorn_f(vG, vE), vC), tau_t))  # τ=f(C)
    # Leibniz : (τ=f(C)) ⇒ ( corps[D:=τ] ⇔ corps[D:=f(C)] )
    leib = N.s6(tau_t, pval(zorn_f(vG, vE), vC), D, corps)   # (τ=f(C))⇒((τ|D)corps ⇔ (f(C)|D)corps)
    eqv = N.modus_ponens(tau_eq_f, leib)
    return N.modus_ponens(temoin_brut, equivalence_avant(eqv))  # (f(C)|D)corps = f(C)∈P et …


def _alpha_forall_x(thm, src, dst, corps_src):
    """De ⊢ (∀src)corps déduit ⊢ (∀dst)(dst|src)corps  (α-renommage du ∀)."""
    if src == dst:
        return thm
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_pour_tout
    ren = alpha_pour_tout(src, dst, corps_src)          # (∀src)corps ⇔ (∀dst)corps'
    return N.modus_ponens(thm, equivalence_avant(ren))


def f_application_dans(G="G", E_set="E", C="C", x="x"):
    """⊢ { est_inductif(G,E), sans_maximal(G,E) } ⊢ application_dans(P,f).

    application_dans(P,f) = (∀x)(x∈P ⇒ f(x)∈P).  Pour C∈P, strict_chaine_existe
    donne (∃D)(D∈P et …) ; f(C) EST ce témoin (τ), donc f(C)∈P.  Preuve faite avec
    le binder « C » puis α-renommée en « x » pour matcher application_dans(P,f)."""
    vG, vE, vC = var(G), var(E_set), var(C)
    Hind = N.assume(est_inductif(vG, vE))
    Hsans = N.assume(sans_maximal(vG, vE))
    ex_strict = strict_chaine_existe(G, E_set, C)       # (∃D)(…)  [Hind,Hsans,C∈P]
    ex_strict = _cut(ex_strict, est_inductif(vG, vE), Hind)
    ex_strict = _cut(ex_strict, sans_maximal(vG, vE), Hsans)
    temoin = _f_temoin(vG, vE, vC, ex_strict)           # f(C)∈P et ((C,f(C))∈Γ et C≠f(C))
    fCP = conjonction_elim_gauche(temoin)               # f(C)∈P
    corps = impl(appartient(vC, P(vG, vE)), appartient(pval(zorn_f(vG, vE), vC), P(vG, vE)))
    body = N.loi_deduction(appartient(vC, P(vG, vE)), fCP)
    allC = N.generalisation(C, body)                    # (∀C)(C∈P ⇒ f(C)∈P)
    return _alpha_forall_x(allC, C, x, corps)           # application_dans(P,f)


def f_inflationnaire_strict(G="G", E_set="E", C="C", x="x"):
    """⊢ { est_inductif(G,E), sans_maximal(G,E) } ⊢ inflationnaire_strict(Γ,P,f).

    inflationnaire_strict(Γ,P,f) = (∀x)(x∈P ⇒ ((x,f(x))∈Γ et x≠f(x))).  Pour C∈P,
    f(C) EST le témoin-τ de la chaîne strictement plus grande, donc (C,f(C))∈Γ et
    C≠f(C).  Preuve binder « C » puis α-renommée en « x »."""
    vG, vE, vC = var(G), var(E_set), var(C)
    Hind = N.assume(est_inductif(vG, vE))
    Hsans = N.assume(sans_maximal(vG, vE))
    ex_strict = strict_chaine_existe(G, E_set, C)
    ex_strict = _cut(ex_strict, est_inductif(vG, vE), Hind)
    ex_strict = _cut(ex_strict, sans_maximal(vG, vE), Hsans)
    temoin = _f_temoin(vG, vE, vC, ex_strict)           # f(C)∈P et ((C,f(C))∈Γ et C≠f(C))
    strict_part = conjonction_elim_droite(temoin)       # (C,f(C))∈Γ et C≠f(C)
    fC = pval(zorn_f(vG, vE), vC)
    corps = impl(appartient(vC, P(vG, vE)),
                 et(_gle(vC, fC, vG, vE), non(egal(vC, fC))))
    body = N.loi_deduction(appartient(vC, P(vG, vE)), strict_part)
    allC = N.generalisation(C, body)                    # (∀C)(C∈P ⇒ ((C,f(C))∈Γ et C≠f(C)))
    return _alpha_forall_x(allC, C, x, corps)           # inflationnaire_strict(Γ,P,f)


def f_inflationnaire(G="G", E_set="E", C="x"):
    """⊢ { est_inductif(G,E), sans_maximal(G,E) } ⊢ inflationnaire(Γ,P,f).

    inflationnaire(Γ,P,f) = (∀x)(x∈P ⇒ (x,f(x))∈Γ).  Affaiblissement de
    inflationnaire_strict (on oublie x≠f(x))."""
    vG, vE, vC = var(G), var(E_set), var(C)
    strict = f_inflationnaire_strict(G, E_set)           # (∀x)(x∈P⇒((x,f(x))∈Γ et x≠f(x)))
    fC = pval(zorn_f(vG, vE), vC)
    hCP = N.assume(appartient(vC, P(vG, vE)))
    strict_C = N.modus_ponens(hCP, instancie(strict, vC))  # (C,f(C))∈Γ et C≠f(C)
    infl_C = conjonction_elim_gauche(strict_C)           # (C,f(C))∈Γ
    body = N.loi_deduction(appartient(vC, P(vG, vE)), infl_C)
    return N.generalisation(C, body)                     # inflationnaire(Γ,P,f)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 5 — ASSEMBLAGE FINAL : 🎯 LE THÉORÈME DE ZORN
#  Sous « E inductif ≠ ∅ SANS maximal », les 5 hyps de Bourbaki–Witt + f
#  STRICTEMENT inflationnaire sont toutes PROUVÉES ⇒ bw_strict_contradiction est
#  violé ⇒ « E sans maximal » est ABSURDE ⇒ (∃m) element_maximal (tertium).
# ════════════════════════════════════════════════════════════════════════════
def _bw_strict_contra_terme(G, E_set):
    """⊢ ¬( bw-hyps(Γ,P,f,∅) ∧ inflationnaire_strict(Γ,P,f) )  pour des TERMES G,E.

    Instancie bw_strict_contradiction (CLOS) aux termes Γ(G,E), P(G,E), f(G,E), ∅.

    SUBTILITÉ DE CAPTURE : Γ/P/f portent les lettres G,E.  Pour éviter que
    l'instanciation d'un binder capture le G/E libre d'un terme déjà substitué, on
    passe par des lettres-PIVOTS fraîches g0,e0 : on construit ¬(…) avec
    Γ(g0,e0)/P(g0,e0)/f(g0,e0), puis on généralise g0,e0 et on instancie en G,E."""
    g0, e0 = "_zg0", "_ze0"
    vg0, ve0 = var(g0), var(e0)
    Gam0, P0, f0 = Gamma(vg0, ve0), P(vg0, ve0), zorn_f(vg0, ve0)
    th = bw_strict_contradiction()                       # CLOS (vars G,E,p,a)
    # instancie les 4 binders aux termes-pivots (g0,e0 ∉ {G,E,p,a} ⇒ aucune capture)
    th = N.generalisation("G", N.generalisation("E", N.generalisation("p",
            N.generalisation("a", th))))                 # (∀a∀p∀E∀G)¬(…)
    th = instancie(th, Gam0)                             # G:=Γ(g0,e0)
    th = instancie(th, P0)                               # E:=P(g0,e0)
    th = instancie(th, f0)                               # p:=f(g0,e0)
    th = instancie(th, E.VIDE)                           # a:=∅
    # maintenant g0,e0 sont les SEULES lettres libres résiduelles ⇒ substituables
    th = instancie(N.generalisation(g0, th), _terme(G))  # g0:=G
    th = instancie(N.generalisation(e0, th), _terme(E_set))  # e0:=E
    return th


def zorn_theoreme(G="G", E_set="E", m="m", C="C", x="x", y="y", z="z"):
    """⊢ ( est_ordre(G,E) et est_inductif(G,E) et E≠∅ ) ⇒ (∃m) element_maximal(G,E,m).

    🎯🎯🎯 THÉORÈME 2 (ZORN), §III.2 — PROUVÉ via Bourbaki–Witt, INCONDITIONNEL
    (theorie_ensembles()=22).  Schéma : on raisonne par l'absurde.  Supposons
    « E sans élément maximal » (sans_maximal).  Sur le poset (P,Γ) des chaînes de E :
      • est_ordre(Γ,P)          — Gamma_est_ordre (inconditionnel) ;
      • chaine_complet(Γ,P)     — Gamma_chaine_complet (⋃ d'une Γ-chaîne, antisym/trans G) ;
      • plus_petit_element(Γ,P,∅) — vide_plus_petit (∅ chaîne vide) ;
      • application_dans(P,f)   — f_application_dans (τ-majorant strict, E inductif sans maximal) ;
      • inflationnaire(Γ,P,f)   — f_inflationnaire ;
      • inflationnaire_strict(Γ,P,f) — f_inflationnaire_strict.
    Ces 5+1 sont EXACTEMENT le crochet de bw_strict_contradiction(Γ,P,f,∅), qui est
    FAUX — contradiction.  Donc ¬sans_maximal, i.e. ¬¬(∃m)maximal, d'où (∃m)maximal.
    Aucun maximal ni point fixe n'est postulé : tout est DÉMONTRÉ."""
    vG, vE = var(G), var(E_set)
    Gam, Pp = Gamma(vG, vE), P(vG, vE)
    f = zorn_f(vG, vE)
    vide = E.VIDE
    # ── hypothèses globales de Zorn ───────────────────────────────────────────
    hyp_zorn = et(et(est_ordre(vG, vE, x, y, z),
                     est_inductif(vG, vE, C, m, x, y, z)),
                  enonce_non_vide(vE, x))
    Hz = N.assume(hyp_zorn)
    ord_E = conjonction_elim_gauche(conjonction_elim_gauche(Hz))   # est_ordre(G,E)
    ind_E = conjonction_elim_droite(conjonction_elim_gauche(Hz))   # est_inductif(G,E)
    antisym_G = conjonction_elim_droite(conjonction_elim_gauche(ord_E))  # antisymetrie(G)
    trans_G = conjonction_elim_droite(ord_E)                       # transitivite_rel(G)

    # ── sous l'hypothèse « E sans maximal », tout le crochet BW est PROUVÉ ─────
    Hsm = N.assume(sans_maximal(vG, vE))                 # sans_maximal(G,E)
    # est_ordre(Γ,P) — inconditionnel
    ord_GP = Gamma_est_ordre(G, E_set)
    # chaine_complet(Γ,P) — antisym/trans de G
    cc_GP = Gamma_chaine_complet(G, E_set)
    cc_GP = _cut(cc_GP, antisymetrie(vG), antisym_G)
    cc_GP = _cut(cc_GP, transitivite_rel(vG), trans_G)
    # plus_petit_element(Γ,P,∅) — antisym/trans de G
    ppe_GP = vide_plus_petit(G, E_set)
    ppe_GP = _cut(ppe_GP, antisymetrie(vG), antisym_G)
    ppe_GP = _cut(ppe_GP, transitivite_rel(vG), trans_G)
    # application_dans(P,f) — est_inductif, sans_maximal
    app_Pf = f_application_dans(G, E_set)
    app_Pf = _cut(app_Pf, est_inductif(vG, vE), ind_E)
    app_Pf = _cut(app_Pf, sans_maximal(vG, vE), Hsm)
    # inflationnaire(Γ,P,f)
    infl_Pf = f_inflationnaire(G, E_set)
    infl_Pf = _cut(infl_Pf, est_inductif(vG, vE), ind_E)
    infl_Pf = _cut(infl_Pf, sans_maximal(vG, vE), Hsm)
    # inflationnaire_strict(Γ,P,f)
    strict_Pf = f_inflationnaire_strict(G, E_set)
    strict_Pf = _cut(strict_Pf, est_inductif(vG, vE), ind_E)
    strict_Pf = _cut(strict_Pf, sans_maximal(vG, vE), Hsm)

    # ── assembler le crochet EXACT de bw_strict_contradiction(Γ,P,f,∅) ────────
    bw_hyp = conjonction_intro(
        conjonction_intro(
            conjonction_intro(
                conjonction_intro(ord_GP, cc_GP),
                app_Pf),
            infl_Pf),
        ppe_GP)                                          # bw-hyps(Γ,P,f,∅)
    conj = conjonction_intro(bw_hyp, strict_Pf)          # bw-hyps ∧ inflationnaire_strict
    # bw_strict_contradiction : ¬conj
    not_conj = _bw_strict_contra_terme(G, E_set)
    # contradiction ⇒ n'importe quoi : ici on vise ¬sans_maximal
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    falso = _ex_falso(conj, not_conj, non(sans_maximal(vG, vE)))   # ¬sans_maximal  [Hsm, Hz]
    not_sm = _refute_self(N.loi_deduction(sans_maximal(vG, vE), falso))  # ¬sans_maximal  [Hz]
    # ¬sans_maximal = ¬¬(∃m)maximal ⇒ (∃m)maximal  (dne)
    from bourbaki.logique.tactiques.tactiques_abrege2 import dne
    ex_max = element_maximal(vG, vE, var(m), x)
    conc = N.modus_ponens(not_sm, dne(existe(m, ex_max)))   # (∃m)element_maximal(G,E,m)  [Hz]
    return N.loi_deduction(hyp_zorn, conc)               # ⊢ hyp_zorn ⇒ (∃m)maximal


__all__ = [
    # ÉTAPE 1 — poset des chaînes
    "P", "axiome_P", "theorie_P", "P_membre",
    "Gamma", "axiome_Gamma", "theorie_Gamma", "Gamma_membre",
    "Gamma_reflexive_sur", "Gamma_antisymetrique", "Gamma_transitive",
    "Gamma_est_ordre",
    # ÉTAPE 2 — réunion d'une Γ-chaîne (CHAÎNE-COMPLET)
    "Union", "axiome_Union", "theorie_Union", "Union_membre", "Union_inclus_E",
    "Union_totalement_ordonne", "Union_dans_P", "Union_majorant", "Union_borne_sup",
    "Gamma_chaine_complet",
    # ÉTAPE 3 — ∅ plus petit élément
    "vide_est_chaine", "vide_dans_P", "vide_plus_petit",
    # ÉTAPE 4 — chaîne augmentée C∪{t} + E sans maximal + strict + f (τ)
    "ajoute_est_chaine", "sans_maximal", "strict_chaine_existe",
    "zorn_f", "axiome_f", "theorie_f",
    "f_application_dans", "f_inflationnaire_strict", "f_inflationnaire",
    # ÉTAPE 5 — 🎯 LE THÉORÈME DE ZORN
    "zorn_theoreme",
]
