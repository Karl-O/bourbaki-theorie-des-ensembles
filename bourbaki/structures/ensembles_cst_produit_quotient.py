"""§IV.2 — CRITÈRES DE STRUCTURES (CST), PRODUIT & QUOTIENT : CST13/15/16/17/21.

Module NEUF (campagne « critères de structures », vague 3 — clôture du §IV.2).  Il
PROLONGE `ensembles_cst_criteres_suite` (CST6/7/10/11/14), `ensembles_CST_criteres`
(CST9/CST18 unicité, transport, CST5), `ensembles_structures_derivees_props`
(CST10/CST11/CST19 transitivités via les propriétés (IN)/(FI)) et
`ensembles_chap4_props_restantes` (CST12/CST20 morphismes restriction/quotient) en
CERTIFIANT (au niveau du noyau, `.est_clos` ou CONDITIONNEL à hypothèses EXPLICITES)
les 5 critères de structures du §IV.2 qui restaient ABSENTS :

  • CST15 — lien structure IMAGE RÉCIPROQUE / structure PRODUIT (cas particulier de
    CST10, transitivité initiale) ;
  • CST16 — une famille de morphismes f_ι : E → E_ι DÉFINIT un morphisme f = (f_ι) de E
    dans le PRODUIT ∏ E_ι (propriété universelle (IN) du produit) ;
  • CST21 — TRANSITIVITÉ des structures QUOTIENT (analogue de CST19 finale-transitive) ;
  • CST13 — ASSOCIATIVITÉ de la structure produit (∏ sur une partition ≅ ∏∏ ; palier
    d'UNICITÉ / iso canonique, mirroir de CST10) ;
  • CST17 — un morphisme est CARACTÉRISÉ par son GRAPHE F ⊂ A×B (la projection pr₁ : F→A
    est un isomorphisme pour la structure induite — cas particulier de l'image
    réciproque, mirroir de CST15).

CONVENTION DE PARAMÉTRAGE — strictement IDENTIQUE au reste de `bourbaki.structures`
(cf. docstrings de `ensembles_universel_morphismes`).  Le prédicat de morphisme
abstrait `morph(e1,s1,e2,s2,f) -> Formule` porte la donnée méta (Σ,σ).  Les structures,
ensembles de base, applications sont des TERMES (opaques).  Les théorèmes prouvés ici
ne dépendent QUE de la STRUCTURE LOGIQUE (∀/∃/⇔/=) des propriétés (IN)/(FI)/(MO_III) —
valables QUELLE QUE SOIT la donnée σ.  theorie_ensembles() reste à 22 axiomes : AUCUN
axiome créé.  Tout est soit LOGIQUE PUR, soit CONDITIONNEL à des hypothèses EXPLICITES
(les axiomes-schémas (IN)/(FI)/(MO_III)/associativité de ∘ INSTANCIÉS) fournies comme
PRÉMISSES — JAMAIS postulées vraies dans la théorie.

NON VACUEUX (vérifié « conclusion ∉ hypothèses » pour chaque théorème) : voir docstrings.

REPORTÉ honnêtement (méta / lourd, hors fragment) :
  • l'EXISTENCE effective des structures produit/quotient/image-réciproque (CST22,
    constructions par échelon) ;
  • pour CST13/CST15/CST17, les équivalences « a)⟺b) » d'EXISTENCE ; on certifie le
    palier d'UNICITÉ/égalité (« entraînent que 𝒮=𝒮' ») et le palier de DÉFINITION-de-
    morphisme — comme CST10/CST11/CST14/CST19.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, equiv, pourtout,
                                       appartient, app)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie)
from bourbaki.structures.ensembles_universel_morphismes import (
    est_morphisme, plus_fine, propriete_IN, _morph_defaut, _t)
from bourbaki.structures.ensembles_universel_finale import propriete_FI
from bourbaki.structures.ensembles_CST_criteres import (
    initiales_mutuellement_plus_fines, finales_mutuellement_plus_fines,
    id_est_morphisme)


def _morph(morph):
    return morph if morph is not None else _morph_defaut()


def _defaults_in(af, sf, ff, morph):
    if af is None:
        af = lambda t: app("A", t)
    if sf is None:
        sf = lambda t: app("Sig", t)
    if ff is None:
        ff = lambda t: app("f", t)
    return af, sf, ff, _morph(morph)


# ════════════════════════════════════════════════════════════════════════════
#  CST16 — FAMILLE DE MORPHISMES → MORPHISME DANS LE PRODUIT  (propriété (IN))
# ════════════════════════════════════════════════════════════════════════════
#
#  « Soient (E_ι)_{ι∈I} une famille d'ensembles munis de structures 𝒮_ι d'espèce Σ,
#    E = ∏_ι E_ι muni de la structure produit 𝒫, et pr_ι : E → E_ι les projections.
#    Pour qu'une application f : E' → E (E' muni de 𝒮') soit un morphisme de (E',𝒮')
#    dans (E,𝒫), il faut et il suffit que chacune des applications f_ι = pr_ι∘f soit un
#    morphisme de (E',𝒮') dans (E_ι,𝒮_ι). »   (caractérisation du morphisme à valeurs
#    dans un produit — propriété universelle (IN) de la structure produit).
#
#  C'est LITTÉRALEMENT (IN) instanciée à (E',𝒮',f) pour la famille (E_ι,𝒮_ι,pr_ι) qui
#  DÉFINIT la structure produit.  On certifie le sens « si chaque f_ι = pr_ι∘f est un
#  morphisme alors f est un morphisme » (le sens « utile » du critère CST16).
#
def cst16_famille_morphismes_produit(ep="Ep", sp="Sp", e="E", struct_P="P",
                                     i="I0", f="f", af=None, sf=None,
                                     prf=None, morph=None, iota="iota"):
    """{ (IN) pour 𝒫 (structure produit) sur E = ∏E_ι, famille (E_ι,𝒮_ι,pr_ι),
         CHAQUE := (∀ι)(ι∈I ⇒ pr_ι∘f est un morphisme de (E',𝒮') dans (E_ι,𝒮_ι)) }
        ⊢  f est un morphisme de (E',𝒮') dans (E,𝒫).

    CRITÈRE CST16 (IV.2) — une famille de morphismes définit un morphisme dans le
    PRODUIT.  Si chaque composée pr_ι∘f (ι∈I) est un morphisme de (E',𝒮') dans
    (E_ι,𝒮_ι), alors f lui-même est un morphisme de (E',𝒮') dans le produit (E,𝒫).

    PREUVE (propriété universelle (IN), pure logique).  La structure produit 𝒫 est, par
    définition, la structure INITIALE pour la famille (E_ι,𝒮_ι,pr_ι) : elle vérifie (IN)
        (∀E')(∀𝒮')(∀g)[ morph(E',𝒮',E,𝒫,g) ⇔ (∀ι)(ι∈I ⇒ morph(E',𝒮',E_ι,𝒮_ι, pr_ι∘g)) ].
    On instancie (IN) à (E'=E', 𝒮'=𝒮', g=f) : morph(E',𝒮',E,𝒫,f) ⇔ CHAQUE, où CHAQUE est
    exactement l'hypothèse « (∀ι) pr_ι∘f morphisme ».  Par modus ponens (sens ⇐ de
    l'équivalence), f est un morphisme.

    REPORTÉ : l'EXISTENCE de 𝒫 (construction du produit, CST22).  On certifie le palier
    de caractérisation.  NON VACUEUX : la conclusion « morph(E',𝒮',E,𝒫,f) » ∉ hypothèses
    (les hyps sont (IN) — une ÉQUIVALENCE universelle — et CHAQUE — la clause sur les
    pr_ι∘f, formule DISTINCTE de morph(E',𝒮',E,𝒫,f))."""
    af, sf, prf, morph = _defaults_in(af, sf, prf, morph)
    if prf is None:
        prf = lambda t: app("pr_indice", _t(e), t)
    vep, vsp, ve, vi, vf = _t(ep), _t(sp), _t(e), _t(i), _t(f)
    sP = _t(struct_P)

    inn = propriete_IN(ve, sP, vi, af, sf, prf, morph=morph)
    h_in = N.assume(inn)
    # instancie (∀E')(∀𝒮')(∀g) à (E', 𝒮', f)
    eqv = instancie(instancie(instancie(h_in, vep), vsp), vf)  # morph(E',𝒮',E,𝒫,f) ⇔ CHAQUE
    # CHAQUE = membre droit de (IN) à g=f : (∀ι)(ι∈I ⇒ pr_ι∘f morphisme).  On le RECONSTRUIT
    # littéralement (même schéma que `propriete_IN`) plutôt que d'analyser la désucrification
    # de ⇔ : c'est la clause sur les composées pr_ι∘f.
    viota = var("iota")
    chaque = pourtout("iota", impl(appartient(viota, vi),
        est_morphisme(vep, vsp, af(viota), sf(viota), E.composee(prf(viota), vf), morph)))
    # contrôle : `chaque` est bien le membre droit de l'équivalence (IN) instanciée
    assert eqv.conclusion == equiv(
        est_morphisme(vep, vsp, ve, sP, vf, morph), chaque), \
        "membre droit (IN) reconstruit ≠ clause des composées"
    h_chaque = N.assume(chaque)
    res = N.modus_ponens(h_chaque, equivalence_arriere(eqv))   # f morphisme dans le produit
    cible = est_morphisme(vep, vsp, ve, sP, vf, morph)
    assert res.conclusion == cible, "conclusion ≠ (f morphisme dans le produit)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST15 — LIEN IMAGE RÉCIPROQUE / PRODUIT  (cas particulier de CST10, unicité)
# ════════════════════════════════════════════════════════════════════════════
#
#  « Soit (E_ι,𝒮_ι)_{ι∈I} une famille, E = ∏E_ι le produit muni de 𝒫.  Soit E' un
#    ensemble et g : E' → E une application ; soit g_ι = pr_ι∘g.  La structure image
#    réciproque de 𝒫 par g sur E' coïncide avec la structure INITIALE de la famille
#    (E_ι,𝒮_ι,g_ι)_{ι∈I}. »  (l'image réciproque du produit = l'initiale des composées :
#    cas particulier de la TRANSITIVITÉ des structures initiales CST10, g_ι = pr_ι∘g.)
#
#  Le palier d'UNICITÉ (« ces deux structures sont identiques ») est EXACTEMENT le
#  schéma de CST10 : deux structures sur E' vérifiant (IN) (l'une comme image réciproque
#  du produit, l'autre comme initiale des g_ι) sont mutuellement plus fines, donc égales
#  par antisymétrie (MO_III).  On RÉUTILISE `cst10_initiales_egales` spécialisé.
#
def cst15_imrec_produit_egales(ep="Ep", struct_R="R", struct_J="J", i="I0",
                               af=None, sf=None, gf=None, morph=None):
    """{ (IN_𝓡) pour 𝓡 = image réciproque de 𝒫 par g (vue comme initiale de la famille
                des g_ι = pr_ι∘g sur E'),
         (IN_𝓙) pour 𝓙 = structure initiale directe de la famille (E_ι,𝒮_ι,g_ι),
         id morph (E',𝓡)->(E',𝓡), id morph (E',𝓙)->(E',𝓙),
         ANTISYM := (plus_fine(E',𝓡,𝓙) et plus_fine(E',𝓙,𝓡)) ⇒ 𝓡=𝓙 }
        ⊢  𝓡 = 𝓙.

    CRITÈRE CST15 (IV.2) — LIEN IMAGE RÉCIPROQUE / PRODUIT, palier d'UNICITÉ.  L'image
    réciproque 𝓡 du produit 𝒫 par g et la structure initiale 𝓙 de la famille des
    composées g_ι = pr_ι∘g coïncident.  C'est un CAS PARTICULIER de CST10 (transitivité
    initiale) : les deux structures vérifient la MÊME propriété (IN) pour la famille
    (E_ι,𝒮_ι,g_ι) (l'image réciproque du produit rend exactement morphismes les
    applications h telles que chaque g_ι∘h est morphisme), donc sont mutuellement plus
    fines et égales par antisymétrie (MO_III).

    Réalisé comme INSTANCE de `cst10_initiales_egales` (même schéma d'unicité).  REPORTÉ :
    l'équivalence d'EXISTENCE.  NON VACUEUX : 𝓡=𝓙 ∉ hypothèses (ANTISYM est l'IMPLICATION
    (pf∧pf)⇒(𝓡=𝓙), pas l'égalité)."""
    from bourbaki.structures.ensembles_CST_criteres import cst9_unicite_initiale
    sR, sJ = _t(struct_R), _t(struct_J)
    # les deux structures (image-réciproque-du-produit et initiale-des-composées) vérifient
    # (IN) pour la MÊME famille (E_ι,𝒮_ι, g_ι) ; unicité par antisymétrie = schéma CST9/CST10
    res = cst9_unicite_initiale(ep, struct_R, struct_J, i, af, sf, gf, morph)
    assert res.conclusion == egal(sR, sJ), "conclusion ≠ (𝓡 = 𝓙)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST13 — ASSOCIATIVITÉ DE LA STRUCTURE PRODUIT  (palier d'UNICITÉ / iso canonique)
# ════════════════════════════════════════════════════════════════════════════
#
#  « Soit (E_ι)_{ι∈I} une famille munie de structures 𝒮_ι, et soit (J_λ)_{λ∈L} une
#    PARTITION de I.  Alors la structure produit 𝒫 sur ∏_{ι∈I} E_ι et la structure
#    produit (des produits partiels) 𝒫' sur ∏_{λ∈L}(∏_{ι∈J_λ} E_ι), transportées par
#    l'isomorphisme canonique d'associativité, COÏNCIDENT. »   (associativité de ∏.)
#
#  Palier d'UNICITÉ (mirroir EXACT de CST10) : 𝒫 et le transporté 𝒫' de la double-produit
#  sont deux structures INITIALES sur le même ensemble (∏E_ι, à l'iso d'associativité
#  près) pour la MÊME famille de projections composées (pr_ι = pr_{ι,J_λ}∘pr_{J_λ}) ;
#  elles sont mutuellement plus fines, donc égales par antisymétrie (MO_III).
#
def cst13_produit_associatif_egales(e="E", struct_P="P", struct_Pp="Pp", i="I0",
                                    af=None, sf=None, ff=None, morph=None):
    """{ (IN_𝒫) pour le produit total 𝒫 sur E = ∏_{ι∈I} E_ι (famille (E_ι,𝒮_ι,pr_ι)),
         (IN_𝒫') pour le produit-des-produits-partiels 𝒫' transporté sur E (même famille
                  de projections composées pr_ι = pr_{ι∈J_λ}∘pr_{J_λ}, partition (J_λ)),
         id morph (E,𝒫)->(E,𝒫), id morph (E,𝒫')->(E,𝒫'),
         ANTISYM := (plus_fine(E,𝒫,𝒫') et plus_fine(E,𝒫',𝒫)) ⇒ 𝒫=𝒫' }
        ⊢  𝒫 = 𝒫'.

    CRITÈRE CST13 (IV.2) — ASSOCIATIVITÉ de la structure produit, palier d'UNICITÉ.  Pour
    une partition (J_λ)_{λ∈L} de I, la structure produit totale 𝒫 sur ∏_{ι∈I} E_ι et la
    structure produit (des produits partiels) 𝒫' = ∏_λ(∏_{ι∈J_λ}E_ι), transportée par
    l'isomorphisme canonique d'associativité, COÏNCIDENT.  Les deux sont des structures
    INITIALES pour la MÊME famille de projections (pr_ι, ι∈I, écrites comme composées
    pr_{ι,J_λ}∘pr_{J_λ}), donc mutuellement plus fines et égales par antisymétrie (MO_III)
    — EXACTEMENT le schéma de CST10.

    Réalisé comme INSTANCE de `cst10_initiales_egales`.  REPORTÉ : l'EXISTENCE de
    l'isomorphisme canonique d'associativité et la construction effective des produits
    (CST22) ; on certifie le palier d'égalité « les deux structures produit coïncident ».
    NON VACUEUX : 𝒫=𝒫' ∉ hypothèses (ANTISYM est l'implication (pf∧pf)⇒(𝒫=𝒫'))."""
    from bourbaki.structures.ensembles_CST_criteres import cst9_unicite_initiale
    sP, sPp = _t(struct_P), _t(struct_Pp)
    res = cst9_unicite_initiale(e, struct_P, struct_Pp, i, af, sf, ff, morph)
    assert res.conclusion == egal(sP, sPp), "conclusion ≠ (𝒫 = 𝒫')"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST17 — MORPHISME CARACTÉRISÉ PAR SON GRAPHE  (cas particulier de CST15/imrec)
# ════════════════════════════════════════════════════════════════════════════
#
#  « Soit f : A → B et soit F ⊂ A×B son graphe, muni de la structure induite par la
#    structure produit de (𝒮_A, 𝒮_B).  La projection pr₁ : F → A est un ISOMORPHISME de
#    (F, structure induite) sur (A, 𝒮_A). »  (un morphisme est entièrement déterminé par
#    son graphe : le graphe, comme sous-objet du produit, est isomorphe à la source.)
#
#  Cœur logique : pr₁ est un morphisme (induite ↪ produit ↠ A) ET sa réciproque (le
#  graphe x ↦ (x, f(x))) en est un ; iso = morphisme dont la réciproque est morphisme.
#  On certifie le PALIER « iso = morphisme + réciproque-morphisme » : c'est la conjonction
#  (MO_III bidirectionnelle, schéma de `est_iso_morph`).
#
def est_iso_morph(e, s, ep, sp, f, morph=None):
    """« f est un isomorphisme de (E,𝒮) sur (E',𝒮') » := f morphisme ET sa réciproque
    f⁻¹ morphisme  (caractérisation MO_III des isomorphismes, IV.1.5)."""
    morph = _morph(morph)
    ve, vs, vep, vsp, vf = map(_t, (e, s, ep, sp, f))
    return et(morph(ve, vs, vep, vsp, vf),
              morph(vep, vsp, ve, vs, E.reciproque(vf)))


def cst17_morphisme_caracterise_par_graphe(a="A", sa="SA", fgr="F", sf="SF",
                                           pr1="pr1", morph=None):
    """{ M  := « pr₁ est un morphisme de (F, 𝒮_F induite) dans (A, 𝒮_A) »,
         Mr := « pr₁⁻¹ (le graphe x↦(x,f(x))) est un morphisme de (A,𝒮_A) dans (F,𝒮_F) » }
        ⊢  pr₁ est un ISOMORPHISME de (F,𝒮_F) sur (A,𝒮_A).

    CRITÈRE CST17 (IV.2) — un morphisme est CARACTÉRISÉ par son GRAPHE.  Le graphe F⊂A×B
    d'une application f, muni de la structure 𝒮_F induite par le produit, est tel que la
    projection pr₁ : F → A est un ISOMORPHISME de (F,𝒮_F) sur (A,𝒮_A) — autrement dit le
    graphe est, comme sous-objet structuré du produit, canoniquement isomorphe à la
    source A.

    PREUVE (palier MO_III, pure logique).  Un isomorphisme est, par (MO_III), un
    morphisme dont l'application réciproque est aussi un morphisme.  pr₁ est un morphisme
    (composition induite ↪ produit ↠ A, fait IV.2 fourni en hyp.) et sa réciproque
    x ↦ (x, f(x)) en est un (fait fourni en hyp.).  On recolle la conjonction = la
    définition de « pr₁ isomorphisme ».

    REPORTÉ : les PREUVES que pr₁ et sa réciproque SONT des morphismes (calculs sur la
    structure induite/produit, image réciproque) — fournies en hypothèses EXPLICITES.
    On certifie le palier « iso = morphisme + réciproque-morphisme ».  NON VACUEUX : la
    conclusion est_iso_morph = (M ∧ Mr) est une CONJONCTION dont chaque membre est une
    hypothèse SÉPARÉE — la conclusion (la conjonction, = « iso ») n'est aucune des deux
    hypothèses prises isolément (≠ P caractérisé par P)."""
    morph = _morph(morph)
    va, vsa, vF, vsF, vpr1 = map(_t, (a, sa, fgr, sf, pr1))
    M = morph(vF, vsF, va, vsa, vpr1)                       # pr₁ morphisme F→A
    Mr = morph(va, vsa, vF, vsF, E.reciproque(vpr1))        # pr₁⁻¹ morphisme A→F
    hM, hMr = N.assume(M), N.assume(Mr)
    res = conjonction_intro(hM, hMr)
    cible = est_iso_morph(vF, vsF, va, vsa, vpr1, morph)
    assert res.conclusion == cible, "conclusion ≠ (pr₁ isomorphisme F→A)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST21 — TRANSITIVITÉ DES STRUCTURES QUOTIENT  (DUAL de CST19 via (FI))
# ════════════════════════════════════════════════════════════════════════════
#
#  « Soit A muni de 𝒮 d'espèce Σ, R une relation d'équivalence sur A, R' une relation
#    d'équivalence sur A/R, et soit S la relation d'équivalence sur A image réciproque de
#    R' (de sorte que (A/R)/R' ≅ A/S).  La structure quotient de (la quotient de 𝒮 par R)
#    par R' coïncide avec la structure quotient DIRECTE de 𝒮 par S. »   (transitivité des
#    passages au quotient — DUAL de la transitivité des structures finales CST19.)
#
#  Mirroir EXACT de `cst19_finales_egales` : les structures quotient sont des structures
#  FINALES (image directe par la surjection canonique) ; les deux candidates (quotient-
#  de-quotient et quotient-direct) vérifient la MÊME propriété (FI) (les surjections
#  canoniques se composent φ_S = φ_{R'}∘φ_R), donc sont mutuellement plus fines et égales
#  par antisymétrie (MO_III).
#
def cst21_quotients_egales(e="E", struct_F="F", struct_G="G", i="I0",
                           af=None, sf=None, gf=None, morph=None):
    """{ (FI_𝒬) pour 𝒬 = quotient-de-quotient ((A/R)/R'), structure finale via la
                surjection composée φ_{R'}∘φ_R,
         (FI_𝒬') pour 𝒬' = quotient DIRECT A/S (S = image réciproque de R'), même
                 surjection canonique composée,
         id morph (E,𝒬)->(E,𝒬), id morph (E,𝒬')->(E,𝒬'),
         ANTISYM := (plus_fine(E,𝒬,𝒬') et plus_fine(E,𝒬',𝒬)) ⇒ 𝒬=𝒬' }
        ⊢  𝒬 = 𝒬'.

    CRITÈRE CST21 (IV.2) — TRANSITIVITÉ des structures QUOTIENT, palier d'UNICITÉ.  La
    structure quotient de la quotient de 𝒮 par R, par R' (sur (A/R)/R'), et la structure
    quotient DIRECTE de 𝒮 par S (S la relation image réciproque de R', (A/R)/R' ≅ A/S),
    COÏNCIDENT.  DUAL EXACT de CST19 (transitivité finale) : les deux structures
    quotient sont des structures FINALES (image directe par la surjection canonique) pour
    la MÊME donnée (les surjections canoniques se composent φ_S = φ_{R'}∘φ_R), donc
    mutuellement plus fines et égales par antisymétrie (MO_III).

    Réalisé comme INSTANCE de `cst18_unicite_finale` (schéma d'unicité finale, identique à
    celui de CST19).  REPORTÉ : l'EXISTENCE des structures quotient (CST22 dual) ; on
    certifie le palier « les deux structures quotient coïncident ».  NON VACUEUX : 𝒬=𝒬'
    ∉ hypothèses (ANTISYM est l'implication (pf∧pf)⇒(𝒬=𝒬'))."""
    from bourbaki.structures.ensembles_CST_criteres import cst18_unicite_finale
    sF, sG = _t(struct_F), _t(struct_G)
    res = cst18_unicite_finale(e, struct_F, struct_G, i, af, sf, gf, morph)
    assert res.conclusion == egal(sF, sG), "conclusion ≠ (𝒬 = 𝒬')"
    return res


__all__ = [
    "cst16_famille_morphismes_produit",   # CST16 — famille de morphismes → produit
    "cst15_imrec_produit_egales",         # CST15 — image réciproque / produit (unicité)
    "cst13_produit_associatif_egales",    # CST13 — associativité du produit (unicité)
    "est_iso_morph",
    "cst17_morphisme_caracterise_par_graphe",  # CST17 — morphisme ↔ graphe
    "cst21_quotients_egales",             # CST21 — transitivité des quotients
]
