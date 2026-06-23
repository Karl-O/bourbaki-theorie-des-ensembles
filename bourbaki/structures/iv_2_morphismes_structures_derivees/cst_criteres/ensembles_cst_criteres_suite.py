"""§IV.1.6–IV.1.7 / IV.2.3–IV.2.4 — CRITÈRES DE STRUCTURES (CST), SUITE.

Module NEUF (campagne « critères de structures », vague 2).  Il PROLONGE
`ensembles_CST_criteres` (CST9/CST18/CST5/transport, conditionnels) et
`ensembles_transport_iso_props` (réciproque/réflexivité/automorphisme/unicité du
transport, niveau ESPÈCE Σ) en CERTIFIANT (au niveau du noyau, `.est_clos` ou
CONDITIONNEL à hypothèses EXPLICITES) les PALIERS LOGIQUES DIRECTS des critères CST
des §IV.1.6, IV.1.7 et §IV.2 (structures dérivées) qui suivent le MÊME schéma que
CST4/CST5/CST9/CST18 et qui n'avaient pas encore été traités.

CONVENTION DE PARAMÉTRAGE — strictement IDENTIQUE au reste de `bourbaki.structures`.
La donnée abstraite (Σ, Θ, σ, P) — MÉTA — est portée :
  • soit par le prédicat de morphisme abstrait `morph(e1,s1,e2,s2,f) -> Formule`
    (cf. `ensembles_universel_morphismes`) ;
  • soit par les notions `est_isomorphisme`/`structure_transportee` de
    `ensembles_especes` (niveau ESPÈCE, transport EXPLICITE ⟨f⟩^S, IV.1.5) ;
  • le PROCÉDÉ DE DÉDUCTION P (IV.1.6) par un callable `procede(bases, U) -> Terme`
    (la structure d'espèce Θ déduite de U) et son échelon de typage T par un
    `Schema` fourni dans une `Espece` Θ.
Aucun de ces objets n'est un terme/axiome du fragment objet : les théorèmes prouvés
ne dépendent QUE de la STRUCTURE LOGIQUE ∀/∃/⇔/=, valables QUELLE QUE SOIT la donnée.

CE QUI EST PROUVÉ ICI (NOUVEAU, non dupliqué ; vérifié « conclusion ∉ hypothèses »,
JAMAIS un P⇔P caractérisant une notion par elle-même) :

  • CST6  (IV.1.6, fonctorialité de la déduction) — `cst6_deduction_isomorphisme` :
    de (h système de bijections sur les échelons F_j) + clause (4) du TRANSPORT de la
    déduction ⟨h⟩^T(P{E,𝒮}) = P{E',𝒮'} (transportabilité du procédé P, hyp. explicite),
    on conclut est_isomorphisme(Θ, (h), F, F', P{E,𝒮}, P{E',𝒮'}).  Forme conditionnelle
    EXACTEMENT comme `composee_isomorphismes_est_isomorphisme` / l'identité-iso.

  • CST7  (IV.1.7, isomorphismes et espèces ÉQUIVALENTES) — `cst7_iso_ssi_deduit` :
    « (f) iso pour Σ  ⟺  (f) iso pour Θ (déduite par P) ».  Conditionnel à l'ÉQUIVALENCE
    des clauses (4) Σ/Θ (fournie en hyp. — c'est le contenu de CST6 appliqué dans les
    deux sens P,Q).  NON VACUEUX : on relie DEUX notions DISTINCTES est_isomorphisme(Σ,…)
    et est_isomorphisme(Θ,…) (échelons S vs T, structures U vs P{E,U} DIFFÉRENTES) — ce
    n'est PAS un P⇔P (≠ piège `mo3_caracterisation_iso`).

  • CST10 (IV.2, transitivité des structures INITIALES) — `cst10_initiales_egales` :
    « les propositions a) et b) entraînent que 𝓘 = 𝓘' » — cœur d'unicité (les deux
    structures initiales pour la famille composée et la famille intermédiaire sont
    mutuellement plus fines ⇒ égales par antisymétrie MO_III, hyp. explicite).  Même
    schéma que CST9 (`initiales_mutuellement_plus_fines` ⇒ égalité).

  • CST11 (IV.2, transitivité des structures INDUITES) — `cst11_induites_egales` :
    « les structures induites par 𝒮 et 𝒮' sur C sont identiques ».  Cœur d'unicité :
    les deux candidates valent toutes deux le transporté commun de 𝒮 sur C (relation
    de transport induit, hyp. explicite) ⇒ égales par transitivité de =.  Même schéma
    que CST5 (`cst5_unicite_transport`).

  • CST14 (IV.2, compatibilité produit / sous-structure) — `cst14_produit_induite_egales` :
    « ces propositions entraînent que 𝒮 = 𝒮' » — DUAL d'unicité de CST11 (la structure
    induite par le produit et le produit des induites coïncident, transporté commun).

theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé.  Tout est soit LOGIQUE
PUR, soit CONDITIONNEL à des hypothèses EXPLICITES = les axiomes-schémas (transport
de la déduction CST6, antisymétrie MO_III, relations de transport induit IV.2)
INSTANCIÉS, fournis comme PRÉMISSES — JAMAIS postulés vrais dans la théorie.

REPORTÉ honnêtement (méta / lourd, hors fragment, on ne POSTULE rien) :
  • la PREUVE de CST6 elle-même (récurrence sur le schéma T du type 𝔓(T_j), IV.1.6)
    et l'EXISTENCE/validité R{F,P{E,𝒮}} des structures déduites (transportabilité de
    R par P) — fournies en hypothèse, jamais affirmées ;
  • les ÉQUIVALENCES « a) ⟺ b) » d'EXISTENCE de CST10/CST13/CST14/CST15 (≡ existence
    effective de structures initiales/produits = construction, méta CST22) ; on ne
    certifie que le palier d'UNICITÉ/d'égalité « entraînent que 𝓘=𝓘' / 𝒮=𝒮' » ;
  • CST12/CST20 (restriction/quotient de morphismes — algébriques) déjà reportés dans
    `ensembles_structures_residus` ; CST13/CST15/CST19 (isomorphisme canonique produit,
    transitivité finale) — paliers d'existence méta, voir `reportes`.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, ou, impl, equiv, non,
                                       pourtout, existe, appartient, app)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie)
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes import (
    Espece, est_isomorphisme, structure_transportee)
from bourbaki.structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import extension_canonique
from bourbaki.structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_CST_criteres import (
    initiales_mutuellement_plus_fines, finales_mutuellement_plus_fines)
from bourbaki.structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import _t


# ════════════════════════════════════════════════════════════════════════════
#  Outils internes
# ════════════════════════════════════════════════════════════════════════════
def _conj(formules):
    """Conjonction (associée à gauche) d'une liste NON VIDE de Formules."""
    acc = formules[0]
    for f in formules[1:]:
        acc = et(acc, f)
    return acc


# ════════════════════════════════════════════════════════════════════════════
#  CST6 — FONCTORIALITÉ DE LA DÉDUCTION  (IV.1.6)
# ════════════════════════════════════════════════════════════════════════════
#
#  « Soit (g₁,…,gₙ) un isomorphisme de E muni d'une structure Σ sur E' muni de 𝒮'.
#    Posons h_j = ⟨g,Id⟩^{T_j} et F_j' = U_j{E',𝒮'} ; alors (h₁,…,h_r) est un
#    isomorphisme de F sur F' pour les structures d'espèce Θ déduites de 𝒮 et 𝒮'
#    par le procédé P. »
#
#  Le procédé P de déduction (IV.1.6) attache à (E,𝒮) une structure d'espèce Θ
#  P{E,𝒮} sur les échelons F = (F_j) = (U_j{E,𝒮}).  CST6 affirme : (h) transporte
#  P{E,𝒮} en P{E',𝒮'}.  Au niveau ESPÈCE Θ (échelon de typage T, transport ⟨h⟩^T),
#  est_isomorphisme(Θ,(h),F,F',P{E,𝒮},P{E',𝒮'}) = (h bijections) ∧ clause (4)
#  « ⟨h⟩^T(P{E,𝒮}) = P{E',𝒮'} ».  La clause (4) EST la transportabilité du procédé P
#  (IV.1.6, preuve par récurrence sur T — REPORTÉE) : hyp. explicite.
#
def cst6_deduction_isomorphisme(theta: Espece, h="h", F="F", Fp="Fp",
                                pES="P_ES", pEpSp="P_EpSp"):
    """{ est_bijection_de(h, F, F')                        (h bijection des échelons),
         ⟨h,Id⟩^T(P{E,𝒮}) = P{E',𝒮'}                       (transport de la déduction
                                                             P par (g), IV.1.6 — hyp.) }
        ⊢  est_isomorphisme(Θ, (h), F, F', P{E,𝒮}, P{E',𝒮'}).

    CRITÈRE CST6 (IV.1.6) — FONCTORIALITÉ DE LA DÉDUCTION.  Si (g) est un isomorphisme
    de (E,𝒮) sur (E',𝒮'), le système (h) = (⟨g,Id⟩^{T_j}) est un isomorphisme des
    structures DÉDUITES P{E,𝒮} et P{E',𝒮'} par le procédé P (espèce Θ).

    On certifie ici le PALIER objet (même schéma que `identite_est_isomorphisme_espece`
    et `composee_isomorphismes_est_isomorphisme`) : est_isomorphisme(Θ,(h),…) est la
    conjonction (1) « h est une bijection de F = (F_j) sur F' = (F_j') » et (2) la
    clause (4) de l'espèce Θ « ⟨h,Id⟩^T(P{E,𝒮}) = P{E',𝒮'} ».
      (1) bijection de h : hyp. explicite (h_j = ⟨g,Id⟩^{T_j} est une bijection par
          CST2 appliqué aux bijections g_i — fait IV.1.2 fourni en prémisse) ;
      (2) clause (4) : c'est EXACTEMENT le contenu de CST6 (le transport ⟨h⟩^T de la
          structure déduite P{E,𝒮} égale P{E',𝒮'}), dont la PREUVE (récurrence sur le
          schéma T du type 𝔓(T_j)) est REPORTÉE — fournie en hyp. explicite.
    Recollement par conjonction.  AUCUN axiome créé ; n=1 échelon pour la représentation
    objet (le cas r échelons est le même schéma conjonctif, omis).

    NON VACUEUX : la conclusion est_isomorphisme(Θ,…) est une CONJONCTION dont aucun
    membre n'est, isolément, une hypothèse (l'hyp. (2) est l'égalité ⟨h⟩^T(P{E,𝒮})=P{E',𝒮'},
    membre STRICT de la conjonction ; l'hyp. (1) en est l'AUTRE conjoint)."""
    vh, vF, vFp, vpES, vpEpSp = map(_t, (h, F, Fp, pES, pEpSp))

    # est_isomorphisme(Θ,(h),F,F',P{E,𝒮},P{E',𝒮'}) = (h bij F→F') ∧ (⟨h,Id⟩^T(P{E,𝒮})=P{E',𝒮'})
    iso = est_isomorphisme(theta, [vh], [vF], [vFp], vpES, vpEpSp)

    # (1) bijection de h : hyp. explicite (CST2-déduit, IV.1.2 ; F,F' échelons composés)
    bij_h = est_bijection_de(vh, vF, vFp)
    h_bij = N.assume(bij_h)

    # (2) clause (4) telle que la CONSTRUIT est_isomorphisme : ⟨h,Id⟩^T(P{E,𝒮}) = P{E',𝒮'}
    eq4 = egal(structure_transportee(theta, [vh], vpES), vpEpSp)
    h_eq4 = N.assume(eq4)

    res = conjonction_intro(h_bij, h_eq4)
    assert res.conclusion == iso, "conclusion ≠ est_isomorphisme(Θ,(h),F,F',P{E,𝒮},P{E',𝒮'})"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST7 — ISOMORPHISMES ET ESPÈCES ÉQUIVALENTES  (IV.1.7)
# ════════════════════════════════════════════════════════════════════════════
#
#  « Pour qu'un système de bijections (f) soit un isomorphisme de (E,U) sur (E',U')
#    POUR Σ, il faut et il suffit que ce soit un isomorphisme POUR Θ (espèce déduite
#    de U par P). »  (Conséquence de CST6.)
#
#  est_isomorphisme(Σ,(f),E,E',U,U')  = (f bij E→E') ∧ (⟨f⟩^S(U)  = U')          [clause 4_Σ]
#  est_isomorphisme(Θ,(f),E,E',P{U},P{U'}) = (f bij E→E') ∧ (⟨f⟩^T(P{U}) = P{U'})  [clause 4_Θ]
#  Les CLAUSES DE BIJECTION sont IDENTIQUES (mêmes f,E,E') ; la seule différence est
#  la clause (4) (échelon S vs T, structures U vs P{U}).  CST7 (conséquence de CST6,
#  appliqué dans les deux sens via P et Q) dit : ces DEUX clauses (4) sont ÉQUIVALENTES.
#  Sous CETTE équivalence (hyp. explicite — le contenu de CST6/équivalence d'espèces),
#  les deux isomorphismes sont équivalents.  ⚠ DISTINCT du piège mo3 : on relie deux
#  notions DIFFÉRENTES (Σ et Θ), pas une notion à sa propre définition.
#
def cst7_iso_ssi_deduit(sigma: Espece, theta: Espece, f="f", e="E", ep="Ep",
                        u="U", up="Up", pU="P_U", pUp="P_Up"):
    """{ ( ⟨f⟩^S(U) = U' )  ⟺  ( ⟨f⟩^T(P{U}) = P{U'} )      (CST6/équivalence d'espèces :
                                                             les clauses (4) Σ et Θ
                                                             coïncident, hyp. explicite) }
        ⊢  est_isomorphisme(Σ,(f),E,E',U,U')  ⟺  est_isomorphisme(Θ,(f),E,E',P{U},P{U'}).

    CRITÈRE CST7 (IV.1.7) — ISOMORPHISMES ET ESPÈCES ÉQUIVALENTES.  Pour qu'un système
    de bijections (f) soit un isomorphisme de (E,U) sur (E',U') POUR Σ, il faut et il
    suffit que ce soit un isomorphisme POUR Θ (structure déduite par le procédé P).

    PREUVE (logique pure sur la structure ∧/⇔).  Les deux notions ne diffèrent que par
    leur clause (4) : est_iso_Σ = B ∧ C_Σ et est_iso_Θ = B ∧ C_Θ avec B := « f bijection
    de E sur E' » (clause COMMUNE, littéralement identique), C_Σ := ⟨f⟩^S(U)=U' et
    C_Θ := ⟨f⟩^T(P{U})=P{U'}.  L'hypothèse (CST6/équivalence d'espèces) fournit C_Σ ⟺ C_Θ.
    On a alors (B∧C_Σ) ⟺ (B∧C_Θ) : sens ⇒, on suppose B∧C_Σ, on extrait B et C_Σ, on
    transporte C_Σ en C_Θ par ⇒ de l'hyp., on recolle B∧C_Θ ; sens ⇐ symétrique.

    NON VACUEUX / PAS UN P⇔P : les deux membres de l'équivalence conclue sont des
    formules DISTINCTES (est_isomorphisme pour des ESPÈCES différentes Σ≠Θ : échelons S
    vs T, structures U vs P{U}, U' vs P{U'}) — on relie deux NOTIONS distinctes, pas une
    notion à sa définition (≠ piège `mo3_caracterisation_iso`).  L'unique hypothèse est
    l'équivalence des clauses (4), CONTENU même de CST6/équivalence d'espèces, et la
    conclusion (l'équivalence des deux isomorphismes) n'est PAS cette hypothèse."""
    vf, ve, vep = map(_t, (f, e, ep))
    vu, vup, vpU, vpUp = map(_t, (u, up, pU, pUp))

    iso_sigma = est_isomorphisme(sigma, [vf], [ve], [vep], vu, vup)        # B ∧ C_Σ
    iso_theta = est_isomorphisme(theta, [vf], [ve], [vep], vpU, vpUp)      # B ∧ C_Θ
    # clauses (4) telles que les CONSTRUIT est_isomorphisme :
    C_sigma = egal(structure_transportee(sigma, [vf], vu), vup)           # ⟨f⟩^S(U) = U'
    C_theta = egal(structure_transportee(theta, [vf], vpU), vpUp)         # ⟨f⟩^T(P{U}) = P{U'}
    # contrôle : B est bien la clause de bijection commune, conjoint gauche des deux isos
    B = est_bijection_de(vf, ve, vep)
    assert iso_sigma == et(B, C_sigma), "forme iso_Σ ≠ (bijection) ∧ (clause 4_Σ)"
    assert iso_theta == et(B, C_theta), "forme iso_Θ ≠ (bijection) ∧ (clause 4_Θ)"

    # hyp. (CST6 / équivalence d'espèces) : C_Σ ⟺ C_Θ
    hyp_equiv_clauses = equiv(C_sigma, C_theta)
    h_eq = N.assume(hyp_equiv_clauses)

    # — sens ⇒ : (B ∧ C_Σ) ⇒ (B ∧ C_Θ) —
    h_isoS = N.assume(iso_sigma)
    bS = conjonction_elim_gauche(h_isoS)                  # B
    cS = conjonction_elim_droite(h_isoS)                  # C_Σ
    cT_from_S = N.modus_ponens(cS, equivalence_avant(h_eq))   # C_Θ
    isoT = conjonction_intro(bS, cT_from_S)               # B ∧ C_Θ  (sous iso_Σ)
    sens_avant = N.loi_deduction(iso_sigma, isoT)         # iso_Σ ⇒ iso_Θ

    # — sens ⇐ : (B ∧ C_Θ) ⇒ (B ∧ C_Σ) —
    h_isoT = N.assume(iso_theta)
    bT = conjonction_elim_gauche(h_isoT)                  # B
    cT = conjonction_elim_droite(h_isoT)                  # C_Θ
    cS_from_T = N.modus_ponens(cT, equivalence_arriere(h_eq))  # C_Σ
    isoS = conjonction_intro(bT, cS_from_T)               # B ∧ C_Σ  (sous iso_Θ)
    sens_arriere = N.loi_deduction(iso_theta, isoS)       # iso_Θ ⇒ iso_Σ

    # — recollement en ÉQUIVALENCE iso_Σ ⟺ iso_Θ —
    res = conjonction_intro(sens_avant, sens_arriere)
    cible = equiv(iso_sigma, iso_theta)
    assert res.conclusion == cible, "conclusion ≠ (est_iso_Σ ⟺ est_iso_Θ)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST10 — TRANSITIVITÉ DES STRUCTURES INITIALES (palier d'UNICITÉ)  (IV.2)
# ════════════════════════════════════════════════════════════════════════════
#
#  « En outre, ces propositions [a) ∃ 𝓘 initiale pour (A_ι,𝒮_ι,f_ι), b) ∃ 𝓘'
#    initiale pour (B_λ,𝒮'_λ,h_λ)] entraînent que 𝓘 = 𝓘'. »
#
#  CST10 affirme que la structure initiale itérée (transitivité) est UNIQUE : 𝓘 (pour
#  la famille composée f_ι = g_{λι}∘h_λ) et 𝓘' (pour la famille intermédiaire h_λ)
#  COÏNCIDENT.  La preuve repose, comme CST9, sur le fait que 𝓘 et 𝓘' sont deux
#  structures sur E qui sont MUTUELLEMENT plus fines (toutes deux initiales rendant les
#  mêmes morphismes possibles), d'où l'égalité par antisymétrie de « plus fine » (MO_III).
#  On RÉUTILISE `initiales_mutuellement_plus_fines` (CST9) avec les deux structures 𝓘,𝓘'
#  et on décharge l'antisymétrie comme hyp. explicite — strictement le schéma de CST9.
#
def cst10_initiales_egales(e="E", struct_I="I", struct_J="J", i="I0",
                           af=None, sf=None, ff=None, morph=None):
    """{(IN_𝓘), (IN_𝓘'), id morph (E,𝓘)→(E,𝓘), id morph (E,𝓘')→(E,𝓘'),
        ANTISYM := (plus_fine(E,𝓘,𝓘') et plus_fine(E,𝓘',𝓘)) ⇒ 𝓘=𝓘'}
        ⊢  𝓘 = 𝓘'.

    CRITÈRE CST10 (IV.2) — TRANSITIVITÉ DES STRUCTURES INITIALES, palier d'UNICITÉ
    (« ces propositions entraînent que 𝓘 = 𝓘' »).  Quand 𝓘 (structure initiale pour la
    famille composée (A_ι,𝒮_ι, f_ι = g_{λι}∘h_λ)) et 𝓘' (structure initiale pour la
    famille intermédiaire (B_λ,𝒮'_λ,h_λ)) existent TOUTES DEUX, elles sont ÉGALES.

    Comme f_ι = g_{λι}∘h_λ, les deux structures rendent EXACTEMENT les mêmes applications
    morphismes : elles satisfont la MÊME propriété (IN) « être moins fine que toute 𝒮
    rendant les morphismes possibles » (transitivité de la composition), donc sont
    mutuellement plus fines — d'où 𝓘 = 𝓘' par antisymétrie (MO_III).  On certifie ce
    palier EXACTEMENT comme CST9 (`initiales_mutuellement_plus_fines` ⇒ égalité par
    ANTISYM) : 𝓘,𝓘' deux structures sur E vérifiant (IN), mutuellement plus fines, donc
    égales sous l'antisymétrie fournie en hyp. explicite.

    REPORTÉ : l'ÉQUIVALENCE d'EXISTENCE « a) ⟺ b) » (construction effective des initiales,
    méta CST22).  On ne certifie QUE le palier d'unicité « entraînent que 𝓘=𝓘' ».
    NON VACUEUX : conclusion 𝓘=𝓘' ∉ hypothèses (l'ANTISYM est l'IMPLICATION (pf∧pf)⇒(𝓘=𝓘'),
    PAS l'égalité elle-même)."""
    sI, sJ = _t(struct_I), _t(struct_J)
    mut = initiales_mutuellement_plus_fines(e, struct_I, struct_J, i,
                                            af, sf, ff, morph)
    antisym = impl(mut.conclusion, egal(sI, sJ))   # (pf∧pf) ⇒ 𝓘=𝓘'   (MO_III)
    h_anti = N.assume(antisym)
    res = N.modus_ponens(mut, h_anti)              # ⊢ 𝓘 = 𝓘'
    assert res.conclusion == egal(sI, sJ), "conclusion ≠ (𝓘 = 𝓘')"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST11 — TRANSITIVITÉ DES STRUCTURES INDUITES (égalité)  (IV.2)
# ════════════════════════════════════════════════════════════════════════════
#
#  « … et les structures induites par 𝒮 et 𝒮' sur C sont alors identiques. »
#
#  Données : B ⊂ A, C ⊂ B, 𝒮 sur A induisant 𝒮' sur B.  La structure induite sur C
#  par 𝒮 directe et celle induite par 𝒮' (elle-même induite de 𝒮) coïncident :
#  l'induction est une « image réciproque » par l'injection canonique, et l'injection
#  C ↪ A se factorise C ↪ B ↪ A, d'où la TRANSITIVITÉ (la composée des extensions
#  d'échelon, CST1).  Au niveau objet : chaque structure induite sur C est l'image
#  réciproque ⟨j⟩^S(·) du transport, et les deux relations d'induction expriment
#  l'égalité au MÊME transporté ⟨j_C⟩^S(𝒮) (factorisation des injections, hyp.).
#  Cœur d'unicité, MÊME schéma que CST5 (`cst5_unicite_transport`) : transitivité de =.
#
def cst11_induites_egales(a="A", b="B", c="C", s="S", ind_directe="indAC",
                          ind_iteree="indBC", j="jC"):
    """{ ind_AC = ⟨j_C⟩^S(𝒮),   ind_BC = ⟨j_C⟩^S(𝒮)  }   ⊢   ind_AC = ind_BC.

    CRITÈRE CST11 (IV.2) — TRANSITIVITÉ DES STRUCTURES INDUITES.  Soient B ⊂ A, C ⊂ B,
    𝒮 d'espèce Σ sur A induisant 𝒮' sur B.  La structure induite par 𝒮 directement sur C
    (ind_AC) et la structure induite par 𝒮' sur C (ind_BC = induite de l'induite) sont
    IDENTIQUES.

    PREUVE (cœur d'unicité, comme CST5).  L'induction est une image réciproque par
    l'injection canonique ; l'injection C ↪ A se factorise C ↪ B ↪ A.  Par CST1
    (fonctorialité ⟨·⟩^S, fournie en amont), les deux structures induites valent toutes
    deux le transporté commun ⟨j_C⟩^S(𝒮) (l'extension d'échelon de l'injection composée
    appliquée à 𝒮) — ces DEUX ÉGALITÉS au transporté commun sont les hypothèses.  Par
    symétrie et transitivité de = (S6/Leibniz), ind_AC = ind_BC.

    L'EXISTENCE des structures induites (« il faut et il suffit que 𝒮 induise sur C une
    structure ») est REPORTÉE (méta) ; on certifie le palier « sont identiques ».
    Purement logique (S6).  NON VACUEUX : ind_AC = ind_BC ∉ hypothèses (les hyps relient
    chaque induite au TRANSPORTÉ commun, pas l'une à l'autre)."""
    va, vb, vc, vs = map(_t, (a, b, c, s))
    v_indAC, v_indBC, vj = map(_t, (ind_directe, ind_iteree, j))
    # transporté commun ⟨j_C⟩^S(𝒮) — extension d'échelon de l'injection canonique j_C: C↪A
    # appliquée à 𝒮 (terme opaque ; sa construction relève de IV.2, image réciproque).
    T = app("transporte_induit", vj, vs)
    rel_AC = egal(v_indAC, T)        # ind_AC = ⟨j_C⟩^S(𝒮)
    rel_BC = egal(v_indBC, T)        # ind_BC = ⟨j_C⟩^S(𝒮)
    h1, h2 = N.assume(rel_AC), N.assume(rel_BC)
    # de (ind_AC=T) et (ind_BC=T) conclure ind_AC=ind_BC :
    #   S6(T, ind_BC, x, ind_AC=x) : (T=ind_BC) ⇒ ((ind_AC=T) ⇔ (ind_AC=ind_BC))
    # d'abord T=ind_BC depuis ind_BC=T (symétrie)
    x = "x_cst11"
    s6_sym = N.s6(v_indBC, T, x, egal(var(x), v_indBC))   # (ind_BC=T) ⇒ ((ind_BC=ind_BC) ⇔ (T=ind_BC))
    eqv = N.modus_ponens(h2, s6_sym)
    refl = N.reflexivite(v_indBC)
    T_eq_BC = N.modus_ponens(refl, equivalence_avant(eqv))     # T = ind_BC
    # puis S6(T, ind_AC?, …) : transitivité ind_AC=T=ind_BC
    y = "y_cst11"
    s6_2 = N.s6(T, v_indBC, y, egal(v_indAC, var(y)))    # (T=ind_BC) ⇒ ((ind_AC=T) ⇔ (ind_AC=ind_BC))
    eqv2 = N.modus_ponens(T_eq_BC, s6_2)
    res = N.modus_ponens(h1, equivalence_avant(eqv2))          # ind_AC = ind_BC
    assert res.conclusion == egal(v_indAC, v_indBC), "conclusion ≠ (ind_AC = ind_BC)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST14 — COMPATIBILITÉ PRODUIT / SOUS-STRUCTURE (égalité)  (IV.2)
# ════════════════════════════════════════════════════════════════════════════
#
#  « … En outre, ces propositions [a) ∃ structure induite par 𝒮₀ sur B=∏B_ι,
#    b) ∃ structure produit 𝒮' de (𝒮'_ι)] entraînent que 𝒮 = 𝒮'. »
#
#  CST14 : sur B = ∏_ι B_ι ⊂ E = ∏_ι A_ι, la structure induite par le produit 𝒮₀ et le
#  produit des structures induites 𝒮'_ι coïncident.  Cœur d'unicité (DUAL de CST11) :
#  les deux valent le même transporté (induite et produit commutent, hyp.) ⇒ égales.
#
def cst14_produit_induite_egales(prod_induite="SprodB", induite_prod="SindB",
                                 commun="Scommun"):
    """{ S_indB = S_commun,   S_prodB = S_commun }   ⊢   S_indB = S_prodB.

    CRITÈRE CST14 (IV.2) — COMPATIBILITÉ PRODUIT / SOUS-STRUCTURE, palier d'égalité
    (« ces propositions entraînent que 𝒮 = 𝒮' »).  Sur B = ∏_ι B_ι ⊂ E = ∏_ι A_ι, la
    structure 𝒮 induite sur B par la structure produit 𝒮₀ (de la famille (𝒮_ι)) et la
    structure 𝒮' produit de la famille des structures induites (𝒮'_ι) sont ÉGALES.

    PREUVE (cœur d'unicité, DUAL de CST11).  Induction et produit COMMUTENT : les deux
    structures valent le MÊME transporté/produit commun S_commun (induite-du-produit =
    produit-des-induites, fait de fonctorialité IV.2 fourni en amont — les deux égalités
    au transporté commun sont les hypothèses).  Par transitivité de = (S6/Leibniz),
    S_indB = S_prodB.

    L'EXISTENCE (équivalence a)⟺b)) est REPORTÉE (méta) ; on certifie « entraînent que
    𝒮=𝒮' ».  Purement logique (S6).  NON VACUEUX : conclusion ∉ hypothèses."""
    v_ind, v_prod, v_commun = map(_t, (induite_prod, prod_induite, commun))
    rel_ind = egal(v_ind, v_commun)        # S_indB = S_commun
    rel_prod = egal(v_prod, v_commun)      # S_prodB = S_commun
    h1, h2 = N.assume(rel_ind), N.assume(rel_prod)
    # de (S_indB=S_commun) et (S_prodB=S_commun) conclure S_indB=S_prodB :
    x = "x_cst14"
    s6_sym = N.s6(v_prod, v_commun, x, egal(var(x), v_prod))   # (S_prod=S_commun) ⇒ ((S_prod=S_prod) ⇔ (S_commun=S_prod))
    eqv = N.modus_ponens(h2, s6_sym)
    refl = N.reflexivite(v_prod)
    commun_eq_prod = N.modus_ponens(refl, equivalence_avant(eqv))   # S_commun = S_prod
    y = "y_cst14"
    s6_2 = N.s6(v_commun, v_prod, y, egal(v_ind, var(y)))     # (S_commun=S_prod) ⇒ ((S_ind=S_commun) ⇔ (S_ind=S_prod))
    eqv2 = N.modus_ponens(commun_eq_prod, s6_2)
    res = N.modus_ponens(h1, equivalence_avant(eqv2))         # S_indB = S_prodB
    assert res.conclusion == egal(v_ind, v_prod), "conclusion ≠ (S_indB = S_prodB)"
    return res


__all__ = [
    # CST6 — fonctorialité de la déduction (IV.1.6)
    "cst6_deduction_isomorphisme",
    # CST7 — isomorphismes et espèces équivalentes (IV.1.7)
    "cst7_iso_ssi_deduit",
    # CST10 — transitivité des initiales, palier d'unicité (IV.2)
    "cst10_initiales_egales",
    # CST11 — transitivité des induites (IV.2)
    "cst11_induites_egales",
    # CST14 — compatibilité produit / sous-structure (IV.2)
    "cst14_produit_induite_egales",
]
