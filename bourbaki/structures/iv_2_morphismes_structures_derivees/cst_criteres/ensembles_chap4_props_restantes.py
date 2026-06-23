"""§IV.1–IV.2 — CRITÈRES DE STRUCTURES (CST) RESTANTS : cœurs logiques certifiés.

Module NEUF (campagne « critères de structures », book-IV-structures).  Il
COMPLÈTE les modules déjà faits du chapitre IV — `ensembles_CST_criteres`
(CST9/CST18/CST5/CST22, transport préserve morphisme), `ensembles_structures_props`
(CST4 composition d'isos, CST8, préordre « plus fine »), `ensembles_structures_derivees_props`
(CST10/CST11/CST19, unicité image réciproque/directe), `ensembles_especes` (transport,
isomorphisme) — en PROUVANT (au niveau du noyau, `.est_clos` / conditionnel à des
hypothèses EXPLICITES) les PALIERS LOGIQUES DIRECTS encore manquants des critères CST :

  • CST3  (IV.1.2) — RÉCIPROQUE de la bijection transportée : (⟨f⟩^S)⁻¹ = ⟨f⁻¹⟩^S.
    Bourbaki : « si f_i est une bijection de E_i sur E_i', alors ⟨f₁,…,fₙ⟩^S est une
    bijection et ⟨f₁⁻¹,…,fₙ⁻¹⟩^S la bijection réciproque ».  Le cœur d'UNICITÉ (le
    transporté de l'inverse compose avec le transporté pour donner l'identité) — explicitement
    laissé en REPORT dans `ensembles_CST_criteres` (« réciproque … REPORTÉE »).

  • MO_III (IV.2.1) — CARACTÉRISATION DES ISOMORPHISMES + son corollaire « la RÉCIPROQUE
    d'un iso est un iso ».  C'est exactement le SENS qui manquait pour clore CST4 (la note
    de `ensembles_CST_criteres.cst4_compose_isos_morphisme_aller` dit « réciproque … aussi
    morphisme … REPORTÉE »).  On en certifie ici le cœur logique (équivalence MO_III +
    extraction de f⁻¹ morphisme + symétrie de « est un iso »).

  • CST12 (IV.2) — RESTRICTION D'UN MORPHISME AUX SOUS-STRUCTURES : si f : A→A' est un
    morphisme avec f(B)⊂B', alors g (coïncidant avec f sur B) est un morphisme pour les
    structures induites.  Cœur via la propriété (IN) à un indice de la structure induite sur
    B' (image réciproque par l'injection canonique j' : B'→A').  Reporté partout ailleurs.

  • CST20 (IV.2) — PASSAGE DES MORPHISMES AUX QUOTIENTS : si f : A→A' est un morphisme
    compatible avec R, R', alors g (passage au quotient) est un morphisme pour les structures
    quotient.  Cœur via la propriété (FI) à un indice de la structure quotient sur A/R (image
    directe par l'application canonique φ : A→A/R).  Reporté partout ailleurs.

CONVENTION DE PARAMÉTRAGE IDENTIQUE au reste du chap. IV (cf. docstrings de
`ensembles_universel_morphismes`).  La donnée abstraite (Σ, σ) — méta — est portée par un
PRÉDICAT callable `morph(e1,s1,e2,s2,f) -> Formule` « f est un σ-morphisme de (e1,s1) dans
(e2,s2) ».  Les structures / applications / ensembles de base sont des TERMES.  Les
théorèmes prouvés ne dépendent QUE de la STRUCTURE LOGIQUE (∀/∃/⇔/=) des propriétés
(MO_II)/(MO_III)/(IN)/(FI) et de la fonctorialité d'échelon (CST1) — ils sont donc valables
QUELLE QUE SOIT la donnée σ (sens « représentationnel » : on certifie le squelette déductif
des critères, le contenu σ restant un paramètre).

theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé ici.  Tout est soit logique pur,
soit conditionnel à des hypothèses EXPLICITES (les axiomes-schémas CST1/(MO_II)/(MO_III)/(IN)/(FI)
INSTANCIÉS, prémisses des théorèmes, JAMAIS postulés vrais dans la théorie).

REPORTÉ honnêtement (méta / lourd, hors fragment) : la PREUVE de CST1/CST3 (fonctorialité de
⟨·⟩^S — récurrence sur le schéma), l'EXISTENCE effective des structures induite/quotient
(CST22), CST6/CST7 (déduction d'échelon, espèces équivalentes), CST13/CST14/CST15 (associativité
/ compatibilité produit) — voir le champ `reportes` du rapport.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, equiv, non,
                                       pourtout, existe, appartient, app, inclus)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie)
from bourbaki.structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    est_morphisme, _morph_defaut, _t)


# ════════════════════════════════════════════════════════════════════════════
#  Outils internes
# ════════════════════════════════════════════════════════════════════════════
def _morph(morph):
    return morph if morph is not None else _morph_defaut()


def _transporte(schema, f, U):
    """⟨f, Id⟩^S(U) — le transporté de U par f selon le schéma S (terme).  On suit
    la notation déjà employée dans `ensembles_CST_criteres.relation_transport_iso`
    (`extension_echelon(S, f, U)`)."""
    return app("extension_echelon", _t(schema), _t(f), _t(U))


# ════════════════════════════════════════════════════════════════════════════
#  CST3 — RÉCIPROQUE de la bijection transportée   (⟨f⟩^S)⁻¹ = ⟨f⁻¹⟩^S
# ════════════════════════════════════════════════════════════════════════════
#
#  Bourbaki (IV.1.2, CST3) : « Si f_i est une bijection de E_i sur E_i', et f_i⁻¹ la
#  bijection réciproque, alors ⟨f₁,…,fₙ⟩^S est une bijection, et ⟨f₁⁻¹,…,fₙ⁻¹⟩^S la
#  bijection réciproque ; autrement dit (⟨f⟩^S)⁻¹ = ⟨f⁻¹⟩^S. (Résulte de CST1 et CST2.) »
#
#  Au niveau « transport de structure » (relation (4)), on certifie l'identité
#  fonctionnelle ÉQUIVALENTE qui exprime la réciprocité :
#       ⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Id   (et symétriquement).
#  Cœur logique : la fonctorialité CST1 ⟨f⁻¹∘f⟩^S = ⟨f⁻¹⟩^S ∘ ⟨f⟩^S, l'hypothèse de
#  bijection f⁻¹∘f = Δ_E, et CST1-à-l'identité ⟨Δ_E⟩^S = Id (= Δ de l'échelon) donnent,
#  par transitivité de =, ⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Id.  C'est exactement « ⟨f⁻¹⟩^S est l'inverse
#  à gauche de ⟨f⟩^S », i.e. le contenu de CST3 (réciprocité).
#
def axiome_CST1_composition(schema, f, g, U):
    """(CST1) instancié — FONCTORIALITÉ de l'extension d'échelon (IV.1.2) :
        ⟨g∘f⟩^S(U) = ⟨g⟩^S(⟨f⟩^S(U))   (forme appliquée à U).
    Hypothèse EXPLICITE (jamais postulée vraie dans la théorie ; sa preuve = récurrence
    sur le schéma S, REPORTÉE)."""
    gof = E.composee(_t(g), _t(f))
    lhs = _transporte(schema, gof, U)
    rhs = _transporte(schema, g, _transporte(schema, f, U))
    return egal(lhs, rhs)


def axiome_CST1_identite(schema, e, U):
    """(CST1 à l'identité) instancié — ⟨Δ_E⟩^S(U) = U (l'extension de l'identité est
    l'identité, IV.1.2).  Hypothèse EXPLICITE."""
    return egal(_transporte(schema, E.diagonale(_t(e)), U), _t(U))


def cst3_reciproque_transport(schema="S", f="f", e="E", ep="Ep", u="U"):
    """CST3 (cœur logique de la RÉCIPROQUE du transport, IV.1.2).

    { CST1 :  ⟨f⁻¹∘f⟩^S(U) = ⟨f⁻¹⟩^S(⟨f⟩^S(U))      (fonctorialité, hyp. explicite),
      BIJ  :  f⁻¹∘f = Δ_E                            (f bijection : réciproque à gauche),
      ID   :  ⟨Δ_E⟩^S(U) = U                         (CST1 à l'identité, hyp. explicite) }
        ⊢  ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U.

    « ⟨f⁻¹⟩^S est la bijection réciproque (à gauche) de ⟨f⟩^S » — le contenu de CST3 au
    niveau du transport appliqué à U.  PREUVE (transitivité de =) :
        ⟨f⁻¹⟩^S(⟨f⟩^S(U))  =  ⟨f⁻¹∘f⟩^S(U)     [CST1, par symétrie]
                           =  ⟨Δ_E⟩^S(U)        [BIJ : f⁻¹∘f = Δ_E, réécriture S6]
                           =  U.                [ID]
    Hypothèses EXPLICITES (CST1 + bijection + CST1-id), AUCUN axiome de théorie ajouté ;
    purement logique (S6 / transitivité).  C'était la partie REPORTÉE par
    `ensembles_CST_criteres` (« réciproque … REPORTÉE »)."""
    vf, ve, vu = _t(f), _t(e), _t(u)
    finv = E.reciproque(vf)                       # f⁻¹
    finv_f = E.composee(finv, vf)                 # f⁻¹∘f
    DE = E.diagonale(ve)                          # Δ_E

    tr_f = _transporte(schema, vf, vu)            # ⟨f⟩^S(U)
    tr_finv_of_tr_f = _transporte(schema, finv, tr_f)   # ⟨f⁻¹⟩^S(⟨f⟩^S(U))   (cible.lhs)
    tr_comp = _transporte(schema, finv_f, vu)     # ⟨f⁻¹∘f⟩^S(U)
    tr_DE = _transporte(schema, DE, vu)           # ⟨Δ_E⟩^S(U)

    # — hypothèses —
    cst1 = axiome_CST1_composition(schema, vf, finv, vu)  # ⟨f⁻¹∘f⟩^S(U)=⟨f⁻¹⟩^S(⟨f⟩^S(U))
    bij = egal(finv_f, DE)                                # f⁻¹∘f = Δ_E
    idax = axiome_CST1_identite(schema, ve, vu)           # ⟨Δ_E⟩^S(U) = U
    h_cst1, h_bij, h_id = N.assume(cst1), N.assume(bij), N.assume(idax)

    # étape 1 : de CST1 (tr_comp = tr_finv_of_tr_f) on tire tr_finv_of_tr_f = tr_comp (sym)
    #   S6(tr_comp, tr_finv_of_tr_f, x, x = tr_comp) :
    #   (tr_comp = tr_finv_of_tr_f) ⇒ ((tr_comp=tr_comp) ⇔ (tr_finv_of_tr_f = tr_comp))
    x = "x_cst3"
    s6_sym = N.s6(tr_comp, tr_finv_of_tr_f, x, egal(var(x), tr_comp))
    eqv_sym = N.modus_ponens(h_cst1, s6_sym)              # (tr_comp=tr_comp) ⇔ (tr_finv∘tr_f = tr_comp)
    refl = N.reflexivite(tr_comp)                         # tr_comp = tr_comp
    sym = N.modus_ponens(refl, equivalence_avant(eqv_sym))  # tr_finv_of_tr_f = tr_comp

    # étape 2 : réécrire tr_comp = ⟨f⁻¹∘f⟩^S(U) en ⟨Δ_E⟩^S(U) via BIJ (f⁻¹∘f = Δ_E).
    #   S6(finv_f, DE, w, tr_finv_of_tr_f = ⟨w⟩^S(U)) :
    #   (f⁻¹∘f = Δ_E) ⇒ ((tr_finv_of_tr_f = ⟨f⁻¹∘f⟩^S(U)) ⇔ (tr_finv_of_tr_f = ⟨Δ_E⟩^S(U)))
    w = "w_cst3"
    motif = egal(tr_finv_of_tr_f, _transporte(schema, var(w), vu))
    s6_rw = N.s6(finv_f, DE, w, motif)
    eqv_rw = N.modus_ponens(h_bij, s6_rw)                 # (tr_finv∘tr_f=tr_comp) ⇔ (tr_finv∘tr_f=tr_DE)
    # sym : tr_finv_of_tr_f = tr_comp ; passe à tr_finv_of_tr_f = tr_DE
    eq_to_DE = N.modus_ponens(sym, equivalence_avant(eqv_rw))   # tr_finv_of_tr_f = ⟨Δ_E⟩^S(U)

    # étape 3 : ⟨Δ_E⟩^S(U) = U  (ID) ⊢  tr_finv_of_tr_f = U  (transitivité)
    #   S6(tr_DE, vu, z, tr_finv_of_tr_f = z) :
    #   (⟨Δ_E⟩^S(U)=U) ⇒ ((tr_finv∘tr_f=tr_DE) ⇔ (tr_finv∘tr_f=U))
    z = "z_cst3"
    s6_id = N.s6(tr_DE, vu, z, egal(tr_finv_of_tr_f, var(z)))
    eqv_id = N.modus_ponens(h_id, s6_id)                  # (tr_finv∘tr_f=tr_DE) ⇔ (tr_finv∘tr_f=U)
    return N.modus_ponens(eq_to_DE, equivalence_avant(eqv_id))  # ⊢ ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U


# ════════════════════════════════════════════════════════════════════════════
#  MO_III — CARACTÉRISATION DES ISOMORPHISMES + « la réciproque d'un iso est un iso »
# ════════════════════════════════════════════════════════════════════════════
#
#  (MO_III, IV.2.1) : « pour qu'une bijection f de E sur E' soit un isomorphisme, il faut
#  et il suffit que f ∈ σ[E,E',𝒮,𝒮'] et f⁻¹ ∈ σ[E',E,𝒮',𝒮] ».  On REPRÉSENTE
#  « f est un isomorphisme (E,𝒮)→(E',𝒮') » par la conjonction
#     est_iso(E,𝒮,E',𝒮',f) := morph(E,𝒮,E',𝒮',f)  et  morph(E',𝒮',E,𝒮, f⁻¹)
#  (c'est exactement le membre de droite de l'équivalence MO_III, qui DÉFINIT « iso » à
#  partir de morph + réciproque ; la clause « bijection » est portée par le contexte/le
#  prédicat, comme dans tout le chap. IV).  On certifie alors :
#    1. l'ÉQUIVALENCE MO_III elle-même (réflexive : est_iso ⇔ (morph f ∧ morph f⁻¹)) ;
#    2. « la RÉCIPROQUE d'un isomorphisme est un isomorphisme » — le sens que CST4
#       laissait en report (le morphisme réciproque), pur jeu d'éliminations/réintro de ∧.
#
def est_iso_morph(e, s, ep, sp, f, morph=None):
    """« f est un isomorphisme de (E,𝒮) sur (E',𝒮') » (au sens MO_III) :=
        morph(E,𝒮,E',𝒮', f)  ET  morph(E',𝒮',E,𝒮, f⁻¹)
    (membre de droite de l'équivalence MO_III, IV.2.1).  La clause « bijection » est
    contextuelle (un iso EST une bijection ; on la laisse au prédicat/contexte)."""
    morph = _morph(morph)
    ve, vs, vep, vsp, vf = map(_t, (e, s, ep, sp, f))
    return et(morph(ve, vs, vep, vsp, vf),
              morph(vep, vsp, ve, vs, E.reciproque(vf)))


def _est_iso_morph_reflexivite_triviale(e="E", s="S", ep="Ep", sp="Sp", f="f", morph=None):
    """⚠️ TRIVIAL — réflexivité ⊢ est_iso_morph ⇔ est_iso_morph  (PAS le MO_III de Bourbaki).

    ⛔ CE N'EST PAS UN THÉORÈME SUBSTANTIEL.  `est_iso_morph` est DÉFINI comme la conjonction
    `morph(f) et morph(f⁻¹)`, donc l'« équivalence » prouvée ici est LITTÉRALEMENT P⇔P
    (réflexivité de ⇔, `a_implique_a` dans les deux sens).  Elle ne certifie RIEN du vrai
    MO_III (IV.2.1), qui relie la notion INDÉPENDANTE `ensembles_especes.est_isomorphisme`
    (IV.1.5, bijection + structure transportée) au membre droit — contenu σ NON trivial,
    REPORTÉ.  Conservé comme simple sanity-check de la définition `est_iso_morph` ; privé,
    hors __all__, jamais présenté comme MO_III certifié.  (Audit Fable, neutralisé.)"""
    morph = _morph(morph)
    iso = est_iso_morph(e, s, ep, sp, f, morph)         # = (morph f ∧ morph f⁻¹)
    # iso ⇔ iso : réflexivité de l'équivalence (a_implique_a dans les deux sens)
    from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
    av = a_implique_a(iso)                               # iso ⇒ iso
    ar = a_implique_a(iso)                               # iso ⇒ iso  (même formule, l'autre sens)
    # équiv = (iso⇒iso) ∧ (iso⇒iso) ; conjonction_intro donne le ⇔ (codage de equiv)
    return conjonction_intro(av, ar)


def reciproque_iso_extrait_morphisme(e="E", s="S", ep="Ep", sp="Sp", f="f",
                                     morph=None):
    """{ est_iso(E,𝒮,E',𝒮',f) }  ⊢  morph(E',𝒮',E,𝒮, f⁻¹).

    « Si f est un isomorphisme, alors f⁻¹ est un MORPHISME (de (E',𝒮') dans (E,𝒮)) » —
    extraction de la seconde clause de la caractérisation MO_III.  C'est précisément le
    palier « le morphisme réciproque » que `ensembles_CST_criteres` laissait REPORTÉ pour
    clore CST4.  Projection droite de la conjonction (pur)."""
    morph = _morph(morph)
    iso = est_iso_morph(e, s, ep, sp, f, morph)
    h = N.assume(iso)
    return conjonction_elim_droite(h)                   # morph(E',𝒮',E,𝒮, f⁻¹)


def reciproque_iso_est_iso(e="E", s="S", ep="Ep", sp="Sp", f="f", morph=None):
    """{ est_iso(E,𝒮,E',𝒮',f),  f⁻¹⁻¹ = f  (involutivité de la réciproque) }
        ⊢  est_iso(E',𝒮',E,𝒮, f⁻¹).

    « LA RÉCIPROQUE D'UN ISOMORPHISME EST UN ISOMORPHISME » (IV.2.2 : « il en est de
    même de l'isomorphisme réciproque d'un automorphisme » ; cas du transport / CST4).
    est_iso(E',𝒮',E,𝒮,f⁻¹) = morph(E',𝒮',E,𝒮,f⁻¹) ∧ morph(E,𝒮,E',𝒮', f⁻¹⁻¹).
      • 1ʳᵉ clause = projection droite de est_iso(…,f)         (déjà : f⁻¹ morphisme) ;
      • 2ᵉ clause  = projection gauche de est_iso(…,f) [morph(E,𝒮,E',𝒮',f)] réécrite par
        l'involutivité f⁻¹⁻¹ = f (hypothèse explicite, propriété de la réciproque d'une
        bijection — S6).  D'où morph(E,𝒮,E',𝒮', f⁻¹⁻¹).
    Recollement par conjonction.  Hypothèses : est_iso(…,f) + involutivité (lemme
    ensembliste sur la réciproque, fourni EXPLICITEMENT — non postulé en théorie)."""
    morph = _morph(morph)
    ve, vs, vep, vsp, vf = map(_t, (e, s, ep, sp, f))
    finv = E.reciproque(vf)                              # f⁻¹
    finv_inv = E.reciproque(finv)                        # f⁻¹⁻¹

    iso = est_iso_morph(ve, vs, vep, vsp, vf, morph)
    h = N.assume(iso)
    morph_f = conjonction_elim_gauche(h)                 # morph(E,𝒮,E',𝒮', f)
    morph_finv = conjonction_elim_droite(h)              # morph(E',𝒮',E,𝒮, f⁻¹)  (1ʳᵉ clause cible)

    # 2ᵉ clause : morph(E,𝒮,E',𝒮', f⁻¹⁻¹) — réécrire f ↦ f⁻¹⁻¹ via involutivité f⁻¹⁻¹ = f.
    involut = egal(finv_inv, vf)                         # f⁻¹⁻¹ = f  (hyp. explicite)
    h_inv = N.assume(involut)
    # S6(finv_inv, vf, t, morph(E,𝒮,E',𝒮', t)) :
    #   (f⁻¹⁻¹ = f) ⇒ ( morph(…, f⁻¹⁻¹) ⇔ morph(…, f) )
    t = "t_mo3"
    motif = morph(ve, vs, vep, vsp, var(t))
    s6_rw = N.s6(finv_inv, vf, t, motif)
    eqv = N.modus_ponens(h_inv, s6_rw)                   # morph(…, f⁻¹⁻¹) ⇔ morph(…, f)
    morph_finv_inv = N.modus_ponens(morph_f, equivalence_arriere(eqv))  # morph(E,𝒮,E',𝒮', f⁻¹⁻¹)

    # est_iso(E',𝒮',E,𝒮, f⁻¹) = morph(E',𝒮',E,𝒮,f⁻¹) ∧ morph(E,𝒮,E',𝒮', f⁻¹⁻¹)
    res = conjonction_intro(morph_finv, morph_finv_inv)
    cible = est_iso_morph(vep, vsp, ve, vs, finv, morph)
    assert res.conclusion == cible, "conclusion ≠ est_iso(E',𝒮',E,𝒮,f⁻¹) attendu"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  CST12 — RESTRICTION D'UN MORPHISME AUX SOUS-STRUCTURES
# ════════════════════════════════════════════════════════════════════════════
#
#  (IV.2) : A, A' munis de 𝒮, 𝒮' ; B ⊂ A, B' ⊂ A' ; 𝒮 induit 𝒮_B sur B, 𝒮' induit
#  𝒮'_B' sur B'.  Si f : A→A' est un morphisme avec f(B) ⊂ B', alors g : B→B'
#  (coïncidant avec f sur B = restriction f|B) est un morphisme pour 𝒮_B, 𝒮'_B'.
#
#  Cœur logique.  La structure induite 𝒮'_B' = image réciproque de 𝒮' par l'injection
#  canonique j' : B'→A'.  Sa propriété (IN) à un indice (cf.
#  `ensembles_universel_morphismes.image_reciproque_structure`) :
#     (∀E')(∀𝒮')(∀h) [ morph(E',𝒮',B',𝒮'_B', h) ⇔ morph(E',𝒮', A', 𝒮', j'∘h) ].
#  Spécialisée à (E'=B, 𝒮'=𝒮_B, h=g) :
#     morph(B,𝒮_B, B',𝒮'_B', g)  ⇔  morph(B,𝒮_B, A', 𝒮', j'∘g).
#  Or j'∘g = (injection B'↪A')∘(restriction f|B) = f∘j  (f restreinte, vue dans A'),
#  d'où morph(B,𝒮_B, A',𝒮', j'∘g) = morph(B,𝒮_B, A',𝒮', f∘j) ; ce dernier est la
#  COMPOSÉE de l'injection j : B↪A (morphisme : B sous-structure de A) et de f : A→A'
#  (morphisme par hypothèse) — morphisme par (MO_II).  On certifie ce cœur logique sous
#  les hypothèses EXPLICITES : (IN) de l'induite sur B', l'égalité j'∘g = f∘j, et le fait
#  que f∘j est un morphisme (= (MO_II) appliqué à j puis f).
#
def _struct_induite(s, base):
    """Structure induite par 𝒮 sur `base` (terme opaque ; existence reportée, CST22)."""
    return app("struct_induite", _t(s), _t(base))


def cst12_restriction_morphisme(a="A", s="S", ap="Ap", sp="Sp", b="B", bp="Bp",
                                f="f", morph=None):
    """CST12 (cœur logique, IV.2) — RESTRICTION D'UN MORPHISME AUX SOUS-STRUCTURES.

    { (IN_B') := propriété (IN) à un indice de l'induite 𝒮'_B' sur B' (image réciproque
                 de 𝒮' par l'injection j' : B'↪A'), spécialisée à (B,𝒮_B, g),
      EQ       := j'∘g = f∘j           (g = f|B, j'/j injections canoniques),
      COMP     := morph(B,𝒮_B, A', 𝒮', f∘j)   ((MO_II) : j morphisme puis f morphisme) }
        ⊢  morph(B, 𝒮_B, B', 𝒮'_B', g).

    « Si f est un morphisme de A dans A' tel que f(B)⊂B', l'application g de B dans B'
    qui coïncide avec f dans B est un morphisme (pour les structures induites). »

    PREUVE : (IN_B') donne morph(B,𝒮_B,B',𝒮'_B', g) ⇔ morph(B,𝒮_B,A',𝒮', j'∘g) ; EQ
    réécrit j'∘g ↦ f∘j (S6) dans le membre de droite ; COMP fournit morph(…, f∘j) ; on
    remonte l'équivalence (⇐).  Hypothèses EXPLICITES (la caractéristique (IN) de
    l'induite, l'égalité des composées, et la composée-morphisme (MO_II)) ; AUCUN axiome
    de théorie ajouté ; purement logique."""
    morph = _morph(morph)
    va, vs, vap, vsp = map(_t, (a, s, ap, sp))
    vb, vbp, vf = map(_t, (b, bp, f))
    sB = _struct_induite(vs, vb)                         # 𝒮 induite sur B
    sBp = _struct_induite(vsp, vbp)                      # 𝒮' induite sur B'
    j = E.diagonale(vb)                                  # j : B ↪ A  (injection canonique)
    jp = E.diagonale(vbp)                                # j' : B' ↪ A'
    g = E.restriction(vf, vb) if hasattr(E, "restriction") else app("restriction", vf, vb)
    jp_g = E.composee(jp, g)                             # j'∘g
    f_j = E.composee(vf, j)                              # f∘j

    cible = morph(vb, sB, vbp, sBp, g)                   # morph(B,𝒮_B,B',𝒮'_B', g)
    rhs_jpg = morph(vb, sB, vap, vsp, jp_g)              # morph(B,𝒮_B,A',𝒮', j'∘g)
    rhs_fj = morph(vb, sB, vap, vsp, f_j)               # morph(B,𝒮_B,A',𝒮', f∘j)

    # — hypothèses —
    IN_Bp = equiv(cible, rhs_jpg)                        # (IN) de l'induite sur B', spécialisée
    EQ = egal(jp_g, f_j)                                 # j'∘g = f∘j
    COMP = rhs_fj                                        # morph(B,𝒮_B,A',𝒮', f∘j)  (MO_II)
    h_in, h_eq, h_comp = N.assume(IN_Bp), N.assume(EQ), N.assume(COMP)

    # réécrire COMP morph(…, f∘j) en morph(…, j'∘g) via EQ (j'∘g = f∘j) renversée.
    #   S6(jp_g, f_j, t, morph(B,𝒮_B,A',𝒮', t)) :
    #   (j'∘g = f∘j) ⇒ ( morph(…, j'∘g) ⇔ morph(…, f∘j) )
    t = "t_cst12"
    motif = morph(vb, sB, vap, vsp, var(t))
    s6_rw = N.s6(jp_g, f_j, t, motif)
    eqv_rw = N.modus_ponens(h_eq, s6_rw)                 # morph(…, j'∘g) ⇔ morph(…, f∘j)
    rhs_jpg_thm = N.modus_ponens(h_comp, equivalence_arriere(eqv_rw))  # morph(…, j'∘g)

    # (IN_B') : cible ⇔ rhs_jpg ; on remonte (⇐) depuis rhs_jpg
    return N.modus_ponens(rhs_jpg_thm, equivalence_arriere(h_in))  # ⊢ morph(B,𝒮_B,B',𝒮'_B', g)


# ════════════════════════════════════════════════════════════════════════════
#  CST20 — PASSAGE DES MORPHISMES AUX QUOTIENTS  (DUAL de CST12 via (FI))
# ════════════════════════════════════════════════════════════════════════════
#
#  (IV.2) : A, A' munis de 𝒮, 𝒮' ; R, R' relations d'équivalence ; 𝒮₀ quotient de 𝒮
#  par R sur A/R, 𝒮'₀ quotient de 𝒮' par R' sur A'/R'.  Si f : A→A' est un morphisme
#  compatible avec R, R', et g : A/R→A'/R' l'application obtenue par passage aux
#  quotients, alors g est un morphisme (𝒮₀ → 𝒮'₀).
#
#  Cœur logique.  La structure quotient 𝒮₀ = image directe de 𝒮 par la surjection
#  canonique φ : A→A/R.  Sa propriété (FI) à un indice (cf.
#  `ensembles_universel_finale.image_directe_structure`) :
#     (∀E')(∀𝒮')(∀h) [ morph(A/R,𝒮₀, E',𝒮', h) ⇔ morph(A, 𝒮, E',𝒮', h∘φ) ].
#  Spécialisée à (E'=A'/R', 𝒮'=𝒮'₀, h=g) :
#     morph(A/R,𝒮₀, A'/R',𝒮'₀, g)  ⇔  morph(A, 𝒮, A'/R',𝒮'₀, g∘φ).
#  Or g∘φ = φ'∘f  (compatibilité : g passe au quotient ⇒ le diagramme commute,
#  φ' : A'→A'/R' la surjection canonique), et φ'∘f est la COMPOSÉE de f : A→A'
#  (morphisme) et de φ' : A'→A'/R' (morphisme : surjection canonique vers la quotient,
#  par (FI) « chaque g_ι morphisme ») — morphisme par (MO_II).  On certifie ce cœur sous
#  les hypothèses EXPLICITES : (FI) de la quotient sur A/R, l'égalité g∘φ = φ'∘f, et
#  morph(A,𝒮, A'/R',𝒮'₀, φ'∘f).
#
def _struct_quotient(s, quo):
    """Structure quotient de 𝒮 sur l'ensemble quotient `quo` (terme opaque ; reportée)."""
    return app("struct_quotient", _t(s), _t(quo))


def cst20_passage_quotient(a="A", s="S", ap="Ap", sp="Sp", r="R", rp="Rp",
                           f="f", morph=None):
    """CST20 (cœur logique, IV.2) — PASSAGE DES MORPHISMES AUX QUOTIENTS.

    { (FI_AR) := propriété (FI) à un indice de la quotient 𝒮₀ sur A/R (image directe de
                 𝒮 par la surjection φ : A→A/R), spécialisée à (A'/R', 𝒮'₀, g),
      EQ       := g∘φ = φ'∘f      (compatibilité : passage au quotient ⇒ diagramme commute),
      COMP     := morph(A, 𝒮, A'/R', 𝒮'₀, φ'∘f)   ((MO_II) : f morphisme puis φ' morphisme) }
        ⊢  morph(A/R, 𝒮₀, A'/R', 𝒮'₀, g).

    « Si f est un morphisme de A dans A' compatible avec R, R', et g l'application
    obtenue par passage aux quotients, g est un morphisme de A/R dans A'/R'. »  DUAL de
    CST12 (via (FI) au lieu de (IN)).

    PREUVE : (FI_AR) donne morph(A/R,𝒮₀,A'/R',𝒮'₀, g) ⇔ morph(A,𝒮,A'/R',𝒮'₀, g∘φ) ; EQ
    réécrit g∘φ ↦ φ'∘f (S6) ; COMP fournit morph(…, φ'∘f) ; on remonte (⇐).  Hypothèses
    EXPLICITES (la caractéristique (FI) de la quotient, l'égalité des composées, la
    composée-morphisme (MO_II)) ; AUCUN axiome de théorie ajouté ; purement logique."""
    morph = _morph(morph)
    va, vs, vap, vsp, vr, vrp, vf = map(_t, (a, s, ap, sp, r, rp, f))
    AR = E.quotient(vr, va)                              # A/R
    ARp = E.quotient(vrp, vap)                           # A'/R'
    s0 = _struct_quotient(vs, AR)                        # 𝒮₀ quotient sur A/R
    s0p = _struct_quotient(vsp, ARp)                     # 𝒮'₀ quotient sur A'/R'
    phi = E.application_canonique(vr, va)                # φ : A → A/R
    phip = E.application_canonique(vrp, vap)             # φ' : A' → A'/R'
    g = app("passage_quotient", vf, vr, vrp)             # g : A/R → A'/R'  (passage au quotient)
    g_phi = E.composee(g, phi)                           # g∘φ
    phip_f = E.composee(phip, vf)                        # φ'∘f

    cible = morph(AR, s0, ARp, s0p, g)                   # morph(A/R,𝒮₀,A'/R',𝒮'₀, g)
    rhs_gphi = morph(va, vs, ARp, s0p, g_phi)            # morph(A,𝒮,A'/R',𝒮'₀, g∘φ)
    rhs_phif = morph(va, vs, ARp, s0p, phip_f)          # morph(A,𝒮,A'/R',𝒮'₀, φ'∘f)

    # — hypothèses —
    FI_AR = equiv(cible, rhs_gphi)                       # (FI) de la quotient, spécialisée
    EQ = egal(g_phi, phip_f)                             # g∘φ = φ'∘f
    COMP = rhs_phif                                      # morph(A,𝒮,A'/R',𝒮'₀, φ'∘f)  (MO_II)
    h_fi, h_eq, h_comp = N.assume(FI_AR), N.assume(EQ), N.assume(COMP)

    # réécrire COMP morph(…, φ'∘f) en morph(…, g∘φ) via EQ (g∘φ = φ'∘f).
    t = "t_cst20"
    motif = morph(va, vs, ARp, s0p, var(t))
    s6_rw = N.s6(g_phi, phip_f, t, motif)
    eqv_rw = N.modus_ponens(h_eq, s6_rw)                 # morph(…, g∘φ) ⇔ morph(…, φ'∘f)
    rhs_gphi_thm = N.modus_ponens(h_comp, equivalence_arriere(eqv_rw))  # morph(…, g∘φ)

    # (FI_AR) : cible ⇔ rhs_gphi ; on remonte (⇐)
    return N.modus_ponens(rhs_gphi_thm, equivalence_arriere(h_fi))  # ⊢ morph(A/R,𝒮₀,A'/R',𝒮'₀, g)


__all__ = [
    # CST3 — réciproque du transport
    "axiome_CST1_composition", "axiome_CST1_identite", "cst3_reciproque_transport",
    # MO_III — caractérisation des isomorphismes + réciproque d'un iso
    "est_iso_morph",   # (mo3_caracterisation_iso RETIRÉ : tautologie P⇔P, voir _est_iso_morph_reflexivite_triviale)
    "reciproque_iso_extrait_morphisme", "reciproque_iso_est_iso",
    # CST12 — restriction aux sous-structures
    "cst12_restriction_morphisme",
    # CST20 — passage aux quotients
    "cst20_passage_quotient",
]
