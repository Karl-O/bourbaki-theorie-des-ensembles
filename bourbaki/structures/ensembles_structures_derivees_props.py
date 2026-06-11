"""§IV.2 (suite) — STRUCTURES DÉRIVÉES : propositions/critères « logiquement directs »
non encore traités sous ce nom.   REPRÉSENTATIONNEL (méta-mathématique documentée).

Module NEUF (campagne « complétude chap. IV », vague IV-structures-derivees).  Il
COMPLÈTE les modules déjà faits du §IV.2 :
  • `ensembles_universel_morphismes`  — initiale, (IN), image réciproque, induite,
    « plus/moins fine », réflexivité de « moins fine » ;
  • `ensembles_universel_finale`      — finale, (FI), image directe, quotient ;
  • `ensembles_CST_criteres`          — CST9/CST18 (unicité initiale/finale via
    mutuelle « plus fine »), CST5 (unicité transport), transport préserve morphisme ;
  • `ensembles_structures_props`      — composition de morphismes, « plus fine »
    réflexive/transitive (préordre), identité/composée iso, unicité solution univ.

CE QUI EST PROUVÉ ICI (NOUVEAU, NON dupliqué — vérifié par GREP) :

  1. CST10 (TRANSITIVITÉ DES STRUCTURES INITIALES) — cœur logique.  Sous (IN) pour 𝓘
     (famille f_ι), (IN) pour 𝓘' (famille h_λ) ET la factorisation f_ι = g_{λι}∘h_λ
     avec (IN) des structures intermédiaires 𝒮'_λ, on certifie le palier décisif :
       • `initiale_transitive_un_sens` — sous (IN_𝓘), (IN_𝓘'), et l'hypothèse de
         factorisation des morphismes, « id_E morphisme (E,𝓘')->(E,𝓘) » =
         plus_fine(E,𝓘',𝓘) ;
       • `cst10_initiales_egales` — 𝓘 = 𝓘' (les deux structures initiales coïncident),
         assemblé via la mutuelle « plus fine » + antisymétrie (MO_III) en hypothèse.

  2. CST11 (TRANSITIVITÉ DES STRUCTURES INDUITES = STRUCTURE INDUITE PAR COMPOSITION)
     — théorème NOUVEAU et au cœur de ma mission :
       • `image_reciproque_par_composition` — la caractérisation (IN à un indice) de
         l'image réciproque par (g∘h) est ÉQUIVALENTE à la composition « image
         réciproque par h de (image réciproque par g de 𝒮) », via l'ASSOCIATIVITÉ
         g∘(h∘k) = (g∘h)∘k (hypothèse explicite) + transitivité d'équivalences.  C'est
         exactement CST11 (« les structures induites par 𝒮 et 𝒮' sur C sont
         identiques ») au niveau des CARACTÉRISATIONS (IN).  PLEINEMENT CLOS quant à
         son squelette logique (cf. test isolé).

  3. CST19 (TRANSITIVITÉ DES STRUCTURES FINALES) — DUAL de CST10 via (FI) :
       • `finale_transitive_un_sens`, `cst19_finales_egales`.

  4. PROPRIÉTÉS LOGIQUES DIRECTES DE L'IMAGE DIRECTE / RÉCIPROQUE :
       • `image_reciproque_unicite` — UNICITÉ de l'image réciproque (cas singleton de
         CST9) : deux structures vérifiant la caractérisation (IN à un indice) sont
         mutuellement « plus fine » ⇒ égales (antisymétrie en hypothèse) ;
       • `image_directe_unicite`    — DUAL (cas singleton de CST18) ;
       • `image_reciproque_rend_f_morphisme` — la structure image réciproque rend f un
         morphisme (sens facile de (IN) à un indice, g=id) ;
       • `image_directe_rend_f_morphisme`    — DUAL (sens facile de (FI) à un indice).

CONVENTION DE PARAMÉTRAGE (identique à tout le chap. IV) : la donnée abstraite
(Σ, σ) — méta — est portée par un PRÉDICAT callable → Formule du fragment objet
(`morph(e1,s1,e2,s2,f)` ; structures/ensembles/applications = termes opaques).  Les
théorèmes prouvés ne dépendent QUE de la structure logique (∀/∃/⇔/=) des propriétés
(IN), (FI), (MO_II), (MO_III) — donc valables QUELLE QUE SOIT la donnée σ : c'est le
« représentationnel / metamath », on certifie le squelette déductif des énoncés de
Bourbaki, le contenu σ restant un paramètre.

theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé ici.  Tout est soit LOGIQUE
PUR (modus ponens, transitivité d'équivalence, S6/Leibniz), soit CONDITIONNEL à des
hypothèses EXPLICITES = les axiomes-schémas (IN)/(FI)/(MO_II)/(MO_III) de Bourbaki
INSTANCIÉS et les ÉGALITÉS de composition (associativité), fournis comme PRÉMISSES —
JAMAIS postulés vrais.

REPORTÉ honnêtement (méta / lourd, hors fragment) : l'EXISTENCE effective des
structures initiale/finale/induite/image (CST22, constructions par échelon) ; la
TRANSPORTABILITÉ de R ; CST12 (restriction d'un morphisme aux sous-structures),
CST13/CST14 (associativité/compatibilité produit), CST15, CST20 (passage aux
quotients), décomposition canonique d'un morphisme — voir le champ `reportes`.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, equiv, pourtout, app)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere,
    equivalence_symetrie, equivalence_transitivite, instancie)
from bourbaki.structures.ensembles_universel_morphismes import (
    est_morphisme, plus_fine, propriete_IN, _morph_defaut, _t)
from bourbaki.structures.ensembles_universel_finale import propriete_FI


# ════════════════════════════════════════════════════════════════════════════
#  Outils internes (convention de défauts, identique au reste du chap. IV)
# ════════════════════════════════════════════════════════════════════════════
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


def id_est_morphisme(e, s, morph=None):
    """Formule « id_E = Δ_E est un σ-morphisme de (E,𝒮) dans (E,𝒮) » — instance d'
    (MO_III) (réflexivité de « plus fine », IV.2.2).  PRÉMISSE structurelle EXPLICITE,
    jamais axiome de la théorie."""
    morph = _morph(morph)
    ve, vs = _t(e), _t(s)
    return est_morphisme(ve, vs, ve, vs, E.diagonale(ve), morph)


# ════════════════════════════════════════════════════════════════════════════
#  1.  CST10 — TRANSITIVITÉ DES STRUCTURES INITIALES (cœur logique)
# ════════════════════════════════════════════════════════════════════════════
#
#  « … les propositions suivantes sont équivalentes : a) il existe une structure
#    initiale 𝓘 sur E pour (A_ι,𝒮_ι,f_ι)_{ι∈I} ; b) il existe une structure initiale
#    𝓘' sur E pour (B_λ,𝒮'_λ,h_λ)_{λ∈L}.  En outre, ces propositions entraînent 𝓘=𝓘'. »
#
#  La PARTIE LOGIQUEMENT DIRECTE (et l'enjeu de ma mission) est « 𝓘 = 𝓘' » : si 𝓘 et
#  𝓘' vérifient TOUTES DEUX (IN) (pour leurs familles respectives), alors id_E est un
#  morphisme de (E,𝓘) dans (E,𝓘') ET réciproquement, d'où 𝓘 = 𝓘' par antisymétrie.
#  La clef est que les MEMBRES DE DROITE des deux (IN), pris en (E'=E, g=id), sont
#  reliés : f_ι∘id morphisme ⇔ (par f_ι = g_{λι}∘h_λ + (IN) intermédiaire) h_λ∘id
#  morphisme.  On certifie ici le palier de transport « un sens » sous l'HYPOTHÈSE
#  EXPLICITE reliant les deux clauses de droite (qui résume le contenu f_ι=g_{λι}∘h_λ
#  + (IN) de 𝒮'_λ — ce contenu, qui exige (MO_II) sur la composition g_{λι}∘h_λ, est
#  fourni en prémisse, jamais postulé).
#
def _cotes_equiv(thm_eq):
    """Renvoie le couple (LHS, RHS) des deux membres d'un théorème d'équivalence
    Γ⊢(A⇔B).  ATTENTION : au niveau abrégé, equiv(A,B) a tag « non » (c'est la
    conjonction ¬(¬(A⇒B)∨¬(B⇒A))), donc on N'ACCÈDE PAS à .sous[1] ; on passe par
    equivalence_avant (qui donne A⇒B) puis antecedent_consequent."""
    return antecedent_consequent(equivalence_avant(thm_eq).conclusion)


def initiale_transitive_un_sens(e="E", struct_I="I", struct_J="J", i="I0",
                                af=None, sf=None, ff=None, hf=None, morph=None):
    """{ (IN_𝓘) pour la famille (A_ι,𝒮_ι,f_ι),
         (IN_𝓘') pour la famille (B_λ,𝒮'_λ,h_λ),
         LIEN := (∀ι… clause de droite via f_ι à E'=E,g=id)
                 ⇔ (∀λ… clause de droite via h_λ à E'=E,g=id)
                 [ = contenu « f_ι=g_{λι}∘h_λ + (IN) de 𝒮'_λ », hypothèse explicite ],
         « id_E morphisme (E,𝓘')->(E,𝓘') » (MO_III) }
        ⊢  plus_fine(E, 𝓘', 𝓘)   ( = « id_E morphisme (E,𝓘')->(E,𝓘) »).

    CŒUR « un sens » de CST10 (transitivité des structures initiales).  Preuve (logique
    pure sur la structure de (IN)) :
      • (IN_𝓘)  à (E'=E, 𝒮'=𝓘', g=id) : morph(E,𝓘',E,𝓘,id)  ⇔ RHS_f  (clause via f_ι) ;
      • (IN_𝓘') à (E'=E, 𝒮'=𝓘', g=id) : morph(E,𝓘',E,𝓘',id) ⇔ RHS_h  (clause via h_λ) ;
      • LIEN : RHS_f ⇔ RHS_h  (fourni en hypothèse — résume f_ι=g_{λι}∘h_λ + (IN) 𝒮'_λ) ;
      • « id (E,𝓘')->(E,𝓘') » vrai (MO_III) ⇒ par (IN_𝓘') RHS_h ⇒ (LIEN⁻¹) RHS_f ⇒ par
        (IN_𝓘) « id (E,𝓘')->(E,𝓘) » = plus_fine(E,𝓘',𝓘).
    Renvoie le conditionnel ; hypothèses = {(IN_𝓘),(IN_𝓘'),LIEN, id morph (E,𝓘')}.  Le
    contenu LIEN est l'instance de (MO_II)+(IN) intermédiaire de Bourbaki, prémisse —
    jamais postulé.  AUCUN axiome de théorie ajouté."""
    af, sf, ff, morph = _defaults_in(af, sf, ff, morph)
    if hf is None:
        hf = lambda t: app("h", t)
    ve, vi = _t(e), _t(i)
    sI, sJ = _t(struct_I), _t(struct_J)
    DE = E.diagonale(ve)

    # (IN_𝓘)  à (E'=E, 𝒮'=𝓘', g=Δ_E) : morph(E,𝓘',E,𝓘,id) ⇔ RHS_f
    inI = propriete_IN(ve, sI, vi, af, sf, ff, morph=morph)
    hI = N.assume(inI)
    eqI = instancie(instancie(instancie(hI, ve), sJ), DE)        # lhs_I ⇔ RHS_f
    # (IN_𝓘') à (E'=E, 𝒮'=𝓘', g=Δ_E) : morph(E,𝓘',E,𝓘',id) ⇔ RHS_h  (famille h_λ)
    inJ = propriete_IN(ve, sJ, vi, af, sf, hf, morph=morph)
    hJ = N.assume(inJ)
    eqJ = instancie(instancie(instancie(hJ, ve), sJ), DE)        # lhs_J ⇔ RHS_h

    # LIEN : RHS_f ⇔ RHS_h.  On récupère RHS_f / RHS_h = membre DROIT de chaque ⇔
    # (la clause (∀ι)(…) de droite de (IN)) — via _cotes_equiv (equiv a tag « non »).
    _, rhs_f = _cotes_equiv(eqI)                                  # RHS via f_ι
    _, rhs_h = _cotes_equiv(eqJ)                                  # RHS via h_λ
    LIEN = equiv(rhs_f, rhs_h)
    h_lien = N.assume(LIEN)

    # « id (E,𝓘')->(E,𝓘') » (MO_III) ⊢, via (IN_𝓘'), RHS_h ; puis LIEN⁻¹ ; puis (IN_𝓘)⁻¹.
    idJ = id_est_morphisme(ve, sJ, morph)                       # morph(E,𝓘',E,𝓘',id)
    h_idJ = N.assume(idJ)
    rhs_h_thm = N.modus_ponens(h_idJ, equivalence_avant(eqJ))   # ⊢ RHS_h
    rhs_f_thm = N.modus_ponens(rhs_h_thm, equivalence_arriere(h_lien))  # ⊢ RHS_f
    return N.modus_ponens(rhs_f_thm, equivalence_arriere(eqI))  # ⊢ morph(E,𝓘',E,𝓘,id) = plus_fine(E,𝓘',𝓘)


def cst10_initiales_egales(e="E", struct_I="I", struct_J="J", i="I0",
                           af=None, sf=None, ff=None, hf=None, morph=None):
    """CST10 — « ces propositions entraînent 𝓘 = 𝓘' » (les deux structures initiales
    coïncident).

    {(IN_𝓘), (IN_𝓘'), LIEN (et son symétrique), 2×(id morph), ANTISYM} ⊢ 𝓘 = 𝓘'.

    Assemble les DEUX sens de `initiale_transitive_un_sens` (plus_fine(E,𝓘',𝓘) et
    plus_fine(E,𝓘,𝓘')) en la mutuelle « plus fine », puis applique l'ANTISYMÉTRIE de
    « moins/plus fine » (MO_III, IV.2.2) fournie en hypothèse EXPLICITE.  Conclut
    l'égalité 𝓘 = 𝓘'.  Rien postulé : LIEN = contenu (MO_II)+(IN) 𝒮'_λ instancié,
    ANTISYM = (MO_III) instancié, prémisses du théorème."""
    sI, sJ = _t(struct_I), _t(struct_J)
    pf_JI = initiale_transitive_un_sens(e, struct_I, struct_J, i, af, sf, ff, hf, morph)  # plus_fine(E,𝓘',𝓘)
    pf_IJ = initiale_transitive_un_sens(e, struct_J, struct_I, i, af, sf, hf, ff, morph)  # plus_fine(E,𝓘,𝓘')
    mut = conjonction_intro(pf_IJ, pf_JI)
    antisym = impl(mut.conclusion, egal(sI, sJ))   # (pf∧pf) ⇒ 𝓘=𝓘'
    h_anti = N.assume(antisym)
    return N.modus_ponens(mut, h_anti)             # ⊢ 𝓘 = 𝓘'


# ════════════════════════════════════════════════════════════════════════════
#  2.  CST11 — STRUCTURE INDUITE PAR COMPOSITION  (transitivité des induites)
# ════════════════════════════════════════════════════════════════════════════
#
#  Image réciproque par f de 𝒮 (sur B) := la structure 𝓘 caractérisée (IN à un indice)
#  par  (∀E')(∀𝒮')(∀g)[ morph(E',𝒮',B,𝓘,g) ⇔ morph(E',𝒮',A,𝒮, f∘g) ].
#
#  CST11 : 𝒮 sur A induit 𝒮' = imrec_g(𝒮) sur B (g : B→A), et 𝒮' induit 𝓙 = imrec_h(𝒮')
#  sur C (h : C→B).  Alors 𝒮 induit DIRECTEMENT sur C la structure imrec_{g∘h}(𝒮), et
#  les deux coïncident.  Le cœur LOGIQUEMENT DIRECT : la caractérisation de 𝓙 (via h sur
#  𝒮') et celle de imrec_{g∘h}(𝒮) (via g∘h sur 𝒮) sont ÉQUIVALENTES, grâce à
#  l'ASSOCIATIVITÉ g∘(h∘k) = (g∘h)∘k.
#
def _carac_imrec(e, struct, a, s, f, ep, sp, g, morph):
    """L'ÉQUIVALENCE-caractérisation (IN à un indice) de la structure image réciproque
    `struct` par `f` de 𝒮 sur l'ensemble `e`, instanciée à (E'=ep, 𝒮'=sp, application g):
        morph(E', 𝒮', e, struct, g)  ⇔  morph(E', 𝒮', a, s, f∘g).
    (Formule, pas théorème.)"""
    morph = _morph(morph)
    ve, vep, vsp, vg = _t(e), _t(ep), _t(sp), _t(g)
    lhs = est_morphisme(vep, vsp, ve, struct, vg, morph)
    rhs = est_morphisme(vep, vsp, _t(a), _t(s), E.composee(_t(f), vg), morph)
    return equiv(lhs, rhs)


def image_reciproque_par_composition(a="A", s="S", b="B", c="C",
                                     g="g", h="h", k="k", ep="Ep", sp="Sp",
                                     struct_I="SI", struct_J="SJ", morph=None):
    """CST11 — STRUCTURE INDUITE PAR COMPOSITION (transitivité des induites).

    {  CAR_𝓘 := « 𝓘 = imrec_g(𝒮) sur B » à (E',𝒮',h∘k) :
           morph(E',𝒮',B,𝓘, h∘k) ⇔ morph(E',𝒮', A, 𝒮, g∘(h∘k)),
       CAR_𝓙 := « 𝓙 = imrec_h(𝓘) sur C » à (E',𝒮', k) :
           morph(E',𝒮',C,𝓙, k)   ⇔ morph(E',𝒮', B, 𝓘, h∘k),
       ASSOC := g∘(h∘k) = (g∘h)∘k    (associativité de ∘, hypothèse explicite) }
        ⊢  morph(E',𝒮',C,𝓙, k)  ⇔  morph(E',𝒮', A, 𝒮, (g∘h)∘k)
           ( = la CARACTÉRISATION (IN à un indice) de 𝓙 comme image réciproque de 𝒮
             par g∘h sur C — donc 𝓙 = imrec_{g∘h}(𝒮), i.e. l'induite directe ).

    C'est EXACTEMENT le contenu de CST11 : « 𝒮' induit sur C une structure ⟺ 𝒮 induit
    sur C une structure, et les structures induites par 𝒮 et 𝒮' sur C sont identiques ».
    Preuve (logique pure) : transitivité d'équivalences
        morph(C,𝓙,k) ⇔[CAR_𝓙] morph(B,𝓘,h∘k) ⇔[CAR_𝓘] morph(A,𝒮,g∘(h∘k))
                     ⇔[ASSOC,S6] morph(A,𝒮,(g∘h)∘k).
    La réécriture g∘(h∘k) ↦ (g∘h)∘k est l'associativité (E.II.3.7, fournie en HYPOTHÈSE
    EXPLICITE — lemme de composition certifié ailleurs ; ici prémisse pour rester
    self-contained et ne créer aucun axiome) appliquée par S6/Leibniz.  PLEINEMENT
    logique ; hypothèses = {CAR_𝓘, CAR_𝓙, ASSOC}, AUCUN axiome de théorie."""
    morph = _morph(morph)
    va, vs, vb, vc = _t(a), _t(s), _t(b), _t(c)
    vg, vh, vk = _t(g), _t(h), _t(k)
    vep, vsp = _t(ep), _t(sp)
    sI, sJ = _t(struct_I), _t(struct_J)
    hk = E.composee(vh, vk)            # h∘k
    g_hk = E.composee(vg, hk)          # g∘(h∘k)
    gh = E.composee(vg, vh)            # g∘h
    gh_k = E.composee(gh, vk)          # (g∘h)∘k

    # CAR_𝓙 : morph(E',𝒮',C,𝓙,k) ⇔ morph(E',𝒮',B,𝓘,h∘k)
    CAR_J = _carac_imrec(vc, sJ, vb, sI, vh, vep, vsp, vk, morph)
    # CAR_𝓘 : morph(E',𝒮',B,𝓘,h∘k) ⇔ morph(E',𝒮',A,𝒮,g∘(h∘k))
    CAR_I = _carac_imrec(vb, sI, va, vs, vg, vep, vsp, hk, morph)
    h_carJ, h_carI = N.assume(CAR_J), N.assume(CAR_I)

    # chaîne : morph(C,𝓙,k) ⇔ morph(B,𝓘,h∘k) ⇔ morph(A,𝒮,g∘(h∘k))
    chaine = equivalence_transitivite(h_carJ, h_carI)
    # ⊢ morph(E',𝒮',C,𝓙,k) ⇔ morph(E',𝒮',A,𝒮, g∘(h∘k))

    # ASSOC : g∘(h∘k) = (g∘h)∘k ; réécrit le dernier argument g∘(h∘k) ↦ (g∘h)∘k via S6
    assoc = egal(g_hk, gh_k)
    h_assoc = N.assume(assoc)
    w = "w_cst11"
    # motif = morph(E',𝒮', A, 𝒮, w)
    motif = est_morphisme(vep, vsp, va, vs, var(w), morph)
    s6 = N.s6(g_hk, gh_k, w, motif)                            # (g∘(h∘k)=(g∘h)∘k) ⇒ (motif[g∘(h∘k)] ⇔ motif[(g∘h)∘k])
    eqv_assoc = N.modus_ponens(h_assoc, s6)                    # morph(A,𝒮,g∘(h∘k)) ⇔ morph(A,𝒮,(g∘h)∘k)
    resultat = equivalence_transitivite(chaine, eqv_assoc)     # morph(C,𝓙,k) ⇔ morph(A,𝒮,(g∘h)∘k)

    # contrôle : la cible EST la caractérisation imrec_{g∘h}(𝒮) sur C à (E',𝒮',k)
    cible = _carac_imrec(vc, sJ, va, vs, gh, vep, vsp, vk, morph)
    assert resultat.conclusion == cible, "conclusion ≠ caractérisation imrec_{g∘h} attendue"
    return resultat


# ════════════════════════════════════════════════════════════════════════════
#  3.  CST19 — TRANSITIVITÉ DES STRUCTURES FINALES  (DUAL de CST10 via (FI))
# ════════════════════════════════════════════════════════════════════════════
def finale_transitive_un_sens(e="E", struct_F="F", struct_G="G", i="I0",
                              af=None, sf=None, gf=None, hf=None, morph=None):
    """{ (FI_𝓕) pour (A_ι,𝒮_ι,g_ι), (FI_𝓕') pour (B_λ,𝒮'_λ,h_λ),
         LIEN := RHS via g_ι (E'=E,f=id) ⇔ RHS via h_λ (E'=E,f=id)
                 [ contenu f_ι=h_λ∘g_{ιλ} + (FI) de 𝒮'_λ, hypothèse explicite ],
         « id_E morphisme (E,𝓕')->(E,𝓕') » (MO_III) }
        ⊢  plus_fine(E, 𝓕, 𝓕')   ( = « id_E morphisme (E,𝓕)->(E,𝓕') »).

    DUAL de `initiale_transitive_un_sens` via (FI) (la SOURCE du morphisme est la
    structure finale).  Même squelette : (FI) instanciée à (E'=E, 𝒮'=l'autre, f=id),
    les RHS reliés par LIEN, « id morphisme » (MO_III) transporte par les ⇔.  Renvoie
    le conditionnel ; hypothèses explicites (les 2 (FI), LIEN, id morph), aucun axiome."""
    af, sf, gf, morph = _defaults_in(af, sf, gf, morph)
    if hf is None:
        hf = lambda t: app("h", t)
    ve, vi = _t(e), _t(i)
    sF, sG = _t(struct_F), _t(struct_G)
    DE = E.diagonale(ve)

    # (FI_𝓕)  à (E'=E, 𝒮'=𝓕', f=Δ_E) : morph(E,𝓕,E,𝓕',id) ⇔ RHS_g
    fiF = propriete_FI(ve, sF, vi, af, sf, gf, morph=morph)
    hF = N.assume(fiF)
    eqF = instancie(instancie(instancie(hF, ve), sG), DE)        # lhs_F ⇔ RHS_g
    # (FI_𝓕') à (E'=E, 𝒮'=𝓕', f=Δ_E) : morph(E,𝓕',E,𝓕',id) ⇔ RHS_h
    fiG = propriete_FI(ve, sG, vi, af, sf, hf, morph=morph)
    hG = N.assume(fiG)
    eqG = instancie(instancie(instancie(hG, ve), sG), DE)        # lhs_G ⇔ RHS_h

    _, rhs_g = _cotes_equiv(eqF)
    _, rhs_h = _cotes_equiv(eqG)
    LIEN = equiv(rhs_g, rhs_h)
    h_lien = N.assume(LIEN)

    idG = id_est_morphisme(ve, sG, morph)                       # morph(E,𝓕',E,𝓕',id)
    h_idG = N.assume(idG)
    rhs_h_thm = N.modus_ponens(h_idG, equivalence_avant(eqG))   # ⊢ RHS_h
    rhs_g_thm = N.modus_ponens(rhs_h_thm, equivalence_arriere(h_lien))  # ⊢ RHS_g
    return N.modus_ponens(rhs_g_thm, equivalence_arriere(eqF))  # ⊢ morph(E,𝓕,E,𝓕',id) = plus_fine(E,𝓕,𝓕')


def cst19_finales_egales(e="E", struct_F="F", struct_G="G", i="I0",
                         af=None, sf=None, gf=None, hf=None, morph=None):
    """CST19 — « ces propositions entraînent 𝓕 = 𝓕' ».  DUAL de `cst10_initiales_egales`.
    {(FI_𝓕),(FI_𝓕'), LIEN (et son symétrique), 2×(id morph), ANTISYM} ⊢ 𝓕 = 𝓕'."""
    sF, sG = _t(struct_F), _t(struct_G)
    pf_FG = finale_transitive_un_sens(e, struct_F, struct_G, i, af, sf, gf, hf, morph)  # plus_fine(E,𝓕,𝓕')
    pf_GF = finale_transitive_un_sens(e, struct_G, struct_F, i, af, sf, hf, gf, morph)  # plus_fine(E,𝓕',𝓕)
    mut = conjonction_intro(pf_FG, pf_GF)
    antisym = impl(mut.conclusion, egal(sF, sG))
    h_anti = N.assume(antisym)
    return N.modus_ponens(mut, h_anti)             # ⊢ 𝓕 = 𝓕'


# ════════════════════════════════════════════════════════════════════════════
#  4.  PROPRIÉTÉS LOGIQUES DIRECTES de l'IMAGE RÉCIPROQUE / DIRECTE
# ════════════════════════════════════════════════════════════════════════════
#  Image réciproque = structure initiale pour le SEUL triplet (A,𝒮,f) ⇒ tous les
#  résultats de CST9 (unicité, « rend f morphisme ») se SPÉCIALISENT au cas |I|=1.
#
def image_reciproque_unicite(e="E", a="A", s="S", f="f",
                             struct_I="I", struct_J="J", morph=None):
    """UNICITÉ de l'image réciproque par f de 𝒮 (cas singleton de CST9).

    {  CAR_𝓘 := « 𝓘 image réciproque » à (E'=E,𝒮'=𝓙,g=id) :
           morph(E,𝓙,E,𝓘,id) ⇔ morph(E,𝓙,A,𝒮, f∘id),
       CAR_𝓙 := « 𝓙 image réciproque » à (E'=E,𝒮'=𝓙,g=id) :
           morph(E,𝓙,E,𝓙,id) ⇔ morph(E,𝓙,A,𝒮, f∘id),
       symétriquement (E'=E,𝒮'=𝓘,g=id) pour l'autre sens,
       « id morph (E,𝓙)->(E,𝓙) », « id morph (E,𝓘)->(E,𝓘) »  (MO_III),
       ANTISYM := (plus_fine(E,𝓘,𝓙) et plus_fine(E,𝓙,𝓘)) ⇒ 𝓘=𝓙 }
        ⊢  𝓘 = 𝓙.

    Deux structures 𝓘, 𝓙 vérifiant la MÊME caractérisation d'image réciproque (IN à un
    indice, même A,𝒮,f) sont égales.  Preuve : leurs membres de droite « morph(·,A,𝒮,
    f∘id) » coïncident (LITTÉRALEMENT), donc — via MO_III — chacune est « plus fine »
    que l'autre ; antisymétrie (MO_III, hypothèse) ⇒ 𝓘=𝓙.  Cas |I|=1 du cœur de CST9.
    Purement logique (transitivité d'équivalence + modus ponens)."""
    morph = _morph(morph)
    ve, va, vs, vf = _t(e), _t(a), _t(s), _t(f)
    sI, sJ = _t(struct_I), _t(struct_J)
    DE = E.diagonale(ve)

    def un_sens(sA, sB):
        """⊢ plus_fine(E, sB, sA) sous {CAR_sA, CAR_sB, id morph (E,sB)}.

        CAR_sX à (E'=E, 𝒮'=sB, g=Δ_E) : morph(E,sB,E,sX,id) ⇔ morph(E,sB,A,𝒮,f∘id).
        Les RHS coïncident (même A,𝒮,f∘id, même source (E,sB)) ; « id (E,sB)->(E,sB) »
        (MO_III) ⊢ morph(E,sB,E,sB,id) ⇒(CAR_sB) RHS ⇒(CAR_sA⁻¹) morph(E,sB,E,sA,id)
        = plus_fine(E,sB,sA)."""
        carA = _carac_imrec(ve, sA, va, vs, vf, ve, sB, DE, morph)   # morph(E,sB,E,sA,id) ⇔ RHS
        carB = _carac_imrec(ve, sB, va, vs, vf, ve, sB, DE, morph)   # morph(E,sB,E,sB,id) ⇔ RHS
        hA, hB = N.assume(carA), N.assume(carB)
        chaine = equivalence_transitivite(hA, equivalence_symetrie(hB))  # morph(...,sA,id) ⇔ morph(...,sB,id)
        idB = id_est_morphisme(ve, sB, morph)
        h_idB = N.assume(idB)
        return N.modus_ponens(h_idB, equivalence_arriere(chaine))   # plus_fine(E,sB,sA)

    pf_JI = un_sens(sI, sJ)     # plus_fine(E, 𝓙, 𝓘)
    pf_IJ = un_sens(sJ, sI)     # plus_fine(E, 𝓘, 𝓙)
    mut = conjonction_intro(pf_IJ, pf_JI)
    antisym = impl(mut.conclusion, egal(sI, sJ))
    h_anti = N.assume(antisym)
    return N.modus_ponens(mut, h_anti)             # ⊢ 𝓘 = 𝓙


def image_directe_unicite(e="E", a="A", s="S", f="f",
                          struct_F="F", struct_G="G", morph=None):
    """UNICITÉ de l'image directe par f de 𝒮 (cas singleton de CST18) — DUAL.

    Caractérisation image directe (FI à un indice) : pour tout (E',𝒮',h),
        morph(E,𝓕,E',𝒮',h) ⇔ morph(A,𝒮,E',𝒮', h∘f).
    Deux structures 𝓕,𝓕' vérifiant cette caractérisation (même A,𝒮,f) sont égales :
    instanciées à (E'=E,𝒮'=l'autre,h=id) leurs RHS « morph(A,𝒮,id∘f) » coïncident, d'où
    mutuelle « plus fine » + antisymétrie (MO_III, hypothèse) ⇒ 𝓕=𝓕'.  Purement logique."""
    morph = _morph(morph)
    ve, va, vs, vf = _t(e), _t(a), _t(s), _t(f)
    sF, sG = _t(struct_F), _t(struct_G)
    DE = E.diagonale(ve)

    def _carac_imdir(struct, ep, sp, hh):
        """morph(E, struct, E', 𝒮', h)  ⇔  morph(A, 𝒮, E', 𝒮', h∘f)  (FI à un indice)."""
        lhs = est_morphisme(ve, struct, _t(ep), _t(sp), _t(hh), morph)
        rhs = est_morphisme(va, vs, _t(ep), _t(sp), E.composee(_t(hh), vf), morph)
        return equiv(lhs, rhs)

    def un_sens(sA, sB):
        """⊢ plus_fine(E, sA, sB) = morph(E,sA,E,sB,id) sous {CAR_sA,CAR_sB, id morph (E,sB)}."""
        carA = _carac_imdir(sA, ve, sB, DE)        # morph(E,sA,E,sB,id) ⇔ RHS
        carB = _carac_imdir(sB, ve, sB, DE)        # morph(E,sB,E,sB,id) ⇔ RHS
        hA, hB = N.assume(carA), N.assume(carB)
        chaine = equivalence_transitivite(hA, equivalence_symetrie(hB))  # morph(E,sA,E,sB,id) ⇔ morph(E,sB,E,sB,id)
        idB = id_est_morphisme(ve, sB, morph)
        h_idB = N.assume(idB)
        return N.modus_ponens(h_idB, equivalence_arriere(chaine))   # plus_fine(E,sA,sB)

    pf_FG = un_sens(sF, sG)     # plus_fine(E, 𝓕, 𝓕')
    pf_GF = un_sens(sG, sF)     # plus_fine(E, 𝓕', 𝓕)
    mut = conjonction_intro(pf_FG, pf_GF)
    antisym = impl(mut.conclusion, egal(sF, sG))
    h_anti = N.assume(antisym)
    return N.modus_ponens(mut, h_anti)             # ⊢ 𝓕 = 𝓕'


def image_reciproque_rend_f_morphisme(e="E", a="A", s="S", f="f",
                                      struct_I="I", morph=None):
    """{ CAR_𝓘 := « 𝓘 = imrec_f(𝒮) » à (E'=E,𝒮'=𝓘,g=id) :
            morph(E,𝓘,E,𝓘,id) ⇔ morph(E,𝓘,A,𝒮, f∘id),
         « id_E morphisme (E,𝓘)->(E,𝓘) » (MO_III) }
        ⊢  morph(E, 𝓘, A, 𝒮, f∘id_E).

    « LA STRUCTURE IMAGE RÉCIPROQUE REND f UN MORPHISME » (sens facile de (IN) à un
    indice, g=id).  En (E'=E,𝒮'=𝓘,g=id) la caractérisation donne
        « id_E morphisme (E,𝓘)->(E,𝓘) » ⇔ « f∘id_E morphisme (E,𝓘)->(A,𝒮) » ;
    le membre de gauche est vrai (MO_III), d'où f∘id_E est un morphisme de (E,𝓘) dans
    (A,𝒮).  On délivre la forme avec f∘Δ_E (le lemme f∘id=f est reporté avec la
    composition).  Purement logique (equivalence_avant + modus ponens)."""
    morph = _morph(morph)
    ve, va, vs, vf = _t(e), _t(a), _t(s), _t(f)
    sI = _t(struct_I)
    DE = E.diagonale(ve)
    car = _carac_imrec(ve, sI, va, vs, vf, ve, sI, DE, morph)   # morph(E,𝓘,E,𝓘,id) ⇔ morph(E,𝓘,A,𝒮,f∘id)
    h_car = N.assume(car)
    idI = id_est_morphisme(ve, sI, morph)                      # morph(E,𝓘,E,𝓘,id)
    h_idI = N.assume(idI)
    return N.modus_ponens(h_idI, equivalence_avant(h_car))     # ⊢ morph(E,𝓘,A,𝒮, f∘id)


def image_directe_rend_f_morphisme(e="E", a="A", s="S", f="f",
                                   struct_F="F", morph=None):
    """{ CAR_𝓕 := « 𝓕 = imdir_f(𝒮) » à (E'=E,𝒮'=𝓕,h=id) :
            morph(E,𝓕,E,𝓕,id) ⇔ morph(A,𝒮,E,𝓕, id∘f),
         « id_E morphisme (E,𝓕)->(E,𝓕) » (MO_III) }
        ⊢  morph(A, 𝒮, E, 𝓕, id_E∘f).

    DUAL : « LA STRUCTURE IMAGE DIRECTE REND f UN MORPHISME » (sens facile de (FI) à un
    indice, h=id).  En (E'=E,𝒮'=𝓕,h=id) la caractérisation donne « id_E morphisme
    (E,𝓕)->(E,𝓕) » ⇔ « id_E∘f morphisme (A,𝒮)->(E,𝓕) » ; gauche vrai (MO_III), d'où
    droite.  Forme avec id_E∘f (le lemme id∘f=f reporté).  Purement logique."""
    morph = _morph(morph)
    ve, va, vs, vf = _t(e), _t(a), _t(s), _t(f)
    sF = _t(struct_F)
    DE = E.diagonale(ve)
    lhs = est_morphisme(ve, sF, ve, sF, DE, morph)             # morph(E,𝓕,E,𝓕,id)
    rhs = est_morphisme(va, vs, ve, sF, E.composee(DE, vf), morph)   # morph(A,𝒮,E,𝓕, id∘f)
    car = equiv(lhs, rhs)                                      # (FI à un indice), h=id
    h_car = N.assume(car)
    idF = id_est_morphisme(ve, sF, morph)                      # morph(E,𝓕,E,𝓕,id)
    h_idF = N.assume(idF)
    return N.modus_ponens(h_idF, equivalence_avant(h_car))     # ⊢ morph(A,𝒮,E,𝓕, id∘f)


__all__ = [
    "id_est_morphisme",
    # 1. CST10 — transitivité des structures initiales
    "initiale_transitive_un_sens", "cst10_initiales_egales",
    # 2. CST11 — structure induite par composition (transitivité des induites)
    "image_reciproque_par_composition",
    # 3. CST19 — transitivité des structures finales
    "finale_transitive_un_sens", "cst19_finales_egales",
    # 4. propriétés directes image réciproque / directe
    "image_reciproque_unicite", "image_directe_unicite",
    "image_reciproque_rend_f_morphisme", "image_directe_rend_f_morphisme",
]
