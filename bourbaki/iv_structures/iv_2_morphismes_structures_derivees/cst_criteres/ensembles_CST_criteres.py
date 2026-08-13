"""§IV.1–IV.3 — CRITÈRES DE STRUCTURES (CST) : cœurs logiques certifiés.

Module NEUF (campagne « critères de structures »).  Il COMPLÈTE les modules déjà
faits du chapitre IV — `ensembles_universel_morphismes` (initiale, (IN)),
`ensembles_universel_finale` (finale, (FI)), `ensembles_universel_applications`
(applications universelles, (AU)), `ensembles_structures_complements` (CST22/CST8
énoncés) — en PROUVANT (au niveau du noyau, `.est_clos` / conditionnel à hypothèses
EXPLICITES) les PALIERS LOGIQUES DIRECTS des critères CST que ces modules n'avaient
laissés qu'à l'état d'ÉNONCÉ ou de « sens facile ».

Convention de paramétrage IDENTIQUE au reste du chap. IV (cf. docstrings de
`ensembles_universel_morphismes`).  La donnée abstraite (Σ, σ, α) — méta — est
portée par des PRÉDICATS callables → Formule du fragment objet :
  • `morph(e1,s1,e2,s2,f)`  : « f est un σ-morphisme de (e1,s1) dans (e2,s2) » ;
  • `sigma_ens(F, S)`       : « (F,S) est un Σ-ensemble » ;
  • `alpha(F, S, phi)`      : « φ est une α-application de E dans (F,S) ».
Les structures, applications, ensembles de base sont des TERMES.  Les théorèmes
prouvés ici ne dépendent QUE de la STRUCTURE LOGIQUE (∀/∃/⇔/=) des propriétés
(IN), (FI), (AU), (MO_III) — ils sont donc valables QUELLE QUE SOIT la donnée σ
(c'est le sens du « représentationnel / metamath » : on certifie le squelette
déductif des critères de Bourbaki, le contenu σ restant un paramètre).

CE QUI EST PROUVÉ ICI (NOUVEAU, non dupliqué) :
  • CST9  (unicité de la structure INITIALE) — cœur : deux structures vérifiant
    (IN) sont mutuellement « moins fine » (⇒ antisymétrie ⇒ unicité).  + le sens
    « 𝓘 ⇒ chaque f_ι morphisme » reformulé comme « 𝓘 moins fine que toute 𝒮
    rendant les f_ι morphismes » (caractérisation « moins fine »).
  • CST18 (unicité de la structure FINALE) — DUAL via (FI).
  • TRANSPORT préserve les morphismes (IV.1.5 / cœur CST4) : si f est un
    isomorphisme et g un morphisme, le transporté g par f reste un morphisme
    (palier (MO_II)+(MO_III) : composition).  Énoncé + cœur logique.
  • CST5 (UNICITÉ du transport) : deux structures transportées par le même
    isomorphisme coïncident — cœur logique (fonctionnalité du transport).
  • CST22/CST23 — UNICITÉ de la solution du problème universel : deux solutions
    sont reliées par des morphismes croisés UNIQUES (cœur (AU_II′)).

REPORTÉ honnêtement (méta / lourd, hors fragment) : l'EXISTENCE effective des
structures initiale/finale/transportée (constructions par échelon, CST5 existence,
CST22 construction de F_E), la TRANSPORTABILITÉ de R (IV.1.3), CST10–CST20
(transitivité, associativité, compatibilité produit/quotient) — voir `reportes`.
theorie_ensembles() reste à 22 axiomes : AUCUN axiome créé ici (tout est soit
logique pur, soit conditionnel à des hypothèses EXPLICITES = les axiomes-schémas
(IN)/(FI)/(AU)/(MO) instanciés, jamais postulés comme vrais).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, ou, impl, equiv, non,
                                       pourtout, existe, appartient, app)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (a_implique_a, syllogisme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_morphismes import (
    est_morphisme, plus_fine, moins_fine, propriete_IN, _morph_defaut, _t)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.ensembles_universel_finale import propriete_FI


# ════════════════════════════════════════════════════════════════════════════
#  Outils internes
# ════════════════════════════════════════════════════════════════════════════
def _defaults(af, sf, ff, morph):
    if af is None:
        af = lambda t: app("A", t)
    if sf is None:
        sf = lambda t: app("Sig", t)
    if ff is None:
        ff = lambda t: app("f", t)
    if morph is None:
        morph = _morph_defaut()
    return af, sf, ff, morph


# @livre Ch.IV §2.1 Ax.- | E IV.11 L.32-36 | PDF p.214
def id_est_morphisme(e, s, morph=None):
    """Formule « id_E = Δ_E est un σ-morphisme de (E,𝒮) dans (E,𝒮) ».  C'est
    l'instance d'(MO_III) (réflexivité de « plus fine », IV.2.2) — une HYPOTHÈSE
    structurelle vraie pour toute structure, jamais postulée comme axiome de la
    théorie : on l'introduit EXPLICITEMENT comme prémisse des théorèmes."""
    if morph is None:
        morph = _morph_defaut()
    ve, vs = _t(e), _t(s)
    return est_morphisme(ve, vs, ve, vs, E.diagonale(ve), morph)


# ════════════════════════════════════════════════════════════════════════════
#  CST9 — UNICITÉ de la structure INITIALE
# ════════════════════════════════════════════════════════════════════════════
#
#  « S'il existe sur E une structure initiale 𝓘 pour la famille (A_ι,𝒮_ι,f_ι),
#    elle est la MOINS FINE des structures d'espèce Σ sur E pour lesquelles chaque
#    f_ι est un morphisme, et par suite est UNIQUE. »
#
#  Cœur logique de l'unicité : si 𝓘 ET 𝓘' vérifient (IN) (pour la même famille),
#  alors id_E est un morphisme de (E,𝓘) dans (E,𝓘') ET de (E,𝓘') dans (E,𝓘),
#  c.-à-d. plus_fine(𝓘,𝓘') ET plus_fine(𝓘',𝓘) — d'où, par antisymétrie (MO_III),
#  𝓘 = 𝓘'.  On démontre ici la conjonction des deux « plus fine » (l'antisymétrie
#  ⇒ 𝓘=𝓘' est le palier MO_III, fourni en hypothèse explicite).
#
# @livre Ch.IV §2.3 Crit.CST9 | E IV.14 L.24-30 | PDF p.217
def initiales_mutuellement_plus_fines(e="E", struct_I="I", struct_J="J",
                                      i="I0", af=None, sf=None, ff=None,
                                      morph=None):
    """{(IN) pour 𝓘, (IN) pour 𝓘', « id_E morphisme (E,𝓘)->(E,𝓘) »,
        « id_E morphisme (E,𝓘')->(E,𝓘') »}
        ⊢  plus_fine(E,𝓘,𝓘')  et  plus_fine(E,𝓘',𝓘).

    CŒUR de CST9 (unicité de l'initiale).  Deux structures initiales 𝓘, 𝓘' pour la
    MÊME famille (A_ι,𝒮_ι,f_ι) sont mutuellement « plus fine ».  Preuve (logique
    pure sur la structure de (IN)) :

      • (IN_𝓘) instanciée à (E'=E, 𝒮'=𝓘', g=id_E) :
          morph(E,𝓘',E,𝓘,id)  ⇔  (∀ι)(ι∈I ⇒ f_ι∘id morphisme de (E,𝓘')->(A_ι,𝒮_ι)).
      • (IN_𝓘') instanciée à (E'=E, 𝒮'=𝓘', g=id_E) :
          morph(E,𝓘',E,𝓘',id) ⇔  (∀ι)(ι∈I ⇒ f_ι∘id morphisme de (E,𝓘')->(A_ι,𝒮_ι)).
      Les MEMBRES DE DROITE sont LITTÉRALEMENT identiques (même famille, même g=id,
      même source (E,𝓘')).  Or « id_E morphisme (E,𝓘')->(E,𝓘') » est vrai (MO_III),
      donc par (IN_𝓘') le membre de droite est vrai, donc par (IN_𝓘) « id_E est un
      morphisme de (E,𝓘') dans (E,𝓘) » = plus_fine(E,𝓘',𝓘).

      Symétriquement (en échangeant 𝓘↔𝓘') on obtient plus_fine(E,𝓘,𝓘').

    Renvoie le théorème conditionnel ; ses hypothèses sont EXACTEMENT les 4 prémisses
    structurelles (les deux (IN) + les deux instances de MO_III), AUCUN axiome de
    théorie ajouté."""
    af, sf, ff, morph = _defaults(af, sf, ff, morph)
    ve, vi = _t(e), _t(i)
    sI, sJ = _t(struct_I), _t(struct_J)
    DE = E.diagonale(ve)

    def un_sens(sA, sB):
        """⊢ plus_fine(E, sB, sA) sous {(IN_sA),(IN_sB), id morph (E,sB)->(E,sB)}.

        Donne « id_E est morphisme de (E,sB) dans (E,sA) » (= plus_fine(E,sB,sA))."""
        inA = propriete_IN(ve, sA, vi, af, sf, ff, morph=morph)
        inB = propriete_IN(ve, sB, vi, af, sf, ff, morph=morph)
        hA, hB = N.assume(inA), N.assume(inB)
        # instancie les deux (IN) à E'=E, 𝒮'=sB, g=Δ_E
        eqA = instancie(instancie(instancie(hA, ve), sB), DE)  # morph(E,sB,E,sA,id) ⇔ RHS
        eqB = instancie(instancie(instancie(hB, ve), sB), DE)  # morph(E,sB,E,sB,id) ⇔ RHS
        # RHS identiques (même famille/source/g) ⇒ morph(...,sA,id) ⇔ morph(...,sB,id)
        chaine = equivalence_transitivite(eqA, equivalence_symetrie(eqB))
        # « id morphisme (E,sB)->(E,sB) » (MO_III) ⊢, via ⇐, « id morphisme (E,sB)->(E,sA) »
        idB = est_morphisme(ve, sB, ve, sB, DE, morph)
        h_idB = N.assume(idB)
        return N.modus_ponens(h_idB, equivalence_arriere(chaine))  # plus_fine(E,sB,sA)

    pf_JI = un_sens(sI, sJ)     # plus_fine(E, 𝓘', 𝓘)
    pf_IJ = un_sens(sJ, sI)     # plus_fine(E, 𝓘, 𝓘')
    return conjonction_intro(pf_IJ, pf_JI)


# @livre Ch.IV §2.3 Crit.CST9 | E IV.14 L.24-30 | PDF p.217
def cst9_unicite_initiale(e="E", struct_I="I", struct_J="J", i="I0",
                          af=None, sf=None, ff=None, morph=None):
    """CST9 — UNICITÉ de la structure initiale (forme complète, antisymétrie en
    hypothèse).

    {(IN_𝓘), (IN_𝓘'), id morph (E,𝓘)->(E,𝓘), id morph (E,𝓘')->(E,𝓘'),
     ANTISYM := (plus_fine(E,𝓘,𝓘') et plus_fine(E,𝓘',𝓘)) ⇒ 𝓘=𝓘'}
        ⊢  𝓘 = 𝓘'.

    Assemble `initiales_mutuellement_plus_fines` (qui produit la conjonction des
    deux « plus fine ») et l'antisymétrie de « moins/plus fine » (MO_III, IV.2.2 :
    « antisymétrique d'après (MO_III) ») fournie en hypothèse EXPLICITE.  Conclut
    l'égalité 𝓘 = 𝓘' (l'unicité de Bourbaki).  Rien postulé : ANTISYM est l'axiome-
    schéma MO_III instancié, prémisse du théorème."""
    sI, sJ = _t(struct_I), _t(struct_J)
    mut = initiales_mutuellement_plus_fines(e, struct_I, struct_J, i,
                                            af, sf, ff, morph)
    antisym = impl(mut.conclusion, egal(sI, sJ))   # (pf∧pf) ⇒ 𝓘=𝓘'
    h_anti = N.assume(antisym)
    return N.modus_ponens(mut, h_anti)             # ⊢ 𝓘 = 𝓘'


# ════════════════════════════════════════════════════════════════════════════
#  CST18 — UNICITÉ de la structure FINALE  (DUAL de CST9 via (FI))
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.IV §2.5 Crit.CST18 | E IV.19 L.20-25 | PDF p.222
def finales_mutuellement_plus_fines(e="E", struct_F="F", struct_G="G",
                                    i="I0", af=None, sf=None, gf=None,
                                    morph=None):
    """{(FI_𝓕), (FI_𝓕'), id morph (E,𝓕)->(E,𝓕), id morph (E,𝓕')->(E,𝓕')}
        ⊢  plus_fine(E,𝓕,𝓕')  et  plus_fine(E,𝓕',𝓕).

    DUAL de `initiales_mutuellement_plus_fines`.  (FI) instanciée à (E'=E, 𝒮'=l'autre
    structure, f=id_E) ; les membres de droite (∀ι)(f∘g_ι morphisme) coïncident, et
    « id morphisme » (MO_III) transporte par l'équivalence.  Renvoie la conjonction
    des deux « plus fine » des deux structures finales pour la MÊME famille."""
    af, sf, gf, morph = _defaults(af, sf, gf, morph)
    ve, vi = _t(e), _t(i)
    sF, sG = _t(struct_F), _t(struct_G)
    DE = E.diagonale(ve)

    def un_sens(sA, sB):
        """⊢ plus_fine(E, sA, sB) = « id morphisme (E,sA)->(E,sB) » sous
        {(FI_sA),(FI_sB), id morph (E,sB)->(E,sB)}.

        Pour (FI), la source du morphisme = la structure finale ; (FI_sA) à
        (E'=E,𝒮'=sB,f=id) donne morph(E,sA,E,sB,id) ⇔ RHS, (FI_sB) donne
        morph(E,sB,E,sB,id) ⇔ RHS (mêmes RHS), d'où la chaîne ; « id (E,sB)->(E,sB) »
        (MO_III) transporte par ⇐ vers morph(E,sA,E,sB,id) = plus_fine(E,sA,sB)."""
        fiA = propriete_FI(ve, sA, vi, af, sf, gf, morph=morph)
        fiB = propriete_FI(ve, sB, vi, af, sf, gf, morph=morph)
        hA, hB = N.assume(fiA), N.assume(fiB)
        # instancie (FI) à E'=E, 𝒮'=sB, f=Δ_E  (lhs = morph(source,E,sB,id))
        eqA = instancie(instancie(instancie(hA, ve), sB), DE)  # morph(E,sA,E,sB,id) ⇔ RHS
        eqB = instancie(instancie(instancie(hB, ve), sB), DE)  # morph(E,sB,E,sB,id) ⇔ RHS
        chaine = equivalence_transitivite(eqA, equivalence_symetrie(eqB))
        idB = est_morphisme(ve, sB, ve, sB, DE, morph)          # « id (E,sB)->(E,sB) » (MO_III)
        h_idB = N.assume(idB)
        return N.modus_ponens(h_idB, equivalence_arriere(chaine))  # plus_fine(E,sA,sB)

    pf_FG = un_sens(sF, sG)     # plus_fine(E, 𝓕, 𝓕')
    pf_GF = un_sens(sG, sF)     # plus_fine(E, 𝓕', 𝓕)
    return conjonction_intro(pf_FG, pf_GF)


# @livre Ch.IV §2.5 Crit.CST18 | E IV.19 L.20-25 | PDF p.222
def cst18_unicite_finale(e="E", struct_F="F", struct_G="G", i="I0",
                         af=None, sf=None, gf=None, morph=None):
    """CST18 — UNICITÉ de la structure finale.  DUAL de `cst9_unicite_initiale`.
    {(FI_𝓕),(FI_𝓕'), 2×(id morph), ANTISYM} ⊢ 𝓕 = 𝓕'."""
    sF, sG = _t(struct_F), _t(struct_G)
    mut = finales_mutuellement_plus_fines(e, struct_F, struct_G, i,
                                          af, sf, gf, morph)
    antisym = impl(mut.conclusion, egal(sF, sG))
    h_anti = N.assume(antisym)
    return N.modus_ponens(mut, h_anti)             # ⊢ 𝓕 = 𝓕'


# ════════════════════════════════════════════════════════════════════════════
#  TRANSPORT DE STRUCTURE préserve les morphismes  (IV.1.5 ; cœur CST4)
# ════════════════════════════════════════════════════════════════════════════
#
#  Énoncé (forme « catégorielle » du transport, niveau morphismes IV.2) : si
#    • h : (E,𝒮) -> (E',𝒮')  est un MORPHISME,
#    • f : (E',𝒮') -> (E'',𝒮'') est un MORPHISME,
#  alors f∘h : (E,𝒮) -> (E'',𝒮'') est un morphisme  (c'est (MO_II) — stabilité par
#  composition).  Lorsque f est un ISOMORPHISME, « transporter » un morphisme par f
#  revient à le composer ; on certifie ici le cœur (MO_II) sous forme paramétrée.
#
# @livre Ch.IV §2.1 Ax.- | E IV.11 L.28-31 | PDF p.214
def axiome_MO_II(e, s, ep, sp, epp, spp, f, g, morph=None):
    """(MO_II) instancié — formule « (morph(E,𝒮,E',𝒮',f) et morph(E',𝒮',E'',𝒮'',g))
    ⇒ morph(E,𝒮,E'',𝒮'', g∘f) »  (stabilité par composition, axiome-schéma IV.2.1).
    Prémisse EXPLICITE (jamais postulée vraie dans la théorie)."""
    if morph is None:
        morph = _morph_defaut()
    e, s, ep, sp, epp, spp, f, g = map(_t, (e, s, ep, sp, epp, spp, f, g))
    m1 = morph(e, s, ep, sp, f)
    m2 = morph(ep, sp, epp, spp, g)
    return impl(et(m1, m2), morph(e, s, epp, spp, E.composee(g, f)))


# @livre Ch.IV §1.5 Crit.CST4 | E IV.6 L.24-27 | PDF p.209
def transport_preserve_morphisme(e="E", s="S", ep="Ep", sp="Sp",
                                 epp="Epp", spp="Spp", f="f", g="g", morph=None):
    """{(MO_II) instancié, morph(E,𝒮,E',𝒮',f), morph(E',𝒮',E'',𝒮'',g)}
        ⊢  morph(E,𝒮,E'',𝒮'', g∘f).

    « Le transport (composition) préserve les morphismes » — cœur (MO_II) /
    composante de CST4 (composition d'isomorphismes : un iso est un morphisme dont
    le réciproque est un morphisme, MO_III ; la composée de deux morphismes est un
    morphisme, MO_II — d'où la composée de deux isos est un iso).  On certifie ici
    le palier décisif : sous (MO_II) et les deux morphismes en hypothèse, la composée
    est un morphisme.  Purement logique (modus ponens sur la conjonction des deux
    hypothèses de morphisme)."""
    if morph is None:
        morph = _morph_defaut()
    e, s, ep, sp, epp, spp, f, g = map(_t, (e, s, ep, sp, epp, spp, f, g))
    mo2 = axiome_MO_II(e, s, ep, sp, epp, spp, f, g, morph)
    h_mo2 = N.assume(mo2)
    h_f = N.assume(morph(e, s, ep, sp, f))
    h_g = N.assume(morph(ep, sp, epp, spp, g))
    conj = conjonction_intro(h_f, h_g)
    return N.modus_ponens(conj, h_mo2)         # morph(E,𝒮,E'',𝒮'', g∘f)


# @livre Ch.IV §1.5 Crit.CST4 | E IV.6 L.24-27 | PDF p.209
def cst4_compose_isos_morphisme_aller(e="E", s="S", ep="Ep", sp="Sp",
                                      epp="Epp", spp="Spp", f="f", g="g",
                                      morph=None):
    """CST4 (cœur, sens « aller ») : sous (MO_II) et « f, g morphismes », la composée
    g∘f est un morphisme de (E,𝒮) dans (E'',𝒮'').  (La partie ISOMORPHISME complète
    de CST4 — réciproque (g∘f)⁻¹=f⁻¹∘g⁻¹ aussi morphisme — exige (MO_II) appliqué aux
    réciproques + (MO_III) ; REPORTÉE, voir `reportes`.)  Alias documenté de
    `transport_preserve_morphisme`."""
    return transport_preserve_morphisme(e, s, ep, sp, epp, spp, f, g, morph)


# ════════════════════════════════════════════════════════════════════════════
#  CST5 — UNICITÉ du transport de structure
# ════════════════════════════════════════════════════════════════════════════
#
#  « Il existe sur E' une structure d'espèce Σ et UNE SEULE telle que (f) soit un
#    isomorphisme de (E,U) sur (E',·). »  La structure transportée est U' :=
#    ⟨f,Id⟩^S(U) (relation (4)).  L'UNICITÉ se ramène à : la condition « (f) est un
#    isomorphisme de (E,U) sur (E',V) » détermine V de façon fonctionnelle —
#    formellement, V est l'image de U par l'application bijective induite ⟨f,Id⟩^S,
#    donc deux V vérifiant (4) sont égaux.  Cœur logique : (4) est une ÉGALITÉ
#    V = ⟨f,Id⟩^S(U), d'où l'unicité par transitivité de =.
#
# @livre Ch.IV §1.5 Def.- | E IV.6 L.11-11 | PDF p.209
def relation_transport_iso(e, u, ep, v, f, schema="S"):
    """Relation (4) de l'isomorphisme (IV.1.5) : « (f) est un isomorphisme de (E,U)
    sur (E',V) » := V = ⟨f, Id⟩^S(U)  — l'extension canonique de schéma S appliquée à
    U vaut V.  ⟨f,Id⟩^S(U) est représenté par le terme `extension_echelon(S,f,U)`."""
    eu, vv, vf = _t(u), _t(v), _t(f)
    transporte = app("extension_echelon", _t(schema), vf, eu)   # ⟨f,Id⟩^S(U)
    return egal(vv, transporte)


# @livre Ch.IV §1.5 Crit.CST5 | E IV.6 L.36-39 | PDF p.209
def cst5_unicite_transport(e="E", u="U", ep="Ep", v="V", v2="V2", f="f",
                           schema="S"):
    """CST5 (UNICITÉ du transport) — cœur logique.

    {  (V  = ⟨f,Id⟩^S(U)),   (V' = ⟨f,Id⟩^S(U))  }   ⊢   V = V'.

    Deux structures V, V' sur E' transportées de U par le MÊME isomorphisme f
    coïncident.  Preuve : chaque relation (4) AFFIRME une égalité au transporté
    commun ⟨f,Id⟩^S(U) ; par symétrie et transitivité de =, V = V'.  C'est l'unicité
    de CST5 (l'EXISTENCE — que ⟨f,Id⟩^S(U) vérifie bien R, via transportabilité — est
    REPORTÉE).  Purement logique sur l'égalité (s6 / réflexivité du noyau)."""
    eu, vv, vv2, vf = _t(u), _t(v), _t(v2), _t(f)
    transporte = app("extension_echelon", _t(schema), vf, eu)   # ⟨f,Id⟩^S(U)
    rel_V = egal(vv, transporte)        # (4) pour V
    rel_V2 = egal(vv2, transporte)      # (4) pour V'
    h1, h2 = N.assume(rel_V), N.assume(rel_V2)
    # V = T  et  V' = T  ⊢  V = V'  via s6 : (V=T) ⇒ ((V|x)(x=V') ⇔ (T|x)(x=V'))
    # plus simple : transitivité V = T = V'  ; on construit T = V' depuis V' = T (sym)
    x = "x_cst5"
    # de h2 : V' = T  ;  s6(V', T, x, x=V')  donne  (V'=T) ⇒ ((V'=V') ⇔ (T=V'))
    s6_sym = N.s6(vv2, transporte, x, egal(var(x), vv2))
    eqv = N.modus_ponens(h2, s6_sym)                    # (V'=V') ⇔ (T=V')
    refl_V2 = N.reflexivite(vv2)                        # V' = V'
    T_eq_V2 = N.modus_ponens(refl_V2, equivalence_avant(eqv))   # T = V'
    # de h1 : V = T ; s6(V, T, y, y=V') : (V=T) ⇒ ((V=V') ⇔ (T=V'))
    y = "y_cst5"
    s6_2 = N.s6(vv, transporte, y, egal(var(y), vv2))
    eqv2 = N.modus_ponens(h1, s6_2)                     # (V=V') ⇔ (T=V')
    return N.modus_ponens(T_eq_V2, equivalence_arriere(eqv2))   # V = V'


# ════════════════════════════════════════════════════════════════════════════
#  CST22 / CST23 — UNICITÉ de la solution du problème d'application universelle
# ════════════════════════════════════════════════════════════════════════════
#
#  (AU_II′) « deux morphismes de F_E dans F qui coïncident dans φ_E(E) sont égaux »
#  donne l'UNICITÉ.  Cœur logique : sous (AU_I′) (existence d'un factorisant) et
#  (AU_II′) (unicité ponctuelle), le morphisme factorisant d'une α-application φ est
#  UNIQUE — ce qui, appliqué croisé à deux solutions, donne l'unicité à isomorphisme
#  unique près (CST8).  Ici on certifie le palier : (AU_I′)+(AU_II′) ⇒ existence-
#  unique du factorisant pour φ (déjà fait dans applications.py), et on AJOUTE le
#  cœur d'unicité CROISÉE de deux solutions.
#
def _morph(morph):
    return morph if morph is not None else _morph_defaut()


# @livre Ch.IV §3.2 Crit.CST22 | E IV.24 L.7-9 | PDF p.227
def factorisation_unique_des_solutions(fe="FE", se="SE", phi_e="phiE",
                                       fep="FEp", sep="SEp", phi_ep="phiEp",
                                       f1="f1", f2="f2", morph=None):
    """CŒUR de l'unicité (CST22/CST23 ⇒ CST8).

    Hypothèses EXPLICITES (les conditions (AU_I′) appliquées CROISÉ aux deux
    solutions (F_E,φ_E) et (F_E',φ_E')) :
      • H1 := morph(F_E, S_E, F_E', S_E', f₁)  et  φ_E' = f₁∘φ_E
              (f₁ factorise φ_E' à travers φ_E — (AU_I′) pour la solution F_E) ;
      • H2 := morph(F_E', S_E', F_E, S_E, f₂)  et  φ_E = f₂∘φ_E'
              (f₂ factorise φ_E à travers φ_E' — (AU_I′) pour la solution F_E') ;
      • ANTISYM := (H1 et H2) ⇒ (f₂∘f₁ = Id_{F_E}  et  f₁∘f₂ = Id_{F_E'})
              — la conclusion d'unicité de (AU_II′) appliquée à F_E (les deux
                morphismes f₂∘f₁ et Id coïncident sur φ_E(E)) et à F_E'.
        ⊢  f₂∘f₁ = Id_{F_E}  et  f₁∘f₂ = Id_{F_E'}.

    C'est exactement le contenu de CST8 (« f₁ est un isomorphisme de F_E sur F_E' et
    f₂ son réciproque »).  Le cœur logique est l'application de l'unicité (AU_II′),
    fournie ici sous forme d'hypothèse ANTISYM (instance de (AU_II′)) ; on conclut
    l'inversibilité croisée par modus ponens.  Rien postulé : ANTISYM est (AU_II′)
    instancié, prémisse du théorème ; l'EXISTENCE même de f₁,f₂ (AU_I′) est aussi en
    hypothèse."""
    morph = _morph(morph)
    fe, se, phi_e = map(_t, (fe, se, phi_e))
    fep, sep, phi_ep = map(_t, (fep, sep, phi_ep))
    vf1, vf2 = _t(f1), _t(f2)
    h1 = et(morph(fe, se, fep, sep, vf1), egal(phi_ep, E.composee(vf1, phi_e)))
    h2 = et(morph(fep, sep, fe, se, vf2), egal(phi_e, E.composee(vf2, phi_ep)))
    inv1 = egal(E.composee(vf2, vf1), E.diagonale(fe))      # f₂∘f₁ = Id_{F_E}
    inv2 = egal(E.composee(vf1, vf2), E.diagonale(fep))     # f₁∘f₂ = Id_{F_E'}
    antisym = impl(et(h1, h2), et(inv1, inv2))
    th1, th2, th_a = N.assume(h1), N.assume(h2), N.assume(antisym)
    conj = conjonction_intro(th1, th2)
    return N.modus_ponens(conj, th_a)          # ⊢ (f₂∘f₁=Id et f₁∘f₂=Id)


def _contraposition_injection_ponctuelle(e="E", phi_e="phiE", x="x", y="y"):
    """HELPER LOGIQUE TRIVIAL (PAS CST23) — pure contraposition.  ⚠ Ce lemme n'est
    PAS le critère CST23 de Bourbaki : il établit seulement l'équivalence logique
    contraposée « (¬(x=y)⇒φx≠φy) ⇒ ((φx=φy)⇒x=y) », sans le contenu mathématique de
    CST23 (∃ α-application séparante + universalité (AU)), qui reste REPORTÉ.

      {  (φ_E(x)=φ_E(y)) ⇒ x=y  ⟸  ¬(x=y) ⇒ ¬(φ_E(x)=φ_E(y))  }
    — i.e. l'équivalence entre « injective » (x,y ⇒ ...) et « sépare » (contraposée).
    Ici : ⊢ (¬(x=y) ⇒ ¬(φ_E(x)=φ_E(y)))  ⇒  ((φ_E(x)=φ_E(y)) ⇒ x=y)  (CONTRAPOSITION
    pure).  C'est l'aller-retour logique de CST23 (« il faut et il suffit ») au niveau
    ponctuel ; le saut « φ séparante ⇔ φ injective » s'en déduit par ∀-introduction.
    L'EXISTENCE de l'α-application séparante (cas où la solution n'est pas injective)
    est REPORTÉE (construction, CST22).  Purement logique (contraposition + dne)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import contraposition, dne
    vphi, vx, vy = _t(phi_e), _t(x), _t(y)
    sep = non(egal(E.valeur(vphi, vx), E.valeur(vphi, vy)))   # φ_E(x) ≠ φ_E(y)
    diff = non(egal(vx, vy))                                  # x ≠ y
    # hypothèse : ¬(x=y) ⇒ ¬(φx=φy)  (séparation ponctuelle)
    h = N.assume(impl(diff, sep))
    # contraposition : ¬¬(φx=φy) ⇒ ¬¬(x=y) ; compose avec dne/dni → (φx=φy) ⇒ (x=y)
    contra = contraposition(h)            # ¬sep ⇒ ¬diff  = ¬¬(φx=φy) ⇒ ¬¬(x=y)
    eq_phi = egal(E.valeur(vphi, vx), E.valeur(vphi, vy))
    # (φx=φy) ⇒ ¬¬(φx=φy)  [dni]  puis contra  puis ¬¬(x=y) ⇒ (x=y) [dne]
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import dni
    step1 = syllogisme(dni(eq_phi), contra)        # (φx=φy) ⇒ ¬¬(x=y)
    step2 = syllogisme(step1, dne(egal(vx, vy)))   # (φx=φy) ⇒ (x=y)
    return N.loi_deduction(impl(diff, sep), step2)  # ⊢ (séparation pt) ⇒ (injection pt)


__all__ = [
    "id_est_morphisme",
    # CST9 / initiale
    "initiales_mutuellement_plus_fines", "cst9_unicite_initiale",
    # CST18 / finale
    "finales_mutuellement_plus_fines", "cst18_unicite_finale",
    # transport / CST4
    "axiome_MO_II", "transport_preserve_morphisme", "cst4_compose_isos_morphisme_aller",
    # CST5
    "relation_transport_iso", "cst5_unicite_transport",
    # CST22 (CST23 vrai = REPORTE : separation existentielle + universalite)
    "factorisation_unique_des_solutions",
]
