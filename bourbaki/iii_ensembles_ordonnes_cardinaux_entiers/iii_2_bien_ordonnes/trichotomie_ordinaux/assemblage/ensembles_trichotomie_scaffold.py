"""§III.2 — Théorème 3 (TRICHOTOMIE des ordinaux) : SCAFFOLDING de l'iso MAXIMAL h.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  Étape (d) du blueprint DESIGN_trichotomie_III2.md : construction de
l'ISOMORPHISME MAXIMAL h entre un segment de E et un segment de F, comme UNION
(recollement) des isomorphismes de couples de segments isomorphes.  C'est le cœur
du Théorème 3 (E.III.2.6).  La cible posée (ensembles_ordinaux.trichotomie_ordinaux)
est le OU d'existence ; cet h en est le témoin maximal.

STRATÉGIE FIDÈLE BOURBAKI (= union des couples de segments isomorphes) :
    Φ = { (S,T) | S segment de E, T segment de F, S ≅ T (iso d'ordre) }.
    Par Cor1+unicité (c), à chaque tel couple correspond UN graphe d'iso h_{S,T} ;
    h := UNION de tous ces graphes.  Par compatibilité + domaines emboîtés, h est
    fonctionnel et injectif (un iso).  dom(h)=S₀ segment de E, img(h)=T₀ segment de F.
    MAXIMALITÉ ⇒ S₀=E ou T₀=F ⇒ la trichotomie.

CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ STRUCTURE INCONDITIONNELLE (theorie=22) :
     • h(E,R,F,Rp) : TERME OPAQUE de l'union des graphes d'iso de segments.
       Collectivisant (S8 sélection dans E×F + A1 unicité), motif `axiome_D`.
       Caractérisé par AXIOME_H dans une THÉORIE DÉDIÉE (theorie_h), JAMAIS dans
       theorie_ensembles (intangible = 22).
     • axiome_h / theorie_h / h_membre : caractérisation de membre de h, instance.
     • h_inclus_produit : h ⊂ E×F  (h est un graphe de E vers F).   INCONDITIONNEL.
     • h_membre_donne_temoin : (u,v)∈h ⇒ (∃ segment S,T, iso φ) témoignant.  INCOND.
     • couple_iso_dans_h : (S seg E, T seg F, φ:S≅T, u∈S) ⇒ (u, φ(u)) ∈ h.  INCOND.
       (CHAQUE graphe d'iso de segments est INCLUS dans h : h est bien leur union.)

  ⚠️ TRACTABLES sous HYPOTHÈSES de COHÉRENCE explicites (la « compatibilité » des
     isos, contenu de l'UNICITÉ (c) + Lemme 1 §III.2 — reportés comme hypothèses) :
     • h_fonctionnel_sous_compatibilite : sous (compat) ⊢ est_fonctionnel(h).
     • h_injectif_sous_compatibilite    : sous (compat, inj) ⊢ injective_dans(h, dom h).
     Ces hypothèses encapsulent EXACTEMENT le verrou dur (unicité de l'iso de chaque
     couple ⇒ recollement cohérent), formulé via l'infra recollement binaire
     généralisée (ensembles_recollement_bijection).  JAMAIS postulées : explicites.

  ⚠️ REPORTÉ — le cœur dur (maximalité ⇒ S₀=E ou T₀=F) : énoncé conditionnel posé
     dans ensembles_trichotomie_scaffold_maximalite.py (hypothèses explicites).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : h est un TERME défini par un
axiome de SÉLECTION (S8) dans E×F, comme D (Knaster–Tarski), le produit, l'image.
NON vacueux : couple_iso_dans_h / h_inclus_produit ont une conclusion ≠ hypothèses.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, app, tau, egal, et, ou, non, impl, equiv, appartient,
    existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, projection_gauche,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ════════════════════════════════════════════════════════════════════════════
#  h(E,R,F,Rp) = UNION des graphes d'iso de couples de segments isomorphes.
#  TERME OPAQUE collectivisant (S8 sélection dans E×F + A1 unicité), motif axiome_D.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-33 | PDF p.124  (démonstration du Th. 3 : ensemble des isos de segments, inductif, élément maximal u0 — ici h = union des graphes)
def h_iso_max(E_set="E", R="R", F_set="F", Rp="Rp"):
    """h := { (u,v) ∈ E×F | (∃S)(∃T)(∃φ)( S segment de E, T segment de F,
                              φ:S≅T iso d'ordre, u∈S, v=φ(u) ) }.

    L'ISOMORPHISME MAXIMAL (étape d du Th3) : union de tous les graphes d'iso de
    segments.  Terme opaque, caractérisé par AXIOME_H (theorie_h dédiée)."""
    return E.app("h_iso_max", _t(E_set), _t(R), _t(F_set), _t(Rp))


def _h_parts(E_set, R, F_set, Rp, u, v, S="S", T="T", phi="phi"):
    """Les DEUX conjoints du corps caractérisant (u,v)∈h :

        dans_produit := (u∈E et v∈F)
        temoin       := (∃S)(∃T)(∃φ)( est_segment(S,R,E) et est_segment(T,Rp,F)
                          et est_isomorphisme_ordre(φ,S,T,R,Rp) et u∈S et v=valeur(φ,u)
                          et est_fonctionnel(φ) et dom(φ)=S et φ⊂S×T ).

    ⚠️ ARCHITECTURE « φ APPLICATION » (func/dom/graphe) : depuis la trichotomie
    fonctionne avec h = UNION de GRAPHES d'isos de segments enregistrés comme
    APPLICATIONS (le témoin φ porte non seulement iso(φ,S,T) mais aussi sa structure
    de graphe fonctionnel : est_fonctionnel(φ), dom(φ)=S, φ⊂S×T).  Ces 3 conjoints
    SUPPLÉMENTAIRES alimentent la PRÉMISSE-APPLICATIONS consommée par
    coincidence_univ_app (cf. ensembles_fusion_app / coincidence_point_app).  La
    CONVENTION du dernier conjoint suit EXACTEMENT coincidence_univ_app :
    inclus(φ, E.produit(S,T)).

    On les RETOURNE séparément (et NON via .sous, car « et » est encodé en ¬(¬∨¬))
    pour pouvoir les passer à projection_gauche / projection_droite."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vu, vv = _t(u), _t(v)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = var(S), var(T), var(phi)
    dans_produit = et(appartient(vu, vE), appartient(vv, vF))
    coeur5 = et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw")),
        appartient(vu, vS)),
        egal(vv, E.valeur(vphi, vu)))
    # ── 3 conjoints « φ APPLICATION » appendus AU NIVEAU EXTERNE (les 5 d'abord) ──
    coeur = et(et(et(coeur5,
        E.est_fonctionnel(vphi)),
        egal(E.dom(vphi), vS)),
        inclus(vphi, E.produit(vS, vT)))
    temoin = existe(S, existe(T, existe(phi, coeur)))
    return dans_produit, temoin


def _corps_h(E_set, R, F_set, Rp, u, v, S="S", T="T", phi="phi"):
    """Le corps caractérisant (u,v)∈h :  dans_produit et temoin  (cf. _h_parts)."""
    dans_produit, temoin = _h_parts(E_set, R, F_set, Rp, u, v, S, T, phi)
    return et(dans_produit, temoin)


def axiome_h(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v"):
    """⊢-schéma (∀E)(∀R)(∀F)(∀Rp)(∀u)(∀v)( (u,v)∈h ⇔ corps_h ).

    Axiome DÉFINITIONNEL de l'union des graphes d'iso de segments (légitime S8 :
    sélection dans E×F ; A1 : unicité).  Motif `axiome_D` (Knaster–Tarski) /
    `axiome_A` (lemme 4).  theorie_ensembles INCHANGÉE (= 22)."""
    vE, vR, vF, vRp = var(E_set), var(R), var(F_set), var(Rp)
    vu, vv = var(u), var(v)
    h = h_iso_max(vE, vR, vF, vRp)
    return pourtout(E_set, pourtout(R, pourtout(F_set, pourtout(Rp,
        pourtout(u, pourtout(v,
            equiv(appartient(E.couple(vu, vv), h),
                  _corps_h(vE, vR, vF, vRp, vu, vv))))))))


def theorie_h(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v"):
    """Théorie dédiée ne portant QUE l'axiome de h (motif theorie_D / theorie_A).

    theorie_ensembles() reste = 22 ; h est introduit hors d'elle, exactement comme
    D (Knaster–Tarski), le mauvais ensemble A (lemme 4), segment_extremite."""
    return N.Theorie("h-iso-maximal-trichotomie", [axiome_h(E_set, R, F_set, Rp, u, v)])


def h_membre(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v"):
    """⊢ ( (u,v)∈h ) ⇔ corps_h.   (axiome de h instancié aux TERMES.)"""
    ax = N.axiome(theorie_h(), axiome_h())
    return instancie(instancie(instancie(instancie(instancie(instancie(
        ax, _t(E_set)), _t(R)), _t(F_set)), _t(Rp)), _t(u)), _t(v))


# ════════════════════════════════════════════════════════════════════════════
#  h_inclus_produit : h ⊂ E×F  —  h est un graphe de E vers F.  INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def h_inclus_produit(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v"):
    """⊢ (∀u)(∀v)( (u,v)∈h ⇒ (u∈E et v∈F) ).

    h ne contient que des couples de E×F (projection gauche du corps de h).
    INCONDITIONNEL, theorie=22.  (Forme « par couples » de h ⊂ E×F, sans dépendre
    d'un terme produit explicite.)"""
    vu, vv = var(u), var(v)
    eq = h_membre(E_set, R, F_set, Rp, vu, vv)           # (u,v)∈h ⇔ corps
    dans_produit, temoin = _h_parts(_t(E_set), _t(R), _t(F_set), _t(Rp), vu, vv)
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_gauche(dans_produit, temoin))
    return N.generalisation(u, N.generalisation(v, z_imp))


def h_inclus_produit_cible(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v"):
    """ÉNONCÉ-cible (test miroir) de h_inclus_produit."""
    vu, vv = var(u), var(v)
    h = h_iso_max(E_set, R, F_set, Rp)
    return pourtout(u, pourtout(v,
        impl(appartient(E.couple(vu, vv), h),
             et(appartient(vu, _t(E_set)), appartient(vv, _t(F_set))))))


# ════════════════════════════════════════════════════════════════════════════
#  h_membre_donne_temoin : (u,v)∈h ⇒ témoin (segment S, segment T, iso φ).  INCOND.
# ════════════════════════════════════════════════════════════════════════════
def h_membre_donne_temoin(E_set="E", R="R", F_set="F", Rp="Rp", u="u", v="v",
                          S="S", T="T", phi="phi"):
    """⊢ (∀u)(∀v)( (u,v)∈h ⇒ (∃S)(∃T)(∃φ)( S segment de E, T segment de F,
            φ:S≅T iso, u∈S, v=φ(u) ) ).

    De l'appartenance à h on EXTRAIT le couple de segments isomorphes témoin
    (projection droite du corps de h).  INCONDITIONNEL, theorie=22.  C'est la
    réciproque (par couples) de couple_iso_dans_h."""
    vu, vv = var(u), var(v)
    eq = h_membre(E_set, R, F_set, Rp, vu, vv)
    dans_produit, temoin = _h_parts(_t(E_set), _t(R), _t(F_set), _t(Rp),
                                    vu, vv, S, T, phi)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import projection_droite
    z_imp = syllogisme(equivalence_avant(eq),
                       projection_droite(dans_produit, temoin))
    return N.generalisation(u, N.generalisation(v, z_imp))


def h_membre_donne_temoin_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                u="u", v="v", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) de h_membre_donne_temoin."""
    vu, vv = var(u), var(v)
    h = h_iso_max(E_set, R, F_set, Rp)
    _, temoin = _h_parts(_t(E_set), _t(R), _t(F_set), _t(Rp), vu, vv, S, T, phi)
    return pourtout(u, pourtout(v,
        impl(appartient(E.couple(vu, vv), h), temoin)))


# ════════════════════════════════════════════════════════════════════════════
#  couple_iso_dans_h : CHAQUE graphe d'iso de segments est INCLUS dans h.  INCOND.
#  ( h est bien l'UNION des graphes d'iso : la brique « ⊃ » du recollement. )
# ════════════════════════════════════════════════════════════════════════════
def couple_iso_dans_h(E_set="E", R="R", F_set="F", Rp="Rp",
                      S="S", T="T", phi="phi", u="u", v="v"):
    """⊢ { est_segment(S,R,E), est_segment(T,Rp,F), est_isomorphisme_ordre(φ,S,T,R,Rp),
           u∈S, u∈E, v∈F, v=φ(u),
           est_fonctionnel(φ), dom(φ)=S, φ⊂S×T }
            ⊢ ( u, v ) ∈ h.

    🎯 CHAQUE couple (u,v) d'un iso φ:S≅T de segments (v=φ(u)) APPARTIENT à h : h est
    bien l'UNION (recollement) de tous les graphes d'iso de couples de segments
    isomorphes (étape d.3 du blueprint).  Sous les hypothèses STRUCTURELLES (S,T
    segments, φ iso, u dans le segment, v dans le produit, v=φ(u)) PLUS la structure
    « φ APPLICATION » (est_fonctionnel(φ), dom(φ)=S, φ⊂S×T — l'iso enregistré comme
    GRAPHE fonctionnel, cf. _h_parts).  INCONDITIONNEL, theorie=22.

    ⚠️ ARCHITECTURE func/dom : depuis le renforcement de _h_parts, le témoin de h
    porte 8 conjoints (les 5 originaux + func + dom + graphe).  couple_iso_dans_h
    requiert donc 3 hypothèses STRUCTURELLES de plus (func/dom/graphe de φ) — les
    données « φ application » du contexte, fidèles à h = union de GRAPHES d'isos.

    ⚠️ v est pris GÉNÉRIQUE (variable) avec l'hypothèse v=φ(u) explicite : c'est
    INDISPENSABLE pour éviter la capture du liant ∃φ par le terme φ(u)=τy((u,y)∈φ)
    (qui mentionne φ).  Avec v générique, h_membre(…,u,v) n'est PAS α-renommé.

    NON vacueux : la conclusion (u,v)∈h n'est aucune hypothèse ; le corps de h
    (∃S∃T∃φ …) est réellement construit à partir des témoins fournis."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi, vu, vv = _t(S), _t(T), _t(phi), _t(u), _t(v)
    fu = E.valeur(vphi, vu)                               # φ(u) — TERME

    Hseg_S = N.assume(E.est_segment(vS, Rf, vE))
    Hseg_T = N.assume(E.est_segment(vT, Rpf, vF))
    Hiso = N.assume(V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw"))
    Hu_S = N.assume(appartient(vu, vS))
    Hu_E = N.assume(appartient(vu, vE))                   # u∈E
    Hv_F = N.assume(appartient(vv, vF))                   # v∈F
    Hveq = N.assume(egal(vv, fu))                         # v=φ(u)
    # ── 3 hypothèses « φ APPLICATION » (func/dom/graphe) ──────────────────────────
    Hfunc = N.assume(E.est_fonctionnel(vphi))            # est_fonctionnel(φ)
    Hdom = N.assume(egal(E.dom(vphi), vS))               # dom(φ)=S
    Hgraph = N.assume(inclus(vphi, E.produit(vS, vT)))   # φ⊂S×T

    # cœur(σ,τ,p) := segments + iso + u∈σ + (v = p(u)) + func + dom + graphe, paramétré
    # par les noms à ré-existentialiser, EXACTEMENT comme dans _h_parts (v GÉNÉRIQUE).
    def coeur(sS, sT, sphi):
        coeur5 = et(et(et(et(
            E.est_segment(sS, Rf, vE),
            E.est_segment(sT, Rpf, vF)),
            V.est_isomorphisme_ordre(sphi, sS, sT, Rf, Rpf, "px", "pw")),
            appartient(vu, sS)),
            egal(vv, E.valeur(sphi, vu)))
        return et(et(et(coeur5,
            E.est_fonctionnel(sphi)),
            egal(E.dom(sphi), sS)),
            inclus(sphi, E.produit(sS, sT)))

    # preuve du cœur aux TÉMOINS (S,T,φ) : 5 conjoints originaux + func + dom + graphe.
    preuve_coeur5 = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(Hseg_S, Hseg_T), Hiso), Hu_S), Hveq)
    preuve_coeur = conjonction_intro(conjonction_intro(conjonction_intro(
        preuve_coeur5, Hfunc), Hdom), Hgraph)

    # ── introduction des 3 existentiels (bottom-up), bodies = ceux de _h_parts ──
    body_phi = coeur(vS, vT, var(phi))                    # phi libre, S,T = témoins
    ex_phi = N.modus_ponens(preuve_coeur, N.s5(body_phi, vphi, phi))   # (∃φ)coeur
    body_T = existe(phi, coeur(vS, var(T), var(phi)))     # T libre ; (∃φ)…
    ex_T = N.modus_ponens(ex_phi, N.s5(body_T, vT, T))    # (∃T)(∃φ)coeur
    body_S = existe(T, existe(phi, coeur(var(S), var(T), var(phi))))   # S libre
    ex_S = N.modus_ponens(ex_T, N.s5(body_S, vS, S))      # (∃S)(∃T)(∃φ)coeur

    # corps complet du membre de h : (u∈E et v∈F) et témoin
    corps = conjonction_intro(conjonction_intro(Hu_E, Hv_F), ex_S)
    # (u,v) ∈ h  via l'axiome de h (sens arrière)
    return N.modus_ponens(corps, equivalence_arriere(
        h_membre(E_set, R, F_set, Rp, vu, vv)))


def couple_iso_dans_h_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                            S="S", T="T", phi="phi", u="u", v="v"):
    """ÉNONCÉ-cible (test miroir) de couple_iso_dans_h :  ( u, v ) ∈ h."""
    vu, vv = _t(u), _t(v)
    h = h_iso_max(E_set, R, F_set, Rp)
    return appartient(E.couple(vu, vv), h)


__all__ = [
    "h_iso_max", "axiome_h", "theorie_h", "h_membre",
    "h_inclus_produit", "h_inclus_produit_cible",
    "h_membre_donne_temoin", "h_membre_donne_temoin_cible",
    "couple_iso_dans_h", "couple_iso_dans_h_cible",
]
