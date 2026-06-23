"""§III.2 — Théorème 3 (TRICHOTOMIE) : PONT « valeur d'un iso de segments dans F ».

────────────────────────────────────────────────────────────────────────────────
RÔLE.  DÉCHARGE le maillon (iii) « val_dans_F » du HARD RÉSIDU de la trichotomie
(cf. n-bien-ordre-route.md, DESIGN_trichotomie_III2.md).  La construction de l'iso
MAXIMAL h (ensembles_trichotomie_scaffold) a besoin, pour clore l'INITIALITÉ de
dom(h) (ensembles_trichotomie_dom_segment.dom_h_initial_sous_val), du fait de
CODOMAINE suivant : pour un iso de segments φ : S ≅ T (S segment de E, T segment de
F) et p ∈ S, on a φ(p) ∈ F.

ensembles_trichotomie_dom_segment prenait CE fait en HYPOTHÈSE OPAQUE val_dans_F
(« valeur(φ,p) ∈ F » postulé universellement).  Ce module le DÉRIVE à partir de la
STRUCTURE DE GRAPHE de φ et du fait que T est un segment de F :

    φ(p) ∈ T     (T = but de l'application φ : S → T, par valeur_dans_codomaine)
    T ⊂ F        (T segment de F ⇒ T ⊂ F, projection gauche de est_segment)
    ⇒ φ(p) ∈ F.

────────────────────────────────────────────────────────────────────────────────
LE MAILLON MANQUANT, RENDU EXPLICITE ET CLEAN.

est_isomorphisme_ordre(φ,S,T,R,Rp) PORTE est_bijective(φ,S,T) (E.III.1.3), mais
est_bijective est défini (ensembles_abrege.est_bijective) via valeur(φ,·) / image(φ,S)
SANS exposer la STRUCTURE DE GRAPHE (φ ⊂ S×T, dom φ = S) qu'exige
valeur_dans_codomaine (le pont graphe §II.3.4, déjà CLOS).  On PREND donc cette
structure de graphe en HYPOTHÈSES EXPLICITES PROPRES — φ ⊂ S×T et dom φ = S —, qui
sont VRAIES pour le graphe d'une application S → T mais que le prédicat
est_bijective ne porte pas littéralement.  RIEN n'est postulé : φ(p)∈F est DÉRIVÉ.

Hypothèses du pont (toutes des FORMULES de structure, jamais un théorème) :
    • φ ⊂ S×T            (structure de graphe : φ est un graphe dans S×T)
    • dom φ = S          (φ est total sur S — c'est l'application S → T)
    • p ∈ S              (p dans le segment domaine)
    • est_segment(T,Rp,F) (T est un segment de F ⇒ T ⊂ F)

Conclusion : valeur(φ,p) ∈ F.

C'est STRICTEMENT MOINS conditionnel que val_dans_F (qui postulait directement la
conclusion ∈ F) : ici la conclusion est DÉRIVÉE des seules hypothèses de structure.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ⚠️ CONDITIONNEL aux hypothèses de STRUCTURE DE GRAPHE (clean, explicites) :
     • valeur_iso_dans_T   : {φ⊂S×T, dom φ=S, p∈S}              ⊢ valeur(φ,p) ∈ T.
     • valeur_iso_dans_F   : {φ⊂S×T, dom φ=S, p∈S, seg(T,Rp,F)} ⊢ valeur(φ,p) ∈ F.
       (= le maillon de val_dans_F, DÉRIVÉ et non plus postulé.)

  • val_dans_F_depuis_structure : la version UNIVERSELLEMENT QUANTIFIÉE
       (∀p)(∀S)(∀T)(∀φ)( STRUCT(p,S,T,φ) ⇒ valeur(φ,p) ∈ F )
    où STRUCT REMPLACE la prémisse opaque de val_dans_F par les hypothèses de
    structure de graphe (+ T segment de F).  Conclue à partir des hypothèses de
    structure UNIQUEMENT (pas de val_dans_F).  Permet de DÉCHARGER le codomaine de
    dom_h_initial_sous_val dès que le scaffold expose la structure de graphe des isos
    témoins.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout DÉRIVE du pont graphe
CLOS valeur_dans_codomaine (§II.3.4), de est_segment (Déf. 2, E.III.2.1) et de
l'inclusion (instanciation de T ⊂ F).  NON vacueux : la conclusion valeur(φ,p)∈F
n'est aucune hypothèse (les hypothèses portent sur φ⊂S×T, dom φ=S, p∈S, T segment).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, appartient, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_valeur_codomaine import valeur_dans_codomaine


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ════════════════════════════════════════════════════════════════════════════
#  (1)  valeur_iso_dans_T :  φ(p) ∈ T   — depuis la structure de graphe seule.
# ════════════════════════════════════════════════════════════════════════════
def valeur_iso_dans_T(phi="phi", S="S", T="T", p="pt"):
    """{ φ ⊂ S×T, dom φ = S, p ∈ S } ⊢ valeur(φ, p) ∈ T.

    C'est EXACTEMENT le pont graphe §II.3.4 (valeur_dans_codomaine, CLOS) appliqué
    au graphe φ de domaine S et de but T : « la valeur d'un graphe fonctionnel total
    de domaine S dans son but T appartient à T ».  CONDITIONNEL aux 3 hypothèses de
    structure (φ⊂S×T, dom φ=S, p∈S) — les MÊMES que valeur_dans_codomaine.
    theorie=22, rien postulé, NON vacueux (φ(p)∈T ∉ hypothèses).

    ⚠️ POINT par DÉFAUT « pt » (≠ p, q) : valeur_dans_codomaine appelle
    couple_dans_produit_ssi qui LIE en interne « p » et « q » ; un point nommé « p »
    y serait capturé (existe_vacuous échoue).  « pt » évite toute collision."""
    vphi, vS, vT, vp = _t(phi), _t(S), _t(T), _t(p)
    return valeur_dans_codomaine(vphi, vS, vT, vp)   # {φ⊂S×T, dom φ=S, p∈S} ⊢ φ(p)∈T


def valeur_iso_dans_T_cible(phi="phi", p="pt", T="T"):
    """ÉNONCÉ-cible (test miroir) : valeur(φ,p) ∈ T."""
    return appartient(E.valeur(_t(phi), _t(p)), _t(T))


# ════════════════════════════════════════════════════════════════════════════
#  (2)  valeur_iso_dans_F :  φ(p) ∈ F   — le maillon de val_dans_F, DÉRIVÉ.
# ════════════════════════════════════════════════════════════════════════════
def valeur_iso_dans_F(phi="phi", S="S", T="T", F_set="F", Rp="Rp", p="pt"):
    """{ φ ⊂ S×T, dom φ = S, p ∈ S, est_segment(T,Rp,F) } ⊢ valeur(φ, p) ∈ F.

    DÉRIVE le fait de codomaine que ensembles_trichotomie_dom_segment postulait via
    val_dans_F.  PREUVE :
        valeur(φ,p) ∈ T               [valeur_iso_dans_T : φ⊂S×T, dom φ=S, p∈S]
        est_segment(T,Rp,F) ⇒ T ⊂ F   [projection gauche de est_segment, Déf. 2]
        T ⊂ F, valeur(φ,p)∈T ⇒ valeur(φ,p)∈F   [instanciation de l'inclusion]
        ⇒ valeur(φ,p) ∈ F.
    CONDITIONNEL aux hypothèses de STRUCTURE (φ⊂S×T, dom φ=S, p∈S) + « T segment de
    F » — toutes VRAIES pour un iso de segments φ:S≅T, AUCUNE n'étant la conclusion.
    theorie=22, rien postulé, NON vacueux."""
    Rpf = _R_de(Rp)
    vphi, vS, vT, vF, vp = _t(phi), _t(S), _t(T), _t(F_set), _t(p)
    phi_p = E.valeur(vphi, vp)                              # φ(p)

    phi_p_in_T = valeur_iso_dans_T(phi, S, T, p)            # φ(p) ∈ T  [3 hyps struct]

    # est_segment(T,Rp,F) ⇒ T ⊂ F  (projection gauche de la Déf. 2)
    h_seg_T = N.assume(E.est_segment(vT, Rpf, vF))          # est_segment(T,Rp,F)
    T_inclus_F = conjonction_elim_gauche(h_seg_T)           # T ⊂ F   (= (∀z)(z∈T ⇒ z∈F))

    # T ⊂ F, instancié en φ(p) : φ(p)∈T ⇒ φ(p)∈F
    incl_inst = instancie(T_inclus_F, phi_p)                # φ(p)∈T ⇒ φ(p)∈F
    return N.modus_ponens(phi_p_in_T, incl_inst)           # φ(p) ∈ F


def valeur_iso_dans_F_cible(phi="phi", p="pt", F_set="F"):
    """ÉNONCÉ-cible (test miroir) : valeur(φ,p) ∈ F."""
    return appartient(E.valeur(_t(phi), _t(p)), _t(F_set))


# ════════════════════════════════════════════════════════════════════════════
#  (3)  STRUCT(p,S,T,φ) — prémisse de la version universelle (structure de graphe).
# ════════════════════════════════════════════════════════════════════════════
def struct_iso_segment(E_set, R, F_set, Rp, vp, vS, vT, vphi):
    """Prémisse STRUCTURELLE de l'iso de segments φ:S≅T (en remplacement de la
    prémisse OPAQUE de val_dans_F), portant la STRUCTURE DE GRAPHE manquante :

        p∈E et est_segment(S,R,E) et est_segment(T,Rp,F)
        et est_isomorphisme_ordre(φ,S,T,R,Rp) et p∈S
        et φ ⊂ S×T  et  dom φ = S.

    Les 5 premiers conjoints = la prémisse de val_dans_F (ensembles_trichotomie_dom_segment) ;
    les DEUX derniers (φ⊂S×T, dom φ=S) = la structure de graphe de l'application φ:S→T
    que est_isomorphisme_ordre ne porte pas littéralement, et qu'on rend EXPLICITE."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    base = et(et(et(et(
        appartient(vp, vE),
        E.est_segment(vS, Rf, vE)),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf)),
        appartient(vp, vS))
    return et(et(base,
                 inclus(vphi, E.produit(vS, vT))),       # φ ⊂ S×T   (structure de graphe)
              egal(E.dom(vphi), vS))                     # dom φ = S (totalité sur S)


def val_dans_F_depuis_structure(E_set="E", R="R", F_set="F", Rp="Rp",
                                p="pt", S="S", T="T", phi="phi"):
    """⊢ (∀p)(∀S)(∀T)(∀φ)( STRUCT(p,S,T,φ) ⇒ valeur(φ,p) ∈ F ).

    Version UNIVERSELLEMENT QUANTIFIÉE remplaçant val_dans_F : la prémisse opaque
    (qui postulait φ(p)∈F) est ICI une prémisse de STRUCTURE DE GRAPHE
    (struct_iso_segment) à partir de laquelle la conclusion φ(p)∈F est DÉRIVÉE
    (valeur_iso_dans_F).  C'est DONC LE MÊME SCHÉMA que val_dans_F, mais INCONDITIONNEL :
    il ne porte AUCUNE hypothèse résiduelle (tout est sous l'antécédent ⇒).

    Pour DÉCHARGER le codomaine dans dom_h_initial_sous_val, il SUFFIT que le scaffold
    expose, pour les isos témoins de h, la structure de graphe (φ⊂S×T, dom φ=S) :
    alors cette implication-ci fournit val_dans_F sans le postuler.

    NON vacueux : la conclusion valeur(φ,p)∈F ne figure pas dans STRUCT(p,S,T,φ)
    (qui ne parle que de p∈E, segments, iso, p∈S, φ⊂S×T, dom φ=S).  CLOS (0 hyp)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vp, vS, vT, vphi = var(p), var(S), var(T), var(phi)

    struct = struct_iso_segment(E_set, R, F_set, Rp, vp, vS, vT, vphi)
    Hs = N.assume(struct)

    # extraire les 4 hypothèses dont valeur_iso_dans_F a besoin
    dom_eq = conjonction_elim_droite(Hs)                      # dom φ = S
    g1 = conjonction_elim_gauche(Hs)                          # base et (φ⊂S×T)
    phi_incl = conjonction_elim_droite(g1)                   # φ ⊂ S×T
    base = conjonction_elim_gauche(g1)                       # p∈E et seg S et seg T et iso et p∈S
    Hp_in_S = conjonction_elim_droite(base)                  # p ∈ S
    base4 = conjonction_elim_gauche(base)                    # p∈E et seg S et seg T et iso
    Hiso = conjonction_elim_droite(base4)                   # iso(φ,S,T) (non requis ici)
    base3 = conjonction_elim_gauche(base4)                   # p∈E et seg S et seg T
    Hseg_T = conjonction_elim_droite(base3)                  # est_segment(T,Rp,F)

    # valeur_iso_dans_F : {φ⊂S×T, dom φ=S, p∈S, seg(T,Rp,F)} ⊢ φ(p) ∈ F
    body = valeur_iso_dans_F(phi, S, T, F_set, Rp, p)
    # fournir ses 4 hypothèses depuis les conjoints de STRUCT
    for hyp_f, preuve in [
        (inclus(vphi, E.produit(vS, vT)), phi_incl),
        (egal(E.dom(vphi), vS), dom_eq),
        (appartient(vp, vS), Hp_in_S),
        (E.est_segment(vT, Rpf, vF), Hseg_T),
    ]:
        body = N.modus_ponens(preuve, N.loi_deduction(hyp_f, body))
    # body : { struct } ⊢ valeur(φ,p) ∈ F
    imp = N.loi_deduction(struct, body)                      # STRUCT ⇒ valeur(φ,p)∈F
    return N.generalisation(p, N.generalisation(S, N.generalisation(T,
        N.generalisation(phi, imp))))


def val_dans_F_depuis_structure_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                      p="pt", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) de la version universelle DÉRIVÉE du codomaine."""
    vE, vF = _t(E_set), _t(F_set)
    vp, vS, vT, vphi = var(p), var(S), var(T), var(phi)
    struct = struct_iso_segment(E_set, R, F_set, Rp, vp, vS, vT, vphi)
    return pourtout(p, pourtout(S, pourtout(T, pourtout(phi,
        impl(struct, appartient(E.valeur(vphi, vp), vF))))))


__all__ = [
    "valeur_iso_dans_T", "valeur_iso_dans_T_cible",
    "valeur_iso_dans_F", "valeur_iso_dans_F_cible",
    "struct_iso_segment",
    "val_dans_F_depuis_structure", "val_dans_F_depuis_structure_cible",
]
