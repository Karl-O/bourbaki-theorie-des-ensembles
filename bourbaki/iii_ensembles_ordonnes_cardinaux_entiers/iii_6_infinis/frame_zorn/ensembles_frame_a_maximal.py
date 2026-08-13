"""§III.6.3 — Théorème 2 (HESSENBERG, Zorn E.III.48) : ASSEMBLAGE vers l'EXISTENCE
d'un ÉLÉMENT MAXIMAL du poset 𝔉(E) des couples-bijections.

CONTEXTE.  Le squelette Zorn de l'argument de Bourbaki (E.III.48) est en place :
  • `frame_ordre_est_ordre(E)`            ⊢ est_ordre(Γ𝔉,𝔉)                  CLOS (0 hyp).
  • `frame_inductif_inconditionnel(E)`    ⊢ est_inductif(Γ𝔉,𝔉) sous {est_ordre,
                                            (∀C)(⋃S(C),⋃φ(C))∈𝔉(E)}.
  • `maximal_pair_existe(E)`              ⊢ (est_ordre et est_inductif et 𝔉≠∅)
                                            ⇒ (∃m)element_maximal(Γ𝔉,𝔉,m).        CLOS.

Ce module apporte :

  (1) `est_infini_union_chaine` — la PREMIÈRE projection ⋃S = union_premiere(C) de la
      réunion-chaîne est INFINIE, pour une chaîne C dont on connaît un membre p∈C (et
      p∈𝔉).  Route SUPERSET-D'UN-INFINI : un membre p=(S,φ)∈𝔉 a S=pr₁(p) INFINI
      (_corps_frame) ; or S=pr₁(p)⊂⋃S (`membre_donne_inclus_premiere`) ; une partie d'un
      ensemble FINI est finie (`partie_finie_est_finie`, INCONDITIONNEL), donc par
      CONTRAPOSÉE un sur-ensemble d'un infini est infini.  CLOS sous {p∈C, p∈𝔉(E)}.

  (2) `frame_inductif_clean` — re-export de `frame_inductif_inconditionnel` avec l'ordre
      DÉCHARGÉ par `frame_ordre_est_ordre` (CLOS).  Reste l'UNIQUE résidu honnête
      `m_dans_frame_universel` (frame-membership du couple-recollement — voir RAPPORT,
      buté sur le pont couple→valeur + Lemme 1).

  (3) `frame_a_maximal` — branche `frame_ordre_est_ordre` (✓ est_ordre), `frame_inductif_
      clean` (est_inductif sous résidu) et l'hyp honnête 𝔉(E)≠∅ dans `maximal_pair_existe`
      ⊢ (∃m)element_maximal(Γ𝔉,𝔉,m), sous résidus honnêtes minimaux.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
conclusion ∉ hyps (non vacuous).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, congruence_terme,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import alpha_bridge
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import projection_premiere

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini_ensemble
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop6_bien_ordonne_iii5 import partie_finie_est_finie

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre, frame_membre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_donne_inclus_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_inductif_assemblage import (
    frame_inductif_inconditionnel, m_dans_frame_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_est_ordre import frame_ordre_est_ordre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import est_ordre, element_maximal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif, enonce_non_vide
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import maximal_pair_existe


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _frame_membre_t(vE, vp):
    """Version TERME de frame_membre : ⊢ (p∈𝔉(E)) ⇔ corps_frame, instancié aux termes."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import theorie_frame, axiome_frame
    ax = N.axiome(theorie_frame(), axiome_frame())          # (∀E)(∀p)( p∈𝔉(E) ⇔ corps )
    return instancie(instancie(ax, _t(vE)), _t(vp))


# ════════════════════════════════════════════════════════════════════════════
#  EXTRACTION — { p∈𝔉(E) } ⊢ est_infini_ensemble(pr₁(p)).
#  (p∈𝔉 ⇒ ∃S∃φ(p=(S,φ) et S⊂E et S infini et φ bij) ; dans le témoin S=pr₁p
#   et S infini ⇒ pr₁p infini, via réécriture S→pr₁p.)
# ════════════════════════════════════════════════════════════════════════════
def _membre_pr1_infini(E_set, p):
    """{ p∈𝔉(E) } ⊢ est_infini_ensemble(pr₁(p)).                  [1 hyp honnête].

    Un membre p=(S,φ) du poset 𝔉 a sa première projection S=pr₁(p) INFINIE (3ᵉ
    conjoint de _corps_frame : « S infini »).  Élimination de l'existentielle (∃S∃φ)
    de `frame_membre`, identification pr₁(p)=S (projection_premiere), réécriture de
    est_infini_ensemble(S) en est_infini_ensemble(pr₁(p))."""
    vE, vp = _t(E_set), _t(p)
    Fr = frame_pair(vE)
    pr1p = E.pr1(vp)
    cible = est_infini_ensemble(pr1p)

    # p∈𝔉 ⇒ (∃S)(∃φ)( ((p=(S,φ) et S⊂E) et S infini) et φ bij )
    decl = N.modus_ponens(N.assume(appartient(vp, Fr)),
                          equivalence_avant(_frame_membre_t(vE, vp)))   # (∃S)(∃φ)(…)
    exS = decl.conclusion
    nS = exS.lieur                                          # "S"
    bodyS = exS.sous[0]                                     # (∃φ)(…)
    nphi = bodyS.lieur                                      # "phi"
    bodyphi = bodyS.sous[0]                                 # (((p=(S,φ) et S⊂E) et S∞) et φbij)

    def inner(b):
        hh = N.assume(b)
        # S infini = 3ᵉ conjoint : conj_droite(conj_gauche(b))
        S_inf = conjonction_elim_droite(conjonction_elim_gauche(hh))   # est_infini_ensemble(S)
        # p=(S,φ) = 1er conjoint
        p_eq = conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(hh)))  # p=(S,φ)
        vS, vphi = var(nS), var(nphi)
        Scpl = E.couple(vS, vphi)
        # pr₁p = pr₁((S,φ)) = S ⇒ S = pr₁p
        cong1 = N.modus_ponens(p_eq, congruence_terme(vp, Scpl, E.pr1(var("w"))))  # pr₁p=pr₁((S,φ))
        from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
        pr1_eq_S = composer_egalites(cong1, projection_premiere(nS, nphi))         # pr₁p=S
        S_eq_pr1 = N.modus_ponens(pr1_eq_S, symetrie(pr1p, vS))                    # S=pr₁p
        # réécrit S→pr₁p dans est_infini_ensemble(S) via S6 sur R(w)=est_infini_ensemble(w)
        s6 = N.s6(vS, pr1p, "w", est_infini_ensemble(var("w")))   # (S=pr₁p)⇒(inf(S)⇔inf(pr₁p))
        inf_pr1 = N.modus_ponens(S_inf, equivalence_avant(N.modus_ponens(S_eq_pr1, s6)))
        assert inf_pr1.conclusion == cible
        return N.loi_deduction(b, inf_pr1)                  # b ⇒ est_infini_ensemble(pr₁p)

    imp_phi = existe_elimination(inner(bodyphi), nphi)      # (∃φ)(…) ⇒ cible
    body_phi = N.modus_ponens(N.assume(bodyS), imp_phi)     # under (∃φ)… ⊢ cible
    imp_S = existe_elimination(N.loi_deduction(bodyS, body_phi), nS)  # (∃S)(∃φ)(…) ⇒ cible
    res = N.modus_ponens(decl, imp_S)                       # { p∈𝔉 } ⊢ est_infini_ensemble(pr₁p)
    assert res.conclusion == cible, "_membre_pr1_infini : ≠ est_infini_ensemble(pr₁p)"
    assert appartient(vp, Fr) in res.hypotheses, "_membre_pr1_infini : p∈𝔉 absente"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (1) est_infini_union_chaine — ⋃S(C) est INFINIE (sur-ensemble d'un infini).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.19-24 | PDF p.151  (⋃S, sur-ensemble d'un membre infini de 𝔐, est infini)
def est_infini_union_chaine(E_set="E", C="Cch", p="pmemb"):
    """{ p∈C, p∈𝔉(E) } ⊢ est_infini_ensemble( ⋃S(C) ).            [2 hyps honnêtes].

    🎯 La première projection ⋃S = union_premiere(C) de la réunion d'une chaîne C de 𝔉
    est INFINIE, pour peu qu'on connaisse un membre p∈C (chaîne NON vide).  En effet :
      • p=(S,φ)∈𝔉 a S=pr₁(p) INFINI                          [`_membre_pr1_infini`] ;
      • S=pr₁(p) ⊂ ⋃S                                        [`membre_donne_inclus_premiere`] ;
      • une partie d'un FINI est finie (`partie_finie_est_finie`, INCONDITIONNEL) ⇒ par
        CONTRAPOSÉE, si ⋃S était fini, pr₁(p)⊂⋃S serait fini, contredisant pr₁(p) infini ;
        donc ⋃S est infini.
    Hyps HONNÊTES p∈C, p∈𝔉(E) (témoin de chaîne non vide ; jamais postulées vraies) ;
    conclusion ∉ hyps ; theorie=22."""
    vE, vC, vp = _t(E_set), _t(C), _t(p)
    US = union_premiere(vC)
    pr1p = E.pr1(vp)
    cible = est_infini_ensemble(US)                         # ¬Fini(⋃S)

    # pr₁(p) ⊂ ⋃S   (sous p∈C)
    incl = membre_donne_inclus_premiere(C, p)              # [p∈C] ⊢ pr₁(p)⊂⋃S
    assert incl.conclusion == inclus(pr1p, US)

    # est_infini_ensemble(pr₁p) = ¬Fini(pr₁p)   (sous p∈𝔉)
    inf_pr1 = _membre_pr1_infini(vE, vp)                   # [p∈𝔉] ⊢ ¬Fini(pr₁p)

    # contraposée : sous H:=Fini(⋃S), pr₁p⊂⋃S ⇒ Fini(pr₁p) ; contredit ¬Fini(pr₁p).
    H = est_fini_ensemble(US)                              # Fini(⋃S)
    h_H = N.assume(H)
    # partie_finie_est_finie(pr₁p,⋃S) : (pr₁p⊂⋃S et Fini(⋃S)) ⇒ Fini(pr₁p)
    pfe = partie_finie_est_finie(pr1p, US)
    assert pfe.conclusion == impl(et(inclus(pr1p, US), H), est_fini_ensemble(pr1p))
    fini_pr1 = N.modus_ponens(conjonction_intro(incl, h_H), pfe)   # Fini(pr₁p)  [sous H, p∈C]

    # _refuter : {H ⊢ Q=Fini(pr₁p)} et {⊢ ¬Q=inf_pr1} ⟹ ⊢ ¬H = est_infini_ensemble(⋃S)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_props import _refuter
    res = _refuter(H, fini_pr1, inf_pr1)                   # ¬Fini(⋃S) = est_infini_ensemble(⋃S)

    assert res.conclusion == cible, "est_infini_union_chaine : ≠ est_infini_ensemble(⋃S)"
    assert appartient(vp, vC) in res.hypotheses, "est_infini_union_chaine : p∈C absente"
    assert appartient(vp, frame_pair(vE)) in res.hypotheses, "est_infini_union_chaine : p∈𝔉 absente"
    assert res.conclusion not in res.hypotheses, "est_infini_union_chaine : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (2) frame_inductif_clean — est_inductif(Γ𝔉,𝔉) avec l'ORDRE déchargé.
# ════════════════════════════════════════════════════════════════════════════
def frame_inductif_clean(E_set="E", C="C", m="m", x="xmaj", y="y", z="z"):
    """{ (∀C)(⋃S(C),⋃φ(C))∈𝔉(E) } ⊢ est_inductif(Γ𝔉(E),𝔉(E)).      [1 hyp honnête].

    `frame_inductif_inconditionnel` avec son hypothèse `est_ordre(Γ𝔉,𝔉)` DÉCHARGÉE par
    `frame_ordre_est_ordre` (CLOS, 0 hyp).  Reste donc l'UNIQUE résidu honnête
    `m_dans_frame_universel` (frame-membership du couple-recollement de chaîne — buté
    sur le pont couple→valeur et le Lemme 1 de Hessenberg ; jamais postulé vrai).
    Conclusion ∉ hyps ; theorie=22."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    fi = frame_inductif_inconditionnel(E_set, C, m, x, y, z)   # {est_ordre, m_dans_frame} ⊢ est_inductif
    # BINDER-ALIGN : l'hyp est_ordre de fi est est_ordre(Γ𝔉,𝔉,x,y,z) (binders de frame_inductif_clean).
    # frame_ordre_est_ordre prend les binders en paramètres (x="p",y="q",z="r") ; on cale (x,y,z).
    ordre = _frame_ordre_xyz_named(E_set, x, y, z)             # ⊢ est_ordre(Γ𝔉,𝔉,x,y,z)   CLOS
    hyp_ord = est_ordre(Gam, Fr, x, y, z)
    assert ordre.conclusion == hyp_ord, "frame_inductif_clean : est_ordre forme inattendue"
    assert hyp_ord in fi.hypotheses, "frame_inductif_clean : est_ordre absente de fi"
    res = N.modus_ponens(ordre, N.loi_deduction(hyp_ord, fi))  # est_inductif, est_ordre déchargée

    cible = est_inductif(Gam, Fr, C, m, x, y, z)
    assert res.conclusion == cible, "frame_inductif_clean : ≠ est_inductif(Γ𝔉,𝔉)"
    assert res.conclusion not in res.hypotheses, "frame_inductif_clean : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  RE-BINDER — aligne les noms de variables LIÉES d'un (∀nm)(…) sur un nom CIBLE,
#  par instanciation (au TERME var(cible)) puis re-généralisation.  Préserve la
#  conclusion à α-équivalence près (mais STRUCTURELLEMENT pour matcher le noyau).
# ════════════════════════════════════════════════════════════════════════════
def _rebind(thm, *cibles):
    """⊢ (∀a₁)…(∀aₙ)(corps)  ⟹  ⊢ (∀c₁)…(∀cₙ)(corps[aᵢ:=cᵢ]).

    Instancie chaque liant successif au TERME var(cibleᵢ) puis re-généralise sur cibleᵢ
    (motif prop9/prop10 d'alignement de binders).  Préserve les hypothèses."""
    cur = thm
    # instancie en CASCADE aux variables cibles
    for c in cibles:
        cur = instancie(cur, var(c))
    # re-généralise en ordre INVERSE
    for c in reversed(cibles):
        cur = N.generalisation(c, cur)
    return cur


def _frame_ordre_xyz_named(E_set, x="x", y="y", z="z"):
    """⊢ est_ordre(Γ𝔉(E),𝔉(E),x,y,z).                                        CLOS.

    `frame_ordre_est_ordre` ne peut PAS produire directement des liants arbitraires
    (collision interne avec le "x" des projections pr₁/pr₂).  On rebinde donc CHAQUE
    composant — réflexivité (1 liant), antisymétrie (2), transitivité (3) — depuis ses
    liants SÛRS (px,py,pz) vers (x,y,z) par instanciation+re-généralisation (motif
    prop9/prop10), puis on reconjugue en est_ordre(x,y,z).  x,y,z = binders CIBLES
    (alignés sur l'hyp est_ordre du consommateur)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_est_ordre import (
        frame_ordre_reflexive, frame_ordre_antisymetrique, frame_ordre_transitive,
    )
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    refl = _rebind(frame_ordre_reflexive(E_set, "px"), x)              # reflexivite_sur(.,.,x)
    anti = _rebind(frame_ordre_antisymetrique(E_set, "px", "py"), x, y)  # antisymetrie(.,x,y)
    trans = _rebind(frame_ordre_transitive(E_set, "px", "py", "pz"), x, y, z)
    res = conjonction_intro(conjonction_intro(refl, anti), trans)
    cible = est_ordre(Gam, Fr, x, y, z)
    assert res.conclusion == cible, f"_frame_ordre_xyz_named : ≠ est_ordre({x},{y},{z})\n{res.conclusion}"
    return res


def _frame_ordre_xyz(E_set):
    """⊢ est_ordre(Γ𝔉(E),𝔉(E),"x","y","z").  CLOS.  (cas par défaut x,y,z.)"""
    return _frame_ordre_xyz_named(E_set, "x", "y", "z")


# ════════════════════════════════════════════════════════════════════════════
#  (3) frame_a_maximal — (∃m)element_maximal(Γ𝔉,𝔉,m) sous résidus honnêtes.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151  (« Il existe donc dans 𝔐 un élément maximal (F,f) en vertu de III, p. 20, th. 2 »)
def frame_a_maximal(E_set="E"):
    """{ 𝔉(E)≠∅, (∀C)(⋃S(C),⋃φ(C))∈𝔉(E) } ⊢ (∃m) element_maximal(Γ𝔉(E),𝔉(E),m).

    🎯 EXISTENCE d'un ÉLÉMENT MAXIMAL du poset 𝔉(E) (E.III.48, « il existe dans 𝔐 un
    élément maximal (F,f) »).  `maximal_pair_existe` exige (est_ordre et est_inductif et
    𝔉≠∅) ⇒ (∃m)maximal ; on décharge :
      • est_ordre(Γ𝔉,𝔉)    par `frame_ordre_est_ordre`        (CLOS) ;
      • est_inductif(Γ𝔉,𝔉)  par `frame_inductif_clean`         (sous m_dans_frame) ;
      • 𝔉(E)≠∅              hyp HONNÊTE `enonce_non_vide(𝔉)`   (la base de l'argument :
        𝔉 contient (D,ψ₀) ; non assemblé ici — porté en prémisse, jamais postulé vrai).
    RÉSIDUS honnêtes : 𝔉(E)≠∅ et m_dans_frame_universel.  Conclusion ∉ hyps ; theorie=22.

    L'antécédent de `maximal_pair_existe` est calé sur les binders de `zorn`
    (G,E,m,C,x,y,z) : est_ordre(.,.,x,y,z) ∧ est_inductif(.,.,C,m,x,y,z) ∧ E≠∅(x)."""
    vE = _t(E_set)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)

    mpe = maximal_pair_existe(E_set)   # (est_ordre et est_inductif et 𝔉≠∅) ⇒ (∃m)maximal

    # composants déchargeants, binders ALIGNÉS sur ceux de `zorn` (x,y,z / C,m,x,y,z).
    ordre = _frame_ordre_xyz(E_set)                        # est_ordre(Γ𝔉,𝔉,x,y,z)
    # ⚠️ τ-HYGIÈNE : frame_inductif_clean(.,x="x") déclenche une CAPTURE interne (le τ
    #   τx((∃y)(x=paire…)) du témoin de chaîne collisionne avec le point x → @0, et la S5
    #   de membre_donne_inclus_premiere échoue).  On le construit donc avec le binder SÛR
    #   "xmaj" (cas qui passe) puis on α-convertit est_inductif(.,xmaj,..) → (.,x,..) via
    #   alpha_bridge — les deux formules sont α-équivalentes (xmaj/x = même binder lié).
    induct_safe = frame_inductif_clean(E_set, "C", "m", "xmaj", "y", "z")  # est_inductif(.,xmaj,y,z)
    induct = alpha_bridge(induct_safe, est_inductif(Gam, Fr, "C", "m", "x", "y", "z"))
    h_nv = N.assume(enonce_non_vide(Fr, "x"))              # 𝔉(E)≠∅(x)             [HONNÊTE]

    conj = conjonction_intro(conjonction_intro(ordre, induct), h_nv)
    res = N.modus_ponens(conj, mpe)                        # (∃m)element_maximal(Γ𝔉,𝔉,m)

    cible = existe("m", element_maximal(Gam, Fr, var("m"), "x"))
    assert res.conclusion == cible, \
        f"frame_a_maximal : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "frame_a_maximal : VACUOUS"
    return res


__all__ = [
    "est_infini_union_chaine",
    "frame_inductif_clean",
    "frame_a_maximal",
]
