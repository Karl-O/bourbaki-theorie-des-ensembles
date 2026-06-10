"""§IV.2.5 (résidu d'audit) — DÉCOMPOSITION CANONIQUE D'UN MORPHISME.

Module NEUF qui INTRODUIT (définition fidèle, niveau objet paramétré) la dernière
notion du §IV.2 encore explicitement REPORTÉE (cf. la docstring de
`ensembles_universel_finale` : « REPORTÉ : … décomposition canonique d'un morphisme »).

ÉNONCÉ FIDÈLE (IV.2.5, Texte.tex, verbatim ROADMAP_chap2-4.md) :

  « Soient A, B deux ensembles munis respectivement de structures 𝒮, 𝒮' d'espèce Σ,
    et f un morphisme de A dans B.  Soient R la relation d'équivalence f(x) = f(y), φ
    l'application canonique de A sur A/R, et j l'injection canonique de f(A) dans B.
    Si A admet une structure quotient 𝒮₀ par R et que 𝒮' induit une structure 𝒮'₀ sur
    f(A), alors dans la décomposition canonique f = j ∘ g ∘ φ, la bijection g de A/R
    sur f(A) associée à f est un morphisme (mais non nécessairement un isomorphisme),
    lorsqu'on munit A/R de 𝒮₀ et f(A) de 𝒮'₀. »

DISTINCTION avec II.6.5 (déjà couvert).  La décomposition ENSEMBLISTE f = j ∘ g ∘ φ
(g bijective, φ surjective, j injective) est DÉFINIE et factorisée dans
`bourbaki.ensembles.relations.ensembles_decomposition_quotient`
(`decomposition_canonique`, `bijection_induite`, `surjection_canonique`,
`injection_canonique`).  On RÉUTILISE ces graphes ici.  Le RÉSIDU §IV.2.5 est le
contenu STRUCTUREL nouveau : g (A/R → f(A)) est un σ-MORPHISME pour les structures
DÉRIVÉES 𝒮₀ (quotient, IV.2) sur A/R et 𝒮'₀ (induite, IV.2) sur f(A).

CONVENTION DE PARAMÉTRAGE — identique au reste de `bourbaki.structures` (cf.
`ensembles_universel_morphismes` / `_finale` / `_applications`).  Σ, σ étant MÉTA, la
notion de morphisme est portée par un PRÉDICAT ABSTRAIT callable → Formule :
  • `morph(e1, s1, e2, s2, f)`  : « f est un σ-morphisme de (e1,s1) dans (e2,s2) ».
Les structures dérivées 𝒮₀ = struct_quotient(A,𝒮,R) et 𝒮'₀ = struct_induite(B,𝒮',f(A))
sont des TERMES OPAQUES (réutilisés des modules IV.2 : `_struct_image_directe` via
`structure_quotient`, `_struct_image_reciproque` via `structure_induite`) — leur
EXISTENCE est une HYPOTHÈSE de l'énoncé (« si A admet une structure quotient … et que
𝒮' induit … »), pas un axiome.

theorie_ensembles() reste à 22 axiomes : ce module n'en crée AUCUN (il ne pose que des
définitions/prédicats et des lemmes purement logiques).

REPORTÉ honnêtement (pour Zorn / salvage, on ne POSTULE rien) : la PREUVE que g est un
morphisme (elle exige le critère CST20 « passage des morphismes aux quotients » + la
restriction d'un morphisme aux sous-structures CST12, eux-mêmes méta/algébriques) et
la factorisation effective f = j∘g∘φ (déjà reportée en II.6.5 ; calcul de composée
triple sur les graphes).  Ici on INTRODUIT l'ÉNONCÉ fidèle (prédicat
`g_est_morphisme`, énoncé complet `decomposition_canonique_morphisme`) et l'on certifie
les LEMMES DIRECTS purement logiques (projections de la conjonction des hypothèses).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, et, impl, appartient, app
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.structures.ensembles_universel_morphismes import (
    est_morphisme, _morph_defaut, _t)
from bourbaki.ensembles.relations.ensembles_decomposition_quotient import (
    relation_egalite_valeurs, surjection_canonique, injection_canonique,
    bijection_induite, decomposition_canonique)


# ════════════════════════════════════════════════════════════════════════════
#  Données dérivées de la décomposition (IV.2.5) — réutilisées de II.6.5 / IV.2
# ════════════════════════════════════════════════════════════════════════════
def relation_du_morphisme(f, x="x", y="y"):
    """R{x,y} := « f(x) = f(y) » (avec x,y ∈ A) — la relation d'équivalence associée
    au morphisme f  (IV.2.5).  Identique à la relation d'égalité-des-valeurs R_f de
    II.6.2 ; alias documenté de `relation_egalite_valeurs` (réutilisée, pas dupliquée).
    Renvoie une fonction (Terme, Terme) → Formule."""
    return relation_egalite_valeurs(f, x, y)


def application_canonique_phi(f, a):
    """Graphe de φ : A → A/R, l'application canonique de A sur A/R  (IV.2.5).

    R = relation associée à f (graphe).  φ = surjection canonique de II.6.2.  Ici on
    prend pour graphe de R celui de R_f ; on note `gR` ce graphe (terme).  Réutilise
    `surjection_canonique` (II.6.5) — non dupliqué."""
    va = _t(a)
    gR = _graphe_R(f, va)
    return surjection_canonique(gR, va)


def injection_canonique_j(f, a, b):
    """Graphe de j : f(A) → B, l'injection canonique de f(A) dans B  (IV.2.5).

    f(A) = E.image(f, A) (image directe).  j = identité de f(A) plongée dans B, de
    graphe Δ_{f(A)} (II.6.5).  Réutilise `injection_canonique` — non dupliqué."""
    vf, va = _t(f), _t(a)
    return injection_canonique(E.image(vf, va))


def bijection_g(f, a):
    """Graphe de g : A/R → f(A), la bijection associée à f  (IV.2.5).

    g(Cl_R(x)) = f(x).  C'est la bijection induite de II.6.5 (à valeurs dans f(A)).
    Réutilise `bijection_induite(gR, A, f)` — non dupliqué.  C'est le terme dont
    l'énoncé IV.2.5 affirme qu'il est un σ-morphisme (pour 𝒮₀ et 𝒮'₀)."""
    vf, va = _t(f), _t(a)
    gR = _graphe_R(f, va)
    return bijection_induite(gR, va, vf)


def _graphe_R(f, a):
    """Graphe (terme opaque) de la relation d'équivalence R associée à f, dans A.

    Terme nommé app("graphe_Rf", f, A) : R{x,y} ⟺ f(x)=f(y) (sa caractérisation est
    `relation_du_morphisme`).  Sert d'argument GRAPHE aux applications canoniques
    (φ, g) qui attendent un graphe de relation."""
    return app("graphe_Rf", _t(f), _t(a))


# ── structures dérivées 𝒮₀ (quotient) et 𝒮'₀ (induite) — IV.2 ──────────────────
def structure_quotient_S0(a, s, f):
    """𝒮₀ — structure quotient de 𝒮 par R sur A/R  (IV.2.5), terme dérivé (IV.2).

    Construction IV.2 « structure quotient » = image directe de 𝒮 par φ ; terme
    opaque app("structure_quotient", A, 𝒮, R) (existence = HYPOTHÈSE de l'énoncé).
    Réutilise la convention de `ensembles_universel_finale.structure_quotient`."""
    va, vs = _t(a), _t(s)
    gR = _graphe_R(f, va)
    return app("structure_quotient", va, vs, gR)


def structure_induite_S0prime(b, sp, f, a):
    """𝒮'₀ — structure induite par 𝒮' sur f(A) ⊂ B  (IV.2.5), terme dérivé (IV.2).

    Construction IV.2 « structure induite » = image réciproque de 𝒮' par l'injection
    canonique f(A) ↪ B ; terme opaque app("structure_induite", B, 𝒮', f(A))
    (existence = HYPOTHÈSE de l'énoncé)."""
    vb, vsp, vf, va = _t(b), _t(sp), _t(f), _t(a)
    return app("structure_induite", vb, vsp, E.image(vf, va))


# ════════════════════════════════════════════════════════════════════════════
#  IV.2.5 — g est un σ-morphisme (le contenu STRUCTUREL nouveau)
# ════════════════════════════════════════════════════════════════════════════
def g_est_morphisme(a, s, b, sp, f, morph=None):
    """« g est un σ-morphisme de (A/R, 𝒮₀) dans (f(A), 𝒮'₀) »  (conclusion IV.2.5).

    Codé est_morphisme(A/R, 𝒮₀, f(A), 𝒮'₀, g) avec :
      • A/R   = E.quotient(graphe_Rf, A)             (ensemble quotient, II.6.2) ;
      • 𝒮₀    = structure_quotient_S0(A,𝒮,f)         (structure quotient, IV.2) ;
      • f(A)  = E.image(f, A)                         (image directe) ;
      • 𝒮'₀   = structure_induite_S0prime(B,𝒮',f,A)  (structure induite, IV.2) ;
      • g     = bijection_g(f, A)                     (bijection induite, II.6.5).
    Porté par le prédicat abstrait `morph` (Σ, σ MÉTA).  C'est la NOTION résiduelle
    introduite : sa VÉRITÉ (preuve via CST20+CST12) est REPORTÉE."""
    if morph is None:
        morph = _morph_defaut()
    va, vs, vb, vsp, vf = _t(a), _t(s), _t(b), _t(sp), _t(f)
    gR = _graphe_R(vf, va)
    quotient_AR = E.quotient(gR, va)                 # A/R
    fA = E.image(vf, va)                             # f(A)
    s0 = structure_quotient_S0(va, vs, vf)           # 𝒮₀
    s0p = structure_induite_S0prime(vb, vsp, vf, va)  # 𝒮'₀
    g = bijection_g(vf, va)                          # g : A/R → f(A)
    return est_morphisme(quotient_AR, s0, fA, s0p, g, morph)


# ── hypothèses structurelles de IV.2.5 ────────────────────────────────────────
def hypothese_f_morphisme(a, s, b, sp, f, morph=None):
    """Hypothèse « f est un morphisme de (A,𝒮) dans (B,𝒮') »  (donnée de IV.2.5).
    Codé est_morphisme(A, 𝒮, B, 𝒮', f)."""
    if morph is None:
        morph = _morph_defaut()
    va, vs, vb, vsp, vf = _t(a), _t(s), _t(b), _t(sp), _t(f)
    return est_morphisme(va, vs, vb, vsp, vf, morph)


def hypothese_structures_derivees(a, s, b, sp, f, morph=None):
    """Hypothèses « A admet une structure quotient 𝒮₀ par R » ET « 𝒮' induit une
    structure 𝒮'₀ sur f(A) »  (conditions d'existence de IV.2.5).

    L'EXISTENCE des structures dérivées est portée, comme dans tout le chap. IV, par
    des prédicats opaques d'« existence d'une structure d'espèce Σ » :
      • exists_quotient(A,𝒮,R)  := « 𝒮₀ ∈ Struct_Σ(A/R) »  (∃ structure quotient) ;
      • exists_induite(B,𝒮',f(A)) := « 𝒮'₀ ∈ Struct_Σ(f(A)) » (∃ structure induite).
    Codés par appartenance à des termes opaques (mêmes que `_sigma_ens_defaut`-style).
    Renvoie la CONJONCTION des deux clauses d'existence."""
    va, vs, vb, vsp, vf = _t(a), _t(s), _t(b), _t(sp), _t(f)
    gR = _graphe_R(vf, va)
    s0 = structure_quotient_S0(va, vs, vf)
    s0p = structure_induite_S0prime(vb, vsp, vf, va)
    quotient_AR = E.quotient(gR, va)
    fA = E.image(vf, va)
    ex_quot = appartient(s0, app("Struct_Sigma", quotient_AR))      # 𝒮₀ existe sur A/R
    ex_ind = appartient(s0p, app("Struct_Sigma", fA))               # 𝒮'₀ existe sur f(A)
    return et(ex_quot, ex_ind)


def hypotheses_decomposition(a, s, b, sp, f, morph=None):
    """Conjonction COMPLÈTE des hypothèses de IV.2.5 :
        « f morphisme »  ET  ( « ∃ 𝒮₀ quotient »  ET  « ∃ 𝒮'₀ induite » ).
    Renvoie hypothese_f_morphisme ∧ hypothese_structures_derivees."""
    return et(hypothese_f_morphisme(a, s, b, sp, f, morph),
              hypothese_structures_derivees(a, s, b, sp, f, morph))


# ════════════════════════════════════════════════════════════════════════════
#  IV.2.5 — ÉNONCÉ COMPLET : décomposition canonique d'un morphisme
# ════════════════════════════════════════════════════════════════════════════
def decomposition_ensembliste(f, a, b):
    """« f = j ∘ g ∘ φ »  (la décomposition canonique ENSEMBLISTE, II.6.5) — RAPPEL.

    Réutilise `decomposition_canonique` (II.6.5) avec g = graphe de R_f (= graphe_Rf),
    e = A, but = B.  Égalité des graphes f = j ∘ (g ∘ φ).  Sa preuve est reportée en
    II.6.5 ; on l'expose ici pour situer la décomposition STRUCTURELLE (IV.2.5)."""
    vf, va, vb = _t(f), _t(a), _t(b)
    gR = _graphe_R(vf, va)
    return decomposition_canonique(vf, gR, va, vb)


def decomposition_canonique_morphisme(a, s, b, sp, f, morph=None):
    """ÉNONCÉ FIDÈLE de IV.2.5 (décomposition canonique d'un morphisme) :

        ( « f morphisme de (A,𝒮) dans (B,𝒮') »
          ET « A admet une structure quotient 𝒮₀ par R »
          ET « 𝒮' induit une structure 𝒮'₀ sur f(A) » )
        ⇒  « g (A/R → f(A)) est un morphisme pour (𝒮₀, 𝒮'₀) ».

    C'est l'implication hypotheses_decomposition ⇒ g_est_morphisme.  La VÉRITÉ de cette
    implication (le contenu de IV.2.5 : g est effectivement un σ-morphisme) est
    REPORTÉE — elle découle de CST20 (passage des morphismes aux quotients) et de
    CST12 (restriction aux sous-structures), eux-mêmes méta/algébriques.  On INTRODUIT
    ici la NOTION et l'énoncé exact ; on ne POSTULE pas (aucun axiome, aucun théorème
    affirmé).  Les LEMMES logiques directs (extraction des hypothèses) sont certifiés
    ci-dessous."""
    hyp = hypotheses_decomposition(a, s, b, sp, f, morph)
    ccl = g_est_morphisme(a, s, b, sp, f, morph)
    return impl(hyp, ccl)


# ── LEMMES DIRECTS purement logiques — extraction des hypothèses ───────────────
def decomp_extrait_f_morphisme(a="A", s="Sa", b="B", sp="Sb", f="f", morph=None):
    """{(f morphisme) ET (∃𝒮₀ quotient ET ∃𝒮'₀ induite)} ⊢ (f morphisme).

    Lemme logique : l'hypothèse de IV.2.5 est la conjonction « f morphisme » ∧
    « structures dérivées existent » ; on en EXTRAIT « f morphisme » (projection
    gauche).  Certifie que l'énoncé est bien FORMÉ et que « f morphisme » en est une
    composante.  Renvoie le théorème conditionnel hyp ⇒ (f morphisme) — clos."""
    hyp = hypotheses_decomposition(a, s, b, sp, f, morph)
    h = N.assume(hyp)                                    # hyp ⊢ hyp
    fm = conjonction_elim_gauche(h)                      # ⊢ (f morphisme)
    return N.loi_deduction(hyp, fm)                      # ⊢ hyp ⇒ (f morphisme)


def decomp_extrait_structures_derivees(a="A", s="Sa", b="B", sp="Sb", f="f",
                                       morph=None):
    """{(f morphisme) ET (∃𝒮₀ ET ∃𝒮'₀)} ⊢ (∃𝒮₀ quotient ET ∃𝒮'₀ induite).

    Projection droite de la conjonction des hypothèses de IV.2.5.  Renvoie le
    théorème conditionnel hyp ⇒ (structures dérivées existent) — clos."""
    hyp = hypotheses_decomposition(a, s, b, sp, f, morph)
    h = N.assume(hyp)
    sd = conjonction_elim_droite(h)                      # ⊢ (∃𝒮₀ ET ∃𝒮'₀)
    return N.loi_deduction(hyp, sd)                      # ⊢ hyp ⇒ (structures dérivées)


def decomp_extrait_existence_quotient(a="A", s="Sa", b="B", sp="Sb", f="f",
                                      morph=None):
    """{(f morphisme) ET (∃𝒮₀ ET ∃𝒮'₀)} ⊢ (∃𝒮₀ quotient).

    Double projection (droite puis gauche) : isole la clause d'existence de la
    structure quotient 𝒮₀ sur A/R.  Renvoie hyp ⇒ (∃𝒮₀) — clos."""
    hyp = hypotheses_decomposition(a, s, b, sp, f, morph)
    h = N.assume(hyp)
    sd = conjonction_elim_droite(h)                      # ⊢ (∃𝒮₀ ET ∃𝒮'₀)
    exq = conjonction_elim_gauche(sd)                    # ⊢ (∃𝒮₀)
    return N.loi_deduction(hyp, exq)                     # ⊢ hyp ⇒ (∃𝒮₀)


__all__ = [
    # données dérivées
    "relation_du_morphisme", "application_canonique_phi", "injection_canonique_j",
    "bijection_g", "structure_quotient_S0", "structure_induite_S0prime",
    # IV.2.5 — contenu structurel
    "g_est_morphisme",
    "hypothese_f_morphisme", "hypothese_structures_derivees",
    "hypotheses_decomposition",
    "decomposition_ensembliste", "decomposition_canonique_morphisme",
    # lemmes directs
    "decomp_extrait_f_morphisme", "decomp_extrait_structures_derivees",
    "decomp_extrait_existence_quotient",
]
