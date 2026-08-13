"""§III.6.3 — Théorème 2 (HESSENBERG, Zorn E.III.48) : CONSTRUCTION DU TÉMOIN-MAJORANT
pour une CHAÎNE ABSTRAITE de 𝔉 — l'UNION DES PROJECTIONS ⋃S = ⋃pr₁(C), ⋃φ = ⋃pr₂(C).

CONTEXTE — OBSTRUCTION A (le crux PROFOND).  Pour décharger `enonce_chaine_majoree`
de `frame_inductif` (`ensembles_hessenberg_inductivite.py`), il faut, pour une chaîne
C de 𝔉 quantifiée UNIVERSELLEMENT, CONSTRUIRE le majorant (⋃S,⋃φ) où
  ⋃S := réunion des PREMIÈRES projections des membres de C,
  ⋃φ := réunion des SECONDES projections des membres de C.
Les membres de C sont des couples p=(S_p,φ_p) ; ⋃S = ⋃{ pr₁(p) : p∈C } et
⋃φ = ⋃{ pr₂(p) : p∈C }.  Cette construction « union des projections sur une chaîne »
n'existait PAS dans le dépôt (l'infra C60 `union_famille` réunit les MEMBRES eux-mêmes,
w∈p, non leurs projections w∈pr₁(p)) ; ce module la fournit.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST CLOS ICI (theorie_ensembles()=22 intangible ; rien postulé) :

  (1) COLLECTIVISATION — `union_premiere(C)` / `union_seconde(C)` :
        ⋃S := { x | (∃p)( p∈C et x∈pr₁(p) ) }       (motif Zermelo `Union`, S8+A1,
        ⋃φ := { x | (∃p)( p∈C et x∈pr₂(p) ) }        dans une THÉORIE DÉDIÉE).
      + caractérisation de membership `membre_union_premiere`/`membre_union_seconde` :
        x∈⋃S ⟺ (∃p)(p∈C et x∈pr₁(p))   (axiome instancié).

  (2) INCLUSION MEMBRE→UNION — `membre_donne_inclus_premiere`/`_seconde` :
        { p∈C } ⊢ pr₁(p) ⊂ ⋃S    (resp. pr₂(p) ⊂ ⋃φ).            [1 hyp honnête].
      Chaque projection d'un membre est incluse dans l'union — c'est la MOITIÉ
      « ordre » du majorant : avec `frame_ordre_membre`, S_p⊂⋃S et φ_p⊂⋃φ donnent
      p ≤ (⋃S,⋃φ) dans Γ𝔉.  CLÉ réutilisable.

  (3) PONT vers le majorant — `temoin_majore_chaine` :
        { p∈C, (⋃S,⋃φ)∈𝔉(E), pr₁ inclusions } ⊢ (p,(⋃S,⋃φ))∈Γ𝔉(E)   [hyps honnêtes],
      i.e. le couple-témoin (⋃S,⋃φ) majore chaque membre p de C dans `frame_ordre`,
      via `frame_ordre_membre` (fraîchement mergé) + (2).  C'est le SECOND conjoint de
      `majorant`.  Il reste sous hyps HONNÊTES (la frame-membership du témoin pour une
      chaîne ABSTRAITE, et p∈𝔉, portent encore des hyps non déchargées — voir RAPPORT).

INVARIANT : theorie_ensembles()=22.  Les nouveaux axiomes (collectivisation ⋃S,⋃φ)
vivent dans une THÉORIE DÉDIÉE `theorie_union_projections` (motif Zermelo `Union` /
`theorie_union_famille`).  Rien postulé ; aucune conclusion vacuous.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, equiv, existe, pourtout, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import frame_ordre_membre_t


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (1) COLLECTIVISATION — ⋃S = ⋃pr₁(C) et ⋃φ = ⋃pr₂(C).
#      Termes opaques + axiomes DÉFINITIONNELS (S8+A1, motif Zermelo `Union`).
#      theorie_ensembles() reste = 22 (axiomes en théorie DÉDIÉE).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-24 | PDF p.151  (majorant d'une chaîne de 𝔐 : union des premières projections ⋃S)
def union_premiere(C):
    """⋃S(C) := { x | (∃p)( p∈C et x∈pr₁(p) ) }   (union des PREMIÈRES projections).

    Réunion des premières coordonnées S_p=pr₁(p) sur les membres p de la chaîne C.
    Terme OPAQUE collectivisant (S8 sur 𝔓(⋃C), unicité A1) ; motif Zermelo `Union`."""
    return E.app("hessenberg_union_premiere", _t(C))


# @livre Ch.III §6.3 Demo.2 | E III.48 L.21-24 | PDF p.151  (majorant d'une chaîne de 𝔐 : union des secondes projections ⋃φ)
def union_seconde(C):
    """⋃φ(C) := { x | (∃p)( p∈C et x∈pr₂(p) ) }   (union des SECONDES projections).

    Réunion des secondes coordonnées φ_p=pr₂(p) sur les membres p de la chaîne C.
    Terme OPAQUE collectivisant (S8 sur 𝔓(⋃C), unicité A1) ; motif Zermelo `Union`."""
    return E.app("hessenberg_union_seconde", _t(C))


def _corps_union_premiere(C, x, p="punionpr"):
    """Corps de ⋃S :  (∃p)( p∈C et x∈pr₁(p) )."""
    vp = var(p)
    return existe(p, et(appartient(vp, _t(C)), appartient(_t(x), E.pr1(vp))))


def _corps_union_seconde(C, x, p="punionpr"):
    """Corps de ⋃φ :  (∃p)( p∈C et x∈pr₂(p) )."""
    vp = var(p)
    return existe(p, et(appartient(vp, _t(C)), appartient(_t(x), E.pr2(vp))))


def axiome_union_premiere(C="Cch", x="xch", p="punionpr"):
    """⊢-schéma (∀C x)( x∈⋃S(C) ⇔ (∃p)( p∈C et x∈pr₁(p) ) ).

    Axiome DÉFINITIONNEL de l'union des premières projections (légitime S8+A1, motif
    Zermelo `Union`).  N'altère PAS theorie_ensembles() (=22)."""
    vC, vx = var(C), var(x)
    return pourtout(C, pourtout(x,
        equiv(appartient(vx, union_premiere(vC)), _corps_union_premiere(vC, vx, p))))


def axiome_union_seconde(C="Cch", x="xch", p="punionpr"):
    """⊢-schéma (∀C x)( x∈⋃φ(C) ⇔ (∃p)( p∈C et x∈pr₂(p) ) )."""
    vC, vx = var(C), var(x)
    return pourtout(C, pourtout(x,
        equiv(appartient(vx, union_seconde(vC)), _corps_union_seconde(vC, vx, p))))


def theorie_union_projections(C="Cch", x="xch", p="punionpr"):
    """Théorie DÉDIÉE ne contenant que les axiomes de ⋃S et ⋃φ (Hessenberg/Zorn).

    Motif `theorie_union_famille` : axiomes définitionnels isolés, HORS
    theorie_ensembles().  theorie_ensembles() reste = 22."""
    return N.Theorie("UnionProjections-Hessenberg",
                     [axiome_union_premiere(C, x, p), axiome_union_seconde(C, x, p)])


def _inst_union_premiere(C, x):
    """⊢ ( x∈⋃S(C) ⇔ (∃p)( p∈C et x∈pr₁(p) ) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_union_projections(), axiome_union_premiere())
    return instancie(instancie(ax, _t(C)), _t(x))


def _inst_union_seconde(C, x):
    """⊢ ( x∈⋃φ(C) ⇔ (∃p)( p∈C et x∈pr₂(p) ) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_union_projections(), axiome_union_seconde())
    return instancie(instancie(ax, _t(C)), _t(x))


def membre_union_premiere(C="Cch", x="xch"):
    """⊢ ( x∈⋃S(C) ) ⇔ ( (∃p)( p∈C et x∈pr₁(p) ) )."""
    return _inst_union_premiere(var(C), var(x))


def membre_union_seconde(C="Cch", x="xch"):
    """⊢ ( x∈⋃φ(C) ) ⇔ ( (∃p)( p∈C et x∈pr₂(p) ) )."""
    return _inst_union_seconde(var(C), var(x))


# ════════════════════════════════════════════════════════════════════════════
#  (2) INCLUSION MEMBRE→UNION — pr₁(p) ⊂ ⋃S  (et pr₂(p) ⊂ ⋃φ)  sous  p∈C.
#      LA CLÉ de la moitié « ordre » du majorant.
# ════════════════════════════════════════════════════════════════════════════
def _inclus_def(A, B, x="xincl"):
    """A⊂B := (∀x)( x∈A ⇒ x∈B )  (forme développée de inclus, pour l'introduction)."""
    vx = var(x)
    return pourtout(x, impl(appartient(vx, _t(A)), appartient(vx, _t(B))))


def membre_donne_inclus_premiere(C="Cch", p="pmemb", x="z"):
    """{ p∈C } ⊢ pr₁(p) ⊂ ⋃S(C).                                    [1 hyp honnête].

    🎯 CLÉ de la moitié « ordre » du majorant.  Pour tout membre p de la chaîne C, sa
    première projection S_p=pr₁(p) est INCLUSE dans l'union ⋃S = ⋃{pr₁(q):q∈C}.  En
    effet, soit x∈pr₁(p) : avec p∈C, le couple (p,x) témoigne (∃q)(q∈C et x∈pr₁(q)),
    donc x∈⋃S par l'axiome de ⋃S.  Couplé à `frame_ordre_membre` (S_p⊂⋃S, φ_p⊂⋃φ),
    c'est p ≤ (⋃S,⋃φ) dans Γ𝔉.  L'hypothèse p∈C est HONNÊTE (jamais postulée ;
    conclusion ∉ hyps ; theorie=22)."""
    vC, vp, vx = var(C), var(p), var(x)
    US = union_premiere(vC)
    pr = E.pr1(vp)

    h_pC = N.assume(appartient(vp, vC))                     # p∈C   [HONNÊTE]
    # supposons x∈pr₁(p) ; témoignons (∃q)(q∈C et x∈pr₁(q)) avec q:=p.
    h_xpr = N.assume(appartient(vx, pr))                    # x∈pr₁(p)
    corps_temoin = conjonction_intro(h_pC, h_xpr)           # p∈C et x∈pr₁(p)
    R = et(appartient(var("punionpr"), vC),
           appartient(vx, E.pr1(var("punionpr"))))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vp, "punionpr"))   # (∃p)(p∈C et x∈pr₁(p))
    x_in_US = N.modus_ponens(ex, equivalence_arriere(_inst_union_premiere(vC, vx)))  # x∈⋃S
    # décharge x∈pr₁(p) : ⊢ x∈pr₁(p) ⇒ x∈⋃S
    impl_x = N.loi_deduction(appartient(vx, pr), x_in_US)
    res = N.generalisation(x, impl_x)                       # (∀x)(x∈pr₁(p) ⇒ x∈⋃S) = pr₁(p)⊂⋃S

    cible = inclus(pr, US)
    assert res.conclusion == cible, "membre_donne_inclus_premiere : ≠ pr₁(p)⊂⋃S"
    assert appartient(vp, vC) in res.hypotheses, "membre_donne_inclus_premiere : p∈C absente"
    assert res.conclusion not in res.hypotheses, "membre_donne_inclus_premiere : VACUOUS"
    return res


def membre_donne_inclus_seconde(C="Cch", p="pmemb", x="z"):
    """{ p∈C } ⊢ pr₂(p) ⊂ ⋃φ(C).                                    [1 hyp honnête].

    Miroir de `membre_donne_inclus_premiere` pour la SECONDE projection : φ_p=pr₂(p)
    ⊂ ⋃φ = ⋃{pr₂(q):q∈C}.  C'est la moitié « ψ' prolonge ψ » de l'ordre d'extension de
    Bourbaki (E.III.48).  Hyp HONNÊTE p∈C ; conclusion ∉ hyps ; theorie=22."""
    vC, vp, vx = var(C), var(p), var(x)
    US = union_seconde(vC)
    pr = E.pr2(vp)

    h_pC = N.assume(appartient(vp, vC))                     # p∈C   [HONNÊTE]
    h_xpr = N.assume(appartient(vx, pr))                    # x∈pr₂(p)
    corps_temoin = conjonction_intro(h_pC, h_xpr)           # p∈C et x∈pr₂(p)
    R = et(appartient(var("punionpr"), vC),
           appartient(vx, E.pr2(var("punionpr"))))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vp, "punionpr"))   # (∃p)(p∈C et x∈pr₂(p))
    x_in_US = N.modus_ponens(ex, equivalence_arriere(_inst_union_seconde(vC, vx)))  # x∈⋃φ
    impl_x = N.loi_deduction(appartient(vx, pr), x_in_US)
    res = N.generalisation(x, impl_x)                       # pr₂(p)⊂⋃φ

    cible = inclus(pr, US)
    assert res.conclusion == cible, "membre_donne_inclus_seconde : ≠ pr₂(p)⊂⋃φ"
    assert appartient(vp, vC) in res.hypotheses, "membre_donne_inclus_seconde : p∈C absente"
    assert res.conclusion not in res.hypotheses, "membre_donne_inclus_seconde : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  (3) PONT vers le majorant — le témoin (⋃S,⋃φ) MAJORE chaque membre p∈C dans Γ𝔉.
#      Second conjoint de `majorant`, via `frame_ordre_membre` (fraîchement mergé) + (2).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (le couple-témoin (⋃S,⋃φ) majore chaque membre de la chaîne dans Γ𝔐)
def temoin_majore_membre(E_set="E", C="Cch", p="pmemb"):
    """{ p∈C, p∈𝔉(E), (⋃S,⋃φ)∈𝔉(E), pr₁(p)=pr₁(⋃S,⋃φ)_premier, pr₂(p)=... }
        ⊢ ( p, (⋃S,⋃φ) ) ∈ Γ𝔉(E).                          [CLOS, hyps HONNÊTES].

    🎯 Le couple-témoin m:=(⋃S,⋃φ) MAJORE chaque membre p de la chaîne C dans l'ordre
    d'extension Γ𝔉 (E.III.48, « X⊂X' et ψ' prolonge ψ »).  Via `frame_ordre_membre`
    (axiome Γ𝔉 fraîchement mergé) :
        (p,m)∈Γ𝔉 ⟺ ( p∈𝔉 et m∈𝔉 et pr₁(p)⊂pr₁(m) et pr₂(p)⊂pr₂(m) ).
    Les inclusions pr₁(p)⊂⋃S et pr₂(p)⊂⋃φ viennent de (2)
    (`membre_donne_inclus_premiere/_seconde`) ; il reste à identifier pr₁(m)=⋃S et
    pr₂(m)=⋃φ pour m=(⋃S,⋃φ) — c'est `pr1_couple`/`pr2_couple` (E.II.31).

    ⚠️ HYPS HONNÊTES (theorie=22 ; jamais postulées) : p∈C (membre de la chaîne),
    p∈𝔉(E) (membre du poset — vrai car C⊂𝔉, non déchargé ici pour C abstraite),
    m∈𝔉(E) (= `union_chaine_dans_frame`, sous SES propres hyps honnêtes pour C
    abstraite).  Conclusion ∉ hyps ; theorie=22."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_premiere, projection_seconde,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
    vE, vC, vp = _t(E_set), _t(C), _t(p)
    US, Uphi = union_premiere(vC), union_seconde(vC)
    m = E.couple(US, Uphi)                                  # le témoin (⋃S,⋃φ)
    Fr = frame_pair(vE)
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)
    pr1m, pr2m = E.pr1(m), E.pr2(m)

    # inclusions de (2) :  pr₁(p)⊂⋃S,  pr₂(p)⊂⋃φ   (sous p∈C)
    incl1 = membre_donne_inclus_premiere(C, p)             # [p∈C] ⊢ pr₁(p)⊂⋃S
    incl2 = membre_donne_inclus_seconde(C, p)             # [p∈C] ⊢ pr₂(p)⊂⋃φ

    # identification pr₁(m)=⋃S et pr₂(m)=⋃φ pour m=(⋃S,⋃φ) : généralise
    # projection_premiere/_seconde (0 hyp) puis instancie aux TERMES US, Uphi.
    pp = N.generalisation("u", N.generalisation("v", projection_premiere("u", "v")))
    e1 = instancie(instancie(pp, US), Uphi)               # pr₁((⋃S,⋃φ))=⋃S
    ps = N.generalisation("u", N.generalisation("v", projection_seconde("u", "v")))
    e2 = instancie(instancie(ps, US), Uphi)               # pr₂((⋃S,⋃φ))=⋃φ
    # forme EXACTE de pr₁(m)/pr₂(m) telle que prouvée (binders internes inclus).
    pr1m = e1.conclusion.termes[0]                        # le terme pr₁((⋃S,⋃φ)) prouvé =⋃S
    pr2m = e2.conclusion.termes[0]                        # le terme pr₂((⋃S,⋃φ)) prouvé =⋃φ

    # réécrit ⋃S → pr₁(m) dans incl1 :  inclus(pr₁p,⋃S) ⇔ inclus(pr₁p,pr₁m) via
    # ⋃S=pr₁m (symétrie de e1) et S6 sur R(w)=inclus(pr₁p,w).
    eq1_sym = N.modus_ponens(e1, symetrie(pr1m, US))       # ⋃S=pr₁m  (symétrie de e1)
    assert eq1_sym.conclusion == egal(US, pr1m)
    s6_1 = N.s6(US, pr1m, "w", inclus(pr1p, var("w")))     # (⋃S=pr₁m) ⇒ (incl(…,⋃S) ⇔ incl(…,pr₁m))
    incl1_m = N.modus_ponens(incl1,
        equivalence_avant(N.modus_ponens(eq1_sym, s6_1)))  # pr₁(p)⊂pr₁(m)
    eq2_sym = N.modus_ponens(e2, symetrie(pr2m, Uphi))
    s6_2 = N.s6(Uphi, pr2m, "w", inclus(pr2p, var("w")))
    incl2_m = N.modus_ponens(incl2,
        equivalence_avant(N.modus_ponens(eq2_sym, s6_2)))  # pr₂(p)⊂pr₂(m)

    # les deux frame-memberships (hyps honnêtes pour C abstraite)
    h_pFr = N.assume(appartient(vp, Fr))                  # p∈𝔉(E)   [HONNÊTE]
    h_mFr = N.assume(appartient(m, Fr))                  # m∈𝔉(E)   [HONNÊTE]

    # corps de Γ𝔉 :  ((p∈𝔉 et m∈𝔉) et pr₁(p)⊂pr₁(m)) et pr₂(p)⊂pr₂(m)
    corps = conjonction_intro(
        conjonction_intro(conjonction_intro(h_pFr, h_mFr), incl1_m), incl2_m)
    eq = frame_ordre_membre_t(vE, vp, m)                  # (p,m)∈Γ𝔉 ⇔ corps
    res = N.modus_ponens(corps, equivalence_arriere(eq))  # (p,m)∈Γ𝔉

    cible = appartient(E.couple(vp, m), frame_ordre(vE))
    assert res.conclusion == cible, "temoin_majore_membre : ≠ (p,(⋃S,⋃φ))∈Γ𝔉"
    assert res.conclusion not in res.hypotheses, "temoin_majore_membre : VACUOUS"
    return res


__all__ = [
    # (1) collectivisation ⋃S = ⋃pr₁(C), ⋃φ = ⋃pr₂(C) (théorie DÉDIÉE)
    "union_premiere", "union_seconde",
    "axiome_union_premiere", "axiome_union_seconde", "theorie_union_projections",
    "membre_union_premiere", "membre_union_seconde",
    # (2) 🎯 inclusion membre→union (clé de l'ordre du majorant)
    "membre_donne_inclus_premiere", "membre_donne_inclus_seconde",
    # (3) pont : le témoin majore chaque membre dans Γ𝔉
    "temoin_majore_membre",
]
