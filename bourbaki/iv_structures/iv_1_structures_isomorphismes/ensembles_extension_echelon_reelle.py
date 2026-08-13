"""§IV.1.2 — Extensions canoniques RÉELLES (non opaques) : ḡ aux parties, g×h au produit.

────────────────────────────────────────────────────────────────────────────────
RÔLE (T1 du plan CST, cf. journal de campagne).  `ensembles_especes_echelon`
représente l'extension canonique ⟨f₁,…,fₙ⟩^S par récurrence méta sur le schéma,
mais ses deux briques `ext_parties` / `produit_applications` sont des termes
OPAQUES (app(...) sans caractérisation) : les critères CST1/CST2 (fonctorialité,
identité) sont INDÉMONTRABLES sur l'opaque — c'est le « mur des objets
terme-définis » de juillet.  Ce module fournit les CONSTRUCTIONS RÉELLES par
graphes de termes (C54), avec leurs caractérisations noyau :

  • ext_parties_reelle(g, A)   := graphe de X ↦ g⟨X⟩       sur 𝔓(A) ;
  • produit_app_reelle(g,h,A,B):= graphe de u ↦ (g(pr₁u), h(pr₂u)) sur A×B ;
  • *_fonctionnel : est_fonctionnel(...)                    [CLOS, 0 hyp] ;
  • *_valeur      : {p∈domaine} ⊢ valeur(..., p) = t[p]     [1 hyp d'appartenance].

⚠️ LIANT « xg » PARTOUT : les liants canoniques {u,v,z} d'est_fonctionnel
(abrege:139) et {x,y} des axiomes image/produit sont PRIS — le liant du graphe
doit leur être étranger (le ROUGE de la sonde T1 au liant « u » l'a confirmé ;
le verrou-τ de juillet, lui, était spécifique aux valeurs Card-valuées et NE
mord PAS ici).  INVARIANT : theorie_ensembles()=22 ; aucun axiome ; les graphes
de termes sont l'infra C54 CLOSE.  NON vacueux.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _au_point(base, dom_set, point):
    """Transporte {pcs∈D} ⊢ Φ(pcs) au POINT-terme donné (loi de déduction →
    généralisation → instanciation → re-assume) ; motif « noms puis termes »
    (membre_graphe_terme n'accepte que des NOMS, famille coupe_membre)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    if point is None:
        return base
    p = _t(point)
    hyp = appartient(var("pcs"), dom_set)
    imp = N.loi_deduction(hyp, base)                 # ⊢ (pcs∈D ⇒ Φ(pcs))   [0 hyp]
    inst = instancie(N.generalisation("pcs", imp), p)
    return N.modus_ponens(N.assume(appartient(p, dom_set)), inst)


_XG = "xg"        # liant du graphe — étranger aux liants canoniques {u,v,z,x,y}


# ─────────────────────────────────────────────────────────────────────────────
#  ext_parties RÉELLE : le graphe de X ↦ g⟨X⟩ sur 𝔓(A).
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.2 Def.- | E IV.2 L.22-23 | PDF p.205  (extension canonique ḡ de g aux ensembles de parties — construction réelle X↦g⟨X⟩, E.II.5)
def terme_ext_parties(g, xg=_XG):
    """Le TERME-valeur de l'extension aux parties : g⟨xg⟩ (image directe)."""
    return E.image(_t(g), var(xg))


def ext_parties_reelle(g, A, xg=_XG):
    """ḡ := graphe_terme(𝔓(A), g⟨xg⟩, xg) — l'application X ↦ g⟨X⟩ RÉELLE."""
    return E.graphe_terme(E.parties(_t(A)), terme_ext_parties(g, xg), xg)


def ext_parties_fonctionnel(g, A, xg=_XG):
    """⊢ est_fonctionnel( ext_parties_reelle(g,A) ).                 [CLOS, 0 hyp]."""
    res = graphe_terme_fonctionnel(E.parties(_t(A)), terme_ext_parties(g, xg), xg)
    assert not res.hypotheses, "ext_parties_fonctionnel : hyps résiduelles"
    return res


def ext_parties_valeur(g, A, point=None, xg=_XG):
    """{ p ∈ 𝔓(A) } ⊢ valeur(ḡ, p) = g⟨p⟩       (p = `point`, défaut var(xg)).

    Caractérisation de VALEUR de l'extension réelle (C54) en un point ARBITRAIRE.
    ⚠️ CONVENTION UNIQUE : la variable du terme est TOUJOURS xg (4e argument de
    graphe_terme_valeur) — l'axiome C54 dédié est paramétré par (terme, x) et
    mélanger deux x sur le MÊME terme minte deux axiomes INCOMPATIBLES (motif
    de l'incohérence de l'intersection, cf. journal)."""
    dom_set = E.parties(_t(A))
    base = graphe_terme_valeur(dom_set, terme_ext_parties(g, xg), "pcs", xg)
    res = _au_point(base, dom_set, point)            # NOM "pcs" → point-terme
    assert len(res.hypotheses) == 1, "ext_parties_valeur : hyps ≠ 1"
    return res


# ─────────────────────────────────────────────────────────────────────────────
#  produit d'applications RÉEL : le graphe de u ↦ (g(pr₁u), h(pr₂u)) sur A×B.
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.2 Def.- | E IV.2 L.24-25 | PDF p.205  (extension canonique g×h à A×B — construction réelle (x,y)↦(g(x),h(y)), E.II.3.9)
def terme_produit_app(g, h, xg=_XG):
    """Le TERME-valeur du produit d'applications : ( g(pr₁ xg), h(pr₂ xg) )."""
    vxg = var(xg)
    return E.couple(E.valeur(_t(g), E.pr1(vxg)), E.valeur(_t(h), E.pr2(vxg)))


def produit_app_reelle(g, h, A, B, xg=_XG):
    """g×h := graphe_terme(A×B, (g(pr₁xg), h(pr₂xg)), xg) — le produit RÉEL."""
    return E.graphe_terme(E.produit(_t(A), _t(B)), terme_produit_app(g, h, xg), xg)


def produit_app_fonctionnel(g, h, A, B, xg=_XG):
    """⊢ est_fonctionnel( produit_app_reelle(g,h,A,B) ).             [CLOS, 0 hyp]."""
    res = graphe_terme_fonctionnel(E.produit(_t(A), _t(B)),
                                   terme_produit_app(g, h, xg), xg)
    assert not res.hypotheses, "produit_app_fonctionnel : hyps résiduelles"
    return res


def produit_app_valeur(g, h, A, B, point=None, xg=_XG):
    """{ p ∈ A×B } ⊢ valeur(g×h, p) = ( g(pr₁ p), h(pr₂ p) )   (p = `point`).

    Caractérisation de VALEUR du produit réel (C54) en un point ARBITRAIRE —
    même CONVENTION UNIQUE xg que ext_parties_valeur (cf. ⚠️ ci-dessus)."""
    dom_set = E.produit(_t(A), _t(B))
    base = graphe_terme_valeur(dom_set, terme_produit_app(g, h, xg), "pcs", xg)
    res = _au_point(base, dom_set, point)            # NOM "pcs" → point-terme
    assert len(res.hypotheses) == 1, "produit_app_valeur : hyps ≠ 1"
    return res


# ─────────────────────────────────────────────────────────────────────────────
#  F1-val : FONCTORIALITÉ de l'extension aux parties (forme VALEUR) — CST1 𝔓.
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.30-32 | PDF p.205  (fonctorialité de l'extension canonique, cas 𝔓 : ⟨g∘f⟩ = ⟨g⟩∘⟨f⟩ au niveau des valeurs)
def fonctorialite_parties_valeur(f="f", g="g", A="A", B="B", X="Xf1", xg=_XG):
    """{ X∈𝔓(A),  image(f,X)∈𝔓(B) } ⊢
        valeur(ext(g∘f, A), X)  =  valeur(ext(g, B), valeur(ext(f, A), X)).

    LE cas 𝔓 du critère CST1, forme valeur : la chaîne compose la
    caractérisation T1 aux trois points (X pour g∘f et f ; image(f,X) — un
    POINT-TERME, via _au_point — pour g) avec `image_composee` (Prop. 5 E.II.42,
    CLOS) puis réécrit S6 au 2e argument de valeur(ext_g, ·).   [2 hyps]."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee import (
        image_composee,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_avant,
    )
    vf, vg = _t(f), _t(g)
    vX = var(X)
    gf = E.composee(vg, vf)
    imfX = E.image(vf, vX)
    ext_gf = ext_parties_reelle(gf, A, xg)
    ext_f = ext_parties_reelle(f, A, xg)
    ext_g = ext_parties_reelle(g, B, xg)

    e1 = ext_parties_valeur(gf, A, vX, xg)           # {X∈𝔓A} ⊢ val(ext_gf,X)=(g∘f)⟨X⟩
    ic = image_composee(vg, vf, vX)                  # ⊢ (g∘f)⟨X⟩ = g⟨f⟨X⟩⟩   [CLOS]
    lhs = composer_egalites(e1, ic)                  # val(ext_gf,X) = g⟨f⟨X⟩⟩
    e4 = ext_parties_valeur(g, B, imfX, xg)          # {f⟨X⟩∈𝔓B} ⊢ val(ext_g,f⟨X⟩)=g⟨f⟨X⟩⟩
    e4s = N.modus_ponens(e4, symetrie(
        E.valeur(ext_g, imfX), E.image(vg, imfX)))   # g⟨f⟨X⟩⟩ = val(ext_g, f⟨X⟩)
    step = composer_egalites(lhs, e4s)               # val(ext_gf,X) = val(ext_g, f⟨X⟩)
    e3 = ext_parties_valeur(f, A, vX, xg)            # {X∈𝔓A} ⊢ val(ext_f,X)=f⟨X⟩
    e3s = N.modus_ponens(e3, symetrie(
        E.valeur(ext_f, vX), imfX))                  # f⟨X⟩ = val(ext_f, X)
    s6r = N.s6(imfX, E.valeur(ext_f, vX), "h6e",
               egal(E.valeur(ext_gf, vX), E.valeur(ext_g, var("h6e"))))
    res = N.modus_ponens(step, equivalence_avant(N.modus_ponens(e3s, s6r)))

    cible = egal(E.valeur(ext_gf, vX),
                 E.valeur(ext_g, E.valeur(ext_f, vX)))
    assert res.conclusion == cible, "F1-val : conclusion ≠ ⟨g∘f⟩(X)=⟨g⟩(⟨f⟩(X))"
    assert res.hypotheses == frozenset({
        appartient(vX, E.parties(_t(A))),
        appartient(imfX, E.parties(_t(B)))}), "F1-val : hyps ≠ {X∈𝔓A, f⟨X⟩∈𝔓B}"
    return res


# ─────────────────────────────────────────────────────────────────────────────
#  F2-val : FONCTORIALITÉ du produit d'applications (forme VALEUR) — CST1 ×.
# ─────────────────────────────────────────────────────────────────────────────
def _proj_t(ta, tb):
    """⊢ pr₁((a,b))=a  et  ⊢ pr₂((a,b))=b, aux TERMES (noms puis instanciation)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
        projection_premiere, projection_seconde,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    p1 = instancie(instancie(N.generalisation("up", N.generalisation(
        "vp", projection_premiere("up", "vp"))), _t(ta)), _t(tb))
    p2 = instancie(instancie(N.generalisation("up", N.generalisation(
        "vp", projection_seconde("up", "vp"))), _t(ta)), _t(tb))
    return p1, p2


# @livre Ch.IV §1.2 Crit.CST1 | E IV.2 L.30-32 | PDF p.205  (fonctorialité de l'extension canonique, cas × : (g×g')∘(f×f') = (g∘f)×(g'∘f') au niveau des valeurs)
def fonctorialite_produit_valeur(f="f", g="g", fp="fp", gp="gp",
                                 A="A", Ap="Ap", A2="A2",
                                 B="B", Bp="Bp", B2="B2", U="Uf2", xg=_XG):
    """{ U∈A×B, pr₁U∈A, pr₂U∈B, (f(pr₁U),fp(pr₂U))∈Ap×Bp,
        est_application(f,A,Ap), est_application(g,Ap,A2),
        est_application(fp,B,Bp), est_application(gp,Bp,B2) }
      ⊢ valeur((g∘f)×(gp∘fp), U) = valeur(g×gp, valeur(f×fp, U)).      [8 hyps].

    LE cas × du critère CST1, forme valeur (produits réels T1).  Chaîne : T1 aux
    trois points (U ×2 et le POINT-TERME (f(pr₁U),fp(pr₂U))), composee_valeur_app
    (ii_3_8) aux points pr₁U/pr₂U, projections du couple (noms→termes), et
    congruences/S6.  Les 8 hypothèses sont STRUCTURELLES honnêtes (les
    appartenances-projections seront déchargées par un lemme _pr_dans ultérieur)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
        composee_valeur_app,
    )
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
        symetrie, composer_egalites, congruence_terme,
    )
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_avant, instancie,
    )
    vf, vg, vfp, vgp = _t(f), _t(g), _t(fp), _t(gp)
    vA, vB, vAp, vBp = _t(A), _t(B), _t(Ap), _t(Bp)
    vU = var(U)
    p1, p2 = E.pr1(vU), E.pr2(vU)
    gf, gpfp = E.composee(vg, vf), E.composee(vgp, vfp)
    prod_gf = produit_app_reelle(gf, gpfp, A, B, xg)
    prod_f = produit_app_reelle(f, fp, A, B, xg)
    prod_g = produit_app_reelle(g, gp, Ap, Bp, xg)
    f_p1, fp_p2 = E.valeur(vf, p1), E.valeur(vfp, p2)
    g_f_p1, gp_fp_p2 = E.valeur(vg, f_p1), E.valeur(vgp, fp_p2)
    Kpt = E.couple(f_p1, fp_p2)

    # (i) valeur du produit composé au point U
    e1 = produit_app_valeur(gf, gpfp, A, B, vU, xg)  # {U∈A×B} ⊢ val=couple(gf(p1),gpfp(p2))

    # (ii) compositions aux points pr₁U / pr₂U (⇒-forme généralisée puis instanciée)
    h_p1 = N.assume(appartient(p1, vA))
    h_p2 = N.assume(appartient(p2, vB))
    imp1 = instancie(N.generalisation("uc",
        composee_valeur_app(g, f, A, Ap, A2, "uc")), p1)
    eq1 = N.modus_ponens(h_p1, imp1)                 # (g∘f)(p1) = g(f(p1))
    imp2 = instancie(N.generalisation("uc",
        composee_valeur_app(gp, fp, B, Bp, B2, "uc")), p2)
    eq2 = N.modus_ponens(h_p2, imp2)                 # (gp∘fp)(p2) = gp(fp(p2))
    c1 = N.modus_ponens(eq1, congruence_terme(
        E.valeur(gf, p1), g_f_p1, E.couple(var("w"), E.valeur(gpfp, p2))))
    c2 = N.modus_ponens(eq2, congruence_terme(
        E.valeur(gpfp, p2), gp_fp_p2, E.couple(g_f_p1, var("w"))))
    lhs = composer_egalites(composer_egalites(e1, c1), c2)
    #     val(prod_gf, U) = couple(g(f(p1)), gp(fp(p2)))

    # (iii)+(iv) valeur de prod_g au POINT-TERME Kpt, projections réécrites
    e4 = produit_app_valeur(g, gp, Ap, Bp, Kpt, xg)  # {Kpt∈Ap×Bp} ⊢ val(prod_g,Kpt)=…pr(Kpt)…
    pj1, pj2 = _proj_t(f_p1, fp_p2)                  # pr₁(Kpt)=f(p1), pr₂(Kpt)=fp(p2)
    d1 = N.modus_ponens(pj1, congruence_terme(
        E.pr1(Kpt), f_p1,
        E.couple(E.valeur(vg, var("w")), E.valeur(vgp, E.pr2(Kpt)))))
    d2 = N.modus_ponens(pj2, congruence_terme(
        E.pr2(Kpt), fp_p2, E.couple(g_f_p1, E.valeur(vgp, var("w")))))
    e4r = composer_egalites(composer_egalites(e4, d1), d2)
    #     val(prod_g, Kpt) = couple(g(f(p1)), gp(fp(p2)))

    # (v) raccord : val(prod_gf,U) = val(prod_g, Kpt), puis Kpt → val(prod_f,U) (S6)
    link = composer_egalites(lhs, N.modus_ponens(
        e4r, symetrie(E.valeur(prod_g, Kpt), e4r.conclusion.termes[1])))
    e3 = produit_app_valeur(f, fp, A, B, vU, xg)     # {U∈A×B} ⊢ val(prod_f,U)=Kpt
    e3s = N.modus_ponens(e3, symetrie(E.valeur(prod_f, vU), Kpt))   # Kpt = val(prod_f,U)
    s6r = N.s6(Kpt, E.valeur(prod_f, vU), "h6e",
               egal(E.valeur(prod_gf, vU), E.valeur(prod_g, var("h6e"))))
    res = N.modus_ponens(link, equivalence_avant(N.modus_ponens(e3s, s6r)))

    cible = egal(E.valeur(prod_gf, vU), E.valeur(prod_g, E.valeur(prod_f, vU)))
    assert res.conclusion == cible, "F2-val : conclusion ≠ (g×gp)∘(f×fp) au point U"
    assert len(res.hypotheses) == 8, \
        "F2-val : hyps ≠ 8 (%d)" % len(res.hypotheses)
    assert res.conclusion not in res.hypotheses, "F2-val : VACUOUS"
    return res


__all__ = [
    "terme_ext_parties", "ext_parties_reelle",
    "ext_parties_fonctionnel", "ext_parties_valeur",
    "terme_produit_app", "produit_app_reelle",
    "produit_app_fonctionnel", "produit_app_valeur",
    "fonctorialite_parties_valeur", "fonctorialite_produit_valeur",
]
