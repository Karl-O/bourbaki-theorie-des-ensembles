"""§III.3 — THÉORÈME DE COMPARABILITÉ DES CARDINAUX (« l'ordre des cardinaux est
total »), E.III.3, via le THÉORÈME DE ZORN.

Module NEUF.  Il PROUVE la comparabilité

    comparabilite_cardinaux() :  inf_egal_card(X, Y)  OU  inf_egal_card(Y, X)

(de deux ensembles X, Y quelconques, l'un s'injecte dans l'autre — modèle fidèle
de E.III.3.2-3, « l'ordre ≤ des cardinaux est total »).  On suit EXACTEMENT le
modèle `inf_egal_parties` (Cantor étape 1) qui établit `inf_egal_card(X, P(X))`
sur les ENSEMBLES X, P(X) eux-mêmes (Card étant fidèle à l'équipotence).

RECETTE (comparabilité ⇐ Zorn par le POSET DES INJECTIONS PARTIELLES) :
  1. Inj := { G ∈ 𝔓(X×Y) | G fonctionnel et G injectif }  ordonné par l'INCLUSION
     ΓI_⊂.   [terme opaque + axiome DÉFINITIONNEL ; motif `axiome_P`/`axiome_M`.]
     Une injection partielle X⇀Y est un graphe fonctionnel injectif G⊂X×Y (dom⊂X,
     pas forcément =X).
  2. (ΓI, Inj) est INDUCTIF : une ΓI-chaîne 𝔇 d'injections partielles a pour
     majorant son UNION ⋃𝔇 ∈ Inj.  [le CŒUR — calque EXACT de chaine_complet de
     Zorn ; ⋃𝔇 = terme opaque + axiome de membership.]
  3. ZORN : est_inductif(ΓI, Inj) et Inj≠∅ ⇒ (∃g) element_maximal(ΓI, Inj, g)
     [zorn_theoreme instancié à (ΓI, Inj)].
  4. g MAXIMAL ⇒ dom(g)=X OU img(g)=Y.  PAR L'ABSURDE : si dom(g)≠X et img(g)≠Y,
     ∃x∈X∖dom(g), ∃y∈Y∖img(g) ; g∪{(x,y)} est une injection partielle STRICTEMENT
     plus grande ⇒ contredit la maximalité.
  5. CONCLUSION : si dom(g)=X, g est une injection TOTALE X→Y ⇒ inf_egal_card(X,Y) ;
     si img(g)=Y, g⁻¹ injection Y→X ⇒ inf_egal_card(Y,X).  Disjonction.

INVARIANT : theorie_ensembles() reste = 22 (axiomes de Inj/ΓI/Union en théories
DÉDIÉES, motif P/Γ/Union de Zorn).  Rien n'est postulé : l'injection / l'inégalité
sont DÉMONTRÉES (le maximal vient de Zorn), JAMAIS supposées.

NOTATIONS :  (a,b)∈G := appartient(couple(a,b),G) ;  G⊂H := inclus(G,H).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus, tau,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition, cas, tiers_exclu, equivalence_avant, equivalence_arriere,
    equivalence_symetrie, equivalence_transitivite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, congruence_existe, alpha_existe, monotonie_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie as _sym
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, reflexivite_sur, antisymetrie, transitivite_rel, totalement_ordonne,
    majorant, borne_superieure, element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine, est_inductif, enonce_non_vide,
)


# Trou de substitution Leibniz GARANTI FRAIS pour ce module.
_H = "hole_leibniz_comp"


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _dans(a, b, G):
    """Formule « (a,b)∈G »."""
    return appartient(E.couple(_terme(a), _terme(b)), _terme(G))


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _incl_refl(t):
    """⊢ t⊂t  pour un TERME t."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import inclusion_reflexive
    th = inclusion_reflexive("_r")
    return instancie(N.generalisation("_r", th), _terme(t))


def _incl_trans(a, b, c, ab, bc):
    """De ⊢ a⊂b [ab] et ⊢ b⊂c [bc] (TERMES) déduit ⊢ a⊂c (avec le binder canonique)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    va, vb, vc = _terme(a), _terme(b), _terme(c)
    cible = inclus(va, vc)
    bndr, _ = _peler_pourtout(cible)
    zt = var(bndr)
    hz = N.assume(appartient(zt, va))
    z_in_b = N.modus_ponens(hz, instancie(ab, zt))
    z_in_c = N.modus_ponens(z_in_b, instancie(bc, zt))
    body = N.loi_deduction(appartient(zt, va), z_in_c)
    return N.generalisation(bndr, body)


def _ou_gauche(thm_p, q):
    """De ⊢ P, déduit ⊢ (P OU Q)."""
    return N.modus_ponens(thm_p, N.s2(thm_p.conclusion, q))


def _ou_droite(thm_q, p):
    """De ⊢ Q, déduit ⊢ (P OU Q)."""
    q = thm_q.conclusion
    return N.modus_ponens(N.modus_ponens(thm_q, N.s2(q, p)), N.s3(q, p))


# ════════════════════════════════════════════════════════════════════════════
#  Le PRÉDICAT « G est une injection partielle X⇀Y »  (graphe fonctionnel
#  injectif G⊂X×Y), exprimé comme une formule directe sur l'appartenance.
# ════════════════════════════════════════════════════════════════════════════
def graphe_injectif(G, a="a", b="b", ap="ap"):
    """G injectif (au sens graphe) := (∀a∀b∀a')(((a,b)∈G et (a',b)∈G) ⇒ a=a').

    « deux antécédents pour une même valeur sont égaux » — l'injectivité PURE du
    graphe (sans référence à un domaine), duale de est_fonctionnel."""
    va, vb, vap = var(a), var(b), var(ap)
    return pourtout(a, pourtout(b, pourtout(ap,
        impl(et(_dans(va, vb, G), _dans(vap, vb, G)), egal(va, vap)))))


def inj_partielle(G, X, Y, a="a", b="b", ap="ap", u="u", v="v", z="z"):
    """inj_partielle(G,X,Y) := G⊂X×Y et est_fonctionnel(G) et graphe_injectif(G).

    « G est (le graphe d')une injection PARTIELLE de X vers Y » : G inclus dans le
    produit X×Y, fonctionnel (au plus une valeur par antécédent) et injectif (au
    plus un antécédent par valeur).  dom G ⊂ X mais pas forcément = X."""
    vG = _terme(G)
    return et(et(inclus(vG, E.produit(_terme(X), _terme(Y))),
                 E.est_fonctionnel(vG)),
              graphe_injectif(vG, a, b, ap))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 — le POSET DES INJECTIONS PARTIELLES :
#  Inj := { G ∈ 𝔓(X×Y) | G fonctionnel et G injectif }
#  Terme opaque + axiome DÉFINITIONNEL (S8+A1, motif axiome_P de Zorn).
#  theorie_ensembles() reste INCHANGÉE = 22.
# ════════════════════════════════════════════════════════════════════════════
def Inj(X, Y):
    """Inj(X,Y) := { G | inj_partielle(G,X,Y) }  (les injections partielles X⇀Y)."""
    return E.app("comp_Inj", _terme(X), _terme(Y))


def axiome_Inj(X="X", Y="Y", G="G"):
    """⊢-schéma (∀X Y G)( G∈Inj ⇔ inj_partielle(G,X,Y) ).

    Axiome DÉFINITIONNEL du poset des injections partielles (sélection S8 dans
    𝔓(X×Y), unicité A1 ; motif axiome_P).  N'altère PAS theorie_ensembles()."""
    vX, vY, vG = var(X), var(Y), var(G)
    return pourtout(X, pourtout(Y, pourtout(G,
        equiv(appartient(vG, Inj(vX, vY)), inj_partielle(vG, vX, vY)))))


def theorie_Inj(X="X", Y="Y", G="G"):
    """Théorie DÉDIÉE ne contenant que l'axiome de Inj (E.III.3, comparabilité)."""
    return N.Theorie("Inj-Comp", [axiome_Inj(X, Y, G)])


def _inst_Inj(X, Y, G):
    """⊢ ( G∈Inj ⇔ inj_partielle(G,X,Y) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Inj(), axiome_Inj())
    for tm in (X, Y, G):
        ax = instancie(ax, _terme(tm))
    return ax


def Inj_membre(X="X", Y="Y", G="G"):
    """⊢ ( G∈Inj ) ⇔ inj_partielle(G,X,Y)."""
    return _inst_Inj(var(X), var(Y), var(G))


# ════════════════════════════════════════════════════════════════════════════
#  Le GRAPHE D'ORDRE ΓI_⊂ sur Inj :  (G,H)∈ΓI ⇔ (G∈Inj et H∈Inj et G⊂H)
#  Terme opaque + axiome DÉFINITIONNEL (motif axiome_Gamma de Zorn).
# ════════════════════════════════════════════════════════════════════════════
def Gamma(X, Y):
    """ΓI(X,Y) := { (G,H) | G∈Inj et H∈Inj et G⊂H }  (l'inclusion sur Inj)."""
    return E.app("comp_Gamma", _terme(X), _terme(Y))


def _corps_Gamma(X, Y, G, H):
    """Corps de ΓI :  G∈Inj et H∈Inj et G⊂H."""
    vI = Inj(_terme(X), _terme(Y))
    return et(et(appartient(_terme(G), vI), appartient(_terme(H), vI)),
              inclus(_terme(G), _terme(H)))


def axiome_Gamma(X="X", Y="Y", G="G", H="H"):
    """⊢-schéma (∀X Y G H)( (G,H)∈ΓI ⇔ (G∈Inj et H∈Inj et G⊂H) ).

    Axiome DÉFINITIONNEL du graphe d'inclusion sur Inj (S8+A1).  N'altère PAS
    theorie_ensembles()."""
    vX, vY, vG, vH = var(X), var(Y), var(G), var(H)
    return pourtout(X, pourtout(Y, pourtout(G, pourtout(H,
        equiv(appartient(E.couple(vG, vH), Gamma(vX, vY)),
              _corps_Gamma(vX, vY, vG, vH))))))


def theorie_Gamma(X="X", Y="Y", G="G", H="H"):
    """Théorie DÉDIÉE ne contenant que l'axiome de ΓI (E.III.3, comparabilité)."""
    return N.Theorie("Gamma-Comp", [axiome_Gamma(X, Y, G, H)])


def _inst_Gamma(X, Y, G, H):
    """⊢ ( (G,H)∈ΓI ⇔ (G∈Inj et H∈Inj et G⊂H) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Gamma(), axiome_Gamma())
    for tm in (X, Y, G, H):
        ax = instancie(ax, _terme(tm))
    return ax


def Gamma_membre(X="X", Y="Y", G="G", H="H"):
    """⊢ ( (G,H)∈ΓI ) ⇔ ( G∈Inj et H∈Inj et G⊂H )."""
    return _inst_Gamma(var(X), var(Y), var(G), var(H))


def _gle(G, H, X, Y):
    """Formule « (G,H)∈ΓI »  (l'ordre du poset Inj, i.e. G⊂H)."""
    return appartient(E.couple(_terme(G), _terme(H)), Gamma(_terme(X), _terme(Y)))


def _Gamma_intro(X, Y, G, H, hGI, hHI, hGH):
    """De ⊢ G∈Inj [hGI], ⊢ H∈Inj [hHI], ⊢ G⊂H [hGH], déduit ⊢ (G,H)∈ΓI."""
    corps = conjonction_intro(conjonction_intro(hGI, hHI), hGH)
    return N.modus_ponens(corps, equivalence_arriere(_inst_Gamma(X, Y, G, H)))


def _gamma_incl(X, Y, G, H, hGamma):
    """De ⊢ (G,H)∈ΓI [hGamma] déduit ⊢ G⊂H  (projection du corps de ΓI)."""
    corps = N.modus_ponens(hGamma, equivalence_avant(_inst_Gamma(X, Y, G, H)))
    return conjonction_elim_droite(corps)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 1 (suite) — ΓI est un ORDRE sur Inj  (⊂ réflexive/antisym/transitive)
#  Calque EXACT de Gamma_reflexive_sur / _antisymetrique / _transitive de Zorn.
# ════════════════════════════════════════════════════════════════════════════
def Gamma_reflexive_sur(X="X", Y="Y", G="x"):
    """⊢ reflexivite_sur(ΓI, Inj).   = (∀x)( x∈Inj ⇒ (x,x)∈ΓI )."""
    vX, vY, vG = var(X), var(Y), var(G)
    hGI = N.assume(appartient(vG, Inj(vX, vY)))
    GG = _incl_refl(vG)
    GG_Gamma = _Gamma_intro(vX, vY, vG, vG, hGI, hGI, GG)
    body = N.loi_deduction(appartient(vG, Inj(vX, vY)), GG_Gamma)
    return N.generalisation(G, body)


def Gamma_antisymetrique(X="X", Y="Y", G="x", H="y"):
    """⊢ antisymetrie(ΓI).   = (∀x∀y)( ((x,y)∈ΓI et (y,x)∈ΓI) ⇒ x=y )."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
    vX, vY, vG, vH = var(X), var(Y), var(G), var(H)
    hyp = et(_gle(vG, vH, vX, vY), _gle(vH, vG, vX, vY))
    h = N.assume(hyp)
    GH = _gamma_incl(vX, vY, vG, vH, conjonction_elim_gauche(h))   # G⊂H
    HG = _gamma_incl(vX, vY, vH, vG, conjonction_elim_droite(h))   # H⊂G
    a1 = extensionnalite_appliquee(vG, vH)                         # (G⊂H et H⊂G)⇒G=H
    G_eq_H = N.modus_ponens(conjonction_intro(GH, HG), a1)
    body = N.loi_deduction(hyp, G_eq_H)
    return N.generalisation(G, N.generalisation(H, body))


def Gamma_transitive(X="X", Y="Y", G="x", H="y", K="z"):
    """⊢ transitivite_rel(ΓI).   = (∀x∀y∀z)( ((x,y)∈ΓI et (y,z)∈ΓI) ⇒ (x,z)∈ΓI )."""
    vX, vY, vG, vH, vK = var(X), var(Y), var(G), var(H), var(K)
    hyp = et(_gle(vG, vH, vX, vY), _gle(vH, vK, vX, vY))
    h = N.assume(hyp)
    ghcorps = N.modus_ponens(conjonction_elim_gauche(h),
                             equivalence_avant(_inst_Gamma(vX, vY, vG, vH)))
    hkcorps = N.modus_ponens(conjonction_elim_droite(h),
                             equivalence_avant(_inst_Gamma(vX, vY, vH, vK)))
    GI = conjonction_elim_gauche(conjonction_elim_gauche(ghcorps))   # G∈Inj
    KI = conjonction_elim_droite(conjonction_elim_gauche(hkcorps))   # K∈Inj
    GH = conjonction_elim_droite(ghcorps)                            # G⊂H
    HK = conjonction_elim_droite(hkcorps)                            # H⊂K
    GK = _incl_trans(vG, vH, vK, GH, HK)                             # G⊂K
    GK_Gamma = _Gamma_intro(vX, vY, vG, vK, GI, KI, GK)
    body = N.loi_deduction(hyp, GK_Gamma)
    return N.generalisation(G, N.generalisation(H, N.generalisation(K, body)))


def Gamma_est_ordre(X="X", Y="Y"):
    """⊢ est_ordre(ΓI, Inj).   (L'inclusion ΓI_⊂ est un ordre sur les inj. partielles.)

    INCONDITIONNEL : réflexivité, antisymétrie (A1), transitivité de ⊂."""
    refl = Gamma_reflexive_sur(X, Y, "x")
    antisym = Gamma_antisymetrique(X, Y, "x", "y")
    trans = Gamma_transitive(X, Y, "x", "y", "z")
    return conjonction_intro(conjonction_intro(refl, antisym), trans)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 — (ΓI, Inj) est INDUCTIF  (le CŒUR : le majorant d'une ΓI-chaîne
#  d'injections partielles 𝔇 est l'UNION ⋃𝔇).  Union(𝔇) = terme opaque + axiome
#  de membership (S8+A1, motif zorn_Union).  theorie_ensembles() reste = 22.
# ════════════════════════════════════════════════════════════════════════════
def Union(X, Y, D):
    """⋃𝔇 := { w | (∃G)(G∈𝔇 et w∈G) }  (réunion d'une famille 𝔇 de graphes)."""
    return E.app("comp_Union", _terme(X), _terme(Y), _terme(D))


def _corps_Union(X, Y, D, w, G="G"):
    """Corps de ⋃𝔇 :  (∃G)( G∈𝔇 et w∈G )."""
    vG = var(G)
    return existe(G, et(appartient(vG, _terme(D)), appartient(_terme(w), vG)))


def axiome_Union(X="X", Y="Y", D="D", w="w", G="G"):
    """⊢-schéma (∀X Y D w)( w∈⋃𝔇 ⇔ (∃G)(G∈𝔇 et w∈G) ).

    Axiome DÉFINITIONNEL de la réunion d'une famille (légitime S8+A1, motif
    reunion_famille / zorn_Union).  N'altère PAS theorie_ensembles()."""
    vX, vY, vD, vw = var(X), var(Y), var(D), var(w)
    return pourtout(X, pourtout(Y, pourtout(D, pourtout(w,
        equiv(appartient(vw, Union(vX, vY, vD)),
              _corps_Union(vX, vY, vD, vw, G))))))


def theorie_Union(X="X", Y="Y", D="D", w="w", G="G"):
    """Théorie DÉDIÉE ne contenant que l'axiome de ⋃𝔇 (E.III.3, comparabilité)."""
    return N.Theorie("Union-Comp", [axiome_Union(X, Y, D, w, G)])


def _inst_Union(X, Y, D, w):
    """⊢ ( w∈⋃𝔇 ⇔ (∃G)(G∈𝔇 et w∈G) )   (axiome instancié aux TERMES)."""
    ax = N.axiome(theorie_Union(), axiome_Union())
    for tm in (X, Y, D, w):
        ax = instancie(ax, _terme(tm))
    return ax


def Union_membre(X="X", Y="Y", D="D", w="w"):
    """⊢ ( w∈⋃𝔇 ) ⇔ ( (∃G)(G∈𝔇 et w∈G) )."""
    return _inst_Union(var(X), var(Y), var(D), var(w))


# ── un élément de 𝔇 est une injection partielle (𝔇⊂Inj) ─────────────────────
def _inj_de_D(X, Y, D, G, hGD, hDI):
    """{ 𝔇⊂Inj [hDI], G∈𝔇 [hGD] } ⊢ inj_partielle(G,X,Y)  (élément de 𝔇 ∈ Inj)."""
    vX, vY = _terme(X), _terme(Y)
    GI = N.modus_ponens(hGD, instancie(hDI, _terme(G)))            # G∈Inj
    return N.modus_ponens(GI, equivalence_avant(_inst_Inj(vX, vY, _terme(G))))


# ── (A) ⋃𝔇 ⊂ X×Y ────────────────────────────────────────────────────────────
def Union_inclus_produit(X="X", Y="Y", D="D", w="w", G="G"):
    """⊢ { 𝔇⊂Inj } ⊢ ⋃𝔇 ⊂ X×Y.

    Si w∈⋃𝔇, témoin G∈𝔇⊂Inj donc G⊂X×Y (inj. partielle), et w∈G, d'où w∈X×Y."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vY, vD = var(X), var(Y), var(D)
    Ut = Union(vX, vY, vD)
    XY = E.produit(vX, vY)
    cible = inclus(Ut, XY)
    bndr, _ = _peler_pourtout(cible)
    vw = var(bndr)
    HDI = N.assume(inclus(vD, Inj(vX, vY)))                       # 𝔇⊂Inj
    hwU = N.assume(appartient(vw, Ut))                            # w∈⋃𝔇
    ex = N.modus_ponens(hwU, equivalence_avant(_inst_Union(vX, vY, vD, vw)))  # (∃G)(G∈𝔇 et w∈G)
    vG = var(G)
    Hw = N.assume(et(appartient(vG, vD), appartient(vw, vG)))
    GD = conjonction_elim_gauche(Hw)                             # G∈𝔇
    wG = conjonction_elim_droite(Hw)                             # w∈G
    inj = _inj_de_D(vX, vY, vD, vG, GD, HDI)                     # inj_partielle(G,X,Y)
    G_XY = conjonction_elim_gauche(conjonction_elim_gauche(inj))  # G⊂X×Y
    wXY = N.modus_ponens(wG, instancie(G_XY, vw))               # w∈X×Y
    wit_imp = N.loi_deduction(et(appartient(vG, vD), appartient(vw, vG)), wXY)
    ex_imp = existe_elimination(wit_imp, G)                      # (∃G)(…) ⇒ w∈X×Y
    wXY_final = N.modus_ponens(ex, ex_imp)                      # w∈X×Y  [w∈⋃𝔇, 𝔇⊂Inj]
    body = N.loi_deduction(appartient(vw, Ut), wXY_final)
    return N.generalisation(bndr, body)                         # ⋃𝔇⊂X×Y


# ── COMMUN : deux couples de ⋃𝔇 sont dans un même membre G* de 𝔇 ──────────────
def _couple_dans_union(X, Y, D, c, h_in_union, G="G"):
    """De ⊢ c∈⋃𝔇 [h_in_union], renvoie ⊢ (∃G)(G∈𝔇 et c∈G)."""
    vX, vY, vD = _terme(X), _terme(Y), _terme(D)
    return N.modus_ponens(h_in_union, equivalence_avant(_inst_Union(vX, vY, vD, _terme(c))))


def _commun_membre(X, Y, D, hDI, Htot, c1, c2, hc1, hc2, but,
                   G1="Ga", G2="Gb"):
    """{ 𝔇⊂Inj [hDI], totalement_ordonne(ΓI,𝔇) [Htot],
        c1∈⋃𝔇 [hc1], c2∈⋃𝔇 [hc2] } ⊢ but,
    où `but` se déduit de « ∃G*∈Inj contenant c1 ET c2 » via la fonction
    `but_de(G*, c1_in_Gstar, c2_in_Gstar, inj_Gstar)` passée comme callback.

    PREUVE : témoins G1,G2∈𝔇 avec c1∈G1, c2∈G2 ; 𝔇 ΓI-total ⇒ (G1,G2)∈ΓI ou
    (G2,G1)∈ΓI ; dans le 1er cas G1⊂G2 donc c1∈G2 et c2∈G2, G*=G2 ; sinon G*=G1."""
    vX, vY, vD = _terme(X), _terme(Y), _terme(D)
    vc1, vc2 = _terme(c1), _terme(c2)
    comp_D = conjonction_elim_droite(Htot)        # (∀Ga∀Gb)((Ga∈𝔇 et Gb∈𝔇)⇒((Ga,Gb)∈ΓI ou (Gb,Ga)∈ΓI))
    ex1 = _couple_dans_union(vX, vY, vD, vc1, hc1)   # (∃G)(G∈𝔇 et c1∈G)
    ex2_G = _couple_dans_union(vX, vY, vD, vc2, hc2)  # (∃G)(G∈𝔇 et c2∈G)
    # α-renomme les deux ∃ vers G1, G2 (binders distincts ; le corps de l'axiome
    # Union utilise le binder « G »)
    ex1 = _alpha_ex(ex1, "G", G1, et(appartient(var("G"), vD), appartient(vc1, var("G"))))
    ex2 = _alpha_ex(ex2_G, "G", G2, et(appartient(var("G"), vD), appartient(vc2, var("G"))))
    vG1, vG2 = var(G1), var(G2)
    Hw1 = N.assume(et(appartient(vG1, vD), appartient(vc1, vG1)))   # G1∈𝔇 et c1∈G1
    Hw2 = N.assume(et(appartient(vG2, vD), appartient(vc2, vG2)))   # G2∈𝔇 et c2∈G2
    G1D = conjonction_elim_gauche(Hw1)                            # G1∈𝔇
    c1G1 = conjonction_elim_droite(Hw1)                           # c1∈G1
    G2D = conjonction_elim_gauche(Hw2)                            # G2∈𝔇
    c2G2 = conjonction_elim_droite(Hw2)                           # c2∈G2
    comp = N.modus_ponens(conjonction_intro(G1D, G2D),
                          instancie(instancie(comp_D, vG1), vG2))  # (G1,G2)∈ΓI ou (G2,G1)∈ΓI
    inj1 = _inj_de_D(vX, vY, vD, vG1, G1D, hDI)                   # inj_partielle(G1,…)
    inj2 = _inj_de_D(vX, vY, vD, vG2, G2D, hDI)                   # inj_partielle(G2,…)
    # BRANCHE (G1,G2)∈ΓI : G1⊂G2 ⇒ c1∈G2 ; G*=G2 contient c1,c2 ; inj2
    H12 = N.assume(_gle(vG1, vG2, vX, vY))
    G1_G2 = _gamma_incl(vX, vY, vG1, vG2, H12)                    # G1⊂G2
    c1G2 = N.modus_ponens(c1G1, instancie(G1_G2, vc1))           # c1∈G2
    b1 = N.loi_deduction(_gle(vG1, vG2, vX, vY), but(vG2, c1G2, c2G2, inj2))
    # BRANCHE (G2,G1)∈ΓI : G2⊂G1 ⇒ c2∈G1 ; G*=G1 contient c1,c2 ; inj1
    H21 = N.assume(_gle(vG2, vG1, vX, vY))
    G2_G1 = _gamma_incl(vX, vY, vG2, vG1, H21)                    # G2⊂G1
    c2G1 = N.modus_ponens(c2G2, instancie(G2_G1, vc2))           # c2∈G1
    b2 = N.loi_deduction(_gle(vG2, vG1, vX, vY), but(vG1, c1G1, c2G1, inj1))
    par_cas = cas(comp, b1, b2)                                  # but  [Hw1, Hw2, …]
    # éliminer les deux ∃ : d'abord G2, puis G1
    wit2 = N.loi_deduction(et(appartient(vG2, vD), appartient(vc2, vG2)), par_cas)
    ex_imp2 = existe_elimination(wit2, G2)                       # (∃G2)(…) ⇒ but   [Hw1,…]
    after2 = N.modus_ponens(ex2, ex_imp2)                       # but   [Hw1,…]
    wit1 = N.loi_deduction(et(appartient(vG1, vD), appartient(vc1, vG1)), after2)
    ex_imp1 = existe_elimination(wit1, G1)                       # (∃G1)(…) ⇒ but
    return N.modus_ponens(ex1, ex_imp1)                         # but   [hDI, Htot, hc1, hc2]


def _alpha_ex(thm_ex, src, dst, corps_src):
    """De ⊢ (∃src)corps déduit ⊢ (∃dst)(dst|src)corps  (α-renommage du ∃)."""
    if src == dst:
        return thm_ex
    ren = alpha_existe(src, dst, corps_src)
    return N.modus_ponens(thm_ex, equivalence_avant(ren))


# ── (B) ⋃𝔇 est FONCTIONNEL ───────────────────────────────────────────────────
def Union_fonctionnel(X="X", Y="Y", D="D", u="u", v="v", z="z"):
    """⊢ { 𝔇⊂Inj, totalement_ordonne(ΓI,𝔇) } ⊢ est_fonctionnel(⋃𝔇).

    est_fonctionnel(⋃𝔇) = (∀u∀v∀z)(((u,v)∈⋃𝔇 et (u,z)∈⋃𝔇) ⇒ v=z).  Les deux
    couples (u,v),(u,z) sont dans un même membre G*∈Inj de 𝔇 (_commun_membre),
    qui est fonctionnel ⇒ v=z."""
    vX, vY, vD = var(X), var(Y), var(D)
    vu, vv, vz = var(u), var(v), var(z)
    Ut = Union(vX, vY, vD)
    HDI = N.assume(inclus(vD, Inj(vX, vY)))
    Htot = N.assume(totalement_ordonne(Gamma(vX, vY), vD))
    c1 = E.couple(vu, vv)
    c2 = E.couple(vu, vz)
    hyp = et(appartient(c1, Ut), appartient(c2, Ut))
    Hpair = N.assume(hyp)
    hc1 = conjonction_elim_gauche(Hpair)                        # (u,v)∈⋃𝔇
    hc2 = conjonction_elim_droite(Hpair)                        # (u,z)∈⋃𝔇
    but_cible = egal(vv, vz)

    def but(Gstar, c1_in, c2_in, inj_Gstar):
        # G* fonctionnel : ((u,v)∈G* et (u,z)∈G*) ⇒ v=z
        func = conjonction_elim_droite(conjonction_elim_gauche(inj_Gstar))  # est_fonctionnel(G*)
        inst = instancie(instancie(instancie(func, vu), vv), vz)
        return N.modus_ponens(conjonction_intro(c1_in, c2_in), inst)        # v=z

    res = _commun_membre(vX, vY, vD, HDI, Htot, c1, c2, hc1, hc2, but)       # v=z
    body = N.loi_deduction(hyp, res)
    return N.generalisation(u, N.generalisation(v, N.generalisation(z, body)))


# ── (C) ⋃𝔇 est INJECTIF (comme graphe) ──────────────────────────────────────
def Union_injectif(X="X", Y="Y", D="D", a="a", b="b", ap="ap"):
    """⊢ { 𝔇⊂Inj, totalement_ordonne(ΓI,𝔇) } ⊢ graphe_injectif(⋃𝔇).

    graphe_injectif(⋃𝔇) = (∀a∀b∀a')(((a,b)∈⋃𝔇 et (a',b)∈⋃𝔇) ⇒ a=a').  Les deux
    couples (a,b),(a',b) sont dans un même membre G*∈Inj de 𝔇 (_commun_membre),
    qui est injectif ⇒ a=a'.  C'EST LE CŒUR : l'union d'une chaîne d'injections
    partielles est INJECTIVE."""
    vX, vY, vD = var(X), var(Y), var(D)
    va, vb, vap = var(a), var(b), var(ap)
    Ut = Union(vX, vY, vD)
    HDI = N.assume(inclus(vD, Inj(vX, vY)))
    Htot = N.assume(totalement_ordonne(Gamma(vX, vY), vD))
    c1 = E.couple(va, vb)
    c2 = E.couple(vap, vb)
    hyp = et(appartient(c1, Ut), appartient(c2, Ut))
    Hpair = N.assume(hyp)
    hc1 = conjonction_elim_gauche(Hpair)                        # (a,b)∈⋃𝔇
    hc2 = conjonction_elim_droite(Hpair)                        # (a',b)∈⋃𝔇

    def but(Gstar, c1_in, c2_in, inj_Gstar):
        # G* injectif : ((a,b)∈G* et (a',b)∈G*) ⇒ a=a'
        ginj = conjonction_elim_droite(inj_Gstar)               # graphe_injectif(G*)
        inst = instancie(instancie(instancie(ginj, va), vb), vap)
        return N.modus_ponens(conjonction_intro(c1_in, c2_in), inst)        # a=a'

    res = _commun_membre(vX, vY, vD, HDI, Htot, c1, c2, hc1, hc2, but)       # a=a'
    body = N.loi_deduction(hyp, res)
    return N.generalisation(a, N.generalisation(b, N.generalisation(ap, body)))


# ── (D) ⋃𝔇 ∈ Inj  (assemblage des 3 conjoints) ──────────────────────────────
def Union_dans_Inj(X="X", Y="Y", D="D"):
    """⊢ { 𝔇⊂Inj, totalement_ordonne(ΓI,𝔇) } ⊢ ⋃𝔇 ∈ Inj.

    ⋃𝔇 est une injection partielle : ⋃𝔇⊂X×Y (Union_inclus_produit), fonctionnel
    (Union_fonctionnel) et injectif (Union_injectif), donc ⋃𝔇∈Inj (axiome de Inj)."""
    vX, vY, vD = var(X), var(Y), var(D)
    Ut = Union(vX, vY, vD)
    U_XY = Union_inclus_produit(X, Y, D)                        # ⋃𝔇⊂X×Y  [𝔇⊂Inj]
    U_func = Union_fonctionnel(X, Y, D)                         # est_fonctionnel(⋃𝔇)  [hyps]
    U_inj = Union_injectif(X, Y, D)                            # graphe_injectif(⋃𝔇)  [hyps]
    inj_U = conjonction_intro(conjonction_intro(U_XY, U_func), U_inj)  # inj_partielle(⋃𝔇,X,Y)
    return N.modus_ponens(inj_U, equivalence_arriere(_inst_Inj(vX, vY, Ut)))  # ⋃𝔇∈Inj


# ── (E) ⋃𝔇 MAJORE 𝔇 dans Inj  (≡ Union_majorant de Zorn) ────────────────────
def _G_inclus_Union(X, Y, D, G, hGD):
    """De ⊢ G∈𝔇 [hGD] déduit ⊢ G⊂⋃𝔇  (tout G∈𝔇 est inclus dans la réunion).

    Pour w∈G : (G∈𝔇 et w∈G) témoigne (∃G)(G∈𝔇 et w∈G), donc w∈⋃𝔇."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vY, vD, vG = _terme(X), _terme(Y), _terme(D), _terme(G)
    Ut = Union(vX, vY, vD)
    cible = inclus(vG, Ut)
    bndr, _ = _peler_pourtout(cible)
    vw = var(bndr)
    hwG = N.assume(appartient(vw, vG))                          # w∈G
    corps_temoin = conjonction_intro(hGD, hwG)                  # G∈𝔇 et w∈G
    R = et(appartient(var("G"), vD), appartient(vw, var("G")))
    ex = N.modus_ponens(corps_temoin, N.s5(R, vG, "G"))        # (∃G)(G∈𝔇 et w∈G)
    wU = N.modus_ponens(ex, equivalence_arriere(_inst_Union(vX, vY, vD, vw)))  # w∈⋃𝔇
    body = N.loi_deduction(appartient(vw, vG), wU)
    return N.generalisation(bndr, body)                        # G⊂⋃𝔇


def Union_majorant(X="X", Y="Y", D="D", G="x"):
    """⊢ { 𝔇⊂Inj, totalement_ordonne(ΓI,𝔇) } ⊢ majorant(ΓI, 𝔇, ⋃𝔇, Inj).

    majorant(ΓI,𝔇,⋃𝔇,Inj) = ⋃𝔇∈Inj et (∀G)(G∈𝔇 ⇒ (G,⋃𝔇)∈ΓI).  ⋃𝔇∈Inj
    (Union_dans_Inj) ; et pour G∈𝔇 : G∈Inj (𝔇⊂Inj), ⋃𝔇∈Inj, G⊂⋃𝔇 ⇒ (G,⋃𝔇)∈ΓI."""
    vX, vY, vD = var(X), var(Y), var(D)
    Ut = Union(vX, vY, vD)
    HDI = N.assume(inclus(vD, Inj(vX, vY)))                     # 𝔇⊂Inj
    U_I = Union_dans_Inj(X, Y, D)                              # ⋃𝔇∈Inj  [2 hyps]
    vG = var(G)
    hGD = N.assume(appartient(vG, vD))                         # G∈𝔇
    GI = N.modus_ponens(hGD, instancie(HDI, vG))              # G∈Inj
    G_U = _G_inclus_Union(vX, vY, vD, vG, hGD)                # G⊂⋃𝔇
    G_U_Gamma = _Gamma_intro(vX, vY, vG, Ut, GI, U_I, G_U)    # (G,⋃𝔇)∈ΓI
    body = N.loi_deduction(appartient(vG, vD), G_U_Gamma)
    allG = N.generalisation(G, body)                          # (∀G)(G∈𝔇⇒(G,⋃𝔇)∈ΓI)
    return conjonction_intro(U_I, allG)                       # majorant(ΓI,𝔇,⋃𝔇,Inj)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 2 (assemblage) — (ΓI, Inj) est INDUCTIF
#  est_inductif(ΓI,Inj) = est_ordre(ΓI,Inj) et (∀C)(chaine(ΓI,Inj,C) ⇒
#  (∃m)majorant(ΓI,C,m,Inj)).  L'ordre vient de Gamma_est_ordre ; le majorant
#  d'une ΓI-chaîne est ⋃C (Union_majorant), TÉMOIN du (∃m).
# ════════════════════════════════════════════════════════════════════════════
def Inj_inductif(X="X", Y="Y", D="C", m="m", x="x", y="y", z="z"):
    """⊢ est_inductif(ΓI, Inj).   (INCONDITIONNEL — theorie_ensembles()=22.)

    🎯 LE CŒUR de la comparabilité : toute ΓI-chaîne d'injections partielles est
    majorée par sa réunion (qui est une injection partielle).  est_ordre(ΓI,Inj)
    inconditionnel ; pour une ΓI-chaîne C (chaine(ΓI,Inj,C) = C⊂Inj et
    totalement_ordonne(ΓI,C)), ⋃C majore C (Union_majorant), témoin du (∃m)."""
    vX, vY, vD = var(X), var(Y), var(D)
    Gam, Inj_set = Gamma(vX, vY), Inj(vX, vY)
    Ut = Union(vX, vY, vD)
    # est_ordre(ΓI,Inj) — inconditionnel
    ord_GI = Gamma_est_ordre(X, Y)
    # corps : chaine(ΓI,Inj,C) ⇒ (∃m) majorant(ΓI,C,m,Inj)
    Hch = N.assume(chaine(Gam, Inj_set, vD, x, y, z))         # chaine(ΓI,Inj,C)
    D_I = conjonction_elim_gauche(Hch)                        # C⊂Inj
    tot_D = conjonction_elim_droite(Hch)                      # totalement_ordonne(ΓI,C)
    maj_U = Union_majorant(X, Y, D)                           # majorant(ΓI,C,⋃C,Inj)  [2 hyps]
    maj_U = _cut(maj_U, inclus(vD, Inj_set), D_I)
    maj_U = _cut(maj_U, totalement_ordonne(Gam, vD), tot_D)   # majorant(ΓI,C,⋃C,Inj)  [aucune hyp]
    # (∃m) majorant(ΓI,C,m,Inj)  via S5, témoin m=⋃C
    corps_m = majorant(Gam, vD, var(m), Inj_set, x)
    s5 = N.s5(corps_m, Ut, m)                                 # (⋃C|m)corps ⇒ (∃m)corps
    ex_maj = N.modus_ponens(maj_U, s5)                        # (∃m)majorant(ΓI,C,m,Inj)
    body = N.loi_deduction(chaine(Gam, Inj_set, vD, x, y, z), ex_maj)
    allD = N.generalisation(D, body)                          # (∀D)(chaine⇒(∃m)majorant)
    # α-renomme le liant D → C pour matcher est_inductif(ΓI,Inj) (binder canonique « C »)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    _, corps_D = _peler_pourtout(allD.conclusion)
    if D != "C":
        from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_pour_tout
        ren = alpha_pour_tout(D, "C", corps_D)
        allD = N.modus_ponens(allD, equivalence_avant(ren))
    return conjonction_intro(ord_GI, allD)                    # est_inductif(ΓI,Inj)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 3 — Inj ≠ ∅ (le GRAPHE VIDE ∅ est une injection partielle), puis ZORN.
# ════════════════════════════════════════════════════════════════════════════
def _nz_vide(z):
    """⊢ ¬( z ∈ ∅ )  pour un TERME z  (axiome du vide instancié)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)
    return instancie(ax, _terme(z))


def _exfalso_vide(z, phi):
    """De z TERME et une formule Φ, déduit ⊢ ( z∈∅ ⇒ Φ )  (vacuité)."""
    nz = _nz_vide(z)
    return N.modus_ponens(nz, N.s2(non(appartient(_terme(z), E.VIDE)), phi))


def _vide_inclus(t, z="_zv"):
    """⊢ ∅ ⊂ t  pour un TERME t  (le vide est inclus dans tout ensemble)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vt = _terme(t)
    cible = inclus(E.VIDE, vt)
    bndr, _ = _peler_pourtout(cible)
    zt = var(bndr)
    imp = _exfalso_vide(zt, appartient(zt, vt))
    return N.generalisation(bndr, imp)


def vide_inj_partielle(X="X", Y="Y"):
    """⊢ inj_partielle(∅, X, Y).   (Le graphe VIDE est une injection partielle.)

    ∅⊂X×Y (vacuité) ; est_fonctionnel(∅) et graphe_injectif(∅) : leurs hypothèses
    « (u,v)∈∅ » sont fausses, donc les implications sont vacuement vraies."""
    vX, vY = var(X), var(Y)
    XY = E.produit(vX, vY)
    # ∅⊂X×Y
    vide_XY = _vide_inclus(XY)
    # est_fonctionnel(∅) = (∀u∀v∀z)(((u,v)∈∅ et (u,z)∈∅) ⇒ v=z)  — vacuité via (u,v)∈∅
    vu, vv, vz = var("u"), var("v"), var("z")
    func_body = _exfalso_vide_conj(E.couple(vu, vv), E.couple(vu, vz), egal(vv, vz))
    func = N.generalisation("u", N.generalisation("v", N.generalisation("z", func_body)))
    # graphe_injectif(∅) = (∀a∀b∀a')(((a,b)∈∅ et (a',b)∈∅) ⇒ a=a')  — vacuité
    va, vb, vap = var("a"), var("b"), var("ap")
    inj_body = _exfalso_vide_conj(E.couple(va, vb), E.couple(vap, vb), egal(va, vap))
    ginj = N.generalisation("a", N.generalisation("b", N.generalisation("ap", inj_body)))
    return conjonction_intro(conjonction_intro(vide_XY, func), ginj)  # inj_partielle(∅,X,Y)


def _exfalso_vide_conj(c1, c2, phi):
    """De c1,c2 TERMES et Φ, déduit ⊢ ( (c1∈∅ et c2∈∅) ⇒ Φ )  (vacuité via c1∈∅)."""
    vc1 = _terme(c1)
    H = N.assume(et(appartient(vc1, E.VIDE), appartient(_terme(c2), E.VIDE)))
    c1_vide = conjonction_elim_gauche(H)
    falso = N.modus_ponens(c1_vide, _exfalso_vide(vc1, phi))
    return N.loi_deduction(et(appartient(vc1, E.VIDE), appartient(_terme(c2), E.VIDE)), falso)


def vide_dans_Inj(X="X", Y="Y"):
    """⊢ ∅ ∈ Inj.   (∅ est une injection partielle (vide_inj_partielle), axiome de Inj.)"""
    vX, vY = var(X), var(Y)
    inj_vide = vide_inj_partielle(X, Y)                       # inj_partielle(∅,X,Y)
    return N.modus_ponens(inj_vide, equivalence_arriere(_inst_Inj(vX, vY, E.VIDE)))  # ∅∈Inj


def Inj_non_vide(X="X", Y="Y", w="w"):
    """⊢ Inj ≠ ∅.   (= enonce_non_vide(Inj) = (∃w)(w∈Inj) ; témoin ∅∈Inj.)"""
    vX, vY = var(X), var(Y)
    vide_I = vide_dans_Inj(X, Y)                              # ∅∈Inj
    R = appartient(var(w), Inj(vX, vY))
    return N.modus_ponens(vide_I, N.s5(R, E.VIDE, w))         # (∃w)(w∈Inj)


# ── ZORN instancié à (ΓI, Inj) ───────────────────────────────────────────────
def _zorn_instancie(X, Y):
    """⊢ ( est_ordre(ΓI,Inj) et est_inductif(ΓI,Inj) et Inj≠∅ ) ⇒ (∃m)maximal(ΓI,Inj,m).

    zorn_theoreme() (CLOS) instancié à G:=ΓI(X,Y), E:=Inj(X,Y) via des PIVOTS frais
    g0,e0 (motif _bw_strict_contra_terme) pour éviter toute capture de X,Y."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn_theoreme import zorn_theoreme
    g0, e0 = "_cg0", "_ce0"
    vg0, ve0 = var(g0), var(e0)
    Gam0, Inj0 = Gamma(vg0, ve0), Inj(vg0, ve0)
    th = zorn_theoreme()                                     # CLOS (binders G,E,m,C,x,y,z)
    th = N.generalisation("G", N.generalisation("E", th))   # (∀E∀G)( … )
    th = instancie(th, Gam0)                                 # G:=ΓI(g0,e0)
    th = instancie(th, Inj0)                                 # E:=Inj(g0,e0)
    # g0,e0 sont les seules lettres libres → substituables
    th = instancie(N.generalisation(g0, th), _terme(X))     # g0:=X
    th = instancie(N.generalisation(e0, th), _terme(Y))     # e0:=Y
    return th


def maximal_existe(X="X", Y="Y", m="m"):
    """⊢ (∃m) element_maximal(ΓI, Inj, m).   (INCONDITIONNEL — via ZORN.)

    Les trois prémisses de Zorn sont PROUVÉES : est_ordre(ΓI,Inj) (Gamma_est_ordre),
    est_inductif(ΓI,Inj) (Inj_inductif), Inj≠∅ (Inj_non_vide).  Donc Zorn donne
    l'existence d'une injection partielle MAXIMALE g.  Rien postulé."""
    vX, vY = var(X), var(Y)
    Gam, Inj_set = Gamma(vX, vY), Inj(vX, vY)
    ord_GI = Gamma_est_ordre(X, Y)                           # est_ordre(ΓI,Inj)  [binders x,y,z]
    ind_GI = Inj_inductif(X, Y)                              # est_inductif(ΓI,Inj)  [binders C,m,x,y,z]
    nv = Inj_non_vide(X, Y, "x")                             # Inj≠∅  [binder x, matche enonce_non_vide]
    premisses = conjonction_intro(conjonction_intro(ord_GI, ind_GI), nv)
    zorn = _zorn_instancie(vX, vY)                           # premisses ⇒ (∃m)maximal
    return N.modus_ponens(premisses, zorn)                  # (∃m)element_maximal(ΓI,Inj,m)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 — un g MAXIMAL vérifie  dom(g)=X OU img(g)=Y.
#  Outillage : dom(g)⊂X, img(g)⊂Y (g⊂X×Y), et « sous-ensemble propre ⇒ témoin ».
# ════════════════════════════════════════════════════════════════════════════
def _inst_dom(g, x):
    """⊢ (x∈dom g) ⇔ (∃y)((x,y)∈g)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _terme(g)), _terme(x))


def _inst_img(g, y):
    """⊢ (y∈img g) ⇔ (∃x)((x,y)∈g)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, _terme(g)), _terme(y))


def _prod_couple(u, v, A, B):
    """⊢ ((u,v)∈A×B) ⇔ (u∈A et v∈B)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import couple_dans_produit_ssi
    return couple_dans_produit_ssi(_terme(u), _terme(v), _terme(A), _terme(B))


def dom_inclus_X(X="X", Y="Y", g="g", x="x", y="y"):
    """⊢ { g⊂X×Y } ⊢ dom(g) ⊂ X.

    x∈dom g ⇒ (∃y)((x,y)∈g) ; (x,y)∈g⊂X×Y ⇒ (x,y)∈X×Y ⇒ x∈X (1re projection)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    XY = E.produit(vX, vY)
    cible = inclus(E.dom(vg), vX)
    bndr, _ = _peler_pourtout(cible)
    vx = var(bndr)
    Hsub = N.assume(inclus(vg, XY))                          # g⊂X×Y
    hxdom = N.assume(appartient(vx, E.dom(vg)))              # x∈dom g
    ex = N.modus_ponens(hxdom, equivalence_avant(_inst_dom(vg, vx)))  # (∃y)((x,y)∈g)
    vy = var(y)
    Hw = N.assume(appartient(E.couple(vx, vy), vg))         # (x,y)∈g
    cpl_XY = N.modus_ponens(Hw, instancie(Hsub, E.couple(vx, vy)))   # (x,y)∈X×Y
    xX = conjonction_elim_gauche(N.modus_ponens(cpl_XY,
            equivalence_avant(_prod_couple(vx, vy, vX, vY))))        # x∈X
    wit_imp = N.loi_deduction(appartient(E.couple(vx, vy), vg), xX)
    ex_imp = existe_elimination(wit_imp, y)                  # (∃y)((x,y)∈g) ⇒ x∈X
    xX_final = N.modus_ponens(ex, ex_imp)                   # x∈X  [x∈dom g, g⊂X×Y]
    body = N.loi_deduction(appartient(vx, E.dom(vg)), xX_final)
    return N.generalisation(bndr, body)                     # dom g ⊂ X


def img_inclus_Y(X="X", Y="Y", g="g", x="x", y="y"):
    """⊢ { g⊂X×Y } ⊢ img(g) ⊂ Y.

    y∈img g ⇒ (∃x)((x,y)∈g) ; (x,y)∈g⊂X×Y ⇒ (x,y)∈X×Y ⇒ y∈Y (2e projection)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    XY = E.produit(vX, vY)
    cible = inclus(E.img(vg), vY)
    bndr, _ = _peler_pourtout(cible)
    vy = var(bndr)
    Hsub = N.assume(inclus(vg, XY))                          # g⊂X×Y
    hyimg = N.assume(appartient(vy, E.img(vg)))             # y∈img g
    ex = N.modus_ponens(hyimg, equivalence_avant(_inst_img(vg, vy)))  # (∃x)((x,y)∈g)
    vx = var(x)
    Hw = N.assume(appartient(E.couple(vx, vy), vg))         # (x,y)∈g
    cpl_XY = N.modus_ponens(Hw, instancie(Hsub, E.couple(vx, vy)))   # (x,y)∈X×Y
    yY = conjonction_elim_droite(N.modus_ponens(cpl_XY,
            equivalence_avant(_prod_couple(vx, vy, vX, vY))))        # y∈Y
    wit_imp = N.loi_deduction(appartient(E.couple(vx, vy), vg), yY)
    ex_imp = existe_elimination(wit_imp, x)                  # (∃x)((x,y)∈g) ⇒ y∈Y
    yY_final = N.modus_ponens(ex, ex_imp)                   # y∈Y  [y∈img g, g⊂X×Y]
    body = N.loi_deduction(appartient(vy, E.img(vg)), yY_final)
    return N.generalisation(bndr, body)                     # img g ⊂ Y


# ── sous-ensemble propre ⇒ témoin d'un point manquant ────────────────────────
def _sous_propre_temoin(A, B, hAB, hAneB, z="z"):
    """{ A⊂B [hAB], A≠B [hAneB] } ⊢ (∃z)(z∈B et z∉A).

    Si B⊂A, alors (A⊂B et B⊂A) ⇒ A=B (A1), contredisant A≠B ; donc ¬(B⊂A) =
    ¬(∀z)(z∈B⇒z∈A), d'où (∃z)¬(z∈B⇒z∈A) ⇔ (∃z)(z∈B et z∉A)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import dne
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self, _neg_impl_equiv
    vA, vB = _terme(A), _terme(B)
    vz = var(z)
    BsubA = inclus(vB, vA)                                   # B⊂A = (∀z)(z∈B⇒z∈A)
    # ¬(B⊂A) : assume B⊂A ⇒ A=B (via A1) ⇒ contredit A≠B
    HBA = N.assume(BsubA)
    a1 = extensionnalite_appliquee(vA, vB)                   # (A⊂B et B⊂A) ⇒ A=B
    A_eq_B = N.modus_ponens(conjonction_intro(hAB, HBA), a1)  # A=B   [hAB, B⊂A]
    nBA = _ex_falso(A_eq_B, hAneB, non(BsubA))              # ¬(B⊂A)  [B⊂A, hAB, hAneB]
    not_BsubA = _refute_self(N.loi_deduction(BsubA, nBA))   # ¬(B⊂A)  [hAB, hAneB]
    # ¬(∀z)(z∈B⇒z∈A) ⇒ (∃z)¬(z∈B⇒z∈A)
    Rz = impl(appartient(vz, vB), appartient(vz, vA))
    ex_negRz = N.modus_ponens(not_BsubA, dne(existe(z, non(Rz))))   # (∃z)¬Rz
    # ¬(z∈B⇒z∈A) ⇔ (z∈B et z∉A)
    eqv = _neg_impl_equiv(appartient(vz, vB), appartient(vz, vA))   # ¬(P⇒Q) ⇔ (P et ¬Q)
    return N.modus_ponens(ex_negRz, equivalence_avant(congruence_existe(eqv, z)))


# ── le graphe étendu  D := g ∪ {(x₀,y₀)}  et son test d'appartenance ──────────
def _ext(g, x0, y0):
    """g ∪ {(x₀,y₀)}  (le graphe g augmenté du couple (x₀,y₀))."""
    return E.reunion(_terme(g), E.singleton(E.couple(_terme(x0), _terme(y0))))


def _membre_ext(g, x0, y0, c):
    """⊢ ( c ∈ g∪{(x₀,y₀)} ) ⇔ ( c∈g ou c=(x₀,y₀) )  (axiome réunion + singleton)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import ou_congruence
    vg, c0 = _terme(g), E.couple(_terme(x0), _terme(y0))
    vc = _terme(c)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_REUNION)
    inst = instancie(instancie(instancie(ax, vg), E.singleton(c0)), vc)  # c∈g∪{c0} ⇔ (c∈g ou c∈{c0})
    sm = singleton_membre(vc, c0)                            # c∈{c0} ⇔ c=c0
    aa = a_implique_a(appartient(vc, vg))
    refl_cg = conjonction_intro(aa, aa)                      # (c∈g) ⇔ (c∈g)
    cong = ou_congruence(refl_cg, sm)                        # (c∈g ou c∈{c0}) ⇔ (c∈g ou c=c0)
    return equivalence_transitivite(inst, cong)


def _ext_intro_g(g, x0, y0, c, hcg):
    """De ⊢ c∈g [hcg] déduit ⊢ c∈g∪{(x₀,y₀)}."""
    vc = _terme(c)
    c0 = E.couple(_terme(x0), _terme(y0))
    disj = N.modus_ponens(hcg, N.s2(appartient(vc, _terme(g)), egal(vc, c0)))
    return N.modus_ponens(disj, equivalence_arriere(_membre_ext(g, x0, y0, c)))


def _ext_intro_couple(g, x0, y0):
    """⊢ (x₀,y₀) ∈ g∪{(x₀,y₀)}  (le couple ajouté y appartient)."""
    vg = _terme(g)
    c0 = E.couple(_terme(x0), _terme(y0))
    d1 = N.modus_ponens(N.reflexivite(c0), N.s2(egal(c0, c0), appartient(c0, vg)))   # c0=c0 ∨ c0∈g
    disj = N.modus_ponens(d1, N.s3(egal(c0, c0), appartient(c0, vg)))                # c0∈g ∨ c0=c0
    return N.modus_ponens(disj, equivalence_arriere(_membre_ext(g, x0, y0, c0)))


# ── x₀∉dom g  et  y₀∉img g  (les points manquants ne sont pas déjà pris) ─────
def _pas_dans_dom(g, x0, y0, b="yb"):
    """⊢ { x₀∉dom g } ⊢ ¬( (x₀, b)∈g )  pour tout TERME b.

    Si (x₀,b)∈g alors (∃y)((x₀,y)∈g) (témoin b), donc x₀∈dom g — contredit x₀∉dom g."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vg, vx0, vb = _terme(g), _terme(x0), _terme(b)
    Hnd = N.assume(non(appartient(vx0, E.dom(vg))))         # x₀∉dom g
    Hin = N.assume(appartient(E.couple(vx0, vb), vg))      # (x₀,b)∈g
    ex = N.modus_ponens(Hin, N.s5(appartient(E.couple(vx0, var("y")), vg), vb, "y"))  # (∃y)((x₀,y)∈g)
    x0_dom = N.modus_ponens(ex, equivalence_arriere(_inst_dom(vg, vx0)))   # x₀∈dom g
    falso = _ex_falso(x0_dom, Hnd, non(appartient(E.couple(vx0, vb), vg)))  # ¬((x₀,b)∈g)
    return _refute_self(N.loi_deduction(appartient(E.couple(vx0, vb), vg), falso))


def _pas_dans_img(g, x0, y0, a="xa"):
    """⊢ { y₀∉img g } ⊢ ¬( (a, y₀)∈g )  pour tout TERME a.

    Si (a,y₀)∈g alors (∃x)((x,y₀)∈g) (témoin a), donc y₀∈img g — contredit y₀∉img g."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vg, vy0, va = _terme(g), _terme(y0), _terme(a)
    Hni = N.assume(non(appartient(vy0, E.img(vg))))        # y₀∉img g
    Hin = N.assume(appartient(E.couple(va, vy0), vg))     # (a,y₀)∈g
    ex = N.modus_ponens(Hin, N.s5(appartient(E.couple(var("x"), vy0), vg), va, "x"))  # (∃x)((x,y₀)∈g)
    y0_img = N.modus_ponens(ex, equivalence_arriere(_inst_img(vg, vy0)))   # y₀∈img g
    falso = _ex_falso(y0_img, Hni, non(appartient(E.couple(va, vy0), vg)))  # ¬((a,y₀)∈g)
    return _refute_self(N.loi_deduction(appartient(E.couple(va, vy0), vg), falso))


# ── helpers Leibniz/couples pour les cas « mixtes » ──────────────────────────
def _couple_comps(p, q, x0, y0, hc_eq):
    """De ⊢ (p,q)=(x₀,y₀) [hc_eq] déduit ⊢ (p=x₀ et q=y₀)."""
    from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import couple_egal_implique_composantes
    return N.modus_ponens(hc_eq, couple_egal_implique_composantes(
        _terme(p), _terme(q), _terme(x0), _terme(y0)))


def _leib_eq(a, b, h_ab, phi_fun):
    """De ⊢ a=b [h_ab] déduit ⊢ ( Φ[a] ⇔ Φ[b] )  via S6 (trou _H)."""
    va, vb = _terme(a), _terme(b)
    return N.modus_ponens(h_ab, N.s6(va, vb, _H, phi_fun(var(_H))))


# ── (B) g∪{(x₀,y₀)} est FONCTIONNEL ──────────────────────────────────────────
def _ext_fonctionnel(X, Y, g, x0, y0, Hxnd, u="u", v="v", z="z"):
    """{ est_fonctionnel(g), x₀∉dom g [Hxnd] } ⊢ est_fonctionnel(g∪{(x₀,y₀)}).

    Cas (g,g): g fonctionnel. Cas mixtes (g,c0)/(c0,g): u=x₀ ⇒ (x₀,·)∈g, contredit
    x₀∉dom g (vacuité). Cas (c0,c0): v=y₀=z."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vg, vx0, vy0 = _terme(g), _terme(x0), _terme(y0)
    vu, vv, vz = var(u), var(v), var(z)
    c0 = E.couple(vx0, vy0)
    D = _ext(g, x0, y0)
    Hfg = N.assume(E.est_fonctionnel(vg))                   # est_fonctionnel(g)
    cuv, cuz = E.couple(vu, vv), E.couple(vu, vz)
    hyp = et(appartient(cuv, D), appartient(cuz, D))
    Hpair = N.assume(hyp)
    duv = N.modus_ponens(conjonction_elim_gauche(Hpair), equivalence_avant(_membre_ext(g, x0, y0, cuv)))  # (u,v)∈g ou (u,v)=c0
    duz = N.modus_ponens(conjonction_elim_droite(Hpair), equivalence_avant(_membre_ext(g, x0, y0, cuz)))  # (u,z)∈g ou (u,z)=c0
    but = egal(vv, vz)
    # not (x0,v) in g, not (x0,z) in g  (sous Hxnd)
    not_x0v = _cut(_pas_dans_dom(g, x0, y0, "vb"), non(appartient(vx0, E.dom(vg))), Hxnd)
    not_x0v = instancie(N.generalisation("vb", not_x0v), vv)  # ¬((x0,v)∈g)
    not_x0z = _cut(_pas_dans_dom(g, x0, y0, "vb"), non(appartient(vx0, E.dom(vg))), Hxnd)
    not_x0z = instancie(N.generalisation("vb", not_x0z), vz)  # ¬((x0,z)∈g)
    # branche (u,v)∈g
    Huv_g = N.assume(appartient(cuv, vg))
    #   sous (u,z)∈g : g fonctionnel
    Huz_g = N.assume(appartient(cuz, vg))
    func_inst = instancie(instancie(instancie(Hfg, vu), vv), vz)  # ((u,v)∈g et (u,z)∈g)⇒v=z
    vz_eq = N.modus_ponens(conjonction_intro(Huv_g, Huz_g), func_inst)   # v=z
    b_vg_zg = N.loi_deduction(appartient(cuz, vg), vz_eq)
    #   sous (u,z)=c0 : u=x0 ⇒ (x0,v)∈g (Leibniz), contredit not_x0v
    Huz_c0 = N.assume(egal(cuz, c0))
    comps_z = _couple_comps(vu, vz, vx0, vy0, Huz_c0)            # u=x0 et z=y0
    u_eq_x0 = conjonction_elim_gauche(comps_z)             # u=x0
    x0v_in = N.modus_ponens(Huv_g, equivalence_avant(
        _leib_eq(vu, vx0, u_eq_x0, lambda w: appartient(E.couple(w, vv), vg))))  # (x0,v)∈g
    falso1 = _ex_falso(x0v_in, not_x0v, but)               # v=z (ex falso)
    b_vg_zc0 = N.loi_deduction(egal(cuz, c0), falso1)
    b_vg = N.loi_deduction(appartient(cuv, vg), cas(duz, b_vg_zg, b_vg_zc0))
    # branche (u,v)=c0
    Huv_c0 = N.assume(egal(cuv, c0))
    comps_v = _couple_comps(vu, vv, vx0, vy0, Huv_c0)           # u=x0 et v=y0
    u_eq_x0_b = conjonction_elim_gauche(comps_v)          # u=x0
    v_eq_y0 = conjonction_elim_droite(comps_v)            # v=y0
    #   sous (u,z)∈g : (x0,z)∈g contredit not_x0z
    Huz_g2 = N.assume(appartient(cuz, vg))
    x0z_in = N.modus_ponens(Huz_g2, equivalence_avant(
        _leib_eq(vu, vx0, u_eq_x0_b, lambda w: appartient(E.couple(w, vz), vg))))  # (x0,z)∈g
    falso2 = _ex_falso(x0z_in, not_x0z, but)
    b_vc0_zg = N.loi_deduction(appartient(cuz, vg), falso2)
    #   sous (u,z)=c0 : z=y0 ; v=y0 et z=y0 ⇒ v=z
    Huz_c0b = N.assume(egal(cuz, c0))
    comps_z2 = _couple_comps(vu, vz, vx0, vy0, Huz_c0b)         # u=x0 et z=y0
    z_eq_y0 = conjonction_elim_droite(comps_z2)           # z=y0
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
    y0_eq_z = N.modus_ponens(z_eq_y0, _sym(vz, vy0))      # y0=z
    v_eq_z = composer_egalites(v_eq_y0, y0_eq_z)          # v=z
    b_vc0_zc0 = N.loi_deduction(egal(cuz, c0), v_eq_z)
    b_vc0 = N.loi_deduction(egal(cuv, c0), cas(duz, b_vc0_zg, b_vc0_zc0))
    res = cas(duv, b_vg, b_vc0)                            # v=z
    body = N.loi_deduction(hyp, res)
    return N.generalisation(u, N.generalisation(v, N.generalisation(z, body)))


# ── (C) g∪{(x₀,y₀)} est INJECTIF (comme graphe) ──────────────────────────────
def _ext_injectif(X, Y, g, x0, y0, Hynd, a="a", b="b", ap="ap"):
    """{ graphe_injectif(g), y₀∉img g [Hynd] } ⊢ graphe_injectif(g∪{(x₀,y₀)}).

    Cas (g,g): g injectif. Cas mixtes (g,c0)/(c0,g): b=y₀ ⇒ (·,y₀)∈g, contredit
    y₀∉img g (vacuité). Cas (c0,c0): a=x₀=a'."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
    vg, vx0, vy0 = _terme(g), _terme(x0), _terme(y0)
    va, vb, vap = var(a), var(b), var(ap)
    c0 = E.couple(vx0, vy0)
    D = _ext(g, x0, y0)
    Hig = N.assume(graphe_injectif(vg))                     # graphe_injectif(g)
    cab, capb = E.couple(va, vb), E.couple(vap, vb)
    hyp = et(appartient(cab, D), appartient(capb, D))
    Hpair = N.assume(hyp)
    dab = N.modus_ponens(conjonction_elim_gauche(Hpair), equivalence_avant(_membre_ext(g, x0, y0, cab)))   # (a,b)∈g ou (a,b)=c0
    dapb = N.modus_ponens(conjonction_elim_droite(Hpair), equivalence_avant(_membre_ext(g, x0, y0, capb))) # (a',b)∈g ou (a',b)=c0
    but = egal(va, vap)
    # not (a,y0) in g, not (a',y0) in g  (sous Hynd)
    not_ay0 = _cut(_pas_dans_img(g, x0, y0, "xa"), non(appartient(vy0, E.img(vg))), Hynd)
    not_ay0 = instancie(N.generalisation("xa", not_ay0), va)   # ¬((a,y0)∈g)
    not_apy0 = _cut(_pas_dans_img(g, x0, y0, "xa"), non(appartient(vy0, E.img(vg))), Hynd)
    not_apy0 = instancie(N.generalisation("xa", not_apy0), vap)  # ¬((a',y0)∈g)
    # branche (a,b)∈g
    Hab_g = N.assume(appartient(cab, vg))
    #   sous (a',b)∈g : g injectif
    Hapb_g = N.assume(appartient(capb, vg))
    inj_inst = instancie(instancie(instancie(Hig, va), vb), vap)  # ((a,b)∈g et (a',b)∈g)⇒a=a'
    va_eq = N.modus_ponens(conjonction_intro(Hab_g, Hapb_g), inj_inst)   # a=a'
    b_ag_apg = N.loi_deduction(appartient(capb, vg), va_eq)
    #   sous (a',b)=c0 : b=y0 ⇒ (a,y0)∈g (Leibniz), contredit not_ay0
    Hapb_c0 = N.assume(egal(capb, c0))
    comps_apb = _couple_comps(vap, vb, vx0, vy0, Hapb_c0)   # a'=x0 et b=y0
    b_eq_y0 = conjonction_elim_droite(comps_apb)           # b=y0
    ay0_in = N.modus_ponens(Hab_g, equivalence_avant(
        _leib_eq(vb, vy0, b_eq_y0, lambda w: appartient(E.couple(va, w), vg))))  # (a,y0)∈g
    falso1 = _ex_falso(ay0_in, not_ay0, but)
    b_ag_apc0 = N.loi_deduction(egal(capb, c0), falso1)
    b_ag = N.loi_deduction(appartient(cab, vg), cas(dapb, b_ag_apg, b_ag_apc0))
    # branche (a,b)=c0
    Hab_c0 = N.assume(egal(cab, c0))
    comps_ab = _couple_comps(va, vb, vx0, vy0, Hab_c0)     # a=x0 et b=y0
    a_eq_x0 = conjonction_elim_gauche(comps_ab)           # a=x0
    b_eq_y0_b = conjonction_elim_droite(comps_ab)         # b=y0
    #   sous (a',b)∈g : (a',y0)∈g contredit not_apy0
    Hapb_g2 = N.assume(appartient(capb, vg))
    apy0_in = N.modus_ponens(Hapb_g2, equivalence_avant(
        _leib_eq(vb, vy0, b_eq_y0_b, lambda w: appartient(E.couple(vap, w), vg))))  # (a',y0)∈g
    falso2 = _ex_falso(apy0_in, not_apy0, but)
    b_ac0_apg = N.loi_deduction(appartient(capb, vg), falso2)
    #   sous (a',b)=c0 : a'=x0 ; a=x0 et a'=x0 ⇒ a=a'
    Hapb_c0b = N.assume(egal(capb, c0))
    comps_apb2 = _couple_comps(vap, vb, vx0, vy0, Hapb_c0b)  # a'=x0 et b=y0
    ap_eq_x0 = conjonction_elim_gauche(comps_apb2)        # a'=x0
    x0_eq_ap = N.modus_ponens(ap_eq_x0, _sym(vap, vx0))   # x0=a'
    a_eq_ap = composer_egalites(a_eq_x0, x0_eq_ap)        # a=a'
    b_ac0_apc0 = N.loi_deduction(egal(capb, c0), a_eq_ap)
    b_ac0 = N.loi_deduction(egal(cab, c0), cas(dapb, b_ac0_apg, b_ac0_apc0))
    res = cas(dab, b_ag, b_ac0)                            # a=a'
    body = N.loi_deduction(hyp, res)
    return N.generalisation(a, N.generalisation(b, N.generalisation(ap, body)))


# ── (A) g∪{(x₀,y₀)} ⊂ X×Y ────────────────────────────────────────────────────
def _ext_inclus_produit(X, Y, g, x0, y0, Hgsub, HxX, HyY, c="c"):
    """{ g⊂X×Y [Hgsub], x₀∈X [HxX], y₀∈Y [HyY] } ⊢ g∪{(x₀,y₀)} ⊂ X×Y.

    c∈D ⇒ c∈g⊂X×Y, ou c=(x₀,y₀) avec x₀∈X et y₀∈Y donc (x₀,y₀)∈X×Y."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    vx0, vy0 = _terme(x0), _terme(y0)
    XY = E.produit(vX, vY)
    c0 = E.couple(vx0, vy0)
    D = _ext(g, x0, y0)
    cible = inclus(D, XY)
    bndr, _ = _peler_pourtout(cible)
    vc = var(bndr)
    hcD = N.assume(appartient(vc, D))                       # c∈D
    disj = N.modus_ponens(hcD, equivalence_avant(_membre_ext(g, x0, y0, vc)))  # c∈g ou c=c0
    # c∈g ⇒ c∈X×Y
    Hcg = N.assume(appartient(vc, vg))
    b1 = N.loi_deduction(appartient(vc, vg), N.modus_ponens(Hcg, instancie(Hgsub, vc)))
    # c=c0 ⇒ c∈X×Y  (c0∈X×Y via x0∈X, y0∈Y ; Leibniz)
    c0_XY = N.modus_ponens(conjonction_intro(HxX, HyY),
                           equivalence_arriere(_prod_couple(vx0, vy0, vX, vY)))  # (x0,y0)∈X×Y
    Hcc0 = N.assume(egal(vc, c0))
    c_XY = N.modus_ponens(c0_XY, equivalence_arriere(
        _leib_eq(vc, c0, Hcc0, lambda w: appartient(w, XY))))   # c∈X×Y
    b2 = N.loi_deduction(egal(vc, c0), c_XY)
    cXY = cas(disj, b1, b2)
    body = N.loi_deduction(appartient(vc, D), cXY)
    return N.generalisation(bndr, body)                     # D⊂X×Y


# ── g ⊂ g∪{(x₀,y₀)}  et  g ≠ g∪{(x₀,y₀)} (strictement plus grand) ────────────
def _g_inclus_ext(g, x0, y0, c="c"):
    """⊢ g ⊂ g∪{(x₀,y₀)}.   (tout c∈g est dans la réunion.)"""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vg = _terme(g)
    D = _ext(g, x0, y0)
    cible = inclus(vg, D)
    bndr, _ = _peler_pourtout(cible)
    vc = var(bndr)
    hcg = N.assume(appartient(vc, vg))
    cD = _ext_intro_g(g, x0, y0, vc, hcg)                   # c∈D
    return N.generalisation(bndr, N.loi_deduction(appartient(vc, vg), cD))


def _g_ne_ext(g, x0, y0, Hxnd):
    """{ x₀∉dom g [Hxnd] } ⊢ g ≠ g∪{(x₀,y₀)}.

    (x₀,y₀)∈D ; si g=D alors (x₀,y₀)∈g (Leibniz), donc (∃y)((x₀,y)∈g), donc
    x₀∈dom g — contredit x₀∉dom g."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso, _refute_self
    vg, vx0, vy0 = _terme(g), _terme(x0), _terme(y0)
    c0 = E.couple(vx0, vy0)
    D = _ext(g, x0, y0)
    Heq = N.assume(egal(vg, D))                            # g=D
    c0_D = _ext_intro_couple(g, x0, y0)                    # (x0,y0)∈D
    # Leibniz : (D=g) ⇒ ((c0∈D) ⇔ (c0∈g))
    D_eq_g = N.modus_ponens(Heq, _sym(vg, D))             # D=g
    c0_g = N.modus_ponens(c0_D, equivalence_avant(
        _leib_eq(D, vg, D_eq_g, lambda w: appartient(c0, w))))  # (x0,y0)∈g
    x0_dom = N.modus_ponens(N.modus_ponens(c0_g, N.s5(appartient(E.couple(vx0, var("y")), vg), vy0, "y")),
                            equivalence_arriere(_inst_dom(vg, vx0)))  # x0∈dom g
    falso = _ex_falso(x0_dom, Hxnd, non(egal(vg, D)))     # ¬(g=D)
    return _refute_self(N.loi_deduction(egal(vg, D), falso))  # g≠D


# ── le graphe étendu est une INJECTION PARTIELLE (3 conjoints) ───────────────
def _ext_dans_Inj(X, Y, g, x0, y0, Hgsub, Hfg, Hig, HxX, HyY, Hxnd, Hynd):
    """{ g⊂X×Y, est_fonctionnel(g), graphe_injectif(g), x₀∈X, y₀∈Y, x₀∉dom g,
        y₀∉img g } ⊢ g∪{(x₀,y₀)} ∈ Inj.

    Les trois conjoints de inj_partielle(D,X,Y) : D⊂X×Y (_ext_inclus_produit),
    est_fonctionnel(D) (_ext_fonctionnel), graphe_injectif(D) (_ext_injectif) ;
    puis l'axiome de Inj."""
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    vx0, vy0 = _terme(x0), _terme(y0)
    D = _ext(g, x0, y0)
    # (A) D⊂X×Y
    D_XY = _ext_inclus_produit(X, Y, g, x0, y0, Hgsub, HxX, HyY)
    # (B) est_fonctionnel(D)  (décharge est_fonctionnel(g) ; x₀∉dom g reste via Hxnd)
    D_func = _ext_fonctionnel(X, Y, g, x0, y0, Hxnd)
    D_func = _cut(D_func, E.est_fonctionnel(vg), Hfg)
    # (C) graphe_injectif(D)  (décharge graphe_injectif(g) ; y₀∉img g via Hynd)
    D_inj = _ext_injectif(X, Y, g, x0, y0, Hynd)
    D_inj = _cut(D_inj, graphe_injectif(vg), Hig)
    inj_D = conjonction_intro(conjonction_intro(D_XY, D_func), D_inj)  # inj_partielle(D,X,Y)
    return N.modus_ponens(inj_D, equivalence_arriere(_inst_Inj(vX, vY, D)))  # D∈Inj


# ── la contradiction avec la maximalité (sous dom≠X et img≠Y) ────────────────
def _extension_contredit_maximal(X, Y, g, x0, y0, Hmax, Hgsub, Hfg, Hig,
                                 HxX, Hxnd, HyY, Hynd):
    """{ element_maximal(ΓI,Inj,g) [Hmax], g⊂X×Y, est_fonctionnel(g),
        graphe_injectif(g), x₀∈X, x₀∉dom g, y₀∈Y, y₀∉img g } ⊢ ⊥ (toute formule).

    Renvoie ¬(g≠D) ET g≠D, sous forme d'une réfutation : on construit la formule
    FALSE = (g=D) à partir de la maximalité, contredite par g≠D ; pratiquement on
    renvoie ⊢ Φ pour Φ arbitraire passé en `but` (via _ex_falso).  Ici on expose
    plutôt directement la conjonction contradictoire via maximalité→D=g, g≠D."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    Gam, Inj_set = Gamma(vX, vY), Inj(vX, vY)
    D = _ext(g, x0, y0)
    # D∈Inj
    D_I = _ext_dans_Inj(X, Y, g, x0, y0, Hgsub, Hfg, Hig, HxX, HyY, Hxnd, Hynd)
    # g∈Inj (depuis maximal : g∈Inj)
    gI = conjonction_elim_gauche(Hmax)                    # g∈Inj
    # (g,D)∈ΓI
    g_D = _g_inclus_ext(g, x0, y0)                        # g⊂D
    gD_Gamma = _Gamma_intro(vX, vY, vg, D, gI, D_I, g_D)  # (g,D)∈ΓI
    # maximalité instanciée en D : (D∈Inj et (g,D)∈ΓI) ⇒ D=g
    max_body = conjonction_elim_droite(Hmax)             # (∀x)((x∈Inj et (g,x)∈ΓI)⇒x=g)
    max_inst = instancie(max_body, D)                    # (D∈Inj et (g,D)∈ΓI)⇒D=g
    D_eq_g = N.modus_ponens(conjonction_intro(D_I, gD_Gamma), max_inst)  # D=g
    g_eq_D = N.modus_ponens(D_eq_g, _sym(D, vg))         # g=D
    g_ne_D = _g_ne_ext(g, x0, y0, Hxnd)                  # g≠D  (sous Hxnd, déjà porté)
    # contradiction : g=D et g≠D ⇒ toute formule (renvoie le couple pour usage amont)
    return g_eq_D, g_ne_D


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 4 (assemblage) — un g MAXIMAL vérifie  dom(g)=X OU img(g)=Y.
# ════════════════════════════════════════════════════════════════════════════
def maximal_dom_ou_img(X="X", Y="Y", g="g", x0="x0", y0="y0", z="z"):
    """⊢ { element_maximal(ΓI, Inj, g) } ⊢ ( dom(g)=X ou img(g)=Y ).

    Par l'absurde sur la disjonction.  Si dom(g)≠X ET img(g)≠Y : g∈Inj donne
    dom g⊂X, img g⊂Y ; les sous-ensembles propres fournissent x₀∈X∖dom g et
    y₀∈Y∖img g ; alors g∪{(x₀,y₀)}∈Inj est STRICTEMENT plus grand que g
    (_extension_contredit_maximal), ce qui contredit la maximalité (D=g et g≠D)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_bourbaki_witt_chaine import _ex_falso
    vX, vY, vg = var(X), var(Y), var(g)
    Gam, Inj_set = Gamma(vX, vY), Inj(vX, vY)
    Hmax = N.assume(element_maximal(Gam, Inj_set, vg, "x"))   # element_maximal(ΓI,Inj,g)
    domX = egal(E.dom(vg), vX)
    imgY = egal(E.img(vg), vY)
    but = ou(domX, imgY)
    # g∈Inj ⇒ inj_partielle(g,X,Y)
    gI = conjonction_elim_gauche(Hmax)                       # g∈Inj
    inj_g = N.modus_ponens(gI, equivalence_avant(_inst_Inj(vX, vY, vg)))  # inj_partielle(g,X,Y)
    Hgsub = conjonction_elim_gauche(conjonction_elim_gauche(inj_g))  # g⊂X×Y
    Hfg = conjonction_elim_droite(conjonction_elim_gauche(inj_g))   # est_fonctionnel(g)
    Hig = conjonction_elim_droite(inj_g)                     # graphe_injectif(g)
    # dom g⊂X, img g⊂Y
    domsub = _cut(dom_inclus_X(X, Y, g), inclus(vg, E.produit(vX, vY)), Hgsub)
    imgsub = _cut(img_inclus_Y(X, Y, g), inclus(vg, E.produit(vX, vY)), Hgsub)

    # ── tiers_exclu sur dom g = X ──────────────────────────────────────────────
    te_dom = tiers_exclu(domX)                               # (dom g=X) ou ¬(dom g=X)
    # cas dom g=X : conclure (dom g=X ou img g=Y) à gauche
    cas_domX = N.loi_deduction(domX, _ou_gauche(N.assume(domX), imgY))
    # cas dom g≠X : prouver img g=Y (à droite)
    HdomNE = N.assume(non(domX))                            # dom g≠X
    # tiers_exclu sur img g = Y
    te_img = tiers_exclu(imgY)
    cas_imgY = N.loi_deduction(imgY, _ou_droite(N.assume(imgY), domX))
    # cas img g≠Y : contradiction ⇒ (dom g=X ou img g=Y) par ex falso
    HimgNE = N.assume(non(imgY))                            # img g≠Y
    # témoins x₀∈X∖dom g, y₀∈Y∖img g
    ex_x0 = _sous_propre_temoin(E.dom(vg), vX, domsub, HdomNE, z)   # (∃z)(z∈X et z∉dom g)
    ex_x0 = _alpha_ex(ex_x0, z, x0, et(appartient(var(z), vX), non(appartient(var(z), E.dom(vg)))))
    ex_y0 = _sous_propre_temoin(E.img(vg), vY, imgsub, HimgNE, z)   # (∃z)(z∈Y et z∉img g)
    ex_y0 = _alpha_ex(ex_y0, z, y0, et(appartient(var(z), vY), non(appartient(var(z), E.img(vg)))))
    vx0, vy0 = var(x0), var(y0)
    # sous les deux témoins : contradiction ⇒ but
    Hwx = N.assume(et(appartient(vx0, vX), non(appartient(vx0, E.dom(vg)))))
    HxX = conjonction_elim_gauche(Hwx)                     # x₀∈X
    Hxnd = conjonction_elim_droite(Hwx)                    # x₀∉dom g
    Hwy = N.assume(et(appartient(vy0, vY), non(appartient(vy0, E.img(vg)))))
    HyY = conjonction_elim_gauche(Hwy)                     # y₀∈Y
    Hynd = conjonction_elim_droite(Hwy)                    # y₀∉img g
    g_eq_D, g_ne_D = _extension_contredit_maximal(
        X, Y, g, x0, y0, Hmax, Hgsub, Hfg, Hig, HxX, Hxnd, HyY, Hynd)  # g=D, g≠D
    contra = _ex_falso(g_eq_D, g_ne_D, but)               # but  [Hwx, Hwy, …]
    # éliminer ∃y₀ puis ∃x₀
    wit_y = N.loi_deduction(et(appartient(vy0, vY), non(appartient(vy0, E.img(vg)))), contra)
    ex_imp_y = existe_elimination(wit_y, y0)              # (∃y₀)(…) ⇒ but   [Hwx,…]
    after_y = N.modus_ponens(ex_y0, ex_imp_y)            # but   [Hwx,…]
    wit_x = N.loi_deduction(et(appartient(vx0, vX), non(appartient(vx0, E.dom(vg)))), after_y)
    ex_imp_x = existe_elimination(wit_x, x0)             # (∃x₀)(…) ⇒ but
    cas_imgNE = N.loi_deduction(non(imgY), N.modus_ponens(ex_x0, ex_imp_x))  # ¬(img g=Y) ⇒ but
    # combiner les cas img
    res_imgY = cas(te_img, cas_imgY, cas_imgNE)          # but  (sous dom g≠X)
    cas_domNE = N.loi_deduction(non(domX), res_imgY)     # ¬(dom g=X) ⇒ but
    return cas(te_dom, cas_domX, cas_domNE)              # but = (dom g=X ou img g=Y)  [Hmax]


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE 5 — CONCLUSION : si dom g=X, g injecte X→Y ; si img g=Y, g⁻¹ injecte Y→X.
# ════════════════════════════════════════════════════════════════════════════
def _injective_dans_de_graphe(g, X, hdomX, Hfg, Hig, u="u", up="up"):
    """{ dom g=X [hdomX], est_fonctionnel(g), graphe_injectif(g) }
       ⊢ injective_dans(g, X).

    injective_dans(g,X) = (∀u∀u')((u∈X et u'∈X et g(u)=g(u')) ⇒ u=u').  u,u'∈X=dom g
    ⇒ (u,g(u))∈g et (u',g(u'))∈g (valeur_dans_graphe) ; g(u)=g(u') ⇒ (u',g(u))∈g
    (Leibniz), donc graphe_injectif(g) donne u=u'."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import valeur_dans_graphe
    vg, vX = _terme(g), _terme(X)
    vu, vup = var(u), var(up)
    gu, gup = E.valeur(vg, vu), E.valeur(vg, vup)
    hyp = et(et(appartient(vu, vX), appartient(vup, vX)), egal(gu, gup))
    H = N.assume(hyp)
    uX = conjonction_elim_gauche(conjonction_elim_gauche(H))    # u∈X
    upX = conjonction_elim_droite(conjonction_elim_gauche(H))   # u'∈X
    gu_eq = conjonction_elim_droite(H)                          # g(u)=g(u')
    # u∈X=dom g ⇒ u∈dom g  (Leibniz X=dom g)
    domX_sym = N.modus_ponens(hdomX, _sym(E.dom(vg), vX))      # X=dom g
    u_dom = N.modus_ponens(uX, equivalence_avant(
        _leib_eq(vX, E.dom(vg), domX_sym, lambda w: appartient(vu, w))))   # u∈dom g
    up_dom = N.modus_ponens(upX, equivalence_avant(
        _leib_eq(vX, E.dom(vg), domX_sym, lambda w: appartient(vup, w))))  # u'∈dom g
    # (∃y)((u,y)∈g) et (∃y)((u',y)∈g)  via axiome domaine
    ex_u = N.modus_ponens(u_dom, equivalence_avant(_inst_dom(vg, vu)))     # (∃y)((u,y)∈g)
    ex_up = N.modus_ponens(up_dom, equivalence_avant(_inst_dom(vg, vup)))  # (∃y)((u',y)∈g)
    # (u,g(u))∈g, (u',g(u'))∈g
    u_gu = _cut(valeur_dans_graphe(vg, vu), existe("y", appartient(E.couple(vu, var("y")), vg)), ex_u)
    up_gup = _cut(valeur_dans_graphe(vg, vup), existe("y", appartient(E.couple(vup, var("y")), vg)), ex_up)
    # (u',g(u))∈g  via g(u')=g(u) Leibniz dans (u', ·)∈g
    gup_gu = N.modus_ponens(gu_eq, _sym(gu, gup))             # g(u')=g(u)
    up_gu = N.modus_ponens(up_gup, equivalence_avant(
        _leib_eq(gup, gu, gup_gu, lambda w: appartient(E.couple(vup, w), vg))))  # (u',g(u))∈g
    # graphe_injectif(g) : ((u,g(u))∈g et (u',g(u))∈g) ⇒ u=u'
    inj_inst = instancie(instancie(instancie(Hig, vu), gu), vup)
    u_eq_up = N.modus_ponens(conjonction_intro(u_gu, up_gu), inj_inst)     # u=u'
    body = N.loi_deduction(hyp, u_eq_up)
    return N.generalisation(u, N.generalisation(up, body))    # injective_dans(g,X)


def _image_inclus_Y(g, X, Y, Himgsub, u="u", z="z"):
    """{ img g⊂Y [Himgsub] } ⊢ image(g,X) ⊂ Y.

    z∈g⟨X⟩ ⇒ (∃u)(u∈X et (u,z)∈g) ; (u,z)∈g ⇒ z∈img g (axiome img) ⇒ z∈Y."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vg, vX, vY = _terme(g), _terme(X), _terme(Y)
    cible = inclus(E.image(vg, vX), vY)
    bndr, _ = _peler_pourtout(cible)
    vz = var(bndr)
    # z∈g⟨X⟩ ⇔ (∃u)(u∈X et (u,z)∈g)  (axiome IMAGE) ; on récupère le liant frais
    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    img_car0 = instancie(instancie(instancie(ax_img, vg), vX), vz)
    impl_LtoEX = img_car0.conclusion.sous[0].sous[0].sous[0]
    rhs_ex = impl_LtoEX.sous[1]
    nom_lie = rhs_ex.lieur
    inner = et(appartient(var(nom_lie), vX), appartient(E.couple(var(nom_lie), vz), vg))
    ren = alpha_existe(nom_lie, u, inner)
    img_car = equivalence_transitivite(img_car0, ren)         # z∈g⟨X⟩ ⇔ (∃u)(u∈X et (u,z)∈g)
    vu = var(u)
    hz = N.assume(appartient(vz, E.image(vg, vX)))            # z∈g⟨X⟩
    ex = N.modus_ponens(hz, equivalence_avant(img_car))      # (∃u)(u∈X et (u,z)∈g)
    body_ex = et(appartient(vu, vX), appartient(E.couple(vu, vz), vg))
    Hw = N.assume(body_ex)
    uz_in = conjonction_elim_droite(Hw)                      # (u,z)∈g
    z_img = N.modus_ponens(N.modus_ponens(uz_in, N.s5(appartient(E.couple(var("x"), vz), vg), vu, "x")),
                           equivalence_arriere(_inst_img(vg, vz)))   # z∈img g
    z_Y = N.modus_ponens(z_img, instancie(Himgsub, vz))      # z∈Y
    ex_imp = existe_elimination(N.loi_deduction(body_ex, z_Y), u)    # (∃u)(…) ⇒ z∈Y
    z_Y_final = N.modus_ponens(ex, ex_imp)
    body = N.loi_deduction(appartient(vz, E.image(vg, vX)), z_Y_final)
    return N.generalisation(bndr, body)                      # g⟨X⟩⊂Y


def g_injecte_X_dans_Y(X="X", Y="Y", g="g"):
    """⊢ { g∈Inj, dom g=X } ⊢ inf_egal_card(X, Y).

    Si dom g=X, g est une injection TOTALE X→Y : est_fonctionnel(g), dom g=X,
    injective_dans(g,X) (graphe injectif), image(g,X)⊂Y (img g⊂Y).  D'où
    est_injection_de(g,X,Y), puis (∃F)est_injection_de(F,X,Y) = inf_egal_card(X,Y)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    gI = N.assume(appartient(vg, Inj(vX, vY)))               # g∈Inj
    hdomX = N.assume(egal(E.dom(vg), vX))                    # dom g=X
    inj_g = N.modus_ponens(gI, equivalence_avant(_inst_Inj(vX, vY, vg)))  # inj_partielle(g,X,Y)
    Hgsub = conjonction_elim_gauche(conjonction_elim_gauche(inj_g))  # g⊂X×Y
    Hfg = conjonction_elim_droite(conjonction_elim_gauche(inj_g))   # est_fonctionnel(g)
    Hig = conjonction_elim_droite(inj_g)                    # graphe_injectif(g)
    # injective_dans(g,X)
    inj_dans = _injective_dans_de_graphe(g, X, hdomX, Hfg, Hig)
    # image(g,X)⊂Y  (via img g⊂Y)
    imgsub = _cut(img_inclus_Y(X, Y, g), inclus(vg, E.produit(vX, vY)), Hgsub)
    img_incl = _cut(_image_inclus_Y(g, X, Y, N.assume(inclus(E.img(vg), vY))),
                    inclus(E.img(vg), vY), imgsub)
    # est_injection_de(g,X,Y) = ((est_fonctionnel(g) et dom g=X) et injective_dans(g,X)) et image(g,X)⊂Y
    inj_de = conjonction_intro(conjonction_intro(conjonction_intro(Hfg, hdomX), inj_dans), img_incl)
    # (∃F)est_injection_de(F,X,Y)
    R = est_injection_de(var("F"), vX, vY)
    return N.modus_ponens(inj_de, N.s5(R, vg, "F"))         # inf_egal_card(X,Y)


# ── BRANCHE img g=Y : g⁻¹ est une injection partielle Y⇀X, totale (dom=Y) ─────
def reciproque_inj_partielle(X="X", Y="Y", g="g", a="a", b="b", ap="ap", c="c"):
    """⊢ { inj_partielle(g,X,Y) } ⊢ inj_partielle(g⁻¹, Y, X).

    g⁻¹⊂Y×X : (X×Y)⁻¹=Y×X et g⊂X×Y ⇒ g⁻¹⊂(X×Y)⁻¹=Y×X.  g⁻¹ fonctionnel ⇐ g
    injectif (graphe).  g⁻¹ injectif (graphe) ⇐ g fonctionnel.  (Échange exact des
    rôles fonctionnel/injectif par la réciproque.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import couple_reciproque, reciproque_produit
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import _peler_pourtout
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    grec = E.reciproque(vg)
    Hinj = N.assume(inj_partielle(vg, vX, vY))             # inj_partielle(g,X,Y)
    Hgsub = conjonction_elim_gauche(conjonction_elim_gauche(Hinj))  # g⊂X×Y
    Hfg = conjonction_elim_droite(conjonction_elim_gauche(Hinj))   # est_fonctionnel(g)
    Hig = conjonction_elim_droite(Hinj)                   # graphe_injectif(g)
    # (1) g⁻¹⊂Y×X : c∈g⁻¹ ⇒ c∈(X×Y)⁻¹=Y×X.  Or g⊂X×Y ⇒ g⁻¹⊂(X×Y)⁻¹.
    #     On montre directement : c∈g⁻¹ ⇒ (∃p,q)(c=(p,q) et (q,p)∈g) (axiome recip),
    #     (q,p)∈g⊂X×Y ⇒ q∈X,p∈Y ⇒ c=(p,q)∈Y×X.
    cibleS = inclus(grec, E.produit(vY, vX))
    bS, _ = _peler_pourtout(cibleS)
    vc = var(bS)
    ax_rec = N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP)
    rec_c0 = instancie(instancie(ax_rec, vg), vc)         # c∈g⁻¹ ⇔ (∃p)(∃q)(c=(p,q) et (q,p)∈g)
    # α-renomme les binders p,q → pr,qr (≠ p,q internes de _prod_couple)
    body_pq = et(egal(vc, E.couple(var("p"), var("q"))), appartient(E.couple(var("q"), var("p")), vg))
    ren_p = alpha_existe("p", "pr", existe("q", body_pq))
    rec_c1 = equivalence_transitivite(rec_c0, ren_p)
    body_pr_q = et(egal(vc, E.couple(var("pr"), var("q"))), appartient(E.couple(var("q"), var("pr")), vg))
    ren_q = congruence_existe(alpha_existe("q", "qr", body_pr_q), "pr")
    rec_c = equivalence_transitivite(rec_c1, ren_q)       # ⇔ (∃pr)(∃qr)(c=(pr,qr) et (qr,pr)∈g)
    Hcrec = N.assume(appartient(vc, grec))                # c∈g⁻¹
    ex_pq = N.modus_ponens(Hcrec, equivalence_avant(rec_c))   # (∃pr)(∃qr)(…)
    vp, vq = var("pr"), var("qr")
    body_q = et(egal(vc, E.couple(vp, vq)), appartient(E.couple(vq, vp), vg))
    c_eq = conjonction_elim_gauche(N.assume(body_q))      # c=(pr,qr)
    qp_g = conjonction_elim_droite(N.assume(body_q))      # (qr,pr)∈g
    qp_XY = N.modus_ponens(qp_g, instancie(Hgsub, E.couple(vq, vp)))   # (qr,pr)∈X×Y
    qp_comps = N.modus_ponens(qp_XY, equivalence_avant(_prod_couple(vq, vp, vX, vY)))  # qr∈X et pr∈Y
    qX = conjonction_elim_gauche(qp_comps)               # qr∈X
    pY = conjonction_elim_droite(qp_comps)               # pr∈Y
    pq_YX = N.modus_ponens(conjonction_intro(pY, qX),
                           equivalence_arriere(_prod_couple(vp, vq, vY, vX)))  # (pr,qr)∈Y×X
    c_YX = N.modus_ponens(pq_YX, equivalence_arriere(
        _leib_eq(vc, E.couple(vp, vq), c_eq, lambda w: appartient(w, E.produit(vY, vX)))))  # c∈Y×X
    inner_imp = N.loi_deduction(body_q, c_YX)
    ex_imp = existe_elimination(existe_elimination(inner_imp, "qr"), "pr")  # (∃pr)(∃qr)(…) ⇒ c∈Y×X
    c_YX_final = N.modus_ponens(ex_pq, ex_imp)           # c∈Y×X  [c∈g⁻¹, g⊂X×Y]
    grec_sub = N.generalisation(bS, N.loi_deduction(appartient(vc, grec), c_YX_final))  # g⁻¹⊂Y×X
    # (2) g⁻¹ fonctionnel : ((u,v)∈g⁻¹ et (u,z)∈g⁻¹) ⇒ v=z, via (v,u)∈g,(z,u)∈g et g injectif
    # NB : binders u,v,z IMPOSÉS par est_fonctionnel(g⁻¹).
    vu, vv, vz = var("u"), var("v"), var("z")
    func_body_hyp = et(appartient(E.couple(vu, vv), grec), appartient(E.couple(vu, vz), grec))
    Hf = N.assume(func_body_hyp)
    vu_g = N.modus_ponens(conjonction_elim_gauche(Hf),
                          equivalence_avant(couple_reciproque(vg, vu, vv)))   # (v,u)∈g
    zu_g = N.modus_ponens(conjonction_elim_droite(Hf),
                          equivalence_avant(couple_reciproque(vg, vu, vz)))   # (z,u)∈g
    inj_inst = instancie(instancie(instancie(Hig, vv), vu), vz)  # ((v,u)∈g et (z,u)∈g)⇒v=z
    vz_eq = N.modus_ponens(conjonction_intro(vu_g, zu_g), inj_inst)   # v=z
    func_rec = N.generalisation("u", N.generalisation("v", N.generalisation("z",
        N.loi_deduction(func_body_hyp, vz_eq))))         # est_fonctionnel(g⁻¹)
    # (3) g⁻¹ injectif (graphe) : ((a,b)∈g⁻¹ et (a',b)∈g⁻¹) ⇒ a=a', via (b,a)∈g,(b,a')∈g et g fonctionnel
    va, vbb, vapp = var(a), var(b), var(ap)
    inj_body_hyp = et(appartient(E.couple(va, vbb), grec), appartient(E.couple(vapp, vbb), grec))
    Hi = N.assume(inj_body_hyp)
    ba_g = N.modus_ponens(conjonction_elim_gauche(Hi),
                          equivalence_avant(couple_reciproque(vg, va, vbb)))    # (b,a)∈g
    bap_g = N.modus_ponens(conjonction_elim_droite(Hi),
                           equivalence_avant(couple_reciproque(vg, vapp, vbb))) # (b,a')∈g
    func_inst = instancie(instancie(instancie(Hfg, vbb), va), vapp)  # ((b,a)∈g et (b,a')∈g)⇒a=a'
    va_eq = N.modus_ponens(conjonction_intro(ba_g, bap_g), func_inst)   # a=a'
    inj_rec = N.generalisation(a, N.generalisation(b, N.generalisation(ap,
        N.loi_deduction(inj_body_hyp, va_eq))))          # graphe_injectif(g⁻¹)
    return conjonction_intro(conjonction_intro(grec_sub, func_rec), inj_rec)  # inj_partielle(g⁻¹,Y,X)


def dom_reciproque_eq_Y(X="X", Y="Y", g="g"):
    """⊢ { img g=Y } ⊢ dom(g⁻¹) = Y.   (pr₁(g⁻¹)=pr₂g=img g=Y.)"""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque import pr1_reciproque
    from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import composer_egalites
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    HimgY = N.assume(egal(E.img(vg), vY))                 # img g=Y  (= pr₂g=Y)
    pr1 = pr1_reciproque(vg)                              # dom(g⁻¹)=img g  (pr₁(g⁻¹)=pr₂g)
    return composer_egalites(pr1, HimgY)                 # dom(g⁻¹)=Y


def g_reciproque_injecte_Y_dans_X(X="X", Y="Y", g="g"):
    """⊢ { g∈Inj, img g=Y } ⊢ inf_egal_card(Y, X).

    Si img g=Y, g⁻¹ est une injection TOTALE Y→X : g⁻¹∈Inj(Y,X)
    (reciproque_inj_partielle) avec dom(g⁻¹)=Y (dom_reciproque_eq_Y) ; on applique
    g_injecte_X_dans_Y à (Y, X, g⁻¹) pour obtenir inf_egal_card(Y, X)."""
    vX, vY, vg = _terme(X), _terme(Y), _terme(g)
    grec = E.reciproque(vg)
    gI = N.assume(appartient(vg, Inj(vX, vY)))            # g∈Inj
    HimgY = N.assume(egal(E.img(vg), vY))                 # img g=Y
    inj_g = N.modus_ponens(gI, equivalence_avant(_inst_Inj(vX, vY, vg)))  # inj_partielle(g,X,Y)
    # inj_partielle(g⁻¹,Y,X)  (décharge inj_partielle(g,X,Y))
    inj_rec = _cut(reciproque_inj_partielle(X, Y, g), inj_partielle(vg, vX, vY), inj_g)
    # g⁻¹∈Inj(Y,X)
    grec_I = N.modus_ponens(inj_rec, equivalence_arriere(_inst_Inj(vY, vX, grec)))  # g⁻¹∈Inj(Y,X)
    # dom(g⁻¹)=Y
    dom_rec = _cut(dom_reciproque_eq_Y(X, Y, g), egal(E.img(vg), vY), HimgY)
    # g_injecte_X_dans_Y(Y, X, g⁻¹) : {g⁻¹∈Inj(Y,X), dom(g⁻¹)=Y} ⊢ inf_egal_card(Y,X)
    th = g_injecte_X_dans_Y(vY, vX, grec)
    th = _cut(th, appartient(grec, Inj(vY, vX)), grec_I)
    th = _cut(th, egal(E.dom(grec), vY), dom_rec)
    return th                                            # inf_egal_card(Y,X)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LE THÉORÈME DE COMPARABILITÉ DES CARDINAUX  (E.III.3 — l'ordre ≤ est total)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.2 Cor.1 | E III.25 L.11-12 | PDF p.128
#   (lignes recalées campagne @livre 2026-07 : Cor. 1 précède Cor. 2 (L.13-15).)
def comparabilite_cardinaux(X="X", Y="Y", g="g", m="m"):
    """⊢ inf_egal_card(X, Y) OU inf_egal_card(Y, X).

    🎯🎯🎯 THÉORÈME DE COMPARABILITÉ DES CARDINAUX, §III.3 — « l'ordre des
    cardinaux est total » — PROUVÉ via ZORN, INCONDITIONNEL (theorie_ensembles()=22).
    De deux ensembles X, Y quelconques, l'un s'injecte dans l'autre.

    Schéma : par ZORN sur le poset (Inj, ΓI) des injections PARTIELLES X⇀Y ordonné
    par inclusion (est_inductif via la réunion d'une chaîne = injection partielle,
    Inj≠∅), il existe une injection partielle MAXIMALE g (maximal_existe).  Un g
    maximal vérifie dom g=X OU img g=Y (maximal_dom_ou_img, par l'absurde via
    l'extension g∪{(x,y)}).  Si dom g=X, g injecte X→Y (inf_egal_card(X,Y)) ; si
    img g=Y, g⁻¹ injecte Y→X (inf_egal_card(Y,X)).  Aucune injection n'est
    postulée : toutes sont DÉMONTRÉES (le maximal vient de Zorn)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
    vX, vY, vg = var(X), var(Y), var(g)
    Gam, Inj_set = Gamma(vX, vY), Inj(vX, vY)
    le_XY = inf_egal_card(vX, vY)
    le_YX = inf_egal_card(vY, vX)
    but = ou(le_XY, le_YX)
    # (∃m) element_maximal(ΓI,Inj,m)  via Zorn
    ex_max = maximal_existe(X, Y, m)                      # (∃m)element_maximal(ΓI,Inj,m)
    # α-renomme le témoin m → g (le binder de maximal_existe est « m »)
    if m != g:
        ex_max = _alpha_ex(ex_max, m, g, element_maximal(Gam, Inj_set, var(m), "x"))
    # per-témoin g : element_maximal(ΓI,Inj,g) ⇒ but
    Hmax = N.assume(element_maximal(Gam, Inj_set, vg, "x"))   # element_maximal(ΓI,Inj,g)
    gI = conjonction_elim_gauche(Hmax)                   # g∈Inj
    # dom g=X ou img g=Y
    disj = _cut(maximal_dom_ou_img(X, Y, g), element_maximal(Gam, Inj_set, vg, "x"), Hmax)
    # branche dom g=X : g injecte X→Y ⇒ inf_egal_card(X,Y) ⇒ but (gauche)
    HdomX = N.assume(egal(E.dom(vg), vX))
    leXY = _cut(_cut(g_injecte_X_dans_Y(X, Y, g),
                     appartient(vg, Inj_set), gI),
                egal(E.dom(vg), vX), HdomX)              # inf_egal_card(X,Y)
    bdom = N.loi_deduction(egal(E.dom(vg), vX), _ou_gauche(leXY, le_YX))
    # branche img g=Y : g⁻¹ injecte Y→X ⇒ inf_egal_card(Y,X) ⇒ but (droite)
    HimgY = N.assume(egal(E.img(vg), vY))
    leYX = _cut(_cut(g_reciproque_injecte_Y_dans_X(X, Y, g),
                     appartient(vg, Inj_set), gI),
                egal(E.img(vg), vY), HimgY)              # inf_egal_card(Y,X)
    bimg = N.loi_deduction(egal(E.img(vg), vY), _ou_droite(leYX, le_XY))
    res = cas(disj, bdom, bimg)                          # but  [Hmax]
    # éliminer ∃g
    wit = N.loi_deduction(element_maximal(Gam, Inj_set, vg, "x"), res)
    ex_imp = existe_elimination(wit, g)                  # (∃g)maximal ⇒ but
    return N.modus_ponens(ex_max, ex_imp)               # but = inf_egal_card(X,Y) ou inf_egal_card(Y,X)


__all__ = [
    "graphe_injectif", "inj_partielle",
    "Inj", "axiome_Inj", "theorie_Inj", "Inj_membre",
    "Gamma", "axiome_Gamma", "theorie_Gamma", "Gamma_membre",
    "Gamma_reflexive_sur", "Gamma_antisymetrique", "Gamma_transitive",
    "Gamma_est_ordre",
    "Union", "axiome_Union", "theorie_Union", "Union_membre",
    "Union_inclus_produit", "Union_fonctionnel", "Union_injectif",
    "Union_dans_Inj", "Union_majorant", "Inj_inductif",
    "vide_inj_partielle", "vide_dans_Inj", "Inj_non_vide", "maximal_existe",
    "dom_inclus_X", "img_inclus_Y", "maximal_dom_ou_img",
    "g_injecte_X_dans_Y", "reciproque_inj_partielle", "dom_reciproque_eq_Y",
    "g_reciproque_injecte_Y_dans_X",
    "comparabilite_cardinaux",
]
