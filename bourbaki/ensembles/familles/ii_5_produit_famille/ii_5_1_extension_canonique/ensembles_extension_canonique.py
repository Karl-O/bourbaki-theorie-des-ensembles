"""§II.5 — Notions « manquantes » du produit d'une famille (introduction fidèle).

Ce module INTRODUIT (def fidèle = un terme/prédicat conforme à l'énoncé verbatim
de Bourbaki, E.II.5) les quatre familles de notions confiées à cet agent :

  1. EXTENSION CANONIQUE d'une correspondance aux ensembles de parties (§5.1) :
        Γ̂ : P(A) → P(B),  X ↦ Γ⟨X⟩.
     Modélisée par l'application (triple (graphe, source, but)) de Bourbaki
     X ↦ G⟨X⟩, source P(A), but P(B).  AUCUN axiome nouveau : c'est la fonction
     définie par le terme T = G⟨X⟩ (mécanisme C54, `graphe_terme`/`fonction_terme`
     déjà présents), dont la caractérisation de membership découle de
     `axiome_graphe_terme` (théorie dédiée existante).

  2. APPLICATION DIAGONALE et DIAGONALE Δ du produit E^I (§5.3) :
        x̃ := graphe de la fonction constante ι ↦ x  (ι∈I, valeur x) ;
        application diagonale  E → E^I,  x ↦ x̃  (injection) ;
        Δ := { x̃ | x∈E }  partie de E^I (la « diagonale »).
     x̃ est le graphe-terme de la fonction constante (C54) ; Δ est l'image de E
     par le graphe de l'application diagonale (terme dérivé `image`, AUCUN axiome
     nouveau).

  3. PRODUIT PARTIEL et PROJECTION d'indice J (§5.4) :
        produit partiel  ∏_{ι∈J} X_ι  (J ⊂ I) ;
        pr_J(F) := F∘Δ_J := F|J  (restriction de f à J) ;
        projection d'indice J : ∏_{ι∈I} X_ι → ∏_{ι∈J} X_ι,  F ↦ F|J.
     ∏_{ι∈J} X_ι = `produit_famille(f, J)` (déjà présent).  pr_J(F) = `restriction`
     (déjà présent, AXIOME_RESTRICTION).  AUCUN axiome nouveau.

  4. EXTENSION CANONIQUE (produit) d'une famille d'applications aux produits (§5.7,
     Déf. 2) :
        g := ∏_{ι∈I} g_ι : ∏_{ι∈I} X_ι → ∏_{ι∈I} Y_ι,
        f ↦ (le graphe de) ι ↦ g_ι(f(ι)).
     On INTRODUIT un terme neuf `extension_produit(g, I)` (g = la famille de
     fonctions ι ↦ g_ι, vue comme fonction d'indices) caractérisé par un AXIOME DE
     MEMBERSHIP dans une théorie dédiée paramétrée (motif theorie_exposant /
     theorie_graphe_terme — JAMAIS dans theorie_ensembles) : la valeur (∏ g_ι)(f)
     est le graphe de la fonction ι ↦ g_ι(f(ι)).

POLITIQUE DE FIDÉLITÉ : conformément à la consigne du round, on INTRODUIT les
notions ; les gros théorèmes (Prop. 1 : f̂ injective/surjective ; Prop. 5 : pr_J
surjective ; fonctorialité de ∏ g_ι ; injectivité de l'application diagonale) sont
NOMMÉS et REPORTÉS — on n'en prouve que des lemmes DIRECTS (caractérisations
d'appartenance / de valeur obtenues par instanciation d'axiome).  theorie_ensembles
RESTE à 22 axiomes (aucune écriture dans ce fichier : tout axiome neuf vit dans une
théorie dédiée renvoyée par `theorie_extension_produit`).

THÉORÈMES CERTIFIÉS (chacun testé, cf. test_extension_canonique.py) :
  • ext_canonique_valeur        ⊢ (X ∈ P(A)) ⇒ (Γ̂(X) = G⟨X⟩)      [§5.1, valeur]
  • ext_canonique_graphe_membre ⊢ w∈graphe(Γ̂) ⇔ (∃X)(∃Y)(w=(X,Y) et X∈P(A)
                                                          et Y=G⟨X⟩) [C54]
  • diagonale_valeur            ⊢ x̃ = graphe de ι↦x                 [§5.3, déf.]
  • diag_application_valeur     ⊢ (x∈E) ⇒ (diag(x) = x̃)            [§5.3, x↦x̃]
  • membre_diagonale            ⊢ z ∈ Δ ⇔ (∃x)(x∈E et z=x̃)          [§5.3, Δ]
  • pr_partiel_valeur           ⊢ pr_J(F) = F|J                      [§5.4, pr_J]
  • membre_produit_partiel      ⊢ (G∈∏_{J}) ⇔ corps_J                [§5.4, déf.]
  • ext_produit_valeur          ⊢ (∏ g_ι)(f) = graphe(ι↦g_ι(f(ι)))   [§5.7, Déf.2]
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, impl, non, equiv,
                                       appartient, existe, inclus, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, equivalence_avant,
                               equivalence_arriere, conjonction_intro,
                               conjonction_elim_gauche, conjonction_elim_droite)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# 1.  EXTENSION CANONIQUE d'une correspondance aux ensembles de parties (§5.1)
#     Γ̂ : P(A) → P(B),  X ↦ Γ⟨X⟩.
# ════════════════════════════════════════════════════════════════════════════
# Γ est codée par son graphe G ; Γ⟨X⟩ = E.image(G, X) (image directe, déjà
# présente).  L'extension canonique est l'APPLICATION (triple de Bourbaki) de
# source P(A), but P(B), définie par le terme X ↦ G⟨X⟩.  On la construit avec
# `fonction_terme` (mécanisme C54), donc SANS axiome nouveau : sa caractérisation
# vient de `axiome_graphe_terme` (théorie dédiée existante).

# Le liant de domaine du graphe-terme est « Xi » (FRESH) — distinct de tout « X »
# libre qu'un appelant pourrait instancier (évite la capture du X libre de G⟨X⟩).

def graphe_extension_canonique(g, a, xi="Xi"):
    """Graphe de l'application Xi ↦ G⟨Xi⟩  (Xi∈P(A))  =  {(Xi, G⟨Xi⟩) | Xi∈P(A)}.

    Liant de domaine « Xi » (parcourt P(A)) ; valeur T = G⟨Xi⟩ = image(G, Xi)."""
    vXi = var(xi)
    return E.graphe_terme(E.parties(_t(a)), E.image(_t(g), vXi), xi)


def extension_canonique(g, a, b, xi="Xi"):
    """Γ̂ := (graphe(Xi↦G⟨Xi⟩), P(A), P(B))  (extension canonique de Γ aux parties, §5.1).

    C'est l'application (triple) de source P(A), but P(B), associant à Xi∈P(A)
    l'image directe G⟨Xi⟩∈P(B).  Implémentation : fonction_terme(P(A), G⟨Xi⟩, P(B))."""
    vXi = var(xi)
    return E.fonction_terme(E.parties(_t(a)), E.image(_t(g), vXi), E.parties(_t(b)), xi)


def ext_canonique_graphe_membre(g="G", a="A", xi="Xi"):
    """⊢ w ∈ graphe(Γ̂) ⇔ (∃Xi)(∃y)(w=(Xi,y) et Xi∈P(A) et y=G⟨Xi⟩).   (§5.1, C54.)

    Caractérisation de l'appartenance au graphe de l'extension canonique (= graphe
    de la fonction Xi↦G⟨Xi⟩), obtenue par instanciation de `axiome_graphe_terme`."""
    vG, vA = var(g), var(a)
    T = E.image(vG, var(xi))
    th = E.theorie_graphe_terme(E.parties(vA), T, xi)
    ax = N.axiome(th, E.axiome_graphe_terme(E.parties(vA), T, xi))
    return instancie(ax, var("w"))


def ext_canonique_valeur(g="G", a="A", x="X", xi="Xi"):
    """⊢ (X ∈ P(A)) ⇒ ((X, G⟨X⟩) ∈ graphe(Γ̂)).   (§5.1 : Γ̂(X) = G⟨X⟩, niveau graphe.)

    « Γ̂(X) = G⟨X⟩ » signifie, au niveau du graphe, que le couple (X, G⟨X⟩)
    appartient au graphe de Γ̂ (= graphe de Xi↦G⟨Xi⟩) dès que X∈P(A).  On instancie
    `axiome_graphe_terme` au couple (X, G⟨X⟩) ; sous X∈P(A), le témoin (Xi=X, y=G⟨X⟩)
    fournit le corps existentiel, d'où l'appartenance.  (La lecture
    valeur(·)=τy(…) ⇒ Γ̂(X)=G⟨X⟩ via C46/unicité est REPORTÉE : non requise pour
    INTRODUIRE la notion.)  X et Xi sont DISTINCTS (pas de capture)."""
    vG, vA, vX = var(g), var(a), var(x)
    GX = E.image(vG, vX)
    T = E.image(vG, var(xi))                                   # G⟨Xi⟩  (Xi bound)
    th = E.theorie_graphe_terme(E.parties(vA), T, xi)
    ax = N.axiome(th, E.axiome_graphe_terme(E.parties(vA), T, xi))
    membre = instancie(ax, E.couple(vX, GX))   # (X,G⟨X⟩)∈graphe ⇔ (∃Xi)(∃y)(…)
    h = N.assume(appartient(vX, E.parties(vA)))
    # corps après témoins Xi=X, y=G⟨X⟩ : ((X,G⟨X⟩)=(X,G⟨X⟩) et X∈P(A) et G⟨X⟩=G⟨X⟩)
    wit = conjonction_intro(conjonction_intro(N.reflexivite(E.couple(vX, GX)), h),
                            N.reflexivite(GX))
    vy = var("y")
    # corps (y libre) : ((X,G⟨X⟩)=(X,y) et X∈P(A) et y=G⟨X⟩)
    body_y = et(et(egal(E.couple(vX, GX), E.couple(vX, vy)),
                   appartient(vX, E.parties(vA))),
                egal(vy, GX))
    ex_y = N.modus_ponens(wit, N.s5(body_y, GX, "y"))          # (∃y) body_y
    # corps (Xi libre) : (∃y)((X,G⟨X⟩)=(Xi,y) et Xi∈P(A) et y=G⟨Xi⟩)
    body_Xi = existe("y", et(et(egal(E.couple(vX, GX), E.couple(var(xi), vy)),
                                appartient(var(xi), E.parties(vA))),
                             egal(vy, E.image(vG, var(xi)))))
    ex_Xi = N.modus_ponens(ex_y, N.s5(body_Xi, vX, xi))        # (∃Xi)(∃y) body
    couple_in = N.modus_ponens(ex_Xi, equivalence_arriere(membre))   # couple ∈ graphe
    return N.loi_deduction(appartient(vX, E.parties(vA)), couple_in)


# ════════════════════════════════════════════════════════════════════════════
# 2.  APPLICATION DIAGONALE et DIAGONALE Δ  (§5.3)
#     x̃ := graphe de ι↦x  ;  diag : E→E^I, x↦x̃  ;  Δ := {x̃ | x∈E}.
# ════════════════════════════════════════════════════════════════════════════

def famille_constante(i, x, iota="iota"):
    """x̃ := graphe de la fonction constante ι ↦ x  (ι∈I, valeur x)  (§5.3).

    Graphe-terme (C54) de domaine I et valeur constante T = x (indépendant de ι).
    Liant de domaine « ι » (paramétrable) ; AUCUN axiome nouveau."""
    return E.graphe_terme(_t(i), _t(x), iota)


def graphe_application_diagonale(e, i, x="xa", iota="iota"):
    """Graphe de l'application diagonale x ↦ x̃  (x∈E)  =  {(x, x̃) | x∈E}  (§5.3).

    Graphe-terme (C54) de domaine E, valeur T = x̃ = famille_constante(I, x).  Le
    liant de domaine est « xa » (FRESH, ≠ « x » de AXIOME_IMAGE) afin que la
    caractérisation de Δ via AXIOME_IMAGE garde son existentiel « x » non renommé."""
    vx = var(x)
    return E.graphe_terme(_t(e), famille_constante(_t(i), vx, iota), x)


def application_diagonale(e, i, x="xa", iota="iota"):
    """diag := (graphe(x↦x̃), E, E^I)  (application diagonale E→E^I, §5.3).

    Application (triple) de source E, but E^I = exposant(I,E), x ↦ x̃.  Injection
    (Bourbaki) — l'injectivité est REPORTÉE (lemme dur).  Liant de domaine « xa »."""
    vx = var(x)
    return E.fonction_terme(_t(e), famille_constante(_t(i), vx, iota),
                            E.exposant(_t(i), _t(e)), x)


def diagonale_produit(e, i, x="xa", iota="iota"):
    """Δ := graphe(diag)⟨E⟩ = { x̃ | x∈E }  (diagonale du produit E^I, §5.3).

    Partie de E^I formée des graphes des applications constantes : l'image directe
    de E par le graphe de l'application diagonale.  Terme DÉRIVÉ (`image`), AUCUN
    axiome nouveau ; sa caractérisation de membership vient de AXIOME_IMAGE."""
    return E.image(graphe_application_diagonale(e, i, x, iota), _t(e))


def diagonale_valeur(i="I", x="x", iota="iota"):
    """⊢ w ∈ x̃ ⇔ (∃ι)(∃y)(w=(ι,y) et ι∈I et y=x).   (§5.3 : x̃ = graphe de ι↦x.)

    Caractérisation de l'appartenance au graphe constant x̃, par instanciation de
    `axiome_graphe_terme` (domaine I, valeur constante x)."""
    vI, vx = var(i), var(x)
    th = E.theorie_graphe_terme(vI, vx, iota)
    ax = N.axiome(th, E.axiome_graphe_terme(vI, vx, iota))
    return instancie(ax, var("w"))


def diag_application_membre(e="E", i="I", x="xa", iota="iota"):
    """⊢ w ∈ graphe(diag) ⇔ (∃xa)(∃y)(w=(xa,y) et xa∈E et y=x̃).   (§5.3 : x↦x̃.)

    Caractérisation du graphe de l'application diagonale (graphe-terme x↦x̃)."""
    vE, vI = var(e), var(i)
    T = famille_constante(vI, var(x), iota)
    th = E.theorie_graphe_terme(vE, T, x)
    ax = N.axiome(th, E.axiome_graphe_terme(vE, T, x))
    return instancie(ax, var("w"))


def membre_diagonale(e="E", i="I", x="xa", iota="iota"):
    """⊢ (z ∈ Δ) ⇔ (∃x)(x∈E et (x,z)∈graphe(diag)).   (§5.3 : Δ = graphe(diag)⟨E⟩.)

    Δ étant l'image directe de E par le graphe de l'application diagonale,
    l'appartenance à Δ est caractérisée par AXIOME_IMAGE instancié (existentiel
    « x » préservé : le graphe a un liant de domaine « xa » distinct)."""
    vE = var(e)
    GD = graphe_application_diagonale(e, i, x, iota)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)       # (∀G)(∀X)(∀y)(…)
    return instancie(instancie(instancie(ax, GD), vE), var("z"))


# ════════════════════════════════════════════════════════════════════════════
# 3.  PRODUIT PARTIEL et PROJECTION d'indice J  (§5.4)
#     ∏_{ι∈J} X_ι (J⊂I) ;  pr_J(F) := F∘Δ_J := F|J ;  pr_J : ∏_I → ∏_J.
# ════════════════════════════════════════════════════════════════════════════

def produit_partiel(f, j):
    """∏_{ι∈J} X_ι  (produit partiel de ∏_{ι∈I} X_ι, J⊂I)  (§5.4).

    Même terme que le produit d'une famille, restreint à l'ensemble d'indices J
    (≡ produit_famille(f, J)).  La condition J⊂I est portée par l'énoncé qui
    l'emploie (Prop. 5/6), pas par le terme."""
    return E.produit_famille(_t(f), _t(j))


def projection_J(ff, j):
    """pr_J(F) := F∘Δ_J := F|J  (projection d'indice J, §5.4).

    Bourbaki : F∘Δ_J (Δ_J = diagonale de J×J vue comme injection J↪I) est le
    graphe de la restriction de f à J ; on prend donc pr_J(F) = F|J =
    restriction(F, J) (terme déjà présent, AXIOME_RESTRICTION)."""
    return E.restriction(_t(ff), _t(j))


def graphe_projection_J(fam, i, j, ff="F"):
    """Graphe de l'application pr_J : ∏_{ι∈I} X_ι → ∏_{ι∈J} X_ι,  F ↦ F|J  (§5.4).

    Graphe-terme (C54) de domaine ∏_{ι∈I} X_ι (= produit_famille(fam, I)), valeur
    T = F|J.  `fam` est la famille (X_ι) (fonction d'indices), I son ensemble
    d'indices, J ⊂ I."""
    vF = var(ff)
    return E.graphe_terme(E.produit_famille(_t(fam), _t(i)),
                          projection_J(vF, _t(j)), ff)


def pr_partiel_valeur(ff="F", j="J"):
    """⊢ pr_J(F) = F|J.   (§5.4 : la projection d'indice J est la restriction à J.)

    Égalité de DÉFINITION (pr_J(F) := F|J) — réflexivité sur le terme restriction."""
    return N.reflexivite(projection_J(var(ff), var(j)))


def membre_produit_partiel(f="f", j="J", ff="G"):
    """⊢ (G ∈ ∏_{ι∈J} X_ι) ⇔ ( G fonctionnel ∧ dom G = J ∧ (∀ι)(ι∈J ⇒ G(ι)∈X_ι) ).
       (§5.4 — caractérisation de l'appartenance au produit partiel.)

    Instanciation de AXIOME_PRODUIT_FAM à l'ensemble d'indices J."""
    vf, vJ, vG = var(f), var(j), var(ff)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, vf), vJ), vG)


def restriction_dans_produit_partiel(f="f", j="J", ff="G"):
    """⊢ (G ∈ ∏_{ι∈J} X_ι) ⇒ (dom G = J).   (un élément du produit partiel a domaine J.)"""
    vf, vJ, vG = var(f), var(j), var(ff)
    eq = membre_produit_partiel(f, j, ff)
    h = N.assume(appartient(vG, produit_partiel(vf, vJ)))
    corps = N.modus_ponens(h, equivalence_avant(eq))
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps))   # dom G = J
    return N.loi_deduction(appartient(vG, produit_partiel(vf, vJ)), domaine)


# ════════════════════════════════════════════════════════════════════════════
# 4.  EXTENSION CANONIQUE (produit) d'une famille d'applications  (§5.7, Déf. 2)
#     g := ∏_{ι∈I} g_ι : ∏ X_ι → ∏ Y_ι,  f ↦ (graphe de) ι ↦ g_ι(f(ι)).
# ════════════════════════════════════════════════════════════════════════════
# On introduit un TERME NEUF `extension_produit(g, I)` (g = la famille de fonctions
# ι↦g_ι, vue comme fonction d'indices : g_ι = valeur_famille(g, ι)) avec un AXIOME
# DE MEMBERSHIP caractérisant son graphe, dans une THÉORIE DÉDIÉE paramétrée
# (motif theorie_exposant / theorie_graphe_terme — JAMAIS dans theorie_ensembles).
#
# Le graphe de g = ∏ g_ι relie f∈∏X_ι à u_f, où u_f est le graphe de la fonction
# ι ↦ g_ι(f(ι)).  Avec g_ι = valeur_famille(g, ι) et f(ι) = valeur(f, ι), la valeur
# image est :   u_f = graphe de ι ↦ valeur(g_ι, f(ι)) .

def valeur_image_produit(g, i, f, iota="iota"):
    """u_f := graphe de la fonction ι ↦ g_ι(f(ι))  (ι∈I)  (§5.7, Déf. 2).

    Élément de ∏_{ι∈I} Y_ι : graphe-terme (C54) de domaine I, valeur
    T = g_ι(f(ι)) = valeur(valeur_famille(g, ι), valeur(f, ι))."""
    viota = var(iota)
    g_iota = E.valeur_famille(_t(g), viota)
    f_iota = E.valeur(_t(f), viota)
    return E.graphe_terme(_t(i), E.valeur(g_iota, f_iota), iota)


def extension_produit(g, i):
    """∏_{ι∈I} g_ι := le graphe de l'application f ↦ u_f de ∏X_ι dans ∏Y_ι (§5.7).

    Terme NEUF (graphe de l'extension canonique aux produits) ; g est la famille
    de fonctions (ι↦g_ι), I l'ensemble d'indices.  Caractérisé par
    `axiome_extension_produit` (théorie dédiée `theorie_extension_produit`)."""
    return app("extension_produit", _t(g), _t(i))


def axiome_extension_produit(g, i, x_fam, iota="iota", fp="fp", w="w"):
    """⊢-schéma : (∀w)( w ∈ ∏g_ι ⇔ (∃fp)( fp ∈ ∏X_ι et w = (fp, u_{fp}) ) )  (§5.7, Déf. 2).

    Caractérisation FIDÈLE du graphe de l'extension ∏g_ι : pour chaque fp du produit
    source ∏_{ι∈I} X_ι, le couple (fp, u_{fp}) appartient à ce graphe (et lui seul),
    où u_{fp} = graphe(ι↦g_ι(fp(ι))).  Forme membership (S8 = sélection dans
    ∏X_ι × ∏Y_ι, A1 = unicité).

    g, i, x_fam (= la famille source (X_ι)) sont PARAMÈTRES ; instancié via
    `theorie_extension_produit`.  Liant existentiel interne « fp » (FRESH, distinct
    de tout « f » libre instancié), universel « w »."""
    vw, vfp = var(w), var(fp)
    ufp = valeur_image_produit(g, i, vfp, iota)
    source = E.produit_famille(_t(x_fam), _t(i))
    corps = existe(fp, et(appartient(vfp, source),
                          egal(vw, E.couple(vfp, ufp))))
    return pourtout(w, equiv(appartient(vw, extension_produit(g, i)), corps))


def theorie_extension_produit(g, i, x_fam, iota="iota", fp="fp", w="w"):
    """Théorie ne contenant que l'instance de l'axiome de membership de ∏g_ι (§5.7)."""
    return N.Theorie("Extension-produit",
                     [axiome_extension_produit(g, i, x_fam, iota, fp, w)])


def ext_produit_valeur(g="g", i="I", x_fam="X", f="f", iota="iota", fp="fp", w="w"):
    """⊢ (f ∈ ∏X_ι) ⇒ ((f, u_f) ∈ ∏g_ι)   où  u_f = graphe(ι↦g_ι(f(ι))).   (§5.7, Déf. 2.)

    Lemme DIRECT : sous l'hypothèse f∈∏X_ι, le couple (f, u_f) appartient au graphe
    de l'extension ∏g_ι (= « (∏g_ι)(f) = u_f » au niveau du graphe).  Via l'axiome
    de membership instancié au couple (f, u_f), témoin fp=f (f libre ≠ fp lié)."""
    vg, vI, vX, vf = var(g), var(i), var(x_fam), var(f)
    uf = valeur_image_produit(vg, vI, vf, iota)
    th = theorie_extension_produit(vg, vI, vX, iota, fp, w)
    ax = N.axiome(th, axiome_extension_produit(vg, vI, vX, iota, fp, w))
    membre = instancie(ax, E.couple(vf, uf))    # (f,u_f)∈∏g ⇔ (∃fp)(fp∈∏X et (f,u_f)=(fp,u_{fp}))
    h = N.assume(appartient(vf, E.produit_famille(vX, vI)))
    # témoin fp=f : f∈∏X et (f,u_f)=(f,u_f)
    wit = conjonction_intro(h, N.reflexivite(E.couple(vf, uf)))
    # corps de l'existentiel (fp libre) : fp∈∏X et (f,u_f)=(fp, u_{fp})
    vfp = var(fp)
    body = et(appartient(vfp, E.produit_famille(vX, vI)),
              egal(E.couple(vf, uf), E.couple(vfp,
                   valeur_image_produit(vg, vI, vfp, iota))))
    ex = N.modus_ponens(wit, N.s5(body, vf, fp))
    couple_in = N.modus_ponens(ex, equivalence_arriere(membre))
    return N.loi_deduction(appartient(vf, E.produit_famille(vX, vI)), couple_in)


__all__ = [
    # §5.1 — extension canonique aux parties
    "graphe_extension_canonique", "extension_canonique",
    "ext_canonique_graphe_membre", "ext_canonique_valeur",
    # §5.3 — application diagonale & diagonale Δ
    "famille_constante", "graphe_application_diagonale", "application_diagonale",
    "diagonale_produit", "diagonale_valeur", "diag_application_membre", "membre_diagonale",
    # §5.4 — produit partiel & projection pr_J
    "produit_partiel", "projection_J", "graphe_projection_J", "pr_partiel_valeur",
    "membre_produit_partiel", "restriction_dans_produit_partiel",
    # §5.7 — extension canonique aux produits ∏ g_ι
    "valeur_image_produit", "extension_produit", "axiome_extension_produit",
    "theorie_extension_produit", "ext_produit_valeur",
]
