"""Chapitre II (abrégé) — axiomes A1, A2 + termes définis {a,b}, {a}, ∅.

A1, A2 : axiomes verbatim. Les TERMES définis (paire, singleton, vide) sont
introduits avec leur axiome de caractérisation (mécanisme « constante
introductrice » de Bourbaki), légitime car existence + unicité sont prouvées
(cf. ensembles_theoremes : existence_paire / unicite_paire).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, app, tau, egal, inclus, ou, et, impl, non, equiv,
                     pourtout, existe, coll, appartient)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N

_X, _Y, _Z = var("x"), var("y"), var("z")


# ── Termes ensemblistes définis ───────────────────────────────────────────────
def paire(t, u):
    """{t, u}."""
    return app("paire", t, u)


def singleton(t):
    """{t} := {t, t}."""
    return paire(t, t)


VIDE = app("vide")          # ∅


def reunion(t, u):
    """t ∪ u."""
    return app("reunion", t, u)


def intersection(t, u):
    """t ∩ u."""
    return app("inter", t, u)


def difference(e, x):
    """E ∖ X := { z | z∈E et ¬(z∈X) }  (différence ; complémentaire de X dans E)."""
    return app("difference", e, x)


# @livre Ch.R §3 Def.- | E.R.11 item 1 (couple (x,y)) | PDF p.314
def couple(t, u):
    """(t, u) := {{t}, {t, u}}  (couple de Bourbaki, E.II.30, Déf.)."""
    return paire(singleton(t), paire(t, u))


# @livre Ch.R §3 Def.- | E.R.11 item 1 (première coordonnée / première projection pr₁) | PDF p.314
def pr1(z, x="x", y="y"):
    """pr₁z := τx((∃y)(z = (x, y)))  (première coordonnée, E.II.31)."""
    vx, vy = var(x), var(y)
    return tau(x, existe(y, egal(z, couple(vx, vy))))


# @livre Ch.R §3 Def.- | E.R.12 item 1 (seconde coordonnée / seconde projection pr₂) | PDF p.315
def pr2(z, x="x", y="y"):
    """pr₂z := τy((∃x)(z = (x, y)))  (seconde coordonnée, E.II.31)."""
    vx, vy = var(x), var(y)
    return tau(y, existe(x, egal(z, couple(vx, vy))))


def est_un_couple(z, x="x", y="y"):
    """« z est un couple » := (∃x)(∃y)(z = (x, y))  (E.II.31)."""
    vx, vy = var(x), var(y)
    return existe(x, existe(y, egal(z, couple(vx, vy))))


# @livre Ch.R §3 Def.- | E.R.11 item 1 (ensemble produit E×F, ensembles facteurs) | PDF p.314
def produit(t, u):
    """t × u  (produit de deux ensembles, E.II.33, Déf. 1)."""
    return app("produit", t, u)


def est_un_graphe(g):
    """« G est un graphe » := (∀z)((z∈G) ⇒ (z est un couple))  (E.II.37, Déf. 1)."""
    return pourtout("z", impl(appartient(var("z"), g), est_un_couple(var("z"))))


def dom(g):
    """pr₁⟨G⟩ := {x | (∃y)((x,y)∈G)}  (domaine / ensemble de définition, E.II.38)."""
    return app("dom", g)


def img(g):
    """pr₂⟨G⟩ := {y | (∃x)((x,y)∈G)}  (image / ensemble des valeurs, E.II.38)."""
    return app("img", g)


# @livre Ch.R §2 Def.- | E.R.7 item 4 (image de X par f, extension aux ensembles de parties) | PDF p.310
# @livre Ch.R §3 Def.- | E.R.14 item 6 (application X↦K(X) définie par la partie K) | PDF p.317
def image(g, x):
    """G⟨X⟩ := {y | (∃x)(x∈X et (x,y)∈G)}  (image directe de X par G, E.II.39, Déf. 3)."""
    return app("image", g, x)


# @livre Ch.R §3 Def.- | E.R.14 item 9 (partie réciproque K⁻¹ et application Y↦K⁻¹(Y)) | PDF p.317
def reciproque(g):
    """G⁻¹ := {z | (∃x)(∃y)(z=(x,y) et (y,x)∈G)}  (graphe réciproque, E.II.41, Déf. 5)."""
    return app("reciproque", g)


# @livre Ch.R §3 Def.- | E.R.14 item 10 (ensemble composé B∘A) | PDF p.317
def composee(gp, g):
    """G'∘G := graphe (en x,z) de (∃y)((x,y)∈G et (y,z)∈G')  (E.II.42, Déf. 6)."""
    return app("composee", gp, g)


# @livre Ch.R §3 Def.- | E.R.13 item 4 (diagonale Δ de E×E) | PDF p.316
def diagonale(x):
    """Δ_X := {z | (∃d)(d∈X et z=(d,d))}  (graphe de l'application identique de X, E.III.3.1).

    C'est le graphe de la bijection identité de X sur X (témoin de Eq(X,X)) : il
    relie chaque d∈X à lui-même.  Existence par S8 (sélection dans X×X), unicité
    par A1, comme produit/réciproque.  Liant interne « d0 » (≠ x,y,z,u,v,p,q,w) pour
    éviter toute capture quand on instancie aux coordonnées u,v,z."""
    return app("diagonale", x)


def graphe_terme(a, t, x="x"):
    """F := {w | (∃x)(∃y)(w=(x,y) et x∈A et y=T)}  (graphe de la fonction x↦T, E.II.46).

    T est le terme (avec x libre). A et T déterminent F (constante introductrice).
    META : l'assemblage de Bourbaki lie x (« ne contient ni x ni y », Critère C54
    et CS-renommage) ; ici F = app(A, T) est paramétrée par A et le terme T."""
    return app("graphe_terme", a, t)


def fonction_terme(a, t, c, x="x"):
    """x ↦ T  (x∈A, T∈C) := la fonction (F, A, C) = ({(x,T)|x∈A}, A, C)  (E.II.46).

    Assemblage couple (F, A, C) avec F = graphe_terme(A, T)."""
    return couple(couple(graphe_terme(a, t, x), a), c)


def est_fonctionnel(f):
    """« F est un graphe fonctionnel » := (∀u)(∀v)(∀z)(((u,v)∈F et (u,z)∈F)⇒v=z)
    (au plus une valeur par antécédent, E.II.43, Déf. 9).

    Liants u,v,z (≠ y milieu de couple_composee, ≠ w trou de congruence) pour
    composer sans capture."""
    u, v, z = var("u"), var("v"), var("z")
    return pourtout("u", pourtout("v", pourtout("z",
        impl(et(appartient(couple(u, v), f), appartient(couple(u, z), f)),
             egal(v, z)))))


def valeur(f, x, b="y"):
    """f(x) := τb((x,b)∈F)  (valeur de la fonction F en x, E II.13, §3.4).

    ⚠️ COQUILLE CORRIGÉE (5 août 2026) : cette docstring citait « E.II.43 », page
    qui ne contient pas cette définition.  Le bon repère est E II.13 (PDF p.64),
    recoupé par trois marqueurs `@livre` indépendants — dont
    `ii_3_4_fonctions/ensembles_valeur_codomaine.py:36` (E II.13 L.24-33).

    Le liant b vaut « y » par défaut (rétro-compatible avec tout le projet et avec
    valeur_caracterisation/C46 qui apparie la coordonnée var("y")).  On peut le
    paramétrer par une lettre fraîche lorsqu'une valeur f(x) figure DANS un terme
    qui sera lui-même quantifié sur « y » (ex. le graphe produit
    (F(pr₁k), G(pr₂k)) plongé dans graphe_terme, où le ∃y du domaine/image et le
    τy de cette valeur entreraient en collision de capture) — levée du « verrou
    liant valeur »."""
    return tau(b, appartient(couple(x, var(b)), f))


# @livre Ch.R §2 Def.- | E.R.11 item 13 (restriction f↾A) | PDF p.314
def restriction(f, x):
    """f|X := restriction de f à X  (graphe {(x,y) | x∈X et y=f(x)}, E.II.45, Déf.).

    Au niveau des graphes : f|X = F ∩ (X × img(F)), caractérisé par
    (u,v)∈f|X ⇔ (u∈X et (u,v)∈F)  (cf. AXIOME_RESTRICTION)."""
    return app("restriction", f, x)


def est_constante(f, x="x", xp="xp"):
    """« f constante » := (∀x)(∀x')((x∈dom F et x'∈dom F) ⇒ f(x)=f(x'))
    (application constante, E.II.45, Déf.)."""
    vx, vxp = var(x), var(xp)
    return pourtout(x, pourtout(xp,
        impl(et(appartient(vx, dom(f)), appartient(vxp, dom(f))),
             egal(valeur(f, vx), valeur(f, vxp)))))


# @livre Ch.R §2 Def.- | E.R.7 item 3 (élément invariant par f) | PDF p.310
def est_invariant(t, f):
    """« t invariant par f » := f(t) = t  (élément invariant, E.II.45, Déf.)."""
    return egal(valeur(f, t), t)


# @livre Ch.R §2 Def.- | E.R.11 item 13 (f et g coïncident dans A) | PDF p.314
def coincident(f, g, e, x="x"):
    """« f et g coïncident dans E » := E⊂dom F et E⊂dom G et (∀x)(x∈E ⇒ f(x)=g(x))
    (coïncidence de deux fonctions dans un ensemble, E.II.45, Déf.)."""
    vx = var(x)
    return et(et(inclus(e, dom(f)), inclus(e, dom(g))),
              pourtout(x, impl(appartient(vx, e), egal(valeur(f, vx), valeur(g, vx)))))


# @livre Ch.R §6 Ex.- | E.R.26 item 2 (« g est un prolongement de f » : relation d'ordre entre applications) | PDF p.329
# @livre Ch.R §2 Def.- | E.R.11 item 13 (prolongement de f↾A à E) | PDF p.314
def prolonge(g, f):
    """« g prolonge f » (au sens des graphes) := F⊂G  (prolongement, E.II.45, Déf.).

    Bourbaki : F⊂G ⇔ (A⊂C et f coïncide avec g dans A). Avec en outre B⊂D, g est
    un prolongement de f. La sous-famille = inclusion des graphes fonctionnels."""
    return inclus(f, g)


# ── §II.4 — Familles d'ensembles : réunion et intersection ────────────────────
# @livre Ch.R §2 Def.- | E.R.11 item 14 (famille d'éléments d'un ensemble) | PDF p.314
# @livre Ch.R §4 Def.- | E.R.16 item 1 (famille de parties d'un ensemble E) | PDF p.319
def valeur_famille(f, i):
    """X_ι := valeur(f, ι) — la valeur en ι de la famille = la fonction f  (E.II.4.1).

    Une famille (X_ι)_{ι∈I} EST une fonction ι ↦ X_ι (graphe fonctionnel, §3.4) ;
    sa valeur en ι EST donc valeur(f, ι) = τy((ι,y)∈f) — même terme, même liant que
    partout ailleurs.  MIGRATION D'ENCODAGE du 2 août 2026 (décision actée au
    journal) : l'ancien terme opaque app('fam', f, i) était un symbole LIBRE
    qu'aucun des 22 axiomes ne reliait à `valeur` — d'où les ponts fam↔valeur
    (HW/HN) mesurés INDÉPENDANTS.  La redéfinition rend ces ponts RÉFLEXIFS (t=t) :
    la FIDÉLITÉ remplace l'hypothèse.
    ⚠️ Hérite du liant b="y" de `valeur` : dans un contexte qui quantifie sur y,
    appeler valeur(f, i, b=frais) au site concerné (« verrou liant valeur »)."""
    return valeur(f, i)


# @livre Ch.R §4 Def.- | E.R.17 item 2 (réunion de la famille d'ensembles) | PDF p.320
def reunion_famille(f, i):
    """⋃_{ι∈I} X_ι := { x | (∃ι)(ι ∈ I et x ∈ X_ι) }  (E.II.4.1, Déf. 1)."""
    return app("reunion_fam", f, i)


# @livre Ch.II §4.1 Def.2 | E II.22 L.49-53 | PDF p.73
# (l'ancien marqueur « Ch.R §4 | E.R.19 item 6 | PDF p.322 » désignait le RÉSUMÉ : c'est de là que
#  venait l'incohérence du 26 juil. 2026 — un résumé condense et suppose le contexte acquis, il ne
#  peut pas servir de source à un AXIOME. Voir AXIOME_INTER_FAM plus bas.)
def inter_famille(f, i):
    """⋂_{ι∈I} X_ι := { x ∈ ⋃_{ι∈I} X_ι | (∀ι)((ι ∈ I) ⇒ (x ∈ X_ι)) }  (E II.22, Déf. 2).

    Sélection S8 dans la réunion (unicité A1) : c'est la réunion qui fournit la borne que
    Bourbaki obtient en supposant I ≠ ∅. On a donc ⋂_{ι∈∅} X_ι = ∅ ; caractérisé par
    AXIOME_INTER_FAM."""
    return app("inter_fam", f, i)


def complement_famille(e, f):
    """(∁_E X_ι)_{ι∈I} := la famille ι ↦ E∖X_ι  (famille des complémentaires).

    Famille définie par le terme ι ↦ E∖X_ι (C54) : son ι-ème terme est E∖X_ι.
    Sert à exprimer les seconds membres des lois de De Morgan des familles
    (E.II.4, Prop. 5) : ⋂_{ι∈I}(E∖X_ι) = inter_famille(complement_famille(E,f), I)."""
    return app("compl_fam", e, f)


# @livre Ch.R §4 Def.- | E.R.18 item 4 (recouvrement d'une partie A de E) | PDF p.321
def est_recouvrement(f, i, e):
    """« (X_ι)_{ι∈I} est un recouvrement de E » := E ⊂ ⋃_{ι∈I} X_ι  (E.II.4.6, Déf. 5)."""
    return inclus(e, reunion_famille(f, i))


def plus_fin(g, k, f, i):
    """« (Y_κ)_{κ∈K} plus fin que (X_ι)_{ι∈I} »
       := (∀κ)(κ ∈ K ⇒ (∃ι)(ι ∈ I et Y_κ ⊂ X_ι))  (E.II.4.6, Déf. 5).

    g, k : famille/indices du recouvrement le plus fin ;
    f, i : famille/indices du recouvrement le moins fin."""
    vk, vi = var("k"), var("i")
    return pourtout("k", impl(appartient(vk, k),
        existe("i", et(appartient(vi, i), inclus(valeur_famille(g, vk),
                                                  valeur_famille(f, vi))))))


def sont_disjoints(a, b):
    """« A et B sont disjoints » := A ∩ B = ∅  (E.II.4.6, Déf. 6)."""
    return egal(intersection(a, b), VIDE)


# @livre Ch.R §4 Def.- | E.R.18 item 4 (parties mutuellement disjointes) | PDF p.321
def famille_disjointe(f, i):
    """« les X_ι sont (deux à deux) disjoints »
       := (∀ι)(∀κ)((ι∈I et κ∈I et ι≠κ) ⇒ X_ι ∩ X_κ = ∅)  (E.II.4.6, Déf. 6)."""
    vi, vk = var("i"), var("k")
    return pourtout("i", pourtout("k",
        impl(et(et(appartient(vi, i), appartient(vk, i)), non(egal(vi, vk))),
             sont_disjoints(valeur_famille(f, vi), valeur_famille(f, vk)))))


# @livre Ch.R §5 Def.- | E.R.22 item 1 (partition d'un ensemble E) | PDF p.325
# @livre Ch.R §4 Def.- | E.R.18 item 4 (partition de E) | PDF p.321
def est_partition(f, i, e):
    """« (X_ι)_{ι∈I} est une partition de E » := recouvrement de E, famille disjointe,
       et parties non vides  (E.II.4.7, Déf. 7)."""
    vi = var("i")
    return et(et(est_recouvrement(f, i, e), famille_disjointe(f, i)),
              pourtout("i", impl(appartient(vi, i), non(egal(valeur_famille(f, vi), VIDE)))))


# @livre Ch.R §4 Def.- | E.R.18 item 5 (somme de la famille ; adjonction) | PDF p.321
def somme_famille(f, i):
    """∑_{ι∈I} X_ι := ⋃_{ι∈I} (X_ι × {ι})  (E.II.4.8, Déf. 8)."""
    return app("somme_fam", f, i)


# ── §II.5 — Ensemble des parties, applications, produit d'une famille ─────────
def parties(x):
    """P(X) := {Y | Y ⊂ X}  (ensemble des parties de X, E.II.5.1, axiome A3)."""
    return app("parties", x)


# @livre Ch.R §4 Def.- | E.R.20 item 9 (exponentiation E^I) | PDF p.323
def exposant(e, f):
    """F^E := {G ∈ P(E×F) | G fonctionnel ∧ pr₁G = E}  (graphes des applications, E.II.5.2)."""
    return app("exposant", e, f)


# @livre Ch.R §4 Def.- | E.R.20 item 9 (E^I ↔ ensemble des applications de I dans E) | PDF p.323
def applications(e, f):
    """𝓕(E;F) := {(G, E, F) | G ∈ F^E}  (ensemble des applications de E dans F, E.II.5.2)."""
    return app("applications", e, f)


# @livre Ch.R §4 Def.- | E.R.20 item 9 (produit de la famille d'ensembles) | PDF p.323
def produit_famille(f, i):
    """∏_{ι∈I} X_ι := { F ∈ 𝔓(I×A) | F fonctionnel, dom F = I, (∀ι)(ι∈I ⇒ F(ι)∈X_ι) }
       avec A = ⋃_{ι∈I} X_ι  (produit d'une famille d'ensembles, E.II.5.3, Déf. 1).

    Les QUATRE conjoints sont ceux de `AXIOME_PRODUIT_FAM` ; « F ∈ 𝔓(I×A) », qui
    est le conjoint de tête, est ce qui fait de F un GRAPHE (et donc une fonction
    au sens du livre) — il a été absent jusqu'au 26 juil. 2026, cf. l'avertissement
    posé sur l'axiome."""
    return app("produit_fam", f, i)


# @livre Ch.R §4 Def.- | E.R.21 item 11 (coordonnée d'indice κ : pr_κ) | PDF p.324
def projection_indice(f, i):
    """pr_ι(F) := F(ι) = valeur(F, ι)  (fonction coordonnée d'indice ι, E.II.5.3)."""
    return valeur(f, i)


# @livre Ch.R §2 Def.- | E.R.8 item 8 (application injective) | PDF p.311
def est_injective(f):
    """« f injective » (forme littérale, NON gardée) := (∀u)(∀u')((f(u)=f(u'))⇒u=u').

    ⚠ Forme dérivée de la Déf. 10 de Bourbaki (§II.3.7, E II.16), valable pour une
    APPLICATION (totale). Pour la fidélité « deux éléments DE A » et pour les
    preuves (un graphe vaut τy(faux) hors de son domaine), on utilise la forme
    GARDÉE `injective_dans(f, A)` — c'est elle qui entre dans est_bijective."""
    u, up = var("u"), var("up")
    return pourtout("u", pourtout("up", impl(egal(valeur(f, u), valeur(f, up)), egal(u, up))))


# @livre Ch.R §2 Def.- | E.R.7 item 4 (application surjective / surjection) | PDF p.310
# @livre Ch.R §2 Def.- | E.R.11 item 14 (représentation paramétrique = application sur F) | PDF p.314
def est_surjective(f, a, b):
    """« f surjective de A sur B » := f⟨A⟩ = B  (E II.16, Déf. 10)."""
    return egal(image(f, a), b)


def est_bijective(f, a, b):
    """« f bijective de A sur B » := injective SUR A et surjective  (E II.17, Déf. 10).

    Injectivité GARDÉE par A (`injective_dans`), fidèle au « deux éléments de A »
    de Bourbaki et compatible avec le codage par graphe (valeur indéterminée hors A)."""
    return et(injective_dans(f, a), est_surjective(f, a, b))


# ── §II.3.8 — Rétractions et sections (Déf. 11) ───────────────────────────────
def est_retraction(r, f, a, x="x"):
    """« r est une rétraction associée à f » (f : A → B injective, r : B → A) :=
       (∀x)(x ∈ A ⇒ r(f(x)) = x)   c.-à-d.  r ∘ f = Id_A   (E II.18, Déf. 11).

    Encodage matriciel de l'implémentation (§3.8) : la composée r∘f restreinte aux
    valeurs vaut l'identité sur A. On dit aussi « inverse à gauche » de f.
    r(f(x)) = valeur(R, valeur(F, x))."""
    vx = var(x)
    return pourtout(x, impl(appartient(vx, a),
                           egal(valeur(r, valeur(f, vx)), vx)))


def est_section(s, f, b, y="y"):
    """« s est une section associée à f » (f : A → B surjective, s : B → A) :=
       (∀y)(y ∈ B ⇒ f(s(y)) = y)   c.-à-d.  f ∘ s = Id_B   (E II.18, Déf. 11).

    Encodage matriciel (§3.8). On dit aussi « inverse à droite » de f.
    f(s(y)) = valeur(F, valeur(S, y))."""
    vy = var(y)
    return pourtout(y, impl(appartient(vy, b),
                           egal(valeur(f, valeur(s, vy)), vy)))


def est_inverse_gauche(r, f, a, x="x"):
    """Synonyme de rétraction : « r est un inverse à gauche de f »  (E II.18, Déf. 11)."""
    return est_retraction(r, f, a, x)


def est_inverse_droite(s, f, b, y="y"):
    """Synonyme de section : « s est un inverse à droite de f »  (E II.18, Déf. 11)."""
    return est_section(s, f, b, y)


def injective_dans(f, a, u="u", up="up"):
    """« f injective sur A » := (∀u)(∀u')((u∈A et u'∈A et f(u)=f(u')) ⇒ u=u').

    Variante GARDÉE (par l'appartenance à A) de l'injectivité, fidèle à la
    démonstration de la Prop. 8 (« où x ∈ A et y ∈ A »). Une rétraction n'impose
    r(f(x))=x que pour x∈A, d'où la garde."""
    vu, vup = var(u), var(up)
    return pourtout(u, pourtout(up,
        impl(et(et(appartient(vu, a), appartient(vup, a)),
                egal(valeur(f, vu), valeur(f, vup))),
             egal(vu, vup))))


# ── §II.6 — Relations d'équivalence ───────────────────────────────────────────
# Une « relation R{x, y} » est modélisée par une fonction Python R : (Terme, Terme)
# → Formule (Bourbaki : R est une relation où figurent les lettres x, y).  Les
# définitions de la section sont les énoncés VERBATIM, construits sur cette R.
# @livre Ch.II §6.1 Def.- | E II.39 L.29-30 | PDF p.90
# @livre Ch.R §3 Def.- | E.R.13 item 4 (relation symétrique : A = A⁻¹) | PDF p.316
def est_symetrique(R, x="x", y="y"):
    """« R symétrique (par rapport à x, y) » := (∀x)(∀y)(R{x,y} ⇒ R{y,x})  (E.II.6.1).

    Bourbaki : R est symétrique si R{x,y} ⇔ R{y,x} ; le sens ⇐ étant l'instance
    obtenue en échangeant x et y, on encode la clôture universelle de R{x,y}⇒R{y,x}."""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y, impl(R(vx, vy), R(vy, vx))))


# @livre Ch.II §6.1 Def.- | E II.39 L.34-35 | PDF p.90
def est_transitive(R, x="x", y="y", z="z"):
    """« R transitive (par rapport à x, y) » := (∀x)(∀y)(∀z)((R{x,y} et R{y,z}) ⇒ R{x,z})
    (E.II.6.1 ; z ne figure pas dans R)."""
    vx, vy, vz = var(x), var(y), var(z)
    return pourtout(x, pourtout(y, pourtout(z,
        impl(et(R(vx, vy), R(vy, vz)), R(vx, vz)))))


# @livre Ch.II §6.1 Def.- | E II.40 L.4-5 | PDF p.91
# @livre Ch.R §5 Def.- | E.R.23 item 2 (relation d'équivalence : réflexive, symétrique, transitive) | PDF p.326
def est_relation_equivalence(R, x="x", y="y", z="z"):
    """« R{x,y} est une relation d'équivalence » := R symétrique ET transitive  (E.II.6.1)."""
    return et(est_symetrique(R, x, y), est_transitive(R, x, y, z))


# @livre Ch.II §6.1 Def.- | E II.40 L.11-14 | PDF p.91
def est_reflexive_dans(R, e, x="x"):
    """« R réflexive dans E » := (∀x)(R{x,x} ⇔ x∈E)  (E.II.6.1 ; x ne figure pas dans E)."""
    vx = var(x)
    return pourtout(x, equiv(R(vx, vx), appartient(vx, e)))


# @livre Ch.II §6.1 Def.- | E II.40 L.15-16 | PDF p.91
def est_relation_equivalence_dans(R, e, x="x", y="y", z="z"):
    """« R relation d'équivalence dans E » := relation d'équivalence ET réflexive dans E
    (E.II.6.1)."""
    return et(est_relation_equivalence(R, x, y, z), est_reflexive_dans(R, e, x))


def rel_graphe(g, x="x", y="y"):
    """Relation associée à un graphe G : R{x,y} := (x,y) ∈ G.

    Renvoie une fonction (Terme, Terme) → Formule, utilisable comme R{·,·}."""
    vg = _terme_var(g)
    return lambda a, b: appartient(couple(a, b), vg)


def _terme_var(t):
    return t if isinstance(t, Terme) else var(t)


# @livre Ch.II §6.2 Def.- | E II.41 L.25-26 | PDF p.92
def classe(g, x):
    """Cl_R(x) := G⟨{x}⟩ = {y∈E | R{x,y}}  (classe d'équivalence de x, E.II.6.2).

    Codée par l'image directe du singleton {x} par le graphe G (Bourbaki E.II.6.2)."""
    return image(g, singleton(_terme_var(x)))


# @livre Ch.II §6.2 Def.- | E II.41 L.29-31 | PDF p.92
# @livre Ch.R §5 Def.- | E.R.23 item 2 (ensemble quotient E/R, classes d'équivalence) | PDF p.326
def quotient(g, e):
    """E/R := { C ∈ P(E) | (∃x)(x∈E et C = Cl_R(x)) }  (ensemble quotient, E.II.6.2)."""
    return app("quotient", g, e)


# @livre Ch.II §6.2 Def.- | E II.41 L.31-33 | PDF p.92
# @livre Ch.R §5 Def.- | E.R.23 item 2 (application canonique de E sur E/R) | PDF p.326
def application_canonique(g, e):
    """p : E → E/R,  p(x) := Cl_R(x)  (application canonique, E.II.6.2).

    Codée par son graphe { (x, Cl_R(x)) | x∈E }."""
    return app("appcanon", g, e)


# @livre Ch.II §6.3 Def.- | E II.42 L.34-37 | PDF p.93
# @livre Ch.R §5 Def.- | E.R.24 item 7 (relation compatible avec R) | PDF p.327
def est_compatible(P, R, x="x", y="y"):
    """« P{x} compatible avec R{x,x'} (par rapport à x) »
       := (∀x)(∀y)((P{x} et R{x,y}) ⇒ P{y})  (E.II.6.3 ; y ne figure ni dans P ni dans R)."""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y, impl(et(P(vx), R(vx, vy)), P(vy))))


def relation_quotient(P, e, g, t="t", x="x"):
    """P'{t} := t∈E/R et (∃x)(x∈t et P{x})  (relation déduite par passage au quotient, E.II.6.3)."""
    vt, vx = var(t), var(x)
    return et(appartient(vt, quotient(g, e)),
              existe(x, et(appartient(vx, vt), P(vx))))


# @livre Ch.II §6.4 Def.- | E II.43 L.16-19 | PDF p.94
# @livre Ch.R §5 Def.- | E.R.24 item 6 (partie saturée pour R) | PDF p.327
def est_saturee(a, g, e, x="x"):
    """« A saturée pour R » := la relation x∈A est compatible (par rapport à x) avec R
    (E.II.6.4) ; équivaut à (∀x)(x∈A ⇒ Cl_R(x) ⊂ A)."""
    return est_compatible(lambda t: appartient(t, a), rel_graphe(g), x)


# @livre Ch.II §6.4 Def.- | E II.43 L.22-34 | PDF p.94
# @livre Ch.R §5 Def.- | E.R.24 item 6 (saturé de A = f⁻¹(f(A))) | PDF p.327
def sature(a, p):
    """Ã := p⁻¹⟨p⟨A⟩⟩  (saturé de A pour R, plus petite partie saturée contenant A, E.II.6.4)."""
    return image(reciproque(p), image(p, a))


def est_compatible_application(f, R, x="x", xp="xp"):
    """« f compatible avec R » := (∀x)(∀x')(R{x,x'} ⇒ f(x)=f(x'))  (E.II.6.5).

    f constante sur toute classe d'équivalence suivant R."""
    vx, vxp = var(x), var(xp)
    return pourtout(x, pourtout(xp, impl(R(vx, vxp), egal(valeur(f, vx), valeur(f, vxp)))))


# @livre Ch.II §6.2 Def.- | E II.41 L.17-19 | PDF p.92
def relation_associee_fonction(f, x="x", y="y"):
    """Relation d'équivalence associée à f : R{x,y} := (x∈E et y∈E et f(x)=f(y))  (E.II.6.2).

    Avec E = dom f.  Renvoie une fonction (Terme, Terme) → Formule."""
    vf = _terme_var(f)
    return lambda a, b: et(et(appartient(a, dom(vf)), appartient(b, dom(vf))),
                           egal(valeur(vf, a), valeur(vf, b)))


def plus_fine(S, R, x="x", y="y"):
    """« S plus fine que R » := (∀x)(∀y)(S{x,y} ⇒ R{x,y})  (E.II.6.7).

    La relation S ⇒ R est vraie (clôture universelle)."""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y, impl(S(vx, vy), R(vx, vy))))


# @livre Ch.R §5 Def.- | E.R.25 item 10 (produit R×S de deux relations d'équivalence) | PDF p.328
def relation_produit(R, Rp, x="x", y="y", xp="xp", yp="yp"):
    """(R × R'){(x,x'), (y,y')} := R{x,y} et R'{x',y'}  (produit de relations, E.II.6.8).

    Renvoie une fonction (Terme, Terme) → Formule prenant deux couples u=(x,x'), v=(y,y').
    Ici on l'expose sous la forme directe sur les composantes."""
    return lambda a, ap, b, bp: et(R(a, b), Rp(ap, bp))


def classe_objets(R, x, y="y"):
    """θ{x} := τ_y(R{x,y})  (classe d'objets équivalents à x, E.II.6.9 ; R sans graphe)."""
    return tau(y, R(_terme_var(x), var(y)))


# ── Chapitre III §1 — Relations d'ordre, ensembles ordonnés ───────────────────
# Une « relation R{x, y} » (x, y lettres distinctes) est modélisée par une
# fonction Python R : (Terme, Terme) → Formule (cf. §II.6).  Les définitions sont
# les énoncés VERBATIM de Bourbaki E.III.1, construits sur cette R.

def ordre_transitif(R, x="x", y="y", z="z"):
    """« R transitive (par rapport à x, y) » := (∀x)(∀y)(∀z)((R{x,y} et R{y,z}) ⇒ R{x,z})
    (E.III.1.1 ; première condition d'une relation d'ordre ; z ne figure pas dans R)."""
    vx, vy, vz = var(x), var(y), var(z)
    return pourtout(x, pourtout(y, pourtout(z,
        impl(et(R(vx, vy), R(vy, vz)), R(vx, vz)))))


def ordre_antisymetrique(R, x="x", y="y"):
    """« R antisymétrique » := (∀x)(∀y)((R{x,y} et R{y,x}) ⇒ x=y)
    (E.III.1.1 ; deuxième condition d'une relation d'ordre)."""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y, impl(et(R(vx, vy), R(vy, vx)), egal(vx, vy))))


def ordre_reflexif_implicite(R, x="x", y="y"):
    """« R{x,y} ⇒ (R{x,x} et R{y,y}) » (clôt. univ.)  (E.III.1.1 ; troisième condition)."""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y, impl(R(vx, vy), et(R(vx, vx), R(vy, vy)))))


# @livre Ch.R §6 Def.- | E.R.25 item 1 (relation d'ordre : transitivité + « ω{x,y} et ω{y,x} » équivaut à x=y) | PDF p.328
def est_relation_ordre(R, x="x", y="y", z="z"):
    """« R{x,y} est une relation d'ordre (entre x et y) » := transitive ET antisymétrique
    ET R{x,y}⇒(R{x,x} et R{y,y})  (E.III.1.1, Définition)."""
    return et(et(ordre_transitif(R, x, y, z), ordre_antisymetrique(R, x, y)),
              ordre_reflexif_implicite(R, x, y))


# @livre Ch.III §1.3 Rem.- | E III.4 L.17-31 | PDF p.107
# (prose du n°3 « Notations et terminologie » : R{x,y} notée x≤y, lectures, y≥x synonyme,
#  x≥y = relation de préordre opposée à x≤y, abus de langage « relation ≤ » —
#  prose, rien à formaliser au-delà de ordre_oppose)
# @livre Ch.R §6 Def.- | E.R.26 item 1 (ordres opposés) | PDF p.329
def ordre_oppose(R):
    """R^op{x,y} := R{y,x}  (relation d'ordre opposée, E.III.1.1, Exemple 3)."""
    return lambda a, b: R(b, a)


# @livre Ch.III §1.3 Rem.- | E III.4 L.38-39 | PDF p.107
# (« si on omet (RO_II), on obtient les conditions pour que x≤y soit une relation de
#  préordre dans E »)
# @livre Ch.R §6 Def.- | E.R.26 item 1 (relation de préordre) | PDF p.329
def est_relation_preordre(R, x="x", y="y", z="z"):
    """« R{x,y} est une relation de préordre » := transitive ET R{x,y}⇒(R{x,x} et R{y,y})
    (sans l'antisymétrie ; E.III.1.2, Définition)."""
    return et(ordre_transitif(R, x, y, z), ordre_reflexif_implicite(R, x, y))


def est_reflexive_dans_ordre(R, e, x="x"):
    """« R réflexive dans E » := (∀x)(R{x,x} ⇔ x∈E)  (E.III.1.1 ; x ne figure pas dans E)."""
    vx = var(x)
    return pourtout(x, equiv(R(vx, vx), appartient(vx, e)))


# @livre Ch.III §1.3 Rem.- | E III.4 L.32-37 | PDF p.107
# (les conditions (RO_I)–(RO_IV) : réécriture en notation ≤ de « relation d'ordre dans E »)
# @livre Ch.R §6 Def.- | E.R.26 item 1 (ensemble ordonné, structure d'ordre) | PDF p.329
def est_relation_ordre_dans(R, e, x="x", y="y", z="z"):
    """« R{x,y} relation d'ordre dans l'ensemble E » := relation d'ordre ET réflexive dans E
    (E.III.1.1, Définition)."""
    return et(est_relation_ordre(R, x, y, z), est_reflexive_dans_ordre(R, e, x))


# @livre Ch.III §1.3 Def.- | E III.5 L.1-4 | PDF p.108
# @livre Ch.R §6 Def.- | E.R.26 item 3 (notation x<y : « x≤y et x≠y ») | PDF p.329
def relation_stricte(R, x="x", y="y"):
    """R{x,y} associée < : x<y := (R{x,y} et x≠y)  (E.III.1.3 ; relation stricte)."""
    return lambda a, b: et(R(a, b), non(egal(a, b)))


# @livre Ch.III §1.1 Ex.2 | E III.2 L.1-4 | PDF p.105
# @livre Ch.III §1.4 Def.- | E III.5 L.32-37 | PDF p.108
# @livre Ch.R §6 Def.- | E.R.26 item 1 (ordre induit sur A, prolongement d'un ordre) | PDF p.329
def ordre_induit(R, e, x="x", y="y"):
    """R induite dans E := « R{x,y} et x∈E et y∈E »  (E.III.1.1, Exemple 2 ; ordre induit)."""
    return lambda a, b: et(et(R(a, b), appartient(a, e)), appartient(b, e))


# ── §III.1.6 — Éléments maximaux / minimaux (Déf. 3) ──────────────────────────
def est_element_minimal(R, e, a, x="x"):
    """« a est un élément minimal de E » := a∈E et (∀x)((x∈E et R{x,a}) ⇒ x=a)
    (E.III.1.6, Déf. 3 ; R notée ≤)."""
    va, vx = _terme_var(a), var(x)
    return et(appartient(va, e),
              pourtout(x, impl(et(appartient(vx, e), R(vx, va)), egal(vx, va))))


def est_element_maximal(R, e, a, x="x"):
    """« a est un élément maximal de E » := a∈E et (∀x)((x∈E et R{a,x}) ⇒ x=a)
    (E.III.1.6, Déf. 3 ; R{a,x} = a≤x = x≥a)."""
    va, vx = _terme_var(a), var(x)
    return et(appartient(va, e),
              pourtout(x, impl(et(appartient(vx, e), R(va, vx)), egal(vx, va))))


# ── §III.1.7 — Plus petit / plus grand élément (Déf. 4) ───────────────────────
# @livre Ch.R §6 Def.- | E.R.27 item 5 (plus petit élément de X) | PDF p.330
def est_plus_petit_element(R, e, a, x="x"):
    """« a est le plus petit élément de E » := a∈E et (∀x)(x∈E ⇒ R{a,x})  (E.III.1.7, Déf. 4)."""
    va, vx = _terme_var(a), var(x)
    return et(appartient(va, e), pourtout(x, impl(appartient(vx, e), R(va, vx))))


# @livre Ch.R §6 Def.- | E.R.27 item 5 (plus grand élément de X) | PDF p.330
def est_plus_grand_element(R, e, a, x="x"):
    """« a est le plus grand élément de E » := a∈E et (∀x)(x∈E ⇒ R{x,a})  (E.III.1.7, Déf. 4)."""
    va, vx = _terme_var(a), var(x)
    return et(appartient(va, e), pourtout(x, impl(appartient(vx, e), R(vx, va))))


# ── §III.1.8 — Majorants, minorants (Déf. 5) ──────────────────────────────────
def majore(R, X, a, y="y"):
    """« a majore X » := (∀y)(y∈X ⇒ R{y,a})   c.-à-d.  a≥y pour tout y∈X  (E.III.1.8, Déf. 5)."""
    va, vy = _terme_var(a), var(y)
    return pourtout(y, impl(appartient(vy, X), R(vy, va)))


def minore(R, X, a, y="y"):
    """« a minore X » := (∀y)(y∈X ⇒ R{a,y})   c.-à-d.  a≤y pour tout y∈X  (E.III.1.8, Déf. 5)."""
    va, vy = _terme_var(a), var(y)
    return pourtout(y, impl(appartient(vy, X), R(va, vy)))


# @livre Ch.R §6 Def.- | E.R.27 item 5 (partie cofinale à E) | PDF p.330
def est_cofinale(R, A, e, x="x", y="y"):
    """« A cofinale à E » := (∀x)(x∈E ⇒ (∃y)(y∈A et R{x,y}))  (E.III.1.8 ; partie cofinale)."""
    vx, vy = var(x), var(y)
    return pourtout(x, impl(appartient(vx, e),
        existe(y, et(appartient(vy, A), R(vx, vy)))))


# @livre Ch.R §6 Def.- | E.R.27 item 5 (partie coïnitiale à E) | PDF p.330
def est_coinitiale(R, A, e, x="x", y="y"):
    """« A coinitiale à E » := (∀x)(x∈E ⇒ (∃y)(y∈A et R{y,x}))  (E.III.1.8 ; partie coinitiale)."""
    vx, vy = var(x), var(y)
    return pourtout(x, impl(appartient(vx, e),
        existe(y, et(appartient(vy, A), R(vy, vx)))))


# ── §III.1.10 — Ensembles filtrants (Déf. 7) ──────────────────────────────────
def est_filtrant_droite(R, e, x="x", y="y", z="z"):
    """« E filtrant à droite » := (∀x)(∀y)((x∈E et y∈E) ⇒ (∃z)(z∈E et R{x,z} et R{y,z}))
    (E.III.1.10, Déf. 7)."""
    vx, vy, vz = var(x), var(y), var(z)
    return pourtout(x, pourtout(y, impl(et(appartient(vx, e), appartient(vy, e)),
        existe(z, et(et(appartient(vz, e), R(vx, vz)), R(vy, vz))))))


def est_filtrant_gauche(R, e, x="x", y="y", z="z"):
    """« E filtrant à gauche » := (∀x)(∀y)((x∈E et y∈E) ⇒ (∃z)(z∈E et R{z,x} et R{z,y}))
    (E.III.1.10, Déf. 7 ; dualité)."""
    vx, vy, vz = var(x), var(y), var(z)
    return pourtout(x, pourtout(y, impl(et(appartient(vx, e), appartient(vy, e)),
        existe(z, et(et(appartient(vz, e), R(vz, vx)), R(vz, vy))))))


# ── §III.1.12 — Comparabilité, ordre total (Déf. 9) ───────────────────────────
def sont_comparables(R, a, b):
    """« a et b comparables » := (R{a,b} ou R{b,a})  (E.III.1.12, Déf. 9)."""
    return ou(R(_terme_var(a), _terme_var(b)), R(_terme_var(b), _terme_var(a)))


# @livre Ch.R §6 Def.- | E.R.26 item 4 (ensemble totalement ordonné) | PDF p.329
def est_totalement_ordonne(R, e, x="x", y="y", z="z"):
    """« E totalement ordonné » := relation d'ordre dans E ET deux éléments quelconques
    comparables : (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x}))  (E.III.1.12, Déf. 9)."""
    vx, vy = var(x), var(y)
    return et(est_relation_ordre_dans(R, e, x, y, z),
              pourtout(x, pourtout(y, impl(et(appartient(vx, e), appartient(vy, e)),
                  ou(R(vx, vy), R(vy, vx))))))


# ── §III.1.13 — Intervalles ───────────────────────────────────────────────────
# Termes définis par compréhension (sélection S8 dans E, unicité A1).  R notée ≤.
# @livre Ch.R §6 Def.- | E.R.27 item 4 (intervalle fermé [a,b]) | PDF p.330
def intervalle_ferme(R, e, a, b):
    """[a, b] := { x∈E | a≤x et x≤b }  (intervalle fermé, E.III.1.13)."""
    return app("interv_ff", e, _terme_var(a), _terme_var(b))


# @livre Ch.R §6 Def.- | E.R.27 item 4 (intervalle ouvert ]a,b[) | PDF p.330
def intervalle_ouvert(R, e, a, b):
    """]a, b[ := { x∈E | a<x et x<b }  (intervalle ouvert, E.III.1.13)."""
    return app("interv_oo", e, _terme_var(a), _terme_var(b))


# @livre Ch.R §6 Def.- | E.R.27 item 4 (intervalle ]<-,a] fermé illimité à gauche) | PDF p.330
def intervalle_illimite_gauche_ferme(R, e, a):
    """]←, a] := { x∈E | x≤a }  (intervalle fermé illimité à gauche, E.III.1.13)."""
    return app("interv_ig", e, _terme_var(a))


# @livre Ch.R §6 Def.- | E.R.27 item 4 (intervalle [a,->[ fermé illimité à droite) | PDF p.330
def intervalle_illimite_droite_ferme(R, e, a):
    """[a, →[ := { x∈E | a≤x }  (intervalle fermé illimité à droite, E.III.1.13)."""
    return app("interv_id", e, _terme_var(a))


# ── §III.5.3 — Intervalle d'entiers [a, b] ────────────────────────────────────
# Spécifique aux ENTIERS : l'ordre ≤ est celui des cardinaux (E.III.3.2), et la
# relation « x est un cardinal et x ≤ a » est collectivisante (E.III.5.3, Remarque
# III.25) ; l'ensemble obtenu est un ensemble d'entiers.  Contrairement aux
# intervalles d'un ordre général (interv_ff…, simples notations), celui-ci porte un
# AXIOME caractérisant (cf. `axiome_intervalle_entiers`, iii_4_1/ensembles_entiers_theoremes.py:203),
# légitimé par S8 (sélection) + A1.
#   ⚠️ CE COMMENTAIRE A CITÉ « AXIOME_INTERV_ENT » : symbole JAMAIS CODÉ (grep : 0 `def`, 0 `=`).
#   Corrigé le 27 juil. 2026. Un nom fantôme cité en commentaire envoie chercher ce qui n'existe
#   pas — c'est le même mode de nuisance qu'un résidu adossé à un symbole inexistant.
def intervalle_entiers(a, b):
    """[a, b] := { x | x cardinal et a ≤ x et x ≤ b }   (E.III.5.3).

    Intervalle d'entiers : sous-ensemble des cardinaux x avec a ≤ x ≤ b (≤ = ordre
    des cardinaux).  Terme collectivisant (Remarque III.25), caractérisé par
    `axiome_intervalle_entiers` (iii_4_1/ensembles_entiers_theoremes.py:203)."""
    return app("interv_ent", _terme_var(a), _terme_var(b))


# ── §III.2 — Ensembles bien ordonnés ─────────────────────────────────────────
# (R notée ≤ : R{a,b} = a≤b.  Définitions lues verbatim E.III.2.1 et §2.4.)

# @livre Ch.R §6 Def.- | E.R.27 item 5 (ensemble bien ordonné) | PDF p.330
def est_bien_ordonne(R, e, x="x", y="y", z="z", X="X", a="a", w="w"):
    """« E est bien ordonné par R » (Définition 1, E.III.2.1) :=
    E est ordonné par R  ET  toute partie non vide de E admet un plus petit élément.

      est_relation_ordre_dans(R,E)  et
      (∀X)((X⊂E et ¬(X=∅)) ⇒ (∃a)(a∈X et (∀w)(w∈X ⇒ R{a,w})))

    (« a est le plus petit élément de X » = a∈X et (∀w)(w∈X ⇒ a≤w).)"""
    vX, va, vw = var(X), var(a), var(w)
    petit = existe(a, et(appartient(va, vX),
                         pourtout(w, impl(appartient(vw, vX), R(va, vw)))))
    return et(est_relation_ordre_dans(R, e, x, y, z),
              pourtout(X, impl(et(inclus(vX, e), non(egal(vX, VIDE))), petit)))


def est_relation_bon_ordre(R, e, x="x", y="y", z="z", X="X", a="a", w="w"):
    """« R{x,y} est une relation de bon ordre sur E » (E.III.2.1) := synonyme de
    « E est bien ordonné par R » (Bourbaki : Déf. 1 « revient au même »)."""
    return est_bien_ordonne(R, e, x, y, z, X, a, w)


def est_segment(S, R, e, x="x", y="y"):
    """« S est un segment de E » (Définition 2, E.III.2.1) :=
    S⊂E  ET  (∀x)(∀y)((x∈S et y∈E et y≤x) ⇒ y∈S).

    (les relations x∈S, y∈E, y≤x entraînent y∈S ; R{y,x} = y≤x.)"""
    vS = _terme_var(S)
    vx, vy = var(x), var(y)
    return et(inclus(vS, e),
              pourtout(x, pourtout(y,
                  impl(et(et(appartient(vx, vS), appartient(vy, e)), R(vy, vx)),
                       appartient(vy, vS)))))


def segment_extremite(G, e, x):
    """S_x := ]←, x[ = { y∈E | (y,x)∈G et y≠x }  (segment d'extrémité x, E.III.2.1).

    Terme collectivisant (sélection S8 dans E, unicité A1) ; caractérisé par
    `axiome_segment_extremite()`.

    ⚠️ SIGNATURE MIGRÉE (2026-07-31).  Le 1ᵉʳ argument est le GRAPHE DE L'ORDRE
    **EN TANT QUE TERME**, plus une relation Python `R(a,b)`.  Avant la migration
    le terme rendu était `app("seg_ext", e, x)` : le paramètre d'ordre DISPARAISSAIT
    du terme, si bien que DEUX ordres différents (par exemple un ordre et son opposé)
    produisaient LE MÊME terme, chacun muni de son propre axiome caractéristique —
    d'où deux axiomes INCOMPATIBLES sur un même terme, et ⊢ ∅∈∅ par gestes purs du
    noyau.  Une garde « R est un ordre » n'y aurait rien changé (l'ordre ET son
    opposé la satisfont) : le défaut était la PERTE D'UN PARAMÈTRE, pas l'absence
    d'une condition.  Le terme porte désormais G, donc deux graphes distincts
    donnent des termes DISTINCTS.

    EFFET DÉRIVÉ : l'axiome associé devient CLOS (∀-clos sur G aussi), donc plus
    aucune variable libre, donc plus de CONSTANTE de théorie — le défaut C27
    (généralisation sur une constante) disparaît DE CE SITE."""
    if callable(G) and not isinstance(G, Terme):
        raise TypeError(
            "segment_extremite : le 1er argument est le GRAPHE (Terme), plus une "
            "relation callable R(a,b).  Migration seg_ext : passer G directement "
            "(p.ex. `_t(G)` au lieu de `_graphe_R(G)` / `_R_de(R)`).")
    return app("seg_ext", _terme_var(G), _terme_var(e), _terme_var(x))


def est_majorant_strict(R, X, v, y="y"):
    """« v est un majorant strict de X » (E.III.2.4) := v majore X et v∉X."""
    vv = _terme_var(v)
    return et(majore(R, X, vv, y), non(appartient(vv, X)))


def est_inductif(R, e, X="X", m="m", x="x", y="y", z="z"):
    """« E ordonné par R est inductif » (Définition 3, E.III.2.4) :=
    toute partie totalement ordonnée de E possède un majorant dans E :

      (∀X)((X⊂E et X est totalement ordonné par R) ⇒ (∃m)(m∈E et m majore X)).

    (X totalement ordonné par R : ordre induit de R sur X total.)"""
    vX, vm = var(X), var(m)
    Rind = ordre_induit(R, vX)
    total = pourtout(x, pourtout(y, impl(et(appartient(var(x), vX), appartient(var(y), vX)),
                ou(R(var(x), var(y)), R(var(y), var(x))))))
    maj = existe(m, et(appartient(vm, e), majore(R, vX, vm)))
    return pourtout(X, impl(et(inclus(vX, e), total), maj))


# ── Axiomes ───────────────────────────────────────────────────────────────────
# A1 — extensionnalité : (∀x)(∀y)((x⊂y et y⊂x) ⇒ x=y)
A1 = pourtout("x", pourtout("y",
        impl(et(inclus(_X, _Y), inclus(_Y, _X)), egal(_X, _Y))))

# A2 — paire : (∀x)(∀y) Coll_z(z=x ou z=y)
A2 = pourtout("x", pourtout("y",
        coll("z", ou(egal(_Z, _X), egal(_Z, _Y)))))

# Déf. de {x,y} : (∀x)(∀y)(∀z)(z ∈ {x,y} ⇔ (z=x ou z=y))
AXIOME_PAIRE = pourtout("x", pourtout("y", pourtout("z",
        equiv(appartient(_Z, paire(_X, _Y)), ou(egal(_Z, _X), egal(_Z, _Y))))))

# Déf. de ∅ : (∀z) ¬(z ∈ ∅)
AXIOME_VIDE = pourtout("z", non(appartient(_Z, VIDE)))

# Déf. de x∪y : (∀x)(∀y)(∀z)(z ∈ x∪y ⇔ (z∈x ou z∈y))
AXIOME_REUNION = pourtout("x", pourtout("y", pourtout("z",
        equiv(appartient(_Z, reunion(_X, _Y)),
              ou(appartient(_Z, _X), appartient(_Z, _Y))))))

# Déf. de x∩y : (∀x)(∀y)(∀z)(z ∈ x∩y ⇔ (z∈x et z∈y))
AXIOME_INTER = pourtout("x", pourtout("y", pourtout("z",
        equiv(appartient(_Z, intersection(_X, _Y)),
              et(appartient(_Z, _X), appartient(_Z, _Y))))))

# Déf. de E∖X (différence) : (∀x)(∀y)(∀z)(z∈x∖y ⇔ (z∈x et ¬(z∈y)))
# (réutilise les noms x,y pour E,X ; légitimé par S8 (sélection dans E) + A1.)
AXIOME_DIFF = pourtout("x", pourtout("y", pourtout("z",
        equiv(appartient(_Z, difference(_X, _Y)),
              et(appartient(_Z, _X), non(appartient(_Z, _Y)))))))

# Déf. de X×Y (E.II.33, Déf. 1 ; existence = Théorème 1 via S8, unicité = A1) :
#   (∀X)(∀Y)(∀z)(z ∈ X×Y ⇔ (∃p)(∃q)(z=(p,q) et p∈X et q∈Y))
# Liants existentiels p,q (≠ x,y des projections pr₁/pr₂) pour éviter toute
# capture quand on applique pr₁ à la composante liée — choix α-équivalent, fidèle.
_GX, _GY = var("X"), var("Y")
_P, _Q, _R = var("p"), var("q"), var("r")
AXIOME_PRODUIT = pourtout("X", pourtout("Y", pourtout("z",
        equiv(appartient(_Z, produit(_GX, _GY)),
              existe("p", existe("q",
                  et(et(egal(_Z, couple(_P, _Q)), appartient(_P, _GX)),
                     appartient(_Q, _GY))))))))


# Déf. du domaine pr₁⟨G⟩ : (∀G)(∀x)(x∈pr₁G ⇔ (∃y)((x,y)∈G))
AXIOME_DOM = pourtout("G", pourtout("x",
        equiv(appartient(_X, dom(var("G"))),
              existe("y", appartient(couple(_X, _Y), var("G"))))))

# Déf. de l'image pr₂⟨G⟩ : (∀G)(∀y)(y∈pr₂G ⇔ (∃x)((x,y)∈G))
AXIOME_IMG = pourtout("G", pourtout("y",
        equiv(appartient(_Y, img(var("G"))),
              existe("x", appartient(couple(_X, _Y), var("G"))))))

# Déf. de l'image directe G⟨X⟩ : (∀G)(∀X)(∀y)(y∈G⟨X⟩ ⇔ (∃x)(x∈X et (x,y)∈G))
AXIOME_IMAGE = pourtout("G", pourtout("X", pourtout("y",
        equiv(appartient(_Y, image(var("G"), var("X"))),
              existe("x", et(appartient(_X, var("X")), appartient(couple(_X, _Y), var("G"))))))))

# Déf. du graphe réciproque G⁻¹ : (∀G)(∀z)(z∈G⁻¹ ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G))
# Liants p,q (≠ x,y) pour rester compatible avec les projections.
AXIOME_RECIP = pourtout("G", pourtout("z",
        equiv(appartient(_Z, reciproque(var("G"))),
              existe("p", existe("q",
                  et(egal(_Z, couple(_P, _Q)), appartient(couple(_Q, _P), var("G"))))))))

# Déf. de la diagonale Δ_X = graphe de l'identité de X (E.III.3.1) :
#   (∀X)(∀z)(z ∈ Δ_X ⇔ (∃u)(u∈X et z=(u,u)))
# Liant interne « u » (≠ x,y,z,p,q,w).  Existence S8 (sélection X×X) + unicité A1.
AXIOME_DIAGONALE = pourtout("X", pourtout("z",
        equiv(appartient(_Z, diagonale(var("X"))),
              existe("d0", et(appartient(var("d0"), var("X")),
                             egal(_Z, couple(var("d0"), var("d0"))))))))

# Déf. du graphe composé G'∘G :
#   (∀G')(∀G)(∀w)(w∈G'∘G ⇔ (∃p)(∃r)(w=(p,r) et (∃y)((p,y)∈G et (y,r)∈G')))
AXIOME_COMPOSEE = pourtout("Gp", pourtout("G", pourtout("w",
        equiv(appartient(var("w"), composee(var("Gp"), var("G"))),
              existe("p", existe("r", et(egal(var("w"), couple(_P, _R)),
                  existe("y", et(appartient(couple(_P, _Y), var("G")),
                                 appartient(couple(_Y, _R), var("Gp")))))))))))


# Déf. de la restriction f|X (E.II.45 ; existence = graphe de « x∈X et y=f(x) »
# par S8, unicité = A1, comme produit/réciproque) :
#   (∀F)(∀X)(∀z)(z ∈ f|X ⇔ (∃p)(∃q)(z=(p,q) et p∈X et (p,q)∈F))
# Liants existentiels p,q (≠ x,y) pour rester compatible avec les projections.
AXIOME_RESTRICTION = pourtout("F", pourtout("X", pourtout("z",
        equiv(appartient(_Z, restriction(var("F"), var("X"))),
              existe("p", existe("q",
                  et(et(egal(_Z, couple(_P, _Q)), appartient(_P, var("X"))),
                     appartient(couple(_P, _Q), var("F")))))))))


# Déf. du graphe d'une fonction par un terme (Critère C54, E.II.46 ; existence =
# graphe de « x∈A et y=T » par S8 — l'assemblage A×B ne contient ni x ni y —,
# unicité = A1, comme produit/réciproque/restriction) :
#   (∀w)(w ∈ F  ⇔  (∃x)(∃y)(w=(x,y) et (x∈A et y=T)))   où F = graphe_terme(A,T).
# A et T sont des PARAMÈTRES : l'axiome est instancié à A, T concrets via la
# theorie dédiée renvoyée par `theorie_graphe_terme`. Les liants x, y sont ceux
# du terme T et du couple ; ils sont liés DANS le corps (donc l'assemblage de F,
# argument τx(T), ne contient ni x ni y — fidèle à C54).
def axiome_graphe_terme(a, t, x="x", y="y", w="w"):
    """Formule caractérisant w∈F pour F = graphe_terme(A,T)  (instance, C54)."""
    vw, vx, vy = var(w), var(x), var(y)
    corps = existe(x, existe(y,
        et(et(egal(vw, couple(vx, vy)), appartient(vx, a)), egal(vy, t))))
    return pourtout(w, equiv(appartient(vw, graphe_terme(a, t, x)), corps))


def theorie_graphe_terme(a, t, x="x", y="y", w="w"):
    """Théorie ne contenant que l'instance C54 de l'axiome du graphe de x↦T."""
    return N.Theorie("Graphe-terme", [axiome_graphe_terme(a, t, x, y, w)])


# Déf. de l'ensemble diagonal de Cantor (E.III.3, argument diagonal) :
#   D_{X,F} := { z ∈ X | ¬(z ∈ F(z)) } = { z | z∈X et ¬(z∈F(z)) }.
# Existence par S8 (sélection dans X), unicité par A1, comme la différence
# E∖X = {z | z∈E et ¬(z∈X)} ; D_{X,F} en est l'analogue où le test « ¬(z∈Y) »
# (Y fixe) est remplacé par « ¬(z∈F(z)) » (la coupe à l'argument courant).
# X et F sont des PARAMÈTRES ; le liant interne est « z ».
def diagonale_cantor(x, f):
    """D_{X,F} := { z∈X | ¬(z ∈ F(z)) }  (ensemble diagonal de Cantor, E.III.3)."""
    return app("diag_cantor", x, f)


def axiome_diagonale_cantor(x, f, z="z"):
    """⊢-schéma : (∀z)(z ∈ D_{X,F} ⇔ (z∈X et ¬(z∈F(z))))  (instance, S8+A1)."""
    vz = var(z)
    return pourtout(z, equiv(appartient(vz, diagonale_cantor(x, f)),
                             et(appartient(vz, x), non(appartient(vz, valeur(f, vz))))))


def theorie_diagonale_cantor(x, f, z="z"):
    """Théorie ne contenant que l'instance de l'axiome de D_{X,F}."""
    return N.Theorie("Diagonale-Cantor", [axiome_diagonale_cantor(x, f, z)])


# ── §II.5.2 — Ensemble des applications 𝓕(E;F) et exposant F^E ────────────────
# Bourbaki (E.II.5.2, Déf. 4 ; E.II.13, Déf. 6 « fonction »).  Une APPLICATION de
# E dans F est un triple f = ((G, E), F) où G est un GRAPHE FONCTIONNEL de domaine
# E inclus dans E×F.  L'ensemble de ces graphes fonctionnels est F^E (« exposant »,
# E.II.5.2), et l'ensemble des triples est 𝓕(E;F) (« applications »).
#
# AXIOMES DE DÉFINITION (membership, S8 + A1) — légitimes : ce sont les définitions
# de Bourbaki (caractérisations d'appartenance), PAS des théorèmes (Propositions).
# Existence des deux ensembles : sélection S8 dans P(E×F) (pour F^E) puis dans
# P(P(P(E×F)) × …) (pour 𝓕), unicité par A1 — exactement comme AXIOME_PRODUIT_FAM,
# dont `axiome_exposant` est le FRÈRE littéral : « ⊂ le produit ∧ fonctionnel ∧
# dom = source », dans cet ordre, avec le conjoint d'inclusion en TÊTE.  (C'est ici
# que le défaut du produit d'une famille s'était vu : le frère avait gardé son
# « G ⊂ E×F », l'autre l'avait perdu — rétabli le 26 juil. 2026.)  Paramétrés par
# E, F, instanciés via les théories dédiées `theorie_exposant` / `theorie_applications`.

# Déf. de F^E = { G ∈ P(E×F) | G fonctionnel ∧ dom G = E }  (E.II.5.2) :
#   (∀G)( G ∈ F^E  ⇔  ( G ⊂ E×F  ∧  G fonctionnel  ∧  dom G = E ) )
# Liant universel externe « G ».  E, F sont des PARAMÈTRES.
def axiome_exposant(e, f, g="G"):
    """⊢-schéma : (∀G)(G ∈ F^E ⇔ (G ⊂ E×F et G fonctionnel et dom G = E))  (Déf., S8+A1).

    Caractérise l'appartenance au support F^E des GRAPHES FONCTIONNELS de E dans F
    (E.II.5.2).  E, F paramètres ; instancié via theorie_exposant."""
    vE, vF, vg = _terme_var(e), _terme_var(f), var(g)
    corps = et(et(inclus(vg, produit(vE, vF)), est_fonctionnel(vg)),
               egal(dom(vg), vE))
    return pourtout(g, equiv(appartient(vg, exposant(vE, vF)), corps))


def theorie_exposant(e, f, g="G"):
    """Théorie ne contenant que l'instance de l'axiome de F^E (E.II.5.2)."""
    return N.Theorie("Exposant", [axiome_exposant(e, f, g)])


# Déf. de 𝓕(E;F) = { ((G,E),F) | G ∈ F^E }  (E.II.5.2, Déf. 4 ; une application est
# le triple (graphe fonctionnel, source, but)) :
#   (∀t)( t ∈ 𝓕(E;F)  ⇔  (∃G)( t = ((G,E),F)  ∧  G ∈ F^E ) )
# Liant universel externe « t », liant existentiel interne « G ».  E, F paramètres.
def axiome_applications(e, f, t="t", g="G"):
    """⊢-schéma : (∀t)(t ∈ 𝓕(E;F) ⇔ (∃G)(t = ((G,E),F) et G ∈ F^E))  (Déf. 4, S8+A1).

    Caractérise l'appartenance à l'ensemble 𝓕(E;F) des APPLICATIONS de E dans F :
    une application est le triple ((G,E),F) d'un graphe fonctionnel G ∈ F^E avec sa
    source E et son but F (E.II.5.2).  E, F paramètres ; via theorie_applications."""
    vE, vF, vt, vg = _terme_var(e), _terme_var(f), var(t), var(g)
    triple = couple(couple(vg, vE), vF)                 # ((G, E), F)
    corps = existe(g, et(egal(vt, triple), appartient(vg, exposant(vE, vF))))
    return pourtout(t, equiv(appartient(vt, applications(vE, vF)), corps))


def theorie_applications(e, f, t="t", g="G"):
    """Théorie ne contenant que l'instance de l'axiome de 𝓕(E;F) (E.II.5.2, Déf. 4)."""
    return N.Theorie("Applications", [axiome_applications(e, f, t, g)])


def application_vide(f):
    """ω_F := ((∅, ∅), F)  (l'application vide ∅→F : graphe vide, source ∅, but F)."""
    return couple(couple(VIDE, VIDE), _terme_var(f))


# Déf. de P(X) (axiome A3, E.II.5.1 ; existence = axiome A3, unicité = A1) :
#   (∀X)(∀Y)(Y ∈ P(X) ⇔ Y ⊂ X)
# Le liant interne de ⊂ est « z » (cohérent avec inclus/A1).
AXIOME_PARTIES = pourtout("X", pourtout("Y",
        equiv(appartient(_GY, parties(_GX)), inclus(_GY, _GX))))


# Déf. du produit ∏_{ι∈I} X_ι (E.II.5.3, Déf. 1 ; existence par S8 = sélection
# dans P(I×A) avec A=⋃X_ι, unicité par A1, comme produit/image/restriction) :
#   (∀f)(∀I)(∀F)(F ∈ ∏  ⇔  ( F ⊂ I×⋃X_ι ∧ F fonctionnel ∧ pr₁F = I
#                            ∧ (∀i)(i∈I ⇒ F(i)∈X_i) ))
# Liant universel externe « F », liant interne « i » (index).  X_i = valeur_famille(f, i).
#
# ⚠️ NE PAS RETIRER le conjoint de TÊTE « F ⊂ I × ⋃_{ι∈I} X_ι ».  Il a été ABSENT
# jusqu'au 26 juil. 2026, et son absence rendait le corpus INFIDÈLE au livre : les
# trois autres conjoints ne contraignent QUE les éléments de F qui sont des couples
# (est_fonctionnel n'est que l'univocité), si bien que {∅} — qui ne contient aucun
# couple — était fonctionnel, de domaine ∅, et donc élément de ∏_{ι∈∅} X_ι.  Le
# corpus démontrait alors ⊢ ¬( ∏_{ι∈∅} X_ι = {∅} ) alors que Bourbaki écrit, MÊME
# page : « Si I = ∅, l'ensemble ∏_{ι∈I} X_ι ne possède qu'un seul élément, savoir
# l'ensemble vide » (E II.32).  Défaut de FIDÉLITÉ, pas de soundness — le noyau ne
# la garantit pas.  Bourbaki pose le conjoint dès le PRÉAMBULE de la Déf. 1 (« F est
# un élément de 𝔓(I × A) », A = ⋃_{ι∈I} X_ι) ; c'est aussi ce que l'axiome FRÈRE
# `axiome_exposant` (F^E, E II.5.2) avait, lui, correctement gardé (« G ⊂ E×F »).
# Les deux sont désormais littéralement homomorphes.  Précédent exact dans ce dépôt :
# la réparation de AXIOME_INTER_FAM, même journée (voir plus bas).
# C'est un REMPLACEMENT, pas un ajout : theorie_ensembles() vaut 22 avant et après.
# Les trois briques du conjoint (⊂ ⟹ graphe ; le PIVOT graphe+fonctionnel+dom+valeurs
# ⟹ ⊂ ; stabilité par adjonction d'un couple) sont dans
# ii_5_produit_famille/ii_5_definitions/ensembles_produit_graphe_briques.py.
# PLACEMENT EN TÊTE (mesuré) : 18 théorèmes à ré-adresser contre 33 en queue — en
# tête, les accesseurs « dom F = I » (chemin g,d) et « (∀i)… » (chemin d) sont
# LITTÉRALEMENT inchangés ; seul « est_fonctionnel » descend d'un cran.
_FF = var("F")
def _corps_produit(ff, f, i):
    vi = var("i")
    return et(et(et(inclus(ff, produit(i, reunion_famille(f, i))),
                    est_fonctionnel(ff)),
                 egal(dom(ff), i)),
              pourtout("i", impl(appartient(vi, i),
                                 appartient(valeur(ff, vi), valeur_famille(f, vi)))))
AXIOME_PRODUIT_FAM = pourtout("f", pourtout("I", pourtout("F",
        equiv(appartient(_FF, produit_famille(var("f"), var("I"))),
              _corps_produit(_FF, var("f"), var("I"))))))


# Déf. de la réunion d'une famille ⋃_{ι∈I} X_ι (E.II.4.1, Déf. 1 ; existence par
# S8 = sélection-réunion, unicité par A1, comme produit/image) :
#   (∀f)(∀I)(∀z)(z ∈ ⋃_{ι∈I} X_ι ⇔ (∃i)(i∈I et z∈X_i))
# Liant existentiel « i » (index), liant universel externe « z » (élément, cohérent
# avec inclus/A1). X_i = valeur_famille(f, var("i")).
_F, _I, _IDX = var("f"), var("I"), var("i")
AXIOME_REUNION_FAM = pourtout("f", pourtout("I", pourtout("z",
        equiv(appartient(_Z, reunion_famille(_F, _I)),
              existe("i", et(appartient(_IDX, _I),
                             appartient(_Z, valeur_famille(_F, _IDX))))))))

# Déf. de l'intersection d'une famille ⋂_{ι∈I} X_ι (E.II.4.1, Déf. 2, E II.22 ; existence par
# S8 = SÉLECTION DANS LA RÉUNION, unicité par A1, comme quotient/produit/image) :
#   (∀f)(∀I)(∀z)(z ∈ ⋂_{ι∈I} X_ι ⇔ ( z ∈ ⋃_{ι∈I} X_ι  et  (∀i)(i∈I ⇒ z∈X_i) ))
#
# ⚠️ NE PAS RETIRER le membre « z ∈ ⋃ ». Cet axiome a été posé jusqu'au 26 juil. 2026 sous sa
# forme inconditionnelle (le seul corps « (∀i)(i∈I ⇒ z∈X_i) »), et sous cette forme il rendait
# `theorie_ensembles()` CONTRADICTOIRE : pour I = ∅ le corps est vide-vrai pour tout z, donc
# ⋂_{ι∈∅} X_ι contenait TOUT objet — un ensemble universel, contredisant `pas_ensemble_universel`
# (Russell, E II.6 Remarque). Preuve machine conservée : outils_ia/audit/preuve_incoherence_inter_vide.py.
# Bourbaki écrit l'hypothèse dans sa Déf. 2 — « une famille d'ensembles dont l'ensemble d'indices I
# n'est pas vide » — et annonce la panne en petits caractères : « Si I = ∅, la relation […] n'est
# pas collectivisante en x […] car ce serait l'ensemble de tous les objets ». La faute venait de
# ce que la notion avait été calée sur le RÉSUMÉ (E.R.19), qui traite l'intersection dans le monde
# des familles de PARTIES de E (Déf. 3, où ⋂_{ι∈∅} = E) : on avait croisé la formule de la Déf. 2
# avec la totalité de la Déf. 3.
# La réunion fournit la borne que Bourbaki obtient par « I ≠ ∅ » (Déf. 2) ou « ⊂ E » (Déf. 3) ;
# on gagne ⋂_{ι∈∅} X_ι = ∅ et l'hypothèse ne subsiste que là où le livre l'exige vraiment.
# Route Grimm B5 (@source sources/grimm_gaia/RR-6999-v7.pdf p.35 §2.7 : « Taking for E the union
# of the family solves the problem »).  Théorèmes-pont, dont l'ANCIEN énoncé récupéré sous
# (∃i)(i∈I) : ii_4_reunion_intersection_famille/ii_4_intersection_fondation/.
AXIOME_INTER_FAM = pourtout("f", pourtout("I", pourtout("z",
        equiv(appartient(_Z, inter_famille(_F, _I)),
              et(appartient(_Z, reunion_famille(_F, _I)),
                 pourtout("i", impl(appartient(_IDX, _I),
                                    appartient(_Z, valeur_famille(_F, _IDX)))))))))


# Déf. de la famille des complémentaires (∁_E X_ι)_{ι∈I} = ι ↦ E∖X_ι (C54, famille
# définie par un terme ; légitime — c'est la fonction ι ↦ E∖X_ι). Caractérisée par
# la valeur de son ι-ème terme :
#   (∀E)(∀f)(∀i)( (E∖X·)_i = E∖X_i )   où X_i = valeur_famille(f, i).
AXIOME_COMPL_FAM = pourtout("E", pourtout("f", pourtout("i",
        egal(valeur_famille(complement_famille(var("E"), _F), _IDX),
             difference(var("E"), valeur_famille(_F, _IDX))))))


# Déf. de l'ensemble quotient E/R (E.II.6.2 ; existence par S8 = sélection dans
# P(E), unicité par A1, comme produit/image) :
#   (∀G)(∀E)(∀C)(C ∈ E/R  ⇔  (C ∈ P(E) et (∃x)(x∈E et C = Cl_R(x))))
# Liant universel externe « C », liant existentiel interne « x ».
_GG, _EE, _CC = var("G"), var("E"), var("C")
AXIOME_QUOTIENT = pourtout("G", pourtout("E", pourtout("C",
        equiv(appartient(_CC, quotient(var("G"), _EE)),
              et(appartient(_CC, parties(_EE)),
                 existe("x", et(appartient(_X, _EE),
                                egal(_CC, classe(var("G"), _X)))))))))


# Déf. du graphe de l'application canonique p : E → E/R (E.II.6.2) :
#   (∀G)(∀E)(∀w)(w ∈ p  ⇔  (∃x)(x∈E et w = (x, Cl_R(x))))
AXIOME_APPCANON = pourtout("G", pourtout("E", pourtout("w",
        equiv(appartient(var("w"), application_canonique(var("G"), _EE)),
              existe("x", et(appartient(_X, _EE),
                             egal(var("w"), couple(_X, classe(var("G"), _X)))))))))


# Déf. de S_x = ]←, x[ : (∀G)(∀E)(∀x)(∀y)(y ∈ seg_ext(G,E,x) ⇔ ((y∈E et (y,x)∈G) et y≠x))
#   (E.III.2.1)  y<x abrégé par « (y≤x) et y≠x », l'ordre ≤ étant PORTÉ PAR SON
#   GRAPHE G : y≤x s'écrit (y,x)∈G.  Liant interne y, externes G, E, x — TOUS
#   quantifiés : la formule est CLOSE.  Légitimé par S8 (sélection dans E) + A1.
def axiome_segment_extremite(G="G", e="E", x="x", y="y"):
    """Axiome CLOS caractérisant seg_ext(G,E,x) = { y∈E | (y,x)∈G et y≠x } (E.III.2.1).

        (∀G)(∀E)(∀x)(∀y)( y ∈ seg_ext(G,E,x) ⇔ ((y∈E et (y,x)∈G) et y≠x) )

    ⚠️ MIGRÉ (2026-07-31) — la formule N'A PLUS DE PARAMÈTRE MATHÉMATIQUE.  Avant,
    elle était paramétrée par une relation Python R et laissait le graphe LIBRE
    dans la conclusion alors qu'il était ABSENT du terme `seg_ext` : deux ordres
    distincts fournissaient deux axiomes contradictoires sur le MÊME terme.  Ici
    G est quantifié universellement en tête, donc `libres(axiome) == []` : plus
    aucune variable libre ⇒ plus de CONSTANTE de théorie ⇒ le défaut C27
    (généralisation sur une constante) ne peut plus naître de ce site.
    Les arguments restants ne sont que des NOMS DE LIANTS : deux clôtures à liants
    différents sont α-égales (`alpha_egal` True — mesuré ; `==` les distingue
    encore, le noyau ne quotiente pas par α).  Il n'y a donc qu'UNE classe, et
    aucune paire d'axiomes incompatibles ne peut plus naître d'ici."""
    vG, vE, vx, vy = var(G), var(e), var(x), var(y)
    return pourtout(G, pourtout(e, pourtout(x, pourtout(y,
        equiv(appartient(vy, segment_extremite(vG, vE, vx)),
              et(et(appartient(vy, vE), appartient(couple(vy, vx), vG)),
                 non(egal(vy, vx))))))))


def theorie_segment_extremite():
    """Théorie ne contenant que l'axiome CLOS caractérisant seg_ext (E.III.2.1).

    Plus de paramètre : le nom « Segment-extremite » désigne désormais UNE seule
    théorie, contenant UN seul axiome clos — alors qu'auparavant le même nom
    recouvrait autant de théories (deux à deux incompatibles) que de relations R.
    Elle reste DÉDIÉE : `theorie_ensembles()` demeure à 22 axiomes."""
    return N.Theorie("Segment-extremite", [axiome_segment_extremite()])


def theorie_ensembles():
    return N.Theorie("Ensembles",
                     [A1, A2, AXIOME_PAIRE, AXIOME_VIDE, AXIOME_REUNION, AXIOME_INTER,
                      AXIOME_DIFF,
                      AXIOME_PRODUIT, AXIOME_DOM, AXIOME_IMG, AXIOME_IMAGE, AXIOME_RECIP,
                      AXIOME_COMPOSEE, AXIOME_RESTRICTION, AXIOME_DIAGONALE,
                      AXIOME_REUNION_FAM, AXIOME_INTER_FAM, AXIOME_COMPL_FAM,
                      AXIOME_PARTIES, AXIOME_PRODUIT_FAM,
                      AXIOME_QUOTIENT, AXIOME_APPCANON])


__all__ = ["paire", "singleton", "VIDE", "reunion", "intersection", "difference",
           "couple", "pr1", "pr2", "est_un_couple", "produit",
           "est_un_graphe", "dom", "img", "image", "reciproque", "composee",
           "est_fonctionnel", "valeur", "est_injective", "est_surjective", "est_bijective",
           "est_retraction", "est_section", "est_inverse_gauche", "est_inverse_droite",
           "injective_dans",
           "restriction", "est_constante", "est_invariant", "coincident", "prolonge",
           "graphe_terme", "fonction_terme", "axiome_graphe_terme", "theorie_graphe_terme",
           "diagonale_cantor", "axiome_diagonale_cantor", "theorie_diagonale_cantor",
           "axiome_exposant", "theorie_exposant",
           "axiome_applications", "theorie_applications", "application_vide",
           "valeur_famille", "reunion_famille", "inter_famille", "est_recouvrement",
           "plus_fin", "sont_disjoints", "famille_disjointe", "est_partition", "somme_famille",
           "parties", "exposant", "applications", "produit_famille", "projection_indice",
           "est_symetrique", "est_transitive", "est_relation_equivalence",
           "est_reflexive_dans", "est_relation_equivalence_dans", "rel_graphe", "classe",
           "quotient", "application_canonique", "est_compatible", "relation_quotient",
           "est_saturee", "sature", "est_compatible_application", "relation_associee_fonction",
           "plus_fine", "relation_produit", "classe_objets",
           "ordre_transitif", "ordre_antisymetrique", "ordre_reflexif_implicite",
           "est_relation_ordre", "ordre_oppose", "est_relation_preordre",
           "est_reflexive_dans_ordre", "est_relation_ordre_dans", "relation_stricte",
           "ordre_induit", "est_element_minimal", "est_element_maximal",
           "est_plus_petit_element", "est_plus_grand_element", "majore", "minore",
           "est_cofinale", "est_coinitiale", "est_filtrant_droite", "est_filtrant_gauche",
           "sont_comparables", "est_totalement_ordonne",
           "intervalle_ferme", "intervalle_ouvert",
           "intervalle_illimite_gauche_ferme", "intervalle_illimite_droite_ferme",
           "intervalle_entiers",
           "est_bien_ordonne", "est_relation_bon_ordre", "est_segment",
           "segment_extremite", "est_majorant_strict", "est_inductif",
           "axiome_segment_extremite", "theorie_segment_extremite",
           "AXIOME_QUOTIENT", "AXIOME_APPCANON",
           "AXIOME_PARTIES", "AXIOME_PRODUIT_FAM",
           "complement_famille",
           "AXIOME_REUNION_FAM", "AXIOME_INTER_FAM", "AXIOME_COMPL_FAM",
           "A1", "A2", "AXIOME_PAIRE", "AXIOME_VIDE", "AXIOME_REUNION",
           "AXIOME_INTER", "AXIOME_DIFF", "AXIOME_PRODUIT", "AXIOME_DOM", "AXIOME_IMG",
           "AXIOME_IMAGE", "AXIOME_RECIP", "AXIOME_COMPOSEE", "AXIOME_RESTRICTION",
           "diagonale", "AXIOME_DIAGONALE",
           "theorie_ensembles"]
