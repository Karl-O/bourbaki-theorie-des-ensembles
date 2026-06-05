"""Chapitre II (abrégé) — axiomes A1, A2 + termes définis {a,b}, {a}, ∅.

A1, A2 : axiomes verbatim. Les TERMES définis (paire, singleton, vide) sont
introduits avec leur axiome de caractérisation (mécanisme « constante
introductrice » de Bourbaki), légitime car existence + unicité sont prouvées
(cf. ensembles_theoremes : existence_paire / unicite_paire).
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, tau, egal, inclus, ou, et, impl, non, equiv,
                     pourtout, existe, coll, appartient)
from bourbaki.logique import noyau_abrege as N

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


def couple(t, u):
    """(t, u) := {{t}, {t, u}}  (couple de Bourbaki, E.II.30, Déf.)."""
    return paire(singleton(t), paire(t, u))


def pr1(z, x="x", y="y"):
    """pr₁z := τx((∃y)(z = (x, y)))  (première coordonnée, E.II.31)."""
    vx, vy = var(x), var(y)
    return tau(x, existe(y, egal(z, couple(vx, vy))))


def pr2(z, x="x", y="y"):
    """pr₂z := τy((∃x)(z = (x, y)))  (seconde coordonnée, E.II.31)."""
    vx, vy = var(x), var(y)
    return tau(y, existe(x, egal(z, couple(vx, vy))))


def est_un_couple(z, x="x", y="y"):
    """« z est un couple » := (∃x)(∃y)(z = (x, y))  (E.II.31)."""
    vx, vy = var(x), var(y)
    return existe(x, existe(y, egal(z, couple(vx, vy))))


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


def image(g, x):
    """G⟨X⟩ := {y | (∃x)(x∈X et (x,y)∈G)}  (image directe de X par G, E.II.39, Déf. 3)."""
    return app("image", g, x)


def reciproque(g):
    """G⁻¹ := {z | (∃x)(∃y)(z=(x,y) et (y,x)∈G)}  (graphe réciproque, E.II.41, Déf. 5)."""
    return app("reciproque", g)


def composee(gp, g):
    """G'∘G := graphe (en x,z) de (∃y)((x,y)∈G et (y,z)∈G')  (E.II.42, Déf. 6)."""
    return app("composee", gp, g)


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
    """f(x) := τb((x,b)∈F)  (valeur de la fonction F en x, E.II.43).

    Le liant b vaut « y » par défaut (rétro-compatible avec tout le projet et avec
    valeur_caracterisation/C46 qui apparie la coordonnée var("y")).  On peut le
    paramétrer par une lettre fraîche lorsqu'une valeur f(x) figure DANS un terme
    qui sera lui-même quantifié sur « y » (ex. le graphe produit
    (F(pr₁k), G(pr₂k)) plongé dans graphe_terme, où le ∃y du domaine/image et le
    τy de cette valeur entreraient en collision de capture) — levée du « verrou
    liant valeur »."""
    return tau(b, appartient(couple(x, var(b)), f))


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


def est_invariant(t, f):
    """« t invariant par f » := f(t) = t  (élément invariant, E.II.45, Déf.)."""
    return egal(valeur(f, t), t)


def coincident(f, g, e, x="x"):
    """« f et g coïncident dans E » := E⊂dom F et E⊂dom G et (∀x)(x∈E ⇒ f(x)=g(x))
    (coïncidence de deux fonctions dans un ensemble, E.II.45, Déf.)."""
    vx = var(x)
    return et(et(inclus(e, dom(f)), inclus(e, dom(g))),
              pourtout(x, impl(appartient(vx, e), egal(valeur(f, vx), valeur(g, vx)))))


def prolonge(g, f):
    """« g prolonge f » (au sens des graphes) := F⊂G  (prolongement, E.II.45, Déf.).

    Bourbaki : F⊂G ⇔ (A⊂C et f coïncide avec g dans A). Avec en outre B⊂D, g est
    un prolongement de f. La sous-famille = inclusion des graphes fonctionnels."""
    return inclus(f, g)


# ── §II.4 — Familles d'ensembles : réunion et intersection ────────────────────
def valeur_famille(f, i):
    """X_ι := la valeur en ι de la famille (X_ι) = la fonction f  (E.II.4.1).

    Une famille (X_ι)_{ι∈I} EST une fonction ι ↦ X_ι (graphe fonctionnel, §3.4).
    On note ici X_ι par le terme app('fam', f, i)."""
    return app("fam", f, i)


def reunion_famille(f, i):
    """⋃_{ι∈I} X_ι := { x | (∃ι)(ι ∈ I et x ∈ X_ι) }  (E.II.4.1, Déf. 1)."""
    return app("reunion_fam", f, i)


def inter_famille(f, i):
    """⋂_{ι∈I} X_ι := { x | (∀ι)((ι ∈ I) ⇒ (x ∈ X_ι)) }  (E.II.4.1, Déf. 2 ; I ≠ ∅)."""
    return app("inter_fam", f, i)


def complement_famille(e, f):
    """(∁_E X_ι)_{ι∈I} := la famille ι ↦ E∖X_ι  (famille des complémentaires).

    Famille définie par le terme ι ↦ E∖X_ι (C54) : son ι-ème terme est E∖X_ι.
    Sert à exprimer les seconds membres des lois de De Morgan des familles
    (E.II.4, Prop. 5) : ⋂_{ι∈I}(E∖X_ι) = inter_famille(complement_famille(E,f), I)."""
    return app("compl_fam", e, f)


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


def famille_disjointe(f, i):
    """« les X_ι sont (deux à deux) disjoints »
       := (∀ι)(∀κ)((ι∈I et κ∈I et ι≠κ) ⇒ X_ι ∩ X_κ = ∅)  (E.II.4.6, Déf. 6)."""
    vi, vk = var("i"), var("k")
    return pourtout("i", pourtout("k",
        impl(et(et(appartient(vi, i), appartient(vk, i)), non(egal(vi, vk))),
             sont_disjoints(valeur_famille(f, vi), valeur_famille(f, vk)))))


def est_partition(f, i, e):
    """« (X_ι)_{ι∈I} est une partition de E » := recouvrement de E, famille disjointe,
       et parties non vides  (E.II.4.7, Déf. 7)."""
    vi = var("i")
    return et(et(est_recouvrement(f, i, e), famille_disjointe(f, i)),
              pourtout("i", impl(appartient(vi, i), non(egal(valeur_famille(f, vi), VIDE)))))


def somme_famille(f, i):
    """∑_{ι∈I} X_ι := ⋃_{ι∈I} (X_ι × {ι})  (E.II.4.8, Déf. 8)."""
    return app("somme_fam", f, i)


# ── §II.5 — Ensemble des parties, applications, produit d'une famille ─────────
def parties(x):
    """P(X) := {Y | Y ⊂ X}  (ensemble des parties de X, E.II.5.1, axiome A3)."""
    return app("parties", x)


def exposant(e, f):
    """F^E := {G ∈ P(E×F) | G fonctionnel ∧ pr₁G = E}  (graphes des applications, E.II.5.2)."""
    return app("exposant", e, f)


def applications(e, f):
    """𝓕(E;F) := {(G, E, F) | G ∈ F^E}  (ensemble des applications de E dans F, E.II.5.2)."""
    return app("applications", e, f)


def produit_famille(f, i):
    """∏_{ι∈I} X_ι := { F | F graphe fonctionnel, dom F = I, (∀ι)(ι∈I ⇒ F(ι)∈X_ι) }
       (produit d'une famille d'ensembles, E.II.5.3, Déf. 1)."""
    return app("produit_fam", f, i)


def projection_indice(f, i):
    """pr_ι(F) := F(ι) = valeur(F, ι)  (fonction coordonnée d'indice ι, E.II.5.3)."""
    return valeur(f, i)


def est_injective(f):
    """« f injective » (forme littérale, NON gardée) := (∀u)(∀u')((f(u)=f(u'))⇒u=u').

    ⚠ Forme de la section « Implémentation » de Bourbaki §II.49, valable pour une
    APPLICATION (totale). Pour la fidélité « deux éléments DE A » et pour les
    preuves (un graphe vaut τy(faux) hors de son domaine), on utilise la forme
    GARDÉE `injective_dans(f, A)` — c'est elle qui entre dans est_bijective."""
    u, up = var("u"), var("up")
    return pourtout("u", pourtout("up", impl(egal(valeur(f, u), valeur(f, up)), egal(u, up))))


def est_surjective(f, a, b):
    """« f surjective de A sur B » := f⟨A⟩ = B  (E.II.49, Déf. 10)."""
    return egal(image(f, a), b)


def est_bijective(f, a, b):
    """« f bijective de A sur B » := injective SUR A et surjective  (E.II.49, Déf. 10).

    Injectivité GARDÉE par A (`injective_dans`), fidèle au « deux éléments de A »
    de Bourbaki et compatible avec le codage par graphe (valeur indéterminée hors A)."""
    return et(injective_dans(f, a), est_surjective(f, a, b))


# ── §II.3.8 — Rétractions et sections (Déf. 11) ───────────────────────────────
def est_retraction(r, f, a, x="x"):
    """« r est une rétraction associée à f » (f : A → B injective, r : B → A) :=
       (∀x)(x ∈ A ⇒ r(f(x)) = x)   c.-à-d.  r ∘ f = Id_A   (E.II.48, Déf. 11).

    Encodage matriciel de l'implémentation (§3.8) : la composée r∘f restreinte aux
    valeurs vaut l'identité sur A. On dit aussi « inverse à gauche » de f.
    r(f(x)) = valeur(R, valeur(F, x))."""
    vx = var(x)
    return pourtout(x, impl(appartient(vx, a),
                           egal(valeur(r, valeur(f, vx)), vx)))


def est_section(s, f, b, y="y"):
    """« s est une section associée à f » (f : A → B surjective, s : B → A) :=
       (∀y)(y ∈ B ⇒ f(s(y)) = y)   c.-à-d.  f ∘ s = Id_B   (E.II.48, Déf. 11).

    Encodage matriciel (§3.8). On dit aussi « inverse à droite » de f.
    f(s(y)) = valeur(F, valeur(S, y))."""
    vy = var(y)
    return pourtout(y, impl(appartient(vy, b),
                           egal(valeur(f, valeur(s, vy)), vy)))


def est_inverse_gauche(r, f, a, x="x"):
    """Synonyme de rétraction : « r est un inverse à gauche de f »  (E.II.48, Déf. 11)."""
    return est_retraction(r, f, a, x)


def est_inverse_droite(s, f, b, y="y"):
    """Synonyme de section : « s est un inverse à droite de f »  (E.II.48, Déf. 11)."""
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
def est_symetrique(R, x="x", y="y"):
    """« R symétrique (par rapport à x, y) » := (∀x)(∀y)(R{x,y} ⇒ R{y,x})  (E.II.6.1).

    Bourbaki : R est symétrique si R{x,y} ⇔ R{y,x} ; le sens ⇐ étant l'instance
    obtenue en échangeant x et y, on encode la clôture universelle de R{x,y}⇒R{y,x}."""
    vx, vy = var(x), var(y)
    return pourtout(x, pourtout(y, impl(R(vx, vy), R(vy, vx))))


def est_transitive(R, x="x", y="y", z="z"):
    """« R transitive (par rapport à x, y) » := (∀x)(∀y)(∀z)((R{x,y} et R{y,z}) ⇒ R{x,z})
    (E.II.6.1 ; z ne figure pas dans R)."""
    vx, vy, vz = var(x), var(y), var(z)
    return pourtout(x, pourtout(y, pourtout(z,
        impl(et(R(vx, vy), R(vy, vz)), R(vx, vz)))))


def est_relation_equivalence(R, x="x", y="y", z="z"):
    """« R{x,y} est une relation d'équivalence » := R symétrique ET transitive  (E.II.6.1)."""
    return et(est_symetrique(R, x, y), est_transitive(R, x, y, z))


def est_reflexive_dans(R, e, x="x"):
    """« R réflexive dans E » := (∀x)(R{x,x} ⇔ x∈E)  (E.II.6.1 ; x ne figure pas dans E)."""
    vx = var(x)
    return pourtout(x, equiv(R(vx, vx), appartient(vx, e)))


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


def classe(g, x):
    """Cl_R(x) := G⟨{x}⟩ = {y∈E | R{x,y}}  (classe d'équivalence de x, E.II.6.2).

    Codée par l'image directe du singleton {x} par le graphe G (Bourbaki E.II.6.2)."""
    return image(g, singleton(_terme_var(x)))


def quotient(g, e):
    """E/R := { C ∈ P(E) | (∃x)(x∈E et C = Cl_R(x)) }  (ensemble quotient, E.II.6.2)."""
    return app("quotient", g, e)


def application_canonique(g, e):
    """p : E → E/R,  p(x) := Cl_R(x)  (application canonique, E.II.6.2).

    Codée par son graphe { (x, Cl_R(x)) | x∈E }."""
    return app("appcanon", g, e)


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


def est_saturee(a, g, e, x="x"):
    """« A saturée pour R » := la relation x∈A est compatible (par rapport à x) avec R
    (E.II.6.4) ; équivaut à (∀x)(x∈A ⇒ Cl_R(x) ⊂ A)."""
    return est_compatible(lambda t: appartient(t, a), rel_graphe(g), x)


def sature(a, p):
    """Ã := p⁻¹⟨p⟨A⟩⟩  (saturé de A pour R, plus petite partie saturée contenant A, E.II.6.4)."""
    return image(reciproque(p), image(p, a))


def est_compatible_application(f, R, x="x", xp="xp"):
    """« f compatible avec R » := (∀x)(∀x')(R{x,x'} ⇒ f(x)=f(x'))  (E.II.6.5).

    f constante sur toute classe d'équivalence suivant R."""
    vx, vxp = var(x), var(xp)
    return pourtout(x, pourtout(xp, impl(R(vx, vxp), egal(valeur(f, vx), valeur(f, vxp)))))


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


def est_relation_ordre(R, x="x", y="y", z="z"):
    """« R{x,y} est une relation d'ordre (entre x et y) » := transitive ET antisymétrique
    ET R{x,y}⇒(R{x,x} et R{y,y})  (E.III.1.1, Définition)."""
    return et(et(ordre_transitif(R, x, y, z), ordre_antisymetrique(R, x, y)),
              ordre_reflexif_implicite(R, x, y))


def ordre_oppose(R):
    """R^op{x,y} := R{y,x}  (relation d'ordre opposée, E.III.1.1, Exemple 3)."""
    return lambda a, b: R(b, a)


def est_relation_preordre(R, x="x", y="y", z="z"):
    """« R{x,y} est une relation de préordre » := transitive ET R{x,y}⇒(R{x,x} et R{y,y})
    (sans l'antisymétrie ; E.III.1.2, Définition)."""
    return et(ordre_transitif(R, x, y, z), ordre_reflexif_implicite(R, x, y))


def est_reflexive_dans_ordre(R, e, x="x"):
    """« R réflexive dans E » := (∀x)(R{x,x} ⇔ x∈E)  (E.III.1.1 ; x ne figure pas dans E)."""
    vx = var(x)
    return pourtout(x, equiv(R(vx, vx), appartient(vx, e)))


def est_relation_ordre_dans(R, e, x="x", y="y", z="z"):
    """« R{x,y} relation d'ordre dans l'ensemble E » := relation d'ordre ET réflexive dans E
    (E.III.1.1, Définition)."""
    return et(est_relation_ordre(R, x, y, z), est_reflexive_dans_ordre(R, e, x))


def relation_stricte(R, x="x", y="y"):
    """R{x,y} associée < : x<y := (R{x,y} et x≠y)  (E.III.1.3 ; relation stricte)."""
    return lambda a, b: et(R(a, b), non(egal(a, b)))


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
def est_plus_petit_element(R, e, a, x="x"):
    """« a est le plus petit élément de E » := a∈E et (∀x)(x∈E ⇒ R{a,x})  (E.III.1.7, Déf. 4)."""
    va, vx = _terme_var(a), var(x)
    return et(appartient(va, e), pourtout(x, impl(appartient(vx, e), R(va, vx))))


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


def est_cofinale(R, A, e, x="x", y="y"):
    """« A cofinale à E » := (∀x)(x∈E ⇒ (∃y)(y∈A et R{x,y}))  (E.III.1.8 ; partie cofinale)."""
    vx, vy = var(x), var(y)
    return pourtout(x, impl(appartient(vx, e),
        existe(y, et(appartient(vy, A), R(vx, vy)))))


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


def est_totalement_ordonne(R, e, x="x", y="y", z="z"):
    """« E totalement ordonné » := relation d'ordre dans E ET deux éléments quelconques
    comparables : (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x}))  (E.III.1.12, Déf. 9)."""
    vx, vy = var(x), var(y)
    return et(est_relation_ordre_dans(R, e, x, y, z),
              pourtout(x, pourtout(y, impl(et(appartient(vx, e), appartient(vy, e)),
                  ou(R(vx, vy), R(vy, vx))))))


# ── §III.1.13 — Intervalles ───────────────────────────────────────────────────
# Termes définis par compréhension (sélection S8 dans E, unicité A1).  R notée ≤.
def intervalle_ferme(R, e, a, b):
    """[a, b] := { x∈E | a≤x et x≤b }  (intervalle fermé, E.III.1.13)."""
    return app("interv_ff", e, _terme_var(a), _terme_var(b))


def intervalle_ouvert(R, e, a, b):
    """]a, b[ := { x∈E | a<x et x<b }  (intervalle ouvert, E.III.1.13)."""
    return app("interv_oo", e, _terme_var(a), _terme_var(b))


def intervalle_illimite_gauche_ferme(R, e, a):
    """]←, a] := { x∈E | x≤a }  (intervalle fermé illimité à gauche, E.III.1.13)."""
    return app("interv_ig", e, _terme_var(a))


def intervalle_illimite_droite_ferme(R, e, a):
    """[a, →[ := { x∈E | a≤x }  (intervalle fermé illimité à droite, E.III.1.13)."""
    return app("interv_id", e, _terme_var(a))


# ── §III.5.3 — Intervalle d'entiers [a, b] ────────────────────────────────────
# Spécifique aux ENTIERS : l'ordre ≤ est celui des cardinaux (E.III.3.2), et la
# relation « x est un cardinal et x ≤ a » est collectivisante (E.III.5.3, Remarque
# III.25) ; l'ensemble obtenu est un ensemble d'entiers.  Contrairement aux
# intervalles d'un ordre général (interv_ff…, simples notations), celui-ci porte un
# AXIOME caractérisant (cf. AXIOME_INTERV_ENT), légitimé par S8 (sélection) + A1.
def intervalle_entiers(a, b):
    """[a, b] := { x | x cardinal et a ≤ x et x ≤ b }   (E.III.5.3).

    Intervalle d'entiers : sous-ensemble des cardinaux x avec a ≤ x ≤ b (≤ = ordre
    des cardinaux).  Terme collectivisant (Remarque III.25), caractérisé par
    AXIOME_INTERV_ENT."""
    return app("interv_ent", _terme_var(a), _terme_var(b))


# ── §III.2 — Ensembles bien ordonnés ─────────────────────────────────────────
# (R notée ≤ : R{a,b} = a≤b.  Définitions lues verbatim E.III.2.1 et §2.4.)

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


def segment_extremite(R, e, x):
    """S_x := ]←, x[ = { y∈E | y<x }  (segment d'extrémité x, E.III.2.1).

    Terme collectivisant (sélection S8 dans E, unicité A1) ; caractérisé par
    AXIOME_SEGMENT_EXTREMITE."""
    return app("seg_ext", e, _terme_var(x))


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


# Déf. de P(X) (axiome A3, E.II.5.1 ; existence = axiome A3, unicité = A1) :
#   (∀X)(∀Y)(Y ∈ P(X) ⇔ Y ⊂ X)
# Le liant interne de ⊂ est « z » (cohérent avec inclus/A1).
AXIOME_PARTIES = pourtout("X", pourtout("Y",
        equiv(appartient(_GY, parties(_GX)), inclus(_GY, _GX))))


# Déf. du produit ∏_{ι∈I} X_ι (E.II.5.3, Déf. 1 ; existence par S8 = sélection
# dans P(I×A) avec A=⋃X_ι, unicité par A1, comme produit/image/restriction) :
#   (∀f)(∀I)(∀F)(F ∈ ∏  ⇔  ( F fonctionnel ∧ pr₁F = I ∧ (∀i)(i∈I ⇒ F(i)∈X_i) ))
# Liant universel externe « F », liant interne « i » (index).  X_i = valeur_famille(f, i).
_FF = var("F")
def _corps_produit(ff, f, i):
    vi = var("i")
    return et(et(est_fonctionnel(ff), egal(dom(ff), i)),
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

# Déf. de l'intersection d'une famille ⋂_{ι∈I} X_ι (E.II.4.1, Déf. 2 ; I ≠ ∅) :
#   (∀f)(∀I)(∀z)(z ∈ ⋂_{ι∈I} X_ι ⇔ (∀i)(i∈I ⇒ z∈X_i))
AXIOME_INTER_FAM = pourtout("f", pourtout("I", pourtout("z",
        equiv(appartient(_Z, inter_famille(_F, _I)),
              pourtout("i", impl(appartient(_IDX, _I),
                                 appartient(_Z, valeur_famille(_F, _IDX))))))))


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


# Déf. de S_x = ]←, x[ : (∀E)(∀x)(∀y)(y ∈ S_x ⇔ (y∈E et y<x))   (E.III.2.1)
#   y<x abrégé par « (y≤x) et y≠x » avec R notée ≤ ; ici on prend la forme
#   inconditionnelle sur l'ordre induit : y ∈ S_x ⇔ (y∈E et y≤x et y≠x).
#   Liant interne y, externes E, x.  Légitimé par S8 (sélection dans E) + A1.
def axiome_segment_extremite(R, x="x", y="y", e="E"):
    """⊢-schéma caractérisant S_x = {y∈E | y≤x et y≠x}, paramétré par la relation R."""
    vE, vx, vy = var(e), var(x), var(y)
    return pourtout(e, pourtout(x, pourtout(y,
        equiv(appartient(vy, segment_extremite(R, vE, vx)),
              et(et(appartient(vy, vE), R(vy, vx)), non(egal(vy, vx)))))))


def theorie_segment_extremite(R, x="x", y="y", e="E"):
    """Théorie ne contenant que l'instance de l'axiome caractérisant S_x (E.III.2.1)."""
    return N.Theorie("Segment-extremite", [axiome_segment_extremite(R, x, y, e)])


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
