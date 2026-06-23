"""§II.6 — Égalité des valeurs R_f, décomposition canonique, quotient R/S.

NOTIONS INTRODUITES (définitions fidèles, E.II.6.2 / E.II.6.5 / E.II.6.7) :

  • **relation d'égalité-des-valeurs R_f associée à f** (E.II.6.2) : pour une
    application f d'ensemble de définition E, R_f{x,y} := « x∈E et y∈E et
    f(x)=f(y) ».  C'est la relation d'équivalence associée à f.  Définition
    réutilisée de `ensembles_abrege.relation_associee_fonction`.

  • **décomposition canonique de f** (E.II.6.5) : f se factorise f = i∘b∘p, où
        – p : E → E/R_f   surjection canonique  (x ↦ Cl_{R_f}(x)) — graphe
          `application_canonique` (E.II.6.2) ;
        – b : E/R_f → f⟨E⟩  bijection induite  (Cl_{R_f}(x) ↦ f(x)) — graphe
          `bijection_induite` défini ici (axiome de membership S8+A1, paramétré) ;
        – i : f⟨E⟩ → F   injection canonique  (y ↦ y) — graphe `injection_canonique`
          = diagonale Δ_{f⟨E⟩} (E.III.3.1).
    L'énoncé `decomposition_canonique` exprime l'égalité de graphes
    F = i∘b∘p  (composée Bourbaki : i∘b∘p applique d'abord p, puis b, puis i).

  • **quotient R/S de deux relations d'équivalence** (E.II.6.7) : lorsque S est
    plus fine que R (S ⇒ R), la relation induite sur E/S : (R/S){t,t'} pour
    t,t'∈E/S est « (∃x)(∃y)(t=Cl_S(x) et t'=Cl_S(y) et R{x,y}) ».  Sur les
    classes, x̄ (R/S) ȳ ⟺ x R y (bien posé car S⊂R).

LEMMES DIRECTS PROUVÉS (noyau abrégé) :
  • R_f est symétrique, transitive, réflexive dans E=dom f — donc une relation
    d'équivalence dans dom f (E.II.6.2, « est une relation d'équivalence dans E ») ;
  • bien-fondé du quotient R/S : sous l'hypothèse « S plus fine que R », S{x,y} ⇒
    R{x,y} (instance directe), socle du « bien défini car S⊂R » de Bourbaki.

REPORTÉ (théorèmes durs) : la factorisation EFFECTIVE f = i∘b∘p (égalité de
graphes prouvée) — elle exige l'injectivité de b déduite par passage au quotient,
la surjectivité de b sur f⟨E⟩, et le calcul de la composée triple sur les graphes
(infra de recollement / valeur de composée). La NOTION est DÉFINIE (prédicat
`decomposition_canonique`), seule sa preuve close est reportée.
"""
from __future__ import annotations

from bourbaki.logique.formule import (Terme, var, app, egal, et, impl, equiv,
                                       appartient, existe, pourtout)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites


def _tv(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
# 1.  Relation d'égalité-des-valeurs R_f associée à une application f (E.II.6.2)
# ════════════════════════════════════════════════════════════════════════════
def relation_egalite_valeurs(f, x="x", y="y"):
    """R_f{x,y} := « x∈E et y∈E et f(x)=f(y) »  (E=dom f), la relation d'équivalence
    associée à f  (E.II.6.2).  Renvoie une fonction (Terme, Terme) → Formule.

    Définition fidèle ; alias documenté de `E.relation_associee_fonction`."""
    return E.relation_associee_fonction(f, x, y)


# ── R_f est une relation d'équivalence dans dom f (lemmes directs) ─────────────
def rf_symetrique(f="f", x="x", y="y"):
    """⊢ R_f symétrique : (∀x)(∀y)(R_f{x,y} ⇒ R_f{y,x})  (E.II.6.2 ; clos).

    De « x∈E et y∈E et f(x)=f(y) » on tire « y∈E et x∈E et f(y)=f(x) » (commutation
    des deux appartenances, symétrie de l'égalité f(x)=f(y) ⇒ f(y)=f(x))."""
    R = relation_egalite_valeurs(f, x, y)
    vx, vy = var(x), var(y)
    vf = _tv(f)
    h = N.assume(R(vx, vy))                       # (x∈E et y∈E) et f(x)=f(y)
    appart = conjonction_elim_gauche(h)           # x∈E et y∈E
    hx = conjonction_elim_gauche(appart)          # x∈E
    hy = conjonction_elim_droite(appart)          # y∈E
    heq = conjonction_elim_droite(h)              # f(x)=f(y)
    heq2 = N.modus_ponens(heq, symetrie(E.valeur(vf, vx), E.valeur(vf, vy)))  # f(y)=f(x)
    but = conjonction_intro(conjonction_intro(hy, hx), heq2)  # (y∈E et x∈E) et f(y)=f(x)
    imp = N.loi_deduction(R(vx, vy), but)
    return N.generalisation(x, N.generalisation(y, imp))


def rf_transitive(f="f", x="x", y="y", z="z"):
    """⊢ R_f transitive : (∀x)(∀y)(∀z)((R_f{x,y} et R_f{y,z}) ⇒ R_f{x,z})  (E.II.6.2 ; clos).

    De f(x)=f(y) et f(y)=f(z) : transitivité de l'égalité → f(x)=f(z) ; x∈E (1er
    conjonct), z∈E (3e conjonct du 2d couple)."""
    R = relation_egalite_valeurs(f, x, y)
    vx, vy, vz = var(x), var(y), var(z)
    vf = _tv(f)
    h = N.assume(et(R(vx, vy), R(vy, vz)))
    hxy = conjonction_elim_gauche(h)              # x∈E et y∈E et f(x)=f(y)
    hyz = conjonction_elim_droite(h)              # y∈E et z∈E et f(y)=f(z)
    hx = conjonction_elim_gauche(conjonction_elim_gauche(hxy))   # x∈E
    hz = conjonction_elim_droite(conjonction_elim_gauche(hyz))   # z∈E
    eq_xy = conjonction_elim_droite(hxy)          # f(x)=f(y)
    eq_yz = conjonction_elim_droite(hyz)          # f(y)=f(z)
    eq_xz = composer_egalites(eq_xy, eq_yz)       # f(x)=f(z)
    but = conjonction_intro(conjonction_intro(hx, hz), eq_xz)
    imp = N.loi_deduction(et(R(vx, vy), R(vy, vz)), but)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, imp)))


def rf_reflexive_dans_dom(f="f", x="x"):
    """⊢ R_f réflexive dans E=dom f : (∀x)(R_f{x,x} ⇔ x∈dom f)  (E.II.6.2 ; clos).

    R_f{x,x} = « x∈E et x∈E et f(x)=f(x) » ; ⇒ donne x∈E (1er conjonct) ; ⇐ : de
    x∈E, on reconstruit x∈E et x∈E (intro) et f(x)=f(x) (réflexivité de =)."""
    R = relation_egalite_valeurs(f, x, x)
    vx = var(x)
    vf = _tv(f)
    E_def = E.dom(vf)
    rxx = R(vx, vx)                               # (x∈E et x∈E) et f(x)=f(x)
    # ⇒ : R_f{x,x} ⇒ x∈E
    h = N.assume(rxx)
    fwd = N.loi_deduction(rxx, conjonction_elim_gauche(conjonction_elim_gauche(h)))
    # ⇐ : x∈E ⇒ R_f{x,x}
    hx = N.assume(appartient(vx, E_def))
    rebuild = conjonction_intro(conjonction_intro(hx, hx),
                                N.reflexivite(E.valeur(vf, vx)))
    bwd = N.loi_deduction(appartient(vx, E_def), rebuild)
    eqv = conjonction_intro(fwd, bwd)             # R_f{x,x} ⇔ x∈E
    return N.generalisation(x, eqv)


def rf_relation_equivalence_dans(f="f", x="x", y="y", z="z"):
    """⊢ R_f est une relation d'équivalence dans dom f  (E.II.6.2 ; clos).

    Assemble : symétrie ∧ transitivité ∧ réflexivité-dans-dom-f (forme
    `est_relation_equivalence_dans` de E.II.6.1)."""
    sym = rf_symetrique(f, x, y)
    trans = rf_transitive(f, x, y, z)
    refl = rf_reflexive_dans_dom(f, x)
    return conjonction_intro(conjonction_intro(sym, trans), refl)


# ════════════════════════════════════════════════════════════════════════════
# 2.  Décomposition canonique f = i ∘ b ∘ p  (E.II.6.5)
# ════════════════════════════════════════════════════════════════════════════
# Les TROIS termes de la décomposition (en tant que GRAPHES) :
#   – p : surjection canonique E → E/R_f       (graphe `application_canonique`)
#   – b : bijection induite  E/R_f → f⟨E⟩      (graphe `bijection_induite`, ci-dessous)
#   – i : injection canonique f⟨E⟩ → F         (graphe `injection_canonique` = Δ)

def surjection_canonique(g, e):
    """Graphe de la surjection canonique p : E → E/R, p(x) = Cl_R(x)  (E.II.6.2).

    C'est l'application canonique de E sur E/R (graphe { (x, Cl_R(x)) | x∈E }) ;
    surjective par construction (toute classe est une valeur)."""
    return E.application_canonique(g, e)


def injection_canonique(b):
    """Graphe de l'injection canonique i : B → F, i(y) = y  (B ⊂ F)  (E.II.6.5).

    L'injection canonique d'une partie B (ici B = f⟨E⟩) dans son sur-ensemble F
    est l'application identique de B ; son graphe est la diagonale Δ_B (E.III.3.1)
    { (y, y) | y∈B }, injective."""
    return E.diagonale(_tv(b))


def bijection_induite(g, e, f):
    """Graphe de la bijection induite b : E/R_f → f⟨E⟩, b(Cl_{R_f}(x)) = f(x)  (E.II.6.5).

    g : graphe de R_f ; e = E (= dom f) ; f : l'application.  Terme défini par son
    axiome de membership (S8+A1, paramétré) : c'est l'application déduite de f par
    passage au quotient suivant R_f, à valeurs dans f⟨E⟩.  Codé par le graphe
    { (Cl_{R_f}(x), f(x)) | x∈E }."""
    return app("bij_induite", g, _tv(e), _tv(f))


def axiome_bijection_induite(g="G", e="E", f="f", w="w", x="x"):
    """⊢-schéma : (∀w)(w ∈ b ⇔ (∃x)(x∈E et w = (Cl_R(x), f(x))))  (membership, S8+A1).

    Caractérise le graphe de la bijection induite b = bijection_induite(G,E,f).
    Existence par S8 (sélection dans (E/R) × f⟨E⟩), unicité par A1 — exactement
    comme AXIOME_APPCANON.  G, E, f sont des PARAMÈTRES."""
    vg, ve, vf = _tv(g), _tv(e), _tv(f)
    vw, vx = var(w), var(x)
    corps = existe(x, et(appartient(vx, ve),
                         egal(vw, E.couple(E.classe(vg, vx), E.valeur(vf, vx)))))
    return pourtout(w, equiv(appartient(vw, bijection_induite(vg, ve, vf)), corps))


def theorie_bijection_induite(g="G", e="E", f="f", w="w", x="x"):
    """Théorie ne contenant que l'instance de l'axiome de la bijection induite."""
    return N.Theorie("Bijection-induite", [axiome_bijection_induite(g, e, f, w, x)])


def membre_bijection_induite(g="G", e="E", f="f", w="w", x="x"):
    """⊢ (w ∈ b) ⇔ (∃x)(x∈E et w = (Cl_R(x), f(x)))  (instance de l'axiome ; clos).

    Théorème de membership pour la bijection induite (sort clos de sa théorie dédiée)."""
    vg, ve, vf, vw = _tv(g), _tv(e), _tv(f), var(w)
    ax = N.axiome(theorie_bijection_induite(g, e, f, w, x),
                  axiome_bijection_induite(g, e, f, w, x))
    return instancie(ax, vw)


def decomposition_canonique(f, g, e, but, x="x"):
    """« f = i ∘ b ∘ p »  (décomposition canonique de f, E.II.6.5) — PRÉDICAT.

    Égalité des GRAPHES : F = i ∘ (b ∘ p), où la composée Bourbaki G'∘G applique
    d'abord G puis G' (E.II.42).  Ici on applique d'abord p (E→E/R_f), puis b
    (E/R_f→f⟨E⟩), puis i (f⟨E⟩→F) :

        F  =  composee( i,  composee( b, p ) )

    avec  p = surjection_canonique(g, e)         (graphe de E→E/R_f) ,
          b = bijection_induite(g, e, f)         (graphe de E/R_f→f⟨E⟩) ,
          i = injection_canonique(f⟨E⟩)          (graphe Δ_{f⟨E⟩}) .

    f : l'application (son GRAPHE est F = graphe de f — ici on prend le paramètre
    F déjà comme graphe) ; g : graphe de R_f ; e : E = dom f ; but : F (codomaine).
    La PREUVE close (factorisation effective) est REPORTÉE (théorèmes durs)."""
    vF = _tv(f)              # graphe de f
    p = surjection_canonique(_tv(g), _tv(e))
    b = bijection_induite(_tv(g), _tv(e), vF)
    i = injection_canonique(E.image(vF, _tv(e)))   # Δ_{f⟨E⟩}, B = f⟨E⟩ = F⟨E⟩
    return egal(vF, E.composee(i, E.composee(b, p)))


# ════════════════════════════════════════════════════════════════════════════
# 3.  Quotient R/S de deux relations d'équivalence (S plus fine que R) (E.II.6.7)
# ════════════════════════════════════════════════════════════════════════════
def relation_quotient_RS(R, S, e=None, t="t", tp="tp", x="x", y="y"):
    """(R/S){t,t'} := la relation induite sur E/S  (E.II.6.7), forme « classe d'objets ».

    Lorsque S est plus fine que R (S ⇒ R), x̄ (R/S) ȳ ⟺ x R y.  Sur les éléments
    t, t' de l'ensemble quotient E/S (codés ici comme classes d'objets θ_S(x),
    θ_S(y) = τ_v(S{·,v}), E.II.6.9) :

        (R/S){t,t'} := (∃x)(∃y)( t = θ_S(x) et t' = θ_S(y) et R{x,y} )

    Renvoie une fonction (Terme, Terme) → Formule (la relation sur E/S).  R, S sont
    des relations (fonctions (Terme,Terme)→Formule) ; lorsque S est donnée par un
    GRAPHE, voir `relation_quotient_RS_graphe` (classes Cl_S(x) = G_S⟨{x}⟩).  Le
    paramètre `e` (= E) est admis mais non requis (la classe d'objets ne le réfère
    pas).  Le quotient « bien défini car S⊂R » est attesté par `quotient_bien_pose`."""
    vx, vy = var(x), var(y)

    def rel(a, b):
        return existe(x, existe(y,
            et(et(egal(a, E.classe_objets(S, vx, y="_y0")),
                  egal(b, E.classe_objets(S, vy, y="_y1"))),
               R(vx, vy))))
    return rel


def relation_quotient_RS_graphe(R, gS, t="t", tp="tp", x="x", y="y"):
    """Variante GRAPHE : (R/S){t,t'} avec S donnée par son graphe gS (Cl_S = G⟨{·}⟩).

        (R/S){t,t'} := (∃x)(∃y)( t = Cl_S(x) et t' = Cl_S(y) et R{x,y} )

    où Cl_S(x) = E.classe(gS, x) = G_S⟨{x}⟩  (E.II.6.2).  R : relation (fonction)."""
    vgS = _tv(gS)
    vx, vy = var(x), var(y)

    def rel(a, b):
        return existe(x, existe(y,
            et(et(egal(a, E.classe(vgS, vx)), egal(b, E.classe(vgS, vy))),
               R(vx, vy))))
    return rel


def quotient_bien_pose(R=None, S=None, x="x", y="y"):
    """{S plus fine que R} ⊢ (∀x)(∀y)(S{x,y} ⇒ R{x,y})  (bien-fondé de R/S, E.II.6.7 ; clos modulo hyp.).

    Socle du « bien défini car S ⊂ R » : « S plus fine que R » signifie exactement
    S ⇒ R (clôture universelle), donc deux représentants S-équivalents sont aussi
    R-équivalents.  C'est l'hypothèse de Bourbaki garantissant que (R/S) ne dépend
    pas des représentants."""
    if R is None:
        R = E.rel_graphe("GR")
    if S is None:
        S = E.rel_graphe("GS")
    hyp = N.assume(E.plus_fine(S, R, x, y))       # (∀x)(∀y)(S{x,y} ⇒ R{x,y})
    return hyp                                    # conclusion = la formule, hyp identique


def quotient_bien_pose_instance(R=None, S=None, a="a", b="b", x="x", y="y"):
    """{S plus fine que R} ⊢ S{a,b} ⇒ R{a,b}  (instance ponctuelle ; E.II.6.7).

    Instance directe (∀∀-élimination) du bien-fondé : si a,b sont S-équivalents,
    ils sont R-équivalents — c'est l'égalité « x̄ (R/S) ȳ ⟺ x R y » lue sur les
    représentants."""
    if R is None:
        R = E.rel_graphe("GR")
    if S is None:
        S = E.rel_graphe("GS")
    va, vb = _tv(a), _tv(b)
    hyp = N.assume(E.plus_fine(S, R, x, y))
    return instancie(instancie(hyp, va), vb)      # S{a,b} ⇒ R{a,b}


__all__ = [
    # 1. R_f
    "relation_egalite_valeurs",
    "rf_symetrique", "rf_transitive", "rf_reflexive_dans_dom",
    "rf_relation_equivalence_dans",
    # 2. décomposition canonique
    "surjection_canonique", "injection_canonique", "bijection_induite",
    "axiome_bijection_induite", "theorie_bijection_induite",
    "membre_bijection_induite", "decomposition_canonique",
    # 3. quotient R/S
    "relation_quotient_RS", "relation_quotient_RS_graphe",
    "quotient_bien_pose", "quotient_bien_pose_instance",
]
