"""§II.3.1 — Tout ensemble de couples est partie d'un produit (Bourbaki E II.10).

Énoncé Bourbaki VERBATIM (E II.10, §3, n°1) :

  « On vérifie aussitôt que G ⊂ (pr₁G) × (pr₂G) : tout ensemble de couples est
    donc une partie d'un produit. »

RÉSULTAT (CLOS SOUS HYPOTHÈSE HONNÊTE — certifié par le noyau LCF) :

  { est_graphe(G) }  ⊢  G ⊂ (pr₁G) × (pr₂G)

où, pr₁G = dom(G) (ensemble de définition, AXIOME_DOM) et pr₂G = img(G)
(ensemble des valeurs, AXIOME_IMG) sont les projections-ENSEMBLE d'un graphe
(distinctes des projections-COUPLE pr₁z, pr₂z, ici notées E.pr1/E.pr2), et

  est_graphe(G) := (∀z)(z ∈ G ⇒ est_couple(z))   (E II.7 ; Déf. 1 graphe E II.37)
  est_couple(z) := (∃a)(∃b)(z = (a, b))           (« z est un couple », inline)

L'hypothèse « G est un ensemble de couples » est HONNÊTE : elle ne contient pas
la conclusion, et c'est exactement la prémisse de Bourbaki (« tout ensemble de
couples »).  On réutilise le prédicat inline `est_couple` (liants a, b) de la
caractérisation du couple plutôt que `est_un_couple` (liants x, y) afin de rester
disjoint des liants τx/τy des projections-couple E.pr1/E.pr2 et de pouvoir
alimenter directement `caracterisation_couple`.

STRATÉGIE (G ⊂ pr₁G×pr₂G = (∀z)(z∈G ⇒ z∈dom G × img G)).  Soit z, assume z∈G :
  (1) est_graphe(G) instanciée en z donne (z∈G ⇒ est_couple(z)), d'où est_couple(z).
      Via `caracterisation_couple` (x:=E.pr1(z), y:=E.pr2(z)) le sens ⇐ donne la
      DÉCOMPOSITION  z = (pr₁z, pr₂z)  (les égalités pr₁z=pr₁z, pr₂z=pr₂z étant
      des réflexivités).
  (2) z∈G réécrit (S6) en (pr₁z, pr₂z)∈G ; alors `couple_dans_dom` ⇒ pr₁z∈dom G
      et son symétrique (via AXIOME_IMG/_inst_img) ⇒ pr₂z∈img G.
  (3) `couple_dans_produit` : (pr₁z∈dom G et pr₂z∈img G) ⇒ (pr₁z,pr₂z)∈dom G×img G ;
      réécrit (S6, z=(pr₁z,pr₂z)) en z∈dom G×img G.
  (4) loi_deduction(z∈G), generalisation(z) ⇒ G⊂dom G×img G ; on GARDE est_graphe(G)
      comme hypothèse honnête (clôture conditionnelle).

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté (primitives N.* seules,
réutilisation de théorèmes existants).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, non, impl, appartient, inclus, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, equivalence_avant, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    congruence_terme, composer_egalites)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couple_caracterisation import (
    est_couple, caracterisation_couple)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi, produit_vide_si)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom)


def _T(v):
    """Coercion nom → terme."""
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.II §3.1 Def.1 | E II.9 L.9-12 | PDF p.60
def est_graphe(g):
    """« G est un ensemble de couples » := (∀z)(z ∈ G ⇒ est_couple(z))  (E II.7/II.37).

    est_couple(z) = (∃a)(∃b)(z = (a, b)) (inline, liants a, b)."""
    vg = _T(g)
    return pourtout("z", impl(appartient(var("z"), vg), est_couple(var("z"))))


def _inst_img(g, y):
    """⊢ (y ∈ pr₂G) ⇔ (∃x)((x,y) ∈ G).   (instance de AXIOME_IMG en G, y.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, g), y)


# @livre Ch.II §3.1 Prop.1 | E II.9 L.27-29 | PDF p.60
def couple_dans_img(g, x, y):
    """{(x,y) ∈ G} ⊢ y ∈ pr₂G = img G.   (la 2ᵈᵉ coordonnée d'un couple de G est une
    valeur ; symétrique de couple_dans_dom.  g, x, y : noms OU termes.)"""
    vg, vx, vy = _T(g), _T(x), _T(y)
    car = _inst_img(vg, vy)                                   # (y∈img G)⇔(∃x)((x,y)∈G)
    in_couple = N.assume(appartient(E.couple(vx, vy), vg))    # (x,y)∈G
    exists_x = N.modus_ponens(                                # (∃x)((x,y)∈G), témoin vx
        in_couple, N.s5(appartient(E.couple(var("x"), vy), vg), vx, "x"))
    return N.modus_ponens(exists_x, equivalence_arriere(car))  # y∈img G


# @livre Ch.II §3.1 Rem.- | E II.10 L.1-2 | PDF p.61
def graphe_inclus_produit(g="G"):
    """{ est_graphe(G) } ⊢ G ⊂ (pr₁G) × (pr₂G).   (Bourbaki E II.10, §3, n°1.)

    « Tout ensemble de couples est une partie d'un produit. »  Clos SOUS l'hypothèse
    honnête est_graphe(G) (= « G est un ensemble de couples »), conservée non
    déchargée (clôture conditionnelle).  pr₁G = dom(G), pr₂G = img(G)."""
    vg = _T(g)
    vz = var("z")
    pr1z, pr2z = E.pr1(vz), E.pr2(vz)                          # projections-COUPLE de z
    prod = E.produit(E.dom(vg), E.img(vg))                     # (pr₁G) × (pr₂G)

    # ── Hypothèses : est_graphe(G) (gardée) et z∈G (déchargée par déduction) ──────
    h_graphe = N.assume(est_graphe(vg))                        # (∀z)(z∈G ⇒ est_couple(z))
    h_zin = N.assume(appartient(vz, vg))                       # z∈G

    # (1) est_couple(z), puis décomposition z = (pr₁z, pr₂z) ──────────────────────
    ec = N.modus_ponens(h_zin, instancie(h_graphe, vz))       # est_couple(z)
    # caracterisation_couple(pr₁z, pr₂z, z) : (z=(pr₁z,pr₂z)) ⇔ (est_couple(z) et
    #   pr₁z=pr₁z et pr₂z=pr₂z) ; le membre droit suit de est_couple(z) + réflexivités.
    car = caracterisation_couple(pr1z, pr2z, vz)
    droite = conjonction_intro(conjonction_intro(ec, N.reflexivite(pr1z)),
                               N.reflexivite(pr2z))            # est_couple(z) et pr₁z=pr₁z et pr₂z=pr₂z
    z_eq = N.modus_ponens(droite, equivalence_arriere(car))   # z = (pr₁z, pr₂z)

    # (2) (pr₁z, pr₂z)∈G [S6 sur z∈G] ; puis pr₁z∈dom G et pr₂z∈img G ─────────────
    cpl = E.couple(pr1z, pr2z)
    # S6 : (z=cpl) ⇒ ((z∈G) ⇔ (cpl∈G)) ; MP(z_eq) puis sens ⇒ et MP(z∈G).
    zin_iff = N.modus_ponens(z_eq, N.s6(vz, cpl, "w", appartient(var("w"), vg)))
    couple_in = N.modus_ponens(h_zin, equivalence_avant(zin_iff))   # (pr₁z, pr₂z)∈G
    in_dom = N.modus_ponens(couple_in, N.loi_deduction(             # pr₁z∈dom G
        appartient(cpl, vg), couple_dans_dom(vg, pr1z, pr2z)))
    in_img = N.modus_ponens(couple_in, N.loi_deduction(             # pr₂z∈img G
        appartient(cpl, vg), couple_dans_img(vg, pr1z, pr2z)))

    # (3) (pr₁z, pr₂z)∈dom G×img G ; réécrit en z∈dom G×img G [S6, z=cpl] ──────────
    # couple_dans_produit_ssi : ((pr₁z,pr₂z)∈domG×imgG) ⇔ (pr₁z∈domG et pr₂z∈imgG).
    cdp = couple_dans_produit_ssi(pr1z, pr2z, E.dom(vg), E.img(vg))
    couple_in_prod = N.modus_ponens(conjonction_intro(in_dom, in_img),
                                    equivalence_arriere(cdp))
    # S6 : (z=cpl) ⇒ ((z∈prod) ⇔ (cpl∈prod)) ; MP(z_eq) puis sens ⇐ et MP(cpl∈prod).
    zprod_iff = N.modus_ponens(z_eq, N.s6(vz, cpl, "w", appartient(var("w"), prod)))
    z_in_prod = N.modus_ponens(couple_in_prod, equivalence_arriere(zprod_iff))  # z∈prod

    # (4) décharge z∈G, généralise z ; GARDE est_graphe(G) (clôture conditionnelle) ─
    imp = N.loi_deduction(appartient(vz, vg), z_in_prod)      # {est_graphe(G)} ⊢ (z∈G ⇒ z∈prod)
    return N.generalisation("z", imp)                         # {est_graphe(G)} ⊢ G⊂dom G×img G


def graphe_inclus_produit_cible(g="G"):
    """Énoncé visé de `graphe_inclus_produit` (pour vérification stricte)."""
    vg = _T(g)
    return inclus(vg, E.produit(E.dom(vg), E.img(vg)))


# ── Corollaire E II.10 : une projection vide force G = ∅ ───────────────────────
# Bourbaki (E II.10, §3, n°1) : « Si l'un des deux ensembles pr₁G, pr₂G est vide,
# on a donc G = ∅ (II, p. 8, prop. 2). »  C'est l'application immédiate de
# G ⊂ (pr₁G)×(pr₂G) (graphe_inclus_produit) au fait qu'un produit dont un facteur
# est vide est vide (Prop. 2 = E.II.34, ici produit_vide_si), puis « X⊂∅ ⇒ X=∅ ».

def _vide_inclus(t):
    """⊢ ∅ ⊂ T  (le vide inclus dans tout ensemble : z∈∅ ⇒ z∈T par ex falso).

    Motif identique à `ensembles_vide.vide_ssi_sans_element` : de ⊢¬(z∈∅)
    (AXIOME_VIDE), S2 donne ¬(z∈∅)∨(z∈T) = (z∈∅ ⇒ z∈T), puis généralisation."""
    vz = var("z")
    n_in = instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE), vz)   # ¬(z∈∅)
    return N.generalisation("z", N.modus_ponens(
        n_in, N.s2(non(appartient(vz, E.VIDE)), appartient(vz, t))))       # ∅ ⊂ T


def _sous_ensemble_du_vide_est_vide(thm_sub_vide, t):
    """Γ ⊢ T⊂∅  ⟹  Γ ⊢ T=∅.   (∅⊂T toujours, puis extensionnalité A1.)"""
    ext = extensionnalite_appliquee(t, E.VIDE)                  # (T⊂∅ et ∅⊂T) ⇒ T=∅
    return N.modus_ponens(conjonction_intro(thm_sub_vide, _vide_inclus(t)), ext)


def _produit_facteur_vide(autre, gauche):
    """⊢ (A × B) = ∅  où le facteur ∅ est A (gauche=True : ∅×autre) ou B (autre×∅).

    Instance close de `produit_vide_si` (⊢ (A=∅ ou B=∅) ⇒ A×B=∅) : on généralise
    ses variables libres A, B puis on instancie aux termes voulus, et on décharge
    par le disjoint correspondant (∅=∅, par réflexivité, replacé du bon côté)."""
    a, b = (E.VIDE, autre) if gauche else (autre, E.VIDE)
    gen = N.generalisation("B", N.generalisation("A", produit_vide_si("A", "B")))
    inst = instancie(instancie(gen, b), a)                      # (A=∅ ou B=∅) ⇒ A×B=∅
    refl = N.reflexivite(E.VIDE)                                # ∅=∅
    if gauche:                                                  # ∅=∅ ⇒ (∅=∅ ou B=∅)
        disj = N.modus_ponens(refl, N.s2(egal(a, E.VIDE), egal(b, E.VIDE)))
    else:                                                       # ∅=∅ ⇒ (B=∅ ou ∅=∅) ⇒ (A=∅ ou B=∅)
        droite = N.modus_ponens(refl, N.s2(egal(b, E.VIDE), egal(a, E.VIDE)))
        disj = N.modus_ponens(droite, N.s3(egal(b, E.VIDE), egal(a, E.VIDE)))
    return N.modus_ponens(disj, inst)                          # A×B = ∅


# @livre Ch.II §3.1 Cor.- | E II.10 L.2-3 | PDF p.61
def projection_vide_implique_graphe_vide(g="G"):
    """{ est_graphe(G), pr₁G = ∅ } ⊢ G = ∅.   (Corollaire E II.10, §3, n°1.)

    « Si pr₁G = ∅, on a donc G = ∅. »  pr₁G = dom(G).  Clos SOUS les deux
    hypothèses HONNÊTES est_graphe(G) (= « G est un ensemble de couples ») et
    dom(G) = ∅ (la prémisse du corollaire) ; la conclusion G=∅ n'y figure pas.

    STRATÉGIE.  graphe_inclus_produit donne G ⊂ dom(G)×img(G).  Sous dom(G)=∅ :
    dom(G)×img(G) = ∅×img(G) [congruence_terme] = ∅ [produit_vide_si, ∅ absorbant].
    D'où G ⊂ ∅ [S6], puis G=∅ (tout sous-ensemble du vide est vide)."""
    vg = _T(g)
    incl = graphe_inclus_produit(vg)                           # {est_graphe G} ⊢ G⊂dom G×img G
    h_dom = N.assume(egal(E.dom(vg), E.VIDE))                  # dom G = ∅

    # dom G×img G = ∅×img G [congruence] = ∅ [∅ absorbant] ⇒ dom G×img G = ∅
    eq1 = N.modus_ponens(h_dom, congruence_terme(            # dom G×img G = ∅×img G
        E.dom(vg), E.VIDE, E.produit(var("w"), E.img(vg)), "w"))
    eq2 = _produit_facteur_vide(E.img(vg), gauche=True)          # ∅×img G = ∅
    eq_prod = composer_egalites(eq1, eq2)                     # dom G×img G = ∅

    return _conclure_g_vide(vg, incl, eq_prod, E.produit(E.dom(vg), E.img(vg)))


# @livre Ch.II §3.1 Cor.- | E II.10 L.2-3 | PDF p.61
def projection_image_vide_implique_graphe_vide(g="G"):
    """{ est_graphe(G), pr₂G = ∅ } ⊢ G = ∅.   (Corollaire E II.10, duale.)

    « Si pr₂G = ∅, on a donc G = ∅. »  pr₂G = img(G).  Dual de
    `projection_vide_implique_graphe_vide` : sous img(G)=∅, dom(G)×img(G) =
    dom(G)×∅ [congruence] = ∅ [∅ absorbant à droite]."""
    vg = _T(g)
    incl = graphe_inclus_produit(vg)                           # {est_graphe G} ⊢ G⊂dom G×img G
    h_img = N.assume(egal(E.img(vg), E.VIDE))                  # img G = ∅

    eq1 = N.modus_ponens(h_img, congruence_terme(            # dom G×img G = dom G×∅
        E.img(vg), E.VIDE, E.produit(E.dom(vg), var("w")), "w"))
    eq2 = _produit_facteur_vide(E.dom(vg), gauche=False)         # dom G×∅ = ∅
    eq_prod = composer_egalites(eq1, eq2)                     # dom G×img G = ∅

    return _conclure_g_vide(vg, incl, eq_prod, E.produit(E.dom(vg), E.img(vg)))


def _conclure_g_vide(vg, incl, eq_prod, prod):
    """De {Γ ⊢ G⊂prod} et {Δ ⊢ prod=∅}, conclure Γ∪Δ ⊢ G=∅  (réécriture S6 + ∅)."""
    s6 = N.modus_ponens(eq_prod, N.s6(prod, E.VIDE, "w", inclus(vg, var("w"))))
    g_sub_vide = N.modus_ponens(incl, equivalence_avant(s6))   # G ⊂ ∅
    return _sous_ensemble_du_vide_est_vide(g_sub_vide, vg)     # G = ∅


def projection_vide_implique_graphe_vide_cible(g="G"):
    """Énoncé visé du corollaire (pour vérification stricte) : G = ∅."""
    return egal(_T(g), E.VIDE)


__all__ = ["est_graphe", "couple_dans_img", "graphe_inclus_produit",
           "graphe_inclus_produit_cible", "projection_vide_implique_graphe_vide",
           "projection_image_vide_implique_graphe_vide",
           "projection_vide_implique_graphe_vide_cible"]
