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

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, impl, appartient, inclus, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, equivalence_avant, instancie)
from bourbaki.ensembles.ii_2_couples_produit.ensembles_couple_caracterisation import (
    est_couple, caracterisation_couple)
from bourbaki.ensembles.familles.ii_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi)
from bourbaki.ensembles.fonctions.ii_3_general.ensembles_extensionnalite import (
    couple_dans_dom)


def _T(v):
    """Coercion nom → terme."""
    return v if isinstance(v, Terme) else var(v)


def est_graphe(g):
    """« G est un ensemble de couples » := (∀z)(z ∈ G ⇒ est_couple(z))  (E II.7/II.37).

    est_couple(z) = (∃a)(∃b)(z = (a, b)) (inline, liants a, b)."""
    vg = _T(g)
    return pourtout("z", impl(appartient(var("z"), vg), est_couple(var("z"))))


def _inst_img(g, y):
    """⊢ (y ∈ pr₂G) ⇔ (∃x)((x,y) ∈ G).   (instance de AXIOME_IMG en G, y.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, g), y)


def couple_dans_img(g, x, y):
    """{(x,y) ∈ G} ⊢ y ∈ pr₂G = img G.   (la 2ᵈᵉ coordonnée d'un couple de G est une
    valeur ; symétrique de couple_dans_dom.  g, x, y : noms OU termes.)"""
    vg, vx, vy = _T(g), _T(x), _T(y)
    car = _inst_img(vg, vy)                                   # (y∈img G)⇔(∃x)((x,y)∈G)
    in_couple = N.assume(appartient(E.couple(vx, vy), vg))    # (x,y)∈G
    exists_x = N.modus_ponens(                                # (∃x)((x,y)∈G), témoin vx
        in_couple, N.s5(appartient(E.couple(var("x"), vy), vg), vx, "x"))
    return N.modus_ponens(exists_x, equivalence_arriere(car))  # y∈img G


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


__all__ = ["est_graphe", "couple_dans_img", "graphe_inclus_produit",
           "graphe_inclus_produit_cible"]
