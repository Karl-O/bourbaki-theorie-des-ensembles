"""§II.3 — Neutralité de la correspondance identique pour la composition (E II.13, Déf. 8).

Bourbaki (E II.13, Déf. 8) : « Si Γ est une correspondance entre A et B, Id_A la
correspondance identique de A, [...] on a Γ∘Id_A = Id_B∘Γ = Γ. »

Au niveau des GRAPHES (Γ = (G, A, B), Id_A = (Δ_A, A, A)), composer à droite par
l'identité Δ_A redonne G, dès lors que A contient le domaine de G :

  { est_graphe(G), pr₁G ⊂ A } ⊢ G∘Δ_A = G.

C'est l'aboutissement des briques au niveau du couple
(`couple_composee_diagonale`, `couple_diagonale`) : on les remonte au niveau
ensembliste par double inclusion + extensionnalité A1.

STRATÉGIE.
  · G∘Δ_A ⊂ G  (INCONDITIONNEL) : tout z∈G∘Δ_A est un couple (p,r) [axiome de
    composition] dont la y-étape (p,y)∈Δ_A force y=p [couple_diagonale], d'où
    (p,r)∈G ; donc z∈G.
  · G ⊂ G∘Δ_A  (CONDITIONNEL) : z∈G est un couple (a,b) [est_graphe] ; a∈pr₁G
    [axiome DOM] ⊂ A donne a∈A, et `couple_composee_diagonale` recompose
    (a,b)∈G∘Δ_A ; donc z∈G∘Δ_A.  est_graphe(G) et pr₁G⊂A sont load-bearing.

theorie_ensembles() INCHANGÉE (= 22).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, appartient, existe, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import congruence_terme
from bourbaki.ensembles.ii_3_correspondances.ensembles_graphe_inclus_produit import est_graphe
from bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple import (
    couple_diagonale, couple_composee_diagonale, diagonale_composee_couple)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee


def _tc(t):
    return t if isinstance(t, Terme) else var(t)


def _inst_composee(vGp, vG, z):
    """⊢ (z∈Gp∘G) ⇔ (∃p)(∃r)(z=(p,r) et (∃y)((p,y)∈G et (y,r)∈Gp))."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_COMPOSEE)
    return instancie(instancie(instancie(ax, vGp), vG), z)


def _inst_dom(vG, z):
    """⊢ (z∈pr₁G) ⇔ (∃y)((z,y)∈G)."""
    return instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_DOM), vG), z)


def _inst_img(vG, z):
    """⊢ (z∈pr₂G) ⇔ (∃x)((x,z)∈G)."""
    return instancie(instancie(N.axiome(E.theorie_ensembles(), E.AXIOME_IMG), vG), z)


def _neutre_incluse(vG, vA):
    """⊢ G∘Δ_A ⊂ G   (INCONDITIONNEL)."""
    vz, vp, vr = var("z"), var("p"), var("r")
    C = E.composee(vG, E.diagonale(vA))
    comp = _inst_composee(vG, E.diagonale(vA), vz)        # z∈C ⇔ (∃p)(∃r)(z=(p,r) et (∃y)(...))
    inner = et(appartient(E.couple(vp, var("y")), E.diagonale(vA)),
               appartient(E.couple(var("y"), vr), vG))
    body = et(egal(vz, E.couple(vp, vr)), existe("y", inner))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(hb)                    # z=(p,r)
    # de (∃y)((p,y)∈Δ_A et (y,r)∈G) tirer (p,r)∈G  (y=p par couple_diagonale, Leibniz) :
    h_inner = N.assume(inner)
    p_eq_y = conjonction_elim_droite(N.modus_ponens(conjonction_elim_gauche(h_inner),
        equivalence_avant(couple_diagonale(vp, "y", vA))))                       # p=y
    pr_in_G_i = N.modus_ponens(conjonction_elim_droite(h_inner), equivalence_arriere(
        N.modus_ponens(p_eq_y, N.s6(vp, var("y"), "w", appartient(E.couple(var("w"), vr), vG)))))
    pr_in_G = N.modus_ponens(conjonction_elim_droite(hb),
                             existe_elimination(N.loi_deduction(inner, pr_in_G_i), "y"))  # (p,r)∈G
    z_in_G = N.modus_ponens(pr_in_G, equivalence_arriere(
        N.modus_ponens(z_eq, N.s6(vz, E.couple(vp, vr), "w", appartient(var("w"), vG)))))  # z∈G
    elim = existe_elimination(existe_elimination(N.loi_deduction(body, z_in_G), "r"), "p")
    z_in_G2 = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, C)), equivalence_avant(comp)), elim)
    return N.generalisation("z", N.loi_deduction(appartient(vz, C), z_in_G2))


def _neutre_contient(vG, vA):
    """⊢ G ⊂ G∘Δ_A   sous { est_graphe(G), pr₁G ⊂ A }."""
    vz, va, vb = var("z"), var("a"), var("b")
    C = E.composee(vG, E.diagonale(vA))
    h_graphe = N.assume(est_graphe(vG))                  # (∀z)(z∈G ⇒ (∃a)(∃b)z=(a,b))
    h_dom = N.assume(inclus(E.dom(vG), vA))              # pr₁G ⊂ A
    h_z = N.assume(appartient(vz, vG))                   # z∈G
    ec = N.modus_ponens(h_z, instancie(h_graphe, vz))    # (∃a)(∃b)(z=(a,b))
    h_eq = N.assume(egal(vz, E.couple(va, vb)))          # z=(a,b)
    ab_in_G = N.modus_ponens(h_z, equivalence_avant(
        N.modus_ponens(h_eq, N.s6(vz, E.couple(va, vb), "w", appartient(var("w"), vG)))))  # (a,b)∈G
    a_in_dom = N.modus_ponens(                            # a∈pr₁G (témoin y=b)
        N.modus_ponens(ab_in_G, N.s5(appartient(E.couple(va, var("y")), vG), vb, "y")),
        equivalence_arriere(_inst_dom(vG, va)))
    a_in_A = N.modus_ponens(a_in_dom, instancie(h_dom, va))   # a∈A (pr₁G⊂A)
    ab_in_C = N.modus_ponens(conjonction_intro(a_in_A, ab_in_G),
        equivalence_arriere(couple_composee_diagonale(vG, vA, va, vb)))   # (a,b)∈G∘Δ_A
    z_in_C = N.modus_ponens(ab_in_C, equivalence_arriere(
        N.modus_ponens(h_eq, N.s6(vz, E.couple(va, vb), "w", appartient(var("w"), C)))))  # z∈C
    elim = existe_elimination(existe_elimination(
        N.loi_deduction(egal(vz, E.couple(va, vb)), z_in_C), "b"), "a")
    z_in_C2 = N.modus_ponens(ec, elim)
    return N.generalisation("z", N.loi_deduction(appartient(vz, vG), z_in_C2))


# @livre Ch.II §3.3 Def.8 | E II.13 L.25-26 | PDF p.64
def composee_diagonale_neutre(g="G", a="A"):
    """⊢ G∘Δ_A = G   sous { est_graphe(G), pr₁G ⊂ A }.   (Bourbaki E II.13 : Γ∘Id_A = Γ.)

    g, a : noms OU termes (≠ p, r, y, a, b, z, w, d0 internes)."""
    vG, vA = _tc(g), _tc(a)
    ext = extensionnalite_appliquee(E.composee(vG, E.diagonale(vA)), vG)
    return N.modus_ponens(conjonction_intro(_neutre_incluse(vG, vA), _neutre_contient(vG, vA)), ext)


def composee_diagonale_neutre_cible(g="G", a="A"):
    """Énoncé visé : G∘Δ_A = G."""
    vG, vA = _tc(g), _tc(a)
    return egal(E.composee(vG, E.diagonale(vA)), vG)


# ── DUAL : Id_B∘Γ = Γ  (neutralité à GAUCHE ; Δ_B∘G = G) ──────────────────────
def _neutre_g_incluse(vG, vB):
    """⊢ Δ_B∘G ⊂ G   (INCONDITIONNEL)."""
    vz, vp, vr = var("z"), var("p"), var("r")
    C = E.composee(E.diagonale(vB), vG)
    comp = _inst_composee(E.diagonale(vB), vG, vz)       # z∈Δ_B∘G ⇔ (∃p)(∃r)(z=(p,r) et (∃y)((p,y)∈G et (y,r)∈Δ_B))
    inner = et(appartient(E.couple(vp, var("y")), vG),
               appartient(E.couple(var("y"), vr), E.diagonale(vB)))
    body = et(egal(vz, E.couple(vp, vr)), existe("y", inner))
    hb = N.assume(body)
    z_eq = conjonction_elim_gauche(hb)
    h_inner = N.assume(inner)
    y_eq_r = conjonction_elim_droite(N.modus_ponens(conjonction_elim_droite(h_inner),
        equivalence_avant(couple_diagonale(var("y"), vr, vB))))                  # y=r
    pr_in_G_i = N.modus_ponens(conjonction_elim_gauche(h_inner), equivalence_avant(
        N.modus_ponens(y_eq_r, N.s6(var("y"), vr, "w", appartient(E.couple(vp, var("w")), vG)))))
    pr_in_G = N.modus_ponens(conjonction_elim_droite(hb),
                             existe_elimination(N.loi_deduction(inner, pr_in_G_i), "y"))
    z_in_G = N.modus_ponens(pr_in_G, equivalence_arriere(
        N.modus_ponens(z_eq, N.s6(vz, E.couple(vp, vr), "w", appartient(var("w"), vG)))))
    elim = existe_elimination(existe_elimination(N.loi_deduction(body, z_in_G), "r"), "p")
    z_in_G2 = N.modus_ponens(N.modus_ponens(N.assume(appartient(vz, C)), equivalence_avant(comp)), elim)
    return N.generalisation("z", N.loi_deduction(appartient(vz, C), z_in_G2))


def _neutre_g_contient(vG, vB):
    """⊢ G ⊂ Δ_B∘G   sous { est_graphe(G), pr₂G ⊂ B }."""
    vz, va, vb = var("z"), var("a"), var("b")
    C = E.composee(E.diagonale(vB), vG)
    h_graphe = N.assume(est_graphe(vG))
    h_img = N.assume(inclus(E.img(vG), vB))              # pr₂G ⊂ B
    h_z = N.assume(appartient(vz, vG))
    ec = N.modus_ponens(h_z, instancie(h_graphe, vz))
    h_eq = N.assume(egal(vz, E.couple(va, vb)))
    ab_in_G = N.modus_ponens(h_z, equivalence_avant(
        N.modus_ponens(h_eq, N.s6(vz, E.couple(va, vb), "w", appartient(var("w"), vG)))))
    b_in_img = N.modus_ponens(                            # b∈pr₂G (témoin x=a)
        N.modus_ponens(ab_in_G, N.s5(appartient(E.couple(var("x"), vb), vG), va, "x")),
        equivalence_arriere(_inst_img(vG, vb)))
    b_in_B = N.modus_ponens(b_in_img, instancie(h_img, vb))   # b∈B (pr₂G⊂B)
    ab_in_C = N.modus_ponens(conjonction_intro(ab_in_G, b_in_B),
        equivalence_arriere(diagonale_composee_couple(vG, vB, va, vb)))   # (a,b)∈Δ_B∘G
    z_in_C = N.modus_ponens(ab_in_C, equivalence_arriere(
        N.modus_ponens(h_eq, N.s6(vz, E.couple(va, vb), "w", appartient(var("w"), C)))))
    elim = existe_elimination(existe_elimination(
        N.loi_deduction(egal(vz, E.couple(va, vb)), z_in_C), "b"), "a")
    z_in_C2 = N.modus_ponens(ec, elim)
    return N.generalisation("z", N.loi_deduction(appartient(vz, vG), z_in_C2))


# @livre Ch.II §3.3 Def.8 | E II.13 L.25-26 | PDF p.64
def diagonale_composee_neutre(g="G", b="B"):
    """⊢ Δ_B∘G = G   sous { est_graphe(G), pr₂G ⊂ B }.   (Bourbaki E II.13 : Id_B∘Γ = Γ.)

    Dual de `composee_diagonale_neutre`.  g, b : noms OU termes (≠ internes)."""
    vG, vB = _tc(g), _tc(b)
    ext = extensionnalite_appliquee(E.composee(E.diagonale(vB), vG), vG)
    return N.modus_ponens(conjonction_intro(_neutre_g_incluse(vG, vB), _neutre_g_contient(vG, vB)), ext)


def diagonale_composee_neutre_cible(g="G", b="B"):
    """Énoncé visé : Δ_B∘G = G."""
    vG, vB = _tc(g), _tc(b)
    return egal(E.composee(E.diagonale(vB), vG), vG)


# ── Neutralité au niveau VALEUR (corollaires de Leibniz sous valeur(·, x)) ─────
# @livre Ch.II §3.3 Def.8 | E II.13 L.25-26 (f∘id=f au niveau valeur) | PDF p.64
def composee_diagonale_neutre_valeur(g="G", a="A", x="x"):
    """⊢ (G∘Δ_A)(x) = G(x)   sous { est_graphe(G), pr₁G ⊂ A }.  (Id_A neutre à droite, valeurs.)

    Corollaire de `composee_diagonale_neutre` (G∘Δ_A = G) par congruence de Leibniz
    sous valeur(·, x).  Lève le REPORTÉ « f∘id = f au niveau valeur » (requis §IV.2,
    ensembles_structures_derivees_props)."""
    vG, vA, vx = _tc(g), _tc(a), _tc(x)
    comp = E.composee(vG, E.diagonale(vA))
    neutre = composee_diagonale_neutre(vG, vA)           # G∘Δ_A = G  {est_graphe(G), pr₁G⊂A}
    return N.modus_ponens(neutre, congruence_terme(comp, vG, E.valeur(var("w"), vx)))


def composee_diagonale_neutre_valeur_cible(g="G", a="A", x="x"):
    """Énoncé visé : (G∘Δ_A)(x) = G(x)."""
    vG, vA, vx = _tc(g), _tc(a), _tc(x)
    return egal(E.valeur(E.composee(vG, E.diagonale(vA)), vx), E.valeur(vG, vx))


# @livre Ch.II §3.3 Def.8 | E II.13 L.25-26 (id∘f=f au niveau valeur) | PDF p.64
def diagonale_composee_neutre_valeur(g="G", b="B", x="x"):
    """⊢ (Δ_B∘G)(x) = G(x)   sous { est_graphe(G), pr₂G ⊂ B }.  (Id_B neutre à gauche, valeurs.)

    Dual : corollaire de `diagonale_composee_neutre` (Δ_B∘G = G) par congruence."""
    vG, vB, vx = _tc(g), _tc(b), _tc(x)
    comp = E.composee(E.diagonale(vB), vG)
    neutre = diagonale_composee_neutre(vG, vB)           # Δ_B∘G = G  {est_graphe(G), pr₂G⊂B}
    return N.modus_ponens(neutre, congruence_terme(comp, vG, E.valeur(var("w"), vx)))


def diagonale_composee_neutre_valeur_cible(g="G", b="B", x="x"):
    """Énoncé visé : (Δ_B∘G)(x) = G(x)."""
    vG, vB, vx = _tc(g), _tc(b), _tc(x)
    return egal(E.valeur(E.composee(E.diagonale(vB), vG), vx), E.valeur(vG, vx))


__all__ = ["composee_diagonale_neutre", "composee_diagonale_neutre_cible",
           "diagonale_composee_neutre", "diagonale_composee_neutre_cible",
           "composee_diagonale_neutre_valeur", "composee_diagonale_neutre_valeur_cible",
           "diagonale_composee_neutre_valeur", "diagonale_composee_neutre_valeur_cible"]
